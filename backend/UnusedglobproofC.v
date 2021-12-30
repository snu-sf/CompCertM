Require Import FSets CoqlibC.
From compcertr Require Import
     Maps Ordered Iteration Errors
     Linking
     Memory Globalenvs Events Smallstep
     Op Registers sflib.
Require Import ASTC.
Require Import IntegersC ValuesC.
Require Import RTLC.
From compcertr Require Import Unusedglob.
From compcertr Require SimMemInj.
(** newly added **)
From compcertr Require Export Unusedglobproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SimSymbDrop.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.
Require Import JunkBlock.

Set Implicit Arguments.


Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog tprog: RTL.program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (RTLC.module2 tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link_src (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link_tgt (Mod.sk md_tgt)).
Hypothesis (WFSRC: SkEnv.wf skenv_link_src).
Hypothesis (WFTGT: SkEnv.wf skenv_link_tgt).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (Mod.sk md_src)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (Mod.sk md_tgt)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (Mod.modsem (md_src) skenv_link_src) (Mod.modsem (md_tgt) skenv_link_tgt)
                (SimSymbDrop.mk (((defs prog) -1 (defs tprog) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop) md_src md_tgt)
                sm_link.

Inductive match_states
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Unusedglobproof.match_states prog tprog (used_set tprog) skenv_link_src skenv_link_tgt ge tge st_src0 st_tgt0 sm0).

Lemma find_funct_inject
      used fptr tfptr fd j
      (SIMGE: meminj_preserves_globals prog tprog used ge tge j)
      (FINDSRC: Genv.find_funct ge fptr = Some fd)
      (INJ: Val.inject j fptr tfptr):
    <<FINDTGT: Genv.find_funct tge tfptr = Some fd>>.
Proof.
  inv SIMGE. uge0. des_ifs_safe. inv INJ.
  exploit defs_inject; et. i; des. clarify. psimpl. des_ifs.
Qed.

Theorem sim_skenv_meminj_preserves_globals: forall sm_arg
    (SIMSKENV: SimSymbDrop.sim_skenv
                 sm_arg (SimSymbDrop.mk (((defs prog) -1 (defs tprog) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop) md_src md_tgt)
                 (SkEnv.project skenv_link_src (Mod.sk md_src)) (SkEnv.project skenv_link_tgt (Mod.sk md_tgt))),
    <<SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)>>.
Proof.
  i. inv SIMSKENV. ss. bar.
  destruct TRANSL as [used0 TRANSL0]. desH TRANSL0. clarify. econs; eauto.
  - i. exploit SIMSYMB1; et. i; des. clarify.
  - i. exploit SIMSYMB2; et.
    { ii. des. unfold used_set, defs in *. ss. des_sumbool. align_bool; bsimpl. des_sumbool. des; clarify. }
  - i. unfold ge in H0. exploit Genv_map_defs_def; et. i; des.
    exploit SIMDEF; et. i; des. clarify. psimpl.
    uo. des_ifs_safe. exploit Genv.invert_find_symbol; et. intro SYMBSRC; des.
    exploit SIMSYMB1; et. i; des. psimpl. clear_tac. exploit Genv.find_invert_symbol; et. intro SYMBTGT; des.

    destruct (classic (defs prog i)); cycle 1.
    { clear - Heq1 H1. contradict H1. unfold defs in *. des_sumbool. apply prog_defmap_spec; et. }
    assert(KEPT0: (defs tprog i \/ Pos.eq_dec (prog_main tprog) i)).
    { tauto. }
    clear KEPT.
    assert(IN: (used_set tprog) i).
    { clarify. unfold used_set. repeat (des_sumbool; des; ss; eauto). right. unfold defs in *. des_sumbool; ss. }

    esplits; et.
    + unfold tge, SkEnv.revive. erewrite Genv_map_defs_def_inv; et. uo.
      des_ifs_safe. erewrite match_prog_def; et. des_ifs.
    + i. eapply used_closed; et.
  - unfold tge. i. exploit Genv_map_defs_def; et. i; des. uo. des_ifs. bsimpl.
    exploit SIMDEFINV; et. i; des. clarify. psimpl. clear_tac.
    exploit Genv.invert_find_symbol; et. intro SYMBTGT; des. exploit SIMSYMB3; et. i; des.
    exploit Genv.find_invert_symbol; et. intro SYMBSRC. esplits; et.

    assert(used_set tprog i).
    { hexploit (match_prog_def _ _ _ TRANSL1 i); et. i. des_ifs. }

    exploit SIMSYMB2; et.
    { unfold used_set in *. clear - H1. des_sumbool. ii. des. align_bool; bsimpl. des_sumbool. ss. des; clarify.
      unfold defs in *. des_sumbool. ss. }
    i; des. clarify. clear_tac.

    assert(blk_src = b) by (eapply DISJ; et). clarify.

    unfold ge. unfold SkEnv.revive. erewrite Genv_map_defs_def_inv; et. uo. des_ifs_safe.

    hexploit (match_prog_def _ _ _ TRANSL1 i); et. intro DEFMAP. des_ifs.
Qed.


Let SEGESRC: senv_genv_compat skenv_link_src ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link_tgt tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  destruct TRANSL as [used0 TRANSL0]. des.
  eapply match_states_sim with (match_states := match_states) (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state); eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    inv INITTGT. des. inv SAFESRC. destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    des. eexists.

    exploit SimMemInjC.inject_junk_blocks_tgt; et. intro P; des.
    exists sm1. esplits; eauto; econs; eauto; ss.
    + inv TYP. folder. ss. inv TYP0.
      exploit find_funct_inject; et. i; des. clarify.
      rpapply match_states_call; ss; eauto.
      { econs; ss; et.
        - inv SIMSKENV. ss. eapply SimSymbDrop.sim_skenv_symbols_inject; et.
        - inv SIMSKENV. inv MWF. inv SIMSKELINK. ss. rewrite NBSRC. extlia.
        - inv SIMSKENV. inv MWF. inv SIMSKELINK. ss. rewrite assign_junk_blocks_nextblock.
          rewrite NBTGT. des_ifs; extlia.
      }
      { eapply inject_list_typify_list; eauto. }
      { eapply MWF0. }
  - des. inv SAFESRC. inv SIMARGS; ss.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    exploit find_funct_inject; et. i; des. clarify. inv TYP.
    esplits; eauto. econs; eauto.
    + econs; et. etrans; try apply LEN; et. symmetry. eapply inject_list_length; et. (* TODO: add lemma *)
    + etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    des. clear_tac.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm0)).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    inv MATCH; ss. inv CALLSRC. inv MATCHST; ss. clarify.
    folder. inv MCOMPAT; ss. clear_tac.
    inv FPTR; try (by des; ss). ss. destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero); clarify; try (by des; ss).
    esplits; try refl; eauto.
    + econs; eauto.
      * folder. ss. des_ifs_safe.
        inv SIMGE. uge0. des_ifs_safe. exploit defs_rev_inject; eauto. i; des. clarify. des_ifs_safe. des_ifs.
      * clear EXTERNAL. des. ss. uge0. des_ifs_safe. psimpl. inv SIMSKENV. inv SIMSKELINK. ss.
        exploit SIMDEF; et. i; des. clarify. des_ifs. esplits; et.
    + econs; ss; et.
  - (* after fsim *)
    des. clear_tac.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm0)).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    inv AFTERSRC. inv SIMRET; ss. exists (SimMemInj.unlift' sm_arg sm_ret).
    inv MATCH; ss. inv MATCHST; ss.
    inv HISTORY. ss. clear_tac.
    esplits; try refl; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      inv MLE0; ss. inv MCOMPAT. clear_tac.
      rpapply match_states_return; ss; eauto; ss.
      { eapply match_stacks_bound; eauto with mem. eapply match_stacks_incr; et.
        i. inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; et. }
      { eapply inject_rettypify; et. }
      { eapply MWFAFTR. }

  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv STACKS. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto; try refl. econs; eauto.
  - (* step *)
    left; i.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm0)).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }

    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii.
    hexploit (@step_simulation prog tprog (used_set tprog) skenv_link_src skenv_link_tgt); eauto. i; des.
    esplits; eauto.
    + left. apply plus_one. econs; eauto. eapply modsem2_determinate; eauto.
    + econs; ss; inv H0; ss; inv MCOMPAT; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module2 tprog) (SimSymbDrop.mk (((defs prog) -1 (defs tprog) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop) (RTLC.module prog) (RTLC.module2 tprog)).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - destruct TRANSL as [used0 TRANSL0]. desH TRANSL0. clarify.
    econs; ss.
    + i. ss. inv TRANSL1.
      specialize (match_prog_def id).
      assert(REL0 := (Sk.of_program_prog_defmap prog fn_sig id)).
      assert(REL1 := (Sk.of_program_prog_defmap tprog fn_sig id)).

      destruct (classic (defs prog id)); cycle 1.
      { rewrite <- (Sk.of_program_defs fn_sig) in H. inv REL0; align_opt; cycle 1.
        { exploit prog_defmap_image; et. i; des. unfold defs in *.
          align_bool; bsimpl. align_bool. des_sumbool. ss. }
        unfold fundef in *. rewrite H1 in *. inv REL1; align_opt; ss; clarify. des_ifs.
      }

      assert(KEPT0: defs tprog id \/ Pos.eq_dec (prog_main tprog) id) by tauto. clear KEPT.

      assert(IN: used_set tprog id).
      { unfold used_set. des_sumbool. ss. des; et; bsimpl.
        - right. unfold defs in *. des_sumbool. ss.
        - des_sumbool. clarify. tauto. }

      des_ifs. unfold fundef in *. rewrite match_prog_def in *.
      erewrite (Sk.of_program_prog_defmap_eq fn_sig prog tprog) in *; ss.

    + i. ss. inv TRANSL1.
      specialize (match_prog_def id).
      assert(REL0 := (Sk.of_program_prog_defmap prog fn_sig id)).
      assert(REL1 := (Sk.of_program_prog_defmap tprog fn_sig id)).

      des. align_bool; bsimpl. align_bool. des_sumbool. inv REL1; ss; align_opt.
      rewrite <- (Sk.of_program_defs fn_sig) in DROP1.
      exploit prog_defmap_image; et. i; des. unfold defs in *; ss. des_sumbool. ss.

    + ii. unfold privs. bsimpl. des. bsimpl. des_sumbool.
      rewrite (Sk.of_program_defs fn_sig). split; ss.
      unfold NW. align_bool; bsimpl. des_sumbool. ii.

      exploit used_public; et. intro IN. unfold used_set, defs in *. des_sumbool. ss. des; clarify; ss.

    + inv TRANSL1; ss.

    + inv TRANSL1; ss.
    + ii. des. inv TRANSL0.
      assert(PROG0: (prog_defmap tprog) ! id = Some (Gvar gv)).
      { generalize (Sk.of_program_prog_defmap tprog fn_sig id). intro REL.
       (* TODO: make lemma!!!!!!!!!!!!!!!!!!! *)
        inv REL; try congruence. rewrite PROG in *. clarify. inv H2. inv H4. ss. destruct i1, i2; ss.
      }
      inv TRANSL1. rewrite match_prog_def in *. des_ifs.
      exploit (used_closed id); et. ii. exploit used_defined; et. i; des.
      { exploit prog_defmap_dom; et. i; des. specialize (match_prog_def id_drop). des_ifs. rewrite H2 in *.
        unfold defs in DROP1. apply DROP1. des_sumbool. eapply prog_defmap_image; et. }
      { clarify. apply DROP0. des_sumbool. ss. }
    + inv TRANSL1. eapply NoDup_norepet; et. rewrite Sk.of_program_defs_names; ss.
    + ii. des. eapply H0. des_sumbool. inv TRANSL1. eauto.
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.
