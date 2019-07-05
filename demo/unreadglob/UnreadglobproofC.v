Require Import FSets CoqlibC Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import IntegersC ValuesC Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC.
Require Import Unreadglob.
Require Import sflib.
Require SimMemInjInv.
(** newly added **)
Require Export Unreadglobproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjInvC.
Require SimSymbDropInv.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.
Require Import JunkBlock.

Set Implicit Arguments.



Let SM := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv SimMemInjInv.top_inv.
Local Existing Instance SM.

Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: RTL.program.
Variable tprog: RTL.program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (RTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link_src md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link_tgt md_tgt.(Mod.sk)).
Hypothesis (WFSRC: SkEnv.wf skenv_link_src).
Hypothesis (WFTGT: SkEnv.wf skenv_link_tgt).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src.(Mod.modsem) skenv_link_src) (md_tgt.(Mod.modsem) skenv_link_tgt)
                ((prog.(defs) -1 tprog.(defs) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop)
                sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Unreadglobproof.match_states prog tprog (used_set tprog) skenv_link_src skenv_link_tgt ge tge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(RTL.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(RTL.get_mem) = sm0.(SimMem.tgt))
.

Lemma find_funct_inject
      invar used fptr tfptr fd j
      (SIMGE: meminj_preserves_globals prog tprog used ge tge invar j)
      (FINDSRC: Genv.find_funct ge fptr = Some fd)
      (INJ: Val.inject j fptr tfptr)
  :
    <<FINDTGT: Genv.find_funct tge tfptr = Some (transf_fundef (transf_function (fun _ i => filter_instr used i)) fd)>>
.
Proof.
  inv SIMGE.
  uge0. des_ifs_safe.
  inv INJ.
  exploit defs_inject; et. i; des. clarify. psimpl. des_ifs.
Qed.

Theorem sim_skenv_meminj_preserves_globals
        sm_arg
        (SIMSKENV:
           SimSymbDropInv.sim_skenv
             sm_arg ((prog.(defs) -1 tprog.(defs) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop)
             (SkEnv.project skenv_link_src md_src.(Mod.sk)) (SkEnv.project skenv_link_tgt md_tgt.(Mod.sk)))
  :
    <<SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm_arg) (SimMemInj.inj sm_arg.(SimMemInjInv.minj))>>
.
Proof.
  exploit SkEnv.project_revive_precise; et.
  { eapply SkEnv.project_impl_spec; et. eapply INCLSRC. }
  { ss. }
  intro GESRC.

  inv SIMSKENV. ss. bar.
  destruct TRANSL as [used0 TRANSL0]. desH TRANSL0. clarify.
  econs.
  - i. exploit SIMSYMB1; et. i; des. clarify. esplits; eauto.
    unfold used_set. des_sumbool. ss. apply not_and_or in KEPT. des; eauto.
    + apply not_and_or in KEPT. des; eauto.
      { exfalso. apply KEPT. inv GESRC. exploit SYMB2P; eauto. }
      { right. apply NNPP in KEPT. unfold defs in KEPT. des_sumbool. ss. }
    + left. apply NNPP in KEPT. des_sumbool. ss.
  - i. exploit SIMSYMB2; et.
    { ii. des. unfold used_set in *. ss. des_sumbool.
      align_bool; bsimpl. des_sumbool.
      des; clarify.
      unfold defs in *. des_sumbool. ss.
    }
  - eauto.
  - ii. dup H0. eapply Genv.find_invert_symbol in H0.
    inv TRANSL1. ss. inv TRANSL0. ss. specialize (match_prog_def id). des_ifs.
    hexploit (SSINV id); eauto. splits.
    + inv GESRC. ss. eapply SYMB2P; eauto.
    + ii. eapply defs_prog_defmap in H2. des. clarify.
    + unfold proj_sumbool in *. rewrite match_prog_main in *. des_ifs.
  - i. unfold ge in H0. exploit Genv_map_defs_def; et. i; des.
    exploit SIMDEF; et. i; des. clarify. psimpl.
    uo. des_ifs_safe.
    exploit Genv.invert_find_symbol; et. intro SYMBSRC; des.
    exploit SIMSYMB1; et. i; des. psimpl. clear_tac.
    exploit Genv.find_invert_symbol; et. intro SYMBTGT; des.

    destruct (classic (defs prog i)); cycle 1.
    { clear - Heq1 H1. contradict H1. unfold defs in *. des_sumbool. apply prog_defmap_spec; et. }
    assert(KEPT0: (defs tprog i \/ Pos.eq_dec (prog_main tprog) i)).
    { tauto. }
    clear KEPT.
    assert(IN: (used_set tprog) i).
    { clarify. unfold used_set. des_sumbool. ss. des; des_sumbool; eauto. right.
      unfold defs in KEPT0. des_sumbool. ss.
    }

    esplits; et.
    + unfold tge.
      unfold SkEnv.revive.
      erewrite Genv_map_defs_def_inv; et.
      uo. des_ifs_safe.
      erewrite match_prog_def; et. rewrite Heq1. ss. des_ifs_safe.
      (* exploit IS.mem_1; et. i; clarify. *)
    + i. eapply used_closed; et.
  - unfold tge. i.
    exploit Genv_map_defs_def; et. i; des.
    uo. des_ifs. bsimpl.
    exploit SIMDEFINV; et. i; des. clarify. psimpl. clear_tac.
    exploit Genv.invert_find_symbol; et. intro SYMBTGT; des.
    exploit SIMSYMB3; et. i; des.
    exploit Genv.find_invert_symbol; et. intro SYMBSRC.

    assert(used_set tprog i).
    { hexploit (match_prog_def _ _ _ TRANSL1 i); et. i. des_ifs. }

    exploit SIMSYMB2; et.
    { unfold used_set in *. clear - H1. des_sumbool.
      ii. des. align_bool; bsimpl. des_sumbool. ss. des; clarify.
      unfold defs in *. des_sumbool. ss.
    }
    i; des.
    clarify. clear_tac.

    assert(blk_src = b).
    { eapply DISJ; et. }
    clarify.

    unfold ge.
    unfold SkEnv.revive.
    erewrite Genv_map_defs_def_inv; et.
    uo.
    des_ifs_safe.

    hexploit (match_prog_def _ _ _ TRANSL1 i); et. intro DEFMAP. des_ifs_safe. unfold option_map in *.
    des_ifs_safe.
    esplits; et.
  - eauto.
Qed.


Let SEGESRC: senv_genv_compat skenv_link_src ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link_tgt tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  destruct TRANSL as [used0 TRANSL0]. des.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    inv INITTGT. ss.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm_arg) (SimMemInj.inj sm_arg.(SimMemInjInv.minj))).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    des.
    esplits; eauto.
    + refl.
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.


        inv TYP.
        exploit find_funct_inject; et. i; des. clarify.
        rpapply match_states_call; ss; eauto.
        { econs; ss; et.
          - inv SIMSKENV. ss. eapply SimSymbDropInv.sim_skenv_symbols_inject; et.
          - inv SIMSKENV. inv MWF. inv WF. inv SIMSKELINK. ss. etrans; eauto. etrans; eauto. rewrite NBSRC. refl. 
          - inv SIMSKENV. inv MWF. inv WF. inv SIMSKELINK. ss. etrans; eauto. etrans; eauto. rewrite NBTGT. refl. 
        }
        { eapply inject_list_typify_list; eauto. }
        { eapply MWF. }
  - des. inv SAFESRC.
    inv SIMARGS; ss.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm_arg) (SimMemInj.inj sm_arg.(SimMemInjInv.minj))).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    exploit find_funct_inject; et. i; des. clarify.
    inv TYP.
    esplits; eauto. econs; eauto.
    + (* TODO: add lemma *)
      econs; et.
      etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
    + etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    des. clear_tac.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm0) (SimMemInj.inj sm0.(SimMemInjInv.minj))).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    inv MATCH; ss.
    inv CALLSRC. inv MATCHST; ss. clarify.
    folder.
    inv MCOMPAT; ss. clear_tac.
    inv FPTR; try (by des; ss).
    ss. destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero); clarify; try (by des; ss).
    esplits; try refl; eauto.
    + econs; eauto.
      * folder.
        ss. des_ifs_safe.
        inv SIMGE. uge0. des_ifs_safe. exploit defs_rev_inject; eauto. i; des. clarify. des_ifs_safe. des_ifs.
      * clear EXTERNAL. des. ss. uge0. des_ifs_safe.
        psimpl.
        inv SIMSKENV. inv SIMSKELINK. ss.
        exploit SIMDEF; et. i; des. clarify. des_ifs. esplits; et.
    + econs; ss; et.
  - (* after fsim *)
    des. clear_tac.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm0) (SimMemInj.inj sm0.(SimMemInjInv.minj))).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }
    inv AFTERSRC.
    inv SIMRET. ss. exists (SimMemInjInvC.unlift' sm_arg sm_ret).
    inv MATCH; ss. inv MATCHST; ss.
    inv HISTORY. ss. clear_tac.
    esplits; try refl; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      inv MLE0; ss. inv MLE1; ss.
      inv MCOMPAT. clear_tac.
      rpapply match_states_return; ss; eauto; ss.
      { eapply match_stacks_bound; et; cycle 1.
        { eauto with mem. }
        { eauto with mem. }
        eapply match_stacks_incr; et.
        { i. inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; et. }
      }
      { eapply inject_typify; et. }
      { eapply MWF. }

  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto. refl.
  - (* step *)
    left; i.
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInjInv.mem_inv_src sm0) (SimMemInj.inj sm0.(SimMemInjInv.minj))).
    { eapply sim_skenv_meminj_preserves_globals; et. apply SIMSKENV. }

    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@step_simulation prog tprog (used_set tprog) skenv_link_src skenv_link_tgt); eauto.
    i; des.
    esplits; eauto.
    + left. apply plus_one. econs; eauto. eapply modsem2_determinate; eauto.
    + econs; ss.
      * inv H0; ss; inv MCOMPAT; ss.
      * inv H0; ss; inv MCOMPAT; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) ((prog.(defs) -1 tprog.(defs) -1 (Pos.eq_dec tprog.(prog_main))): ident -> Prop)
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - destruct TRANSL as [used0 TRANSL0]. desH TRANSL0. clarify.
    econs; ss.
    + i. ss. inv TRANSL1.
      specialize (match_prog_def id).
      generalize (Sk.of_program_prog_defmap prog fn_sig id). intro REL0.
      generalize (Sk.of_program_prog_defmap tprog fn_sig id). intro REL1.

      destruct (classic (defs prog id)); cycle 1.
      {
        rewrite <- (Sk.of_program_defs fn_sig) in H.
        inv REL0; align_opt; cycle 1.
        { exploit prog_defmap_image; et. i; des. unfold defs in *. align_bool; bsimpl. align_bool. des_sumbool. ss. }
        unfold fundef in *.
        rewrite H1 in *.
        inv REL1; align_opt; ss; clarify.
        des_ifs.
      }

      assert(KEPT0: defs tprog id \/ Pos.eq_dec (prog_main tprog) id).
      { tauto. }
      clear KEPT.

      assert(IN: used_set tprog id).
      { unfold used_set. des_sumbool. ss. des; et; bsimpl.
        - right. unfold defs in *. des_sumbool. ss.
        - des_sumbool. clarify. tauto.
      }

      des_ifs.
      unfold fundef in *. rewrite match_prog_def in *.
      unfold option_map in *. des_ifs; cycle 1.
      { unfold defs in *. des_sumbool. apply prog_defmap_spec in H. des; clarify. }
      inv REL1. inv REL0.
      destruct g; ss.
      * destruct f; ss.
        { inv H2; ss. des_ifs. inv H4; ss. des_ifs. }
        { inv H2; ss. des_ifs. inv H4; ss. des_ifs. des_sumbool. clarify. }
      * { inv H2; ss. des_ifs. inv H4; ss. des_ifs. inv H5; inv H2; ss. repeat f_equal. destruct i2, i3; ss. }

    + i. ss. inv TRANSL1.
      specialize (match_prog_def id).
      generalize (Sk.of_program_prog_defmap prog fn_sig id). intro REL0.
      generalize (Sk.of_program_prog_defmap tprog fn_sig id). intro REL1.

      des. align_bool; bsimpl. align_bool. des_sumbool.
      inv REL1; ss; align_opt.
      rewrite <- (Sk.of_program_defs fn_sig) in DROP1.
      exploit prog_defmap_image; et. i; des. unfold defs in *; ss. des_sumbool. ss.

    + ii. unfold privs. bsimpl. des. bsimpl. des_sumbool.
      rewrite (Sk.of_program_defs fn_sig). split; ss.
      unfold NW. align_bool; bsimpl. des_sumbool.
      ii.

      exploit used_public; et. intro IN. unfold used_set in IN. des_sumbool. ss. des; clarify; ss.
      unfold defs in *. des_sumbool. ss.

    + inv TRANSL1; ss.

    + inv TRANSL1; ss.
    + ii. des.
      inv TRANSL0.
      assert(PROG0: (prog_defmap tprog) ! id = Some (Gvar gv)).
      {
        (* TODO: make lemma!!!!!!!!!!!!!!!!!!! *)
        generalize (Sk.of_program_prog_defmap tprog fn_sig id). intro REL.
        inv REL; try congruence.
        rewrite PROG in *. clarify.
        inv H2. inv H4. ss. destruct i1, i2; ss.
      }
      inv TRANSL1.
      rewrite match_prog_def in *. des_ifs.
      unfold option_map in PROG0. des_ifs. unfold map_globdef in H1. des_ifs.
      exploit (used_closed id); et. ii.
      exploit used_defined; et. i; des.
      { exploit prog_defmap_dom; et. i; des. specialize (match_prog_def id_drop). des_ifs. rewrite H2 in *.
        unfold defs in DROP1. apply DROP1. des_sumbool. eapply prog_defmap_image; et.
      }
      { clarify. apply DROP0. des_sumbool. ss. }
    + inv TRANSL1. eapply NoDup_norepet; et. rewrite Sk.of_program_defs_names; ss.
    + ii. des. eapply H0. des_sumbool. inv TRANSL1. eauto.
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.
