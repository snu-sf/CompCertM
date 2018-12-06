Require Import FSets CoqlibC Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import IntegersC ValuesC Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC.
Require Import Unusedglob.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export Unusedglobproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SimSymbDrop.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.
Local Existing Instance Val.mi_normal.









(* TODO: move to CoqlibC *)
Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *;
                   (repeat match goal with
                           | [ H: true <> true |- _ ] => tauto
                           | [ H: false <> false |- _ ] => tauto
                           | [ H: true <> _ |- _ ] => symmetry in H
                           | [ H: false <> _ |- _ ] => symmetry in H
                           | [ H: _ <> true |- _ ] => apply not_true_is_false in H
                           | [ H: _ <> false |- _ ] => apply not_false_is_true in H
                           end);
                   autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.











Definition from_list (ids: list ident): IS.t :=
  fold_right (fun i s => IS.add i s) IS.empty ids
.

Lemma from_list_spec
      x xs
  :
    IS.In x (from_list xs) <-> In x xs
.
Proof.
  unfold from_list.
  split; i.
  - ginduction xs; ii; ss.
    { rewrite ISF.empty_iff in *. ss. }
    rewrite ISF.add_iff in *. des; et.
  - ginduction xs; ii; ss.
    rewrite ISF.add_iff in *. des; et.
Qed.

Fixpoint list_diff X (dec: (forall x0 x1, {x0 = x1} + {x0 <> x1})) (xs0 xs1: list X): list X :=
  match xs0 with
  | [] => []
  | hd :: tl =>
    if in_dec dec hd xs1
    then list_diff dec tl xs1
    else hd :: list_diff dec tl xs1
  end
.

Lemma list_diff_spec
      X dec (xs0 xs1 xs2: list X)
      (DIFF: list_diff dec xs0 xs1 = xs2)
  :
    <<SPEC: forall x0, In x0 xs2 <-> (In x0 xs0 /\ ~ In x0 xs1)>>
.
Proof.
  subst.
  split; i.
  - ginduction xs0; ii; des; ss.
    des_ifs.
    { exploit IHxs0; et. i; des. esplits; et. }
    ss. des; clarify.
    { tauto. }
    exploit IHxs0; et. i; des. esplits; et.
  - ginduction xs0; ii; des; ss.
    des; clarify; des_ifs; ss; try tauto.
    { exploit IHxs0; et. }
    { exploit IHxs0; et. }
Qed.





Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge: RTL.genv := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge: RTL.genv := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem skenv_link_src prog) (RTLC.modsem skenv_link_tgt tprog)
                ((prog.(defs) -1 tprog.(defs) -1 (fun id => Pos.eq_dec id tprog.(prog_main))): ident -> Prop)
                sm_link
.

(* Definition used: IS.t := from_list (prog.(prog_defmap).(PTree.elements)) *)

(* Definition used: ident -> bool := fun id => in_dec Pos.eq_dec id (tprog.(prog_defs_names)). *)



(* Definition used: IS.t := *)
(*   (* from_list (list_diff Pos.eq_dec (prog.(prog_defs_names)) (tprog.(prog_defs_names))) *) *)
(*   from_list (tprog.(prog_defs_names)) *)
(* . *)


(* TODO: Add bsimpl/des_sumbool this functionality (not_true_is_false) --> "A <> true |= A = false" and "A <> false |= A = true" *)

(* Lemma used_spec *)
(*       id *)
(*   : *)
(*     <<KEPT: kept used id>> <-> <<SPEC: defs tprog id>> *)
(* . *)
(* Proof. *)
(*   unfold used, kept. ss. *)
(* Qed. *)

(* Definition used': option IS.t := used_globals prog (prog_defmap prog). *)

(* Lemma used'_spec *)
(*       id *)
(*       used'' *)
(*       (SOME: used' = Some used'') *)
(*   : *)
(*     <<KEPT: kept used'' id>> <-> <<SPEC: defs tprog id>> *)
(* . *)
(* Proof. *)
(*   unfold used', kept in *. ss. *)
(*   unfold defs. unfold NW. *)
(*   split; i; r; des. *)
(*   - rewrite from_list_spec in *. *)
(*     des_sumbool. ss. *)
(*   - rewrite from_list_spec in *. *)
(*     des_sumbool. ss. *)
(* Qed. *)

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Unusedglobproof.match_states prog tprog (used_set tprog) ge tge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(RTLC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(RTLC.get_mem) = sm0.(SimMem.tgt))
.

(* Theorem make_match_genvs : *)
(*   SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) -> *)
(*   Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge. *)
(* Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. { ii. clarify. u. des_ifs. } Qed. *)

(* Theorem make_match_genvs : *)
(*   SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) -> *)
(*   Genv.match_genvs (match_globdef (fun (ctx: AST.program fundef type) f tf => transf_fundef f = OK tf) eq prog) ge tge /\ prog_comp_env prog = prog_comp_env tprog. *)
(* Proof. *)
(*   subst_locals. ss. *)
(*   rr in TRANSL. destruct TRANSL. r in H. *)
(*   esplits. *)
(*   - eapply SimSymbId.sim_skenv_revive; eauto. *)
(*     { ii. u. unfold transf_fundef, bind in MATCH. des_ifs; ss; clarify. } *)
(*   - hexploit (prog_comp_env_eq prog); eauto. i. *)
(*     hexploit (prog_comp_env_eq tprog); eauto. i. *)
(*     ss. congruence. *)
(* Qed. *)

Lemma find_funct_inject
      used fptr tfptr fd j
      (SIMGE: meminj_preserves_globals prog tprog used ge tge j)
      (FINDSRC: Genv.find_funct ge fptr = Some fd)
      (INJ: Val.inject j fptr tfptr)
  :
    <<FINDTGT: Genv.find_funct tge tfptr = Some fd>>
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
           SimSymbDrop.sim_skenv
             sm_arg ((prog.(defs) -1 tprog.(defs) -1 (fun id => Pos.eq_dec id tprog.(prog_main))): ident -> Prop)
             (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)))
  :
    <<SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)>>
.
Proof.
  inv SIMSKENV. ss. bar.
  destruct TRANSL as [used0 TRANSL0]. desH TRANSL0. clarify.
  econs.
  - i. exploit SIMSYMB1; et. i; des. clarify.
  - i. exploit SIMSYMB2; et.
    { ii. des. unfold used_set in *. ss. des_sumbool.
      bsimpl. des_sumbool.
      des; clarify.
      unfold defs in *. des_sumbool. ss.
    }
  - eauto.
  - i. unfold ge in H0. exploit Genv_map_defs_def; et. i; des.
    exploit SIMDEF; et. i; des. clarify. psimpl.
    Ltac uo := unfold o_bind, o_map, o_join in *.
    uo. des_ifs_safe.
    exploit Genv.invert_find_symbol; et. intro SYMBSRC; des.
    exploit SIMSYMB1; et. i; des. psimpl. clear_tac. 
    exploit Genv.find_invert_symbol; et. intro SYMBTGT; des.

    (* assert(KEPT0: ~defs prog i \/ (defs tprog i \/ Pos.eq_dec i (prog_main tprog))). *)
    (* { tauto. } *)
    (* clear KEPT. *)
    (* + clear - Heq1 KEPT0. contradict KEPT0. unfold defs in *. des_sumbool. apply prog_defmap_spec; et. *)

    destruct (classic (defs prog i)); cycle 1.
    { clear - Heq1 H1. contradict H1. unfold defs in *. des_sumbool. apply prog_defmap_spec; et. }
    assert(KEPT0: (defs tprog i \/ Pos.eq_dec i (prog_main tprog))).
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
      erewrite match_prog_def; et. des_ifs.
      (* exploit IS.mem_1; et. i; clarify. *)
    + i. eapply used_closed; et.
  - unfold tge. i.
    exploit Genv_map_defs_def; et. i; des.
    uo. des_ifs. bsimpl.
    exploit SIMDEFINV; et. i; des. clarify. psimpl. clear_tac.
    exploit Genv.invert_find_symbol; et. intro SYMBTGT; des.
    exploit SIMSYMB3; et. i; des.
    exploit Genv.find_invert_symbol; et. intro SYMBSRC.
    esplits; et.

    assert(used_set tprog i).
    { hexploit (match_prog_def _ _ _ TRANSL1 i); et. i. des_ifs. }

    exploit SIMSYMB2; et.
    { unfold used_set in *. clear - H1. des_sumbool.
      ii. des. bsimpl. des_sumbool. ss. des; clarify.
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

    hexploit (match_prog_def _ _ _ TRANSL1 i); et. intro DEFMAP. des_ifs.
  - eauto.
Qed.

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
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    (* exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des. *)
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. }
    des.
    eexists. exists sm_arg.
    esplits; eauto.
    { refl. }
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.


        inv TYP.
        exploit find_funct_inject; et. i; des. clarify.
        rpapply match_states_call; ss; eauto.
        { econs; ss; et.
          - admit "ez - genb".
          - admit "ez - genb".
        }
        {
          admit "ez".
        }
        { eapply MWF. }
  - des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    (* exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des. *)
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. }
    exploit find_funct_inject; et. i; des. clarify.
    (* exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder. *)
    (* hexploit (@sim_external_inject_eq_fsim); try apply FINDF; eauto. clear FPTR. intro FPTR. *)
    (* unfold transf_function, bind in *. des_ifs. *)
    (* unfold bind in *. des_ifs. *)
    inv TYP.
    esplits; eauto. econs; eauto.
    + (* TODO: add lemma *)
      econs; et.
      etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
    + etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    admit "".
  - (* after fsim *)
    admit "".
  - (* final fsim *)
    admit "".
  - (* step *)
    assert(SIMGE: meminj_preserves_globals prog tprog (used_set tprog) ge tge (SimMemInj.inj sm0)).
    { eapply sim_skenv_meminj_preserves_globals; et. }

    esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog tprog (used_set tprog)); eauto.
    i; des.
    esplits; eauto.
    + left. apply plus_one. econs; eauto. eapply modsem_determinate; eauto.
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
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) ((prog.(defs) -1 tprog.(defs) -1 (fun id => Pos.eq_dec id tprog.(prog_main))): ident -> Prop)
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
        { exploit prog_defmap_image; et. i; des. unfold defs in *. bsimpl. des_sumbool. ss. }
        unfold fundef in *.
        rewrite H1 in *.
        inv REL1; align_opt; ss; clarify.
        des_ifs.
      }

      assert(KEPT0: defs tprog id \/ Pos.eq_dec id (prog_main tprog)).
      { tauto. }
      clear KEPT.

      assert(IN: used_set tprog id).
      { unfold used_set. des_sumbool. ss. des; et; bsimpl.
        - right. unfold defs in *. des_sumbool. ss.
        - des_sumbool. clarify. tauto.
      }

      des_ifs.
      unfold fundef in *. rewrite match_prog_def in *.
      erewrite (Sk.of_program_prog_defmap_eq fn_sig prog tprog) in *; ss.

    + i. ss. inv TRANSL1.
      specialize (match_prog_def id).
      generalize (Sk.of_program_prog_defmap prog fn_sig id). intro REL0.
      generalize (Sk.of_program_prog_defmap tprog fn_sig id). intro REL1.

      des. bsimpl. des_sumbool.
      inv REL1; ss; align_opt.
      rewrite <- (Sk.of_program_defs fn_sig) in DROP1.
      exploit prog_defmap_image; et. i; des. unfold defs in *; ss. des_sumbool. ss.

    + ii. unfold privs. bsimpl. des. bsimpl. des_sumbool.
      rewrite (Sk.of_program_defs fn_sig). split; ss.
      unfold NW. bsimpl. des_sumbool.
      ii.

      exploit used_public; et. intro IN. unfold used_set in IN. des_sumbool. ss. des; clarify; ss.
      unfold defs in *. des_sumbool. ss.

    + inv TRANSL1; ss.

    + inv TRANSL1; ss.
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.

