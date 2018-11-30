Require Import FunInd.
Require Import CoqlibC Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import Registers Op RTLC.
Require Import ValueDomain ValueAnalysisC NeedDomain NeedOp Inlining.
Require Import sflib.
(** newly added **)
Require Export Inliningproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInj SimMemInjC.
Require UnreachC.

Set Implicit Arguments.

Lemma unit_ord_wf
  :
    well_founded (bot2: unit -> unit -> Prop)
.
Proof.
  ii. induction a; ii; ss.
Qed.



Section SIMMODSEM.
  
Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Local Existing Instance Val.mi_normal.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem skenv_link_src prog) (RTLC.modsem skenv_link_tgt tprog) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: unit) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Inliningproof.match_states prog ge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) ->
  Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. { ii. u. des_ifs; ss; unfold Errors.bind in *; des_ifs. } Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4)
                               (* (sound_state := fun su0 m0 st0 => sound_state prog ge su0 st0) *)
  ;
    eauto; ii; ss.
  - eapply unit_ord_wf.
  - eapply Preservation.local_preservation_strong_spec.
    eapply sound_state_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    exploit make_match_genvs; inv SIMSKENV; eauto. intro SIMGE. des.
    eexists. eexists (SimMemInj.mk _ _ _ _ _ _ _).
    esplits; eauto.
    + econs; eauto; ss.
      * eapply Mem.unchanged_on_refl.
      * eapply Mem.unchanged_on_refl.
      * eapply SimMemInj.frozen_refl.
    + econs; eauto; ss.
      * inv TYP. rpapply match_call_states; eauto.
        { econs; eauto. }
        { apply match_stacks_nil with (Mem.nextblock (Args.m args_tgt)); try xomega. admit "A".
          (* inv INJECT. ss. constructor; intros. *)
          (* - admit "A". *)
          (* - admit "A". *)
          (* - eapply Genv.find_symbol_not_fresh; eauto. admit "A". *)
          (* - eapply Genv.find_funct_ptr_not_fresh; eauto. *)
          (* eapply Genv.find_var_info_not_fresh; eauto. *)
          (* apply Ple_refl. *)
          (* { eapply Mem.flat_inj_ptr; eauto. eapply Genv.find_symbol_not_fresh; eauto. } *)
          (* eapply Genv.initmem_inject; eauto. *)
        }
        { eapply inject_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply inject_list_length; eauto. }
        { inv MWF. ss. }
        folder. inv SAFESRC.
        inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
        destruct (Args.fptr args_src); inv FINDF0. des_ifs.
        destruct (Args.fptr args_tgt); inv FINDF. des_ifs.
        inv FPTR. inv INJECT. rewrite DOMAIN in H7; cycle 1. admit "TODO". clarify.
        inv H. des_ifs. unfold transf_function in *. des_ifs. inv H0. ss.
      * admit "?".
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    exploit make_match_genvs; inv SIMSKENV; eauto. intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold Errors.bind in *. folder. des_ifs.
    inv TYP.
    unfold transf_function in *. des_ifs.
    esplits; eauto. econs; eauto.
    + folder. destruct (Args.fptr args_src); inv FINDF. des_ifs.
      inv INJECT. inv FPTR. rewrite DOMAIN in H5; cycle 1. admit "TODO". clarify. ss. des_ifs. eauto.
    + econs; eauto. ss.
      erewrite <- inject_list_length; eauto.
    + erewrite <- inject_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder.
    esplits; eauto.
    inv MCOMPAT.
    + econs; eauto.
      * folder. des.
        r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { ii. destruct f_src, f_tgt; ss; try unfold Errors.bind in *; des_ifs. }
        { inv SIMSKENV. eauto. }
        intro GE.
        apply (sim_external_id GE); ss.
        folder.
        inv SIMSKENV. inv SIMSKENV0. inv INJECT. inv FPTR; ss. des_ifs.
        rewrite DOMAIN in H. clarify. ss. admit "TODO".
      * des. esplits; eauto. inv SIMSKENVLINK. eapply SimSymb.simskenv_func_fsim; eauto; ss.
        { inv FPTR; eauto; inv SIG; inv EXTERNAL. des_ifs. admit "revive?". }
    + inv MCOMPAT. ss.
    + eapply SimMemInj.le'_PreOrder_obligation_1.
    + admit "A".
  - (* after fsim *)
    inv AFTERSRC.
    inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify. econs; eauto.
      * econs; eauto.
      * admit "A".
  (* eapply match_stacks_bound. eapply match_stacks_le. eauto. *)
      * inv MWF. ss.
    + admit "A".
    + admit "A".
  - (* final fsim *)
    (* inv MATCH. inv FINALSRC; inv MATCHST; ss. *)
    (* inv MS. destruct sm0; ss. clarify. *)
  (* eexists (SimMemInj.mk _ _ _ _ _ _ _). esplits; ss; eauto. *)
    admit "A".
  - esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog _ ge tge); eauto.
    { ss. admit "genv_compat". }
    { apply make_match_genvs; inv SIMSKENV; eauto. }
    i; des.
    + esplits; eauto.
      * left. ss. unfold DPlus, DStep in *. admit "A". (* esplits; eauto. apply modsem_determinate. *)
      * assert(MCOMPAT: get_mem st_src1 = SimMem.src sm1 /\ get_mem S2' = SimMem.tgt sm1).
        { inv H0; inv MCOMPAT; ss. }
        des. econs; eauto; ss.
    + esplits; eauto; cycle 1.
      * assert(MCOMPAT: get_mem st_src1 = SimMem.src sm1 /\ get_mem st_tgt0 = SimMem.tgt sm1).
        { inv H1; inv MCOMPAT; ss. }
        des. econs; eauto; ss.
      * right. subst tr. split. econs. unfold bot2. inv STEPSRC; inv H1; inv MATCHST; ss; try omega.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - econs; eauto. admit "easy".
  - ii. eapply sim_modsem; eauto.
Unshelve.
  ss.
Qed.

End SIMMOD.

