Require Import FunInd.
Require Import CoqlibC Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import Registers Op RTLC.
Require Import ValueDomain ValueAnalysisC NeedDomain NeedOp Deadcode.
Require Import sflib.
(** newly added **)
Require Export Deadcodeproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemExt.
Require UnreachC.

Set Implicit Arguments.




Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variables prog tprog: program.
Hypothesis INCLSRC: SkEnv.includes skenv_link_src (Sk.of_program fn_sig prog).

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
    (MATCHST: Deadcodeproof.match_states prog ge st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) ->
  Genv.match_genvs (match_globdef (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. { ii. u. des_ifs; ss; unfold bind in *; des_ifs. } Qed.

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
    eapply sound_state_preservation; auto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    exploit make_match_genvs; eauto. intro SIMGE. des.
    eexists. eexists (SimMemExt.mk _ _).
    esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_call_states; eauto.
        { econs; eauto. }
        { eapply lessdef_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply lessdef_list_length; eauto. }
        folder. inv SAFESRC.
        inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
        inv FPTR; cycle 1.
        { rewrite <- H2 in *. ss. }
        rewrite H3 in *. clarify.
        unfold transf_function in *. des_ifs.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    inv FPTR; cycle 1.
    { rewrite <- H0 in *. ss. }
    exploit make_match_genvs; eauto. intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
    inv TYP.
    unfold transf_function in *. des_ifs.
    esplits; eauto. econs; eauto.
    + folder. rewrite <- H1. eauto.
    + econs; eauto.
      erewrite <- lessdef_list_length; eauto.
    + erewrite <- lessdef_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder.
    esplits; eauto.
    + econs; eauto.
      * folder. des.
        r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { ii. destruct f_src, f_tgt; ss; try unfold bind in *; des_ifs. }
        intro GE.
        apply (sim_external_funct_id GE); ss.
        folder.
        inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss. destruct SIMSKENVLINK. ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemExt.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC.
    inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify. econs; eauto.
      eapply lessdef_typify_opt; ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS; ss. destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
  - esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog ge tge); eauto.
    { apply make_match_genvs; eauto. }
    { ss. des. eauto. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate.
    + instantiate (1:= (SimMemExt.mk _ _)). ss.
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
  - r. eapply Sk.match_program_eq; eauto.
    ii.
    admit "ez".
    (* transf_partial_fundef_external *)
    (* transf_partial_fundef_is_external_fd *)
  - ii.
    eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.
