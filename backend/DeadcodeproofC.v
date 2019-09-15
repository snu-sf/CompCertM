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

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog tprog: program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (RTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).

Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: unit) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Deadcodeproof.match_states prog ge st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt)).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4);
    eauto; ii; ss.
  - eapply unit_ord_wf.
  - eapply Preservation.local_preservation_strong_spec. eapply sound_state_preservation; auto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemExt.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_call_states; eauto.
        { econs; eauto. }
        { eapply lessdef_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply lessdef_list_length; eauto. }
        folder. inv SAFESRC. inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
        inv FPTR; clarify. unfold transf_function in *. des_ifs.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. inv FPTR; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
    inv TYP. unfold transf_function in *. des_ifs.
    esplits; eauto. econs; swap 1 2; eauto.
    + econs; eauto. erewrite <- lessdef_list_length; eauto.
    + erewrite <- lessdef_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
        folder. inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemExt.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. clarify. econs; eauto.
      eapply lessdef_typify; ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv STACKS; ss. destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto. econs; et.
  - left; i. esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii. hexploit (@step_simulation prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    { ss. des. eauto. }
    i; des. esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
    + instantiate (1:= (SimMemExt.mk _ _)). ss.
Unshelve.
  all: ss. apply msp.
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t := SimSymbId.mk_mp (RTLC.module prog) (RTLC.module tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. des_ifs. esplits; eauto. unfold transf_function in *. des_ifs.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
