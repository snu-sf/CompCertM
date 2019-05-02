Require Import Wellfounded CoqlibC Maps AST Linking.
Require Import Integers ValuesC Memory Events Smallstep Globalenvs.
Require Import Switch Registers Cminor Op CminorSelC RTLC.
Require Import RTLgen RTLgenspec.
Require Import sflib.
(** newly added **)
Require Export RTLgenproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemExt.
Require SoundTop.

Set Implicit Arguments.


Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Let md_src: Mod.t := (CminorSelC.module prog).
Let md_tgt: Mod.t := (RTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).

Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat * nat) (st_src0: CminorSel.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: RTLgenproof.match_states st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(CminorSelC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (MEASRUE: idx = measure_state st_src0)
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Inductive match_states_at: Cminor.state -> CminorSel.state -> SimMem.t -> SimMem.t -> Prop :=
| match_states_at_intro
    fptr sg vs k m
    st_tgt sm_at sm_arg
    (ATEXT: Genv.find_funct ge fptr = None)
  :
    match_states_at (Cminor.Callstate fptr sg vs k m) st_tgt sm_at sm_arg
.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4)
  ;
    eauto; ii; ss.
  - eapply wf_lex_ord; eauto.
    + apply lt_wf.
    + apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation; eauto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemExt.mk _ _).
    esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_callstate; eauto.
        { econs; eauto. }
        { eapply lessdef_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply lessdef_list_length; eauto. }
        folder. inv SAFESRC.
        inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. folder.
        inv FPTR; cycle 1.
        { rewrite <- H3 in *. ss. }
        rewrite H4 in *. clarify.
        rr in H0. des. ss. unfold Errors.bind in *. des_ifs.
        unfold fundef in *. clarify.
        assert(SGEQ: CminorSel.fn_sig fd0 = fn_sig fd).
        { destruct fd0; ss. unfold transl_function in *. ss. unfold bind in *. des_ifs. }
        f_equal; try congruence.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    inv FPTR; cycle 1.
    { rewrite <- H0 in *. ss. }
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
    inv TYP.
    rr in H0. des. ss. unfold Errors.bind in *. des_ifs.
    assert(SGEQ: (CminorSel.fn_sig fd) = f.(fn_sig)).
    { destruct fd; ss. unfold transl_function in *. ss. unfold bind in *. des_ifs. }
    esplits; eauto. econs; eauto.
    + folder. rewrite <- H1. eauto.
    + econs; eauto with congruence.
      erewrite <- lessdef_list_length; eauto. etrans; eauto with congruence.
    + erewrite <- lessdef_list_length; eauto. etrans; eauto with congruence.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss; cycle 1.
    folder.
    esplits; eauto.
    + econs; eauto.
      * folder. des.
        r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE.
        apply (fsim_external_funct_id GE); ss.
        folder.
        inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
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
      eapply lessdef_typify; ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv MS. destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
  - left; i.
    esplits; eauto.
    { apply CminorSelC.modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@transl_step_correct prog skenv_link skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des_safe. folder. des.
    + esplits; eauto.
      * left. eapply ModSemProps.spread_dplus; et. apply modsem_determinate; et.
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
    + clarify. esplits; eauto.
      * right. esplits; eauto. { instantiate (1:= R2). eapply ModSemProps.spread_dstar; eauto. eapply modsem_determinate; eauto. }
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.




Section SIMMOD.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t := ModPair.mk (CminorSelC.module prog) (RTLC.module tprog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. inv MATCH. des. unfold Errors.bind, transl_function in *. ss. des_ifs. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
