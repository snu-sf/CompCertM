Require Import CoqlibC Maps Integers AST Linking.
Require Import ValuesC Memory Events Globalenvs Smallstep.
Require Import Op Registers RTLC Conventions Tailcall.
Require Import sflib.
(** newly added **)
Require Export Tailcallproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemExt.
Require SoundTop.

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
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Tailcallproof.match_states st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (MCOMPATIDX: idx = Tailcallproof.measure st_src0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cu f tf => tf = transf_fundef f) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq);
    eauto; ii; ss.
  - eapply Nat.lt_wf_0.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemExt.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_states_call; eauto.
        { econs; eauto. }
        { eapply lessdef_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply lessdef_list_length; eauto. }
        folder. inv SAFESRC. inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. folder. des_ifs.
        inv FPTR; ss. unfold transf_function in *. des_ifs.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. inv FPTR; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. folder. des_ifs.
    inv TYP. erewrite <- (sig_preserved fd) in *. esplits; eauto. econs; eauto.
    + econs; eauto. erewrite <- lessdef_list_length; eauto.
    + erewrite <- lessdef_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify. u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
        folder. inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
    + econs; ss; eauto.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; econs; ss; eauto.
    + econs; ss; eauto. eapply lessdef_typify; ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv H2. destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto. econs; eauto.
  - left; i. esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii. hexploit (@transf_step_correct prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des.
    + esplits; eauto.
      * left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
    + esplits; eauto.
      * right. subst tr. split. econs. eauto.
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t := ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt.

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
    + clarify. right. esplits; eauto. unfold fn_sig. rewrite sig_preserved; et.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
