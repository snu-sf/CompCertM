Require Import CoqlibC.
From compcertr Require Import
     Maps Postorder
     AST Linking
     Memory Globalenvs Events Smallstep
     Op Registers sflib.
Require Import ValuesC.
Require Import RTLC.
From compcertr Require Import Renumber.
(** newly added **)
From compcertr Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog tprog: program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (RTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Renumberproof.match_states st_src0 st_tgt0)
    (MCOMPATSRC: (get_mem st_src0) = sm0.(SimMem.src))
    (MCOMPATTGT: (get_mem st_tgt0) = sm0.(SimMem.tgt)).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src))
                      (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss; clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemId.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_callstates; eauto.
        { econs; eauto. }
        inv SAFESRC. ss. folder. inv TYP.
        exploit (Genv.find_funct_transf_genv SIMGE); eauto. intro FINDFSRC; clarify.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP. esplits; eauto. econs; swap 1 2; eauto; ss.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss. folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemId.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. clarify. econs; eauto.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS; ss. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto. econs; ss; eauto.
  - left; i. esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii. hexploit (@step_simulation prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des. esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := SimSymbId.mk_mp (RTLC.module prog) (RTLC.module tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
    + clarify. right. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
