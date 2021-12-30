Require Import FunInd.
Require Import CoqlibC IntegersC.
Require Import ASTC LinkingC.
Require Import ValuesC MemoryC EventsC GlobalenvsC.
From compcertr Require Import
     Maps Errors
     Smallstep
     Ctypes Cop Csyntax Csem
     sflib.
Require Import CstrategyC ClightC.
From compcertr Require Import SimplExpr SimplExprspec.
(** newly added **)
From compcertr Require Export SimplExprproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemSR SimSymb SimMem MatchSimModSemSR.
Require Import ModSemProps.
Require Import CtypesC.
Require Import CtypingC.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Csyntax.program.
Variable tprog: Clight.program.
Let md_src: Mod.t := (CstrategyC.module prog).
Let md_tgt: Mod.t := (ClightC.module1 tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge: Csem.genv := Csem.Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog) prog.(prog_comp_env).
Let tge: genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) tprog) tprog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: Csem.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: SimplExprproof.match_states tge st_src0 st_tgt0)
    (MWF: SimMem.wf sm0)
    (MEASURE: measure st_src0 = idx).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src))
                      (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef (fun (ctx : AST.program Csyntax.fundef type) f tf => tr_fundef f tf) eq prog) ge tge /\ prog_comp_env prog = prog_comp_env tprog.
Proof.
  subst_locals. ss. rr in TRANSL. destruct TRANSL. r in H. esplits.
  - eapply SimSymbId.sim_skenv_revive; eauto.
  - hexploit (prog_comp_env_eq prog); eauto. i.
    hexploit (prog_comp_env_eq tprog); eauto. i.
    ss. congruence.
Qed.

Theorem sim_modsem: ModSemPair.simSR msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify. inv INITTGT.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemId.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_callstates; eauto.
        { econs; eauto. }
        inv SAFESRC. folder. inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. intro TFPTR; des. ss.
        f_equal; ss. inv TFPTR0; ss. inv H0; ss. unfold Csyntax.type_of_function, Clight.type_of_function.
        f_equal; try congruence.
    + des. inv SAFESRC. ss.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP. inv H0. esplits; eauto. econs; eauto.
    folder. inv H3. ss. econs; try rewrite H5; eauto.
  - (* call wf *)
    inv MATCH; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * ss. folder. des. destruct TRANSL as [TRANSL0 _].
        exploit (SimSymbId.sim_skenv_revive TRANSL0); eauto.
        { apply SIMSKENV. }
        intro GE; des. apply (fsim_external_funct_id GE); ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemId.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; cycle 1.
    { inv CSTYLE. }
    ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto; econs; ss; eauto.
    clarify. econs; eauto.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv H3. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto. econs; ss; eauto.
  - left; i. esplits; eauto.
    { apply modsem_strongly_receptive; et. }
    inv MATCH. ii. hexploit (@simulation prog skenv_link skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { exploit make_match_genvs; eauto. { eapply SIMSKENV. } intro T; des. esplits; eauto. }
    i. des_safe. esplits; eauto.
    + des.
      * left. eapply spread_dplus; eauto.
        { eapply modsem1_determinate; eauto. }
      * right. esplits; eauto. eapply spread_dstar; eauto.
        { eapply modsem1_determinate; eauto. }
    + econs; eauto.
Unshelve.
  all: ss; try (by econs); try eapply Mem.empty.
Qed.

End SIMMODSEM.




Section SIMMOD.

Variable prog: Csyntax.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := SimSymbId.mk_mp (Mod.Atomic.trans (CstrategyC.module prog)) (ClightC.module1 tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. inv TRANSL. eapply CSk.match_program_eq; et.
    ii. destruct f1; ss.
    + clarify. right. inv MATCH. esplits; eauto. inv H2.
      unfold CsemC.signature_of_function, signature_of_function. f_equal; congruence.
    + clarify. left. inv MATCH. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply factor_simmodsem_source; eauto.
    { ii. ss. hexploit (@modsem_strongly_receptive skenv_link_tgt prog s); eauto. intro SR.
      inv SR. exploit ssr_traces_at; eauto.
    }
    { ii. ss. eapply modsem1_receptive; ss; eauto. }
    ss. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
