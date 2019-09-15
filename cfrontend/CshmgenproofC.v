Require Import CoqlibC Errors Maps Integers Floats.
Require Import AST Linking.
Require Import ValuesC Events Memory Globalenvs Smallstep.
Require Import CtypesC Cop ClightC Cminor CsharpminorC.
Require Import Cshmgen.
Require Import sflib.
(** newly added **)
Require Export Cshmgenproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.




Lemma proj_sig_res_type
      targs0 tres0 cconv0
  :
    proj_sig_res (signature_of_type targs0 tres0 cconv0) = typ_of_type tres0
.
Proof.
  destruct tres0; ss.
Qed.


Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Let md_src: Mod.t := (ClightC.module2 prog).
Let md_tgt: Mod.t := (CsharpminorC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog) prog.(prog_comp_env).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Clight.state) (st_tgt0: Csharpminor.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Cshmgenproof.match_states prog ge st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(ClightC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(CsharpminorC.get_mem) = sm0.(SimMem.tgt)).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef match_fundef match_varinfo prog) ge tge.
Proof. subst_locals. ss. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemId.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. inv SAFESRC. folder.
        rpapply match_callstate; eauto.
        { econs; eauto. }
        { ss. }
        inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. intro FINDFSRC; des.
        inv FINDFSRC0. ss. clarify. monadInv H0; ss. f_equal; try congruence.
        { exploit (function_type_implies_sig fd0); et. unfold type_of_function. ss. }
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP. inv H0. ss.
    assert(TYEQ: (ClightC.signature_of_function fd) = fn_sig tf0).
    { monadInv H3. ss. }
    esplits; eauto. econs; swap 1 2; ss; eauto.
    + esplits; ss. unfold ClightC.signature_of_function in *. rewrite <- TYEQ. ss.
    + ss. econs; ss. rewrite <- TYEQ. ss.
    + rewrite <- TYEQ. ss.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
      * des. clarify. esplits; eauto.
    + econs; ss; eauto.
      * instantiate (1:= SimMemId.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; inv CSTYLE. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. clarify.
      rpapply match_returnstate; eauto. repeat f_equal. rewrite proj_sig_res_type. ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv MK; ss. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto. econs; ss; eauto.
  - left; i. esplits; eauto.
    { apply modsem2_receptive. }
    inv MATCH. ii. hexploit (@transl_step prog skenv_link skenv_link); eauto; ss.
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des. esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := SimSymbId.mk_mp (ClightC.module2 prog) (CsharpminorC.module tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. inv TRANSL. des. unfold CSk.of_program, Sk.of_program. ss. f_equal; ss.
    revert H. generalize prog at 1 as CTX. i.
    destruct prog, tprog; ss. clear - H.
    ginduction prog_defs; ii; ss; inv H; ss.
    erewrite IHprog_defs; et. f_equal; ss.
    inv H2. destruct a, b1; ss. clarify. inv H0; ss.
    + unfold update_snd. ss. f_equal. destruct f1; inv H1; ss.
      unfold transl_function in H2. unfold bind in *. ss. des_ifs.
    + inv H. ss.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
