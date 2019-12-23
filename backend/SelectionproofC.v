Require Import FunInd.
Require Import CoqlibC Maps.
Require Import ASTC LinkingC Errors Integers ValuesC Memory Events Globalenvs Smallstep.
Require Import Switch CminorC Op CminorSelC.
Require Import SelectOp SelectDiv SplitLong SelectLong Selection.
Require Import SelectOpproof SelectDivproof SplitLongproof SelectLongproof.
Require Import sflib.
(* newly added *)
Require Export Selectionproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemExt.
Require SoundTop.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.


Set Implicit Arguments.


Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let md_src: Mod.t := (CminorC.module prog).
Let md_tgt: Mod.t := (CminorSelC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).

Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: Cminor.state) (st_tgt0: CminorSel.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Selectionproof.match_states prog ge st_src0 st_tgt0)
    (MCOMPATSRC: (CminorC.get_mem st_src0) = sm0.(SimMem.src))
    (MCOMPATTGT: (CminorSelC.get_mem st_tgt0) = sm0.(SimMem.tgt))
    (MEASURE: idx = measure st_src0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src))
                      (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef match_fundef eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Inductive match_states_at: Cminor.state -> CminorSel.state -> SimMem.t -> SimMem.t -> Prop :=
| match_states_at_intro
    fptr sg vs k m st_tgt sm_at sm_arg
    (ATEXT: Genv.find_funct ge fptr = None):
    match_states_at (Cminor.Callstate fptr sg vs k m) st_tgt sm_at sm_arg.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := match_states_at);
    eauto; ii; ss.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation; eauto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemExt.mk _ _). esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_callstate; eauto.
        { econs; eauto. }
        { eapply lessdef_list_typify_list; try apply VALS; eauto. rewrite <- LEN.
          symmetry. eapply lessdef_list_length; eauto. }
        folder. inv SAFESRC. inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. folder.
        inv FPTR; ss.
        rr in H0. des. ss. unfold bind in *. des_ifs.
        assert(SGEQ: Cminor.fn_sig fd0 = fn_sig fd).
        { destruct fd0; ss. unfold sel_function in *. ss. unfold bind in *. des_ifs. }
        f_equal; try congruence.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. inv FPTR; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. unfold bind in *. folder. des_ifs.
    inv TYP. rr in H0. des. ss. unfold bind in *. des_ifs.
    assert(SGEQ: (Cminor.fn_sig fd) = f.(fn_sig)).
    { destruct fd; ss. unfold sel_function in *. ss. unfold bind in *. des_ifs. }
    esplits; eauto. econs; eauto.
    + rewrite <- SGEQ. ss.
    + econs; eauto with congruence.
      erewrite <- lessdef_list_length; eauto. etrans; eauto with congruence.
    + erewrite <- lessdef_list_length; eauto. etrans; eauto with congruence.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify. u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss; cycle 1.
    { folder. clarify. }
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
    + econs; ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss; cycle 1.
    { inv HISTORY. ss. inv MATCHARG. folder. clarify. }
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. econs; eauto.
      eapply lessdef_typify; ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. rr in MC. destruct sm0; ss. clarify.
    inv MC.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto. econs; eauto.
  - left; i. esplits; eauto.
    { apply CminorC.modsem_receptive; et. }
    inv MATCH. ii. hexploit (@sel_step_correct prog tprog); eauto.
    { inv SIMSKENV. ss. }
    { clear - skenv_link INCLSRC WF.
      exploit SkEnv.project_revive_precise; eauto.
      { eapply SkEnv.project_impl_spec; eauto. }
      intro SPEC. inv SPEC. inv INCLSRC. econs; eauto.
      - i.
        exploit P2GE; eauto. i; des.
        esplits; eauto. des_ifs. i. ss. unfold negb in *. des_ifs.
      - i. des. exploit GE2P; eauto. i; des.
        ss.
        rpapply PROG. f_equal. eapply Genv.genv_vars_inj; eauto.
    }
    { clear - skenv_link INCLTGT WF.
      exploit SkEnv.project_revive_precise; eauto.
      { eapply SkEnv.project_impl_spec; eauto. }
      intro SPEC. inv SPEC. inv INCLTGT. econs; eauto.
      - i. exploit P2GE; eauto. i; des.
        esplits; eauto. des_ifs. i. ss. unfold negb in *. des_ifs.
      - i. des. exploit GE2P; eauto. i; des. ss.
        rpapply PROG. f_equal. eapply Genv.genv_vars_inj; eauto.
    }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    { admit "FILL THIS". }
    i; des_safe. folder. des.
    + esplits; eauto.
      * left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
    + clarify. esplits; eauto.
      * right. esplits; eauto. { apply star_refl. }
      * instantiate (1:= (SimMemExt.mk _ _)). ss.
    + admit "".
      (* clarify. esplits; eauto. *)
      (* * left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et. *)
      (* * instantiate (1:= (SimMemExt.mk _ _)). ss. *)
Unshelve.
  all: ss. apply msp.
  (* { eapply mk_helper_functions; ss; eauto. all: repeat econs; eauto. } *)
Qed.

End SIMMODSEM.




Section SIMMOD.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t := SimSymbId.mk_mp (CminorC.module prog) (CminorSelC.module tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. inv MATCH. des. unfold sel_fundef in *. ss. unfold bind in *. des_ifs. esplits; eauto. unfold sel_function, bind in *. des_ifs.
    + clarify. left. rr in MATCH. des. ss. clarify. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
