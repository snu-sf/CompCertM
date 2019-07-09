Require Import Coq.Program.Equality FSets Permutation.
Require Import FSets FSetAVL Orders Mergesort.
Require Import CoqlibC Maps Ordered Errors IntegersC Floats.
Require Intv.
Require Import AST Linking.
Require Import ValuesC Memory Events GlobalenvsC Smallstep.
Require Import CsharpminorC Switch CminorC Cminorgen.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export Cminorgenproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Let md_src: Mod.t := (CsharpminorC.module prog).
Let md_tgt: Mod.t := (CminorC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge: Csharpminor.genv := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge: Cminor.genv := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Csharpminor.state) (st_tgt0: Cminor.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Cminorgenproof.match_states skenv_link skenv_link ge st_src0 st_tgt0 sm0)
    (MCOMPATIDX: idx = Cminorgenproof.measure st_src0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cu f tf => transl_fundef f = OK tf) eq prog) ge tge.
Proof. subst_locals. ss. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - eapply Nat.lt_wf_0.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    inv INITTGT. des. inv SAFESRC. destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. exists sm_arg. esplits; eauto; try refl; econs; eauto.
    + inv TYP. folder. ss.
      exploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. intro FINDFTGT; des. ss.
      assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link)).
      {
        inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
        econs; eauto.
        + ii. ss. eapply Plt_Ple_trans. { genext. } ss. refl.
        + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
        + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
      }
      hexploit fsim_external_inject_eq; try apply FINDF0; et. i; clarify.
      rpapply match_callstate; ss; eauto.
      { apply MWF. }
      { i. inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
        econs; eauto.
        - eapply SimMemInjC.sim_skenv_symbols_inject; et.
        - etrans; try apply MWF. ss. etrans; try apply MWF. rewrite NBSRC. xomega.
        - etrans; try apply MWF. ss. etrans; try apply MWF. rewrite NBTGT. xomega.
      }
      { econs; et. }
      { inv TYP0. eapply inject_list_typify_list; eauto. }
      assert(fn_sig fd = Csharpminor.fn_sig fd0).
      { unfold transl_function in *. unfold bind in *. des_ifs. eapply sig_preserved_body; eauto. }
      f_equal; try congruence.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR.
    (* unfold transf_function, bind in *. des_ifs. *)
    unfold bind in *. des_ifs.
    assert(FN_SIG: fn_sig f = Csharpminor.fn_sig fd).
    { unfold transl_function in *. unfold bind in *. des_ifs. eapply sig_preserved_body; eauto. }
    esplits; eauto. econs; eauto; rewrite FN_SIG; ss.
    + inv TYP. econs; ss. exploit inject_list_length; et. congruence.
    (* inv TYP. econs. eapply typecheck_inject; et. congruence. *)
    + ss. exploit inject_list_length; et. congruence.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
    folder. inv MCOMPAT; ss. clear_tac.
    exploit (fsim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT.
    esplits; eauto.
    + econs; eauto.
      * des. clarify. esplits; eauto.
        (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *)

        (* Arguments sim_internal_funct_inject [_]. *)
        (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *)
        (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *)
        (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *)
        (* { inv SIMSKENV. ss. } *)

        (***************** TODO: Add as a lemma in GlobalenvsC. *******************)
        inv SIMSKENV.
        assert(fptr_arg = tfptr).
        { inv FPTR; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
          inv SIMSKE. ss. inv INJECT; ss.
          exploit (DOMAIN b1); eauto.
          { eapply Genv.genv_defs_range; et. }
          i; clarify.
        }
        clarify.
    + econs; ss.
    + reflexivity.
  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv AFTERSRC. inv SIMRET; ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. inv HISTORY. ss. clear_tac. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      inv MLE0; ss. inv MCOMPAT. clear_tac.
      rpapply match_returnstate; ss; eauto; ss.
      { eapply MWFAFTR. }
      { eapply match_callstack_le; eauto. eapply match_callstack_incr_bound; try eapply Mem.unchanged_on_nextblock; eauto.
        eapply match_callstack_external_call; try eapply MCS; et; try xomega.
        - eapply SkEnv.senv_genv_compat; ss.
        - eapply SkEnv.senv_genv_compat; ss.
        - eapply Mem.unchanged_on_implies; try eassumption. ss.
        - eapply Mem.unchanged_on_implies; try eassumption. ss.
        - eapply SimMemInj.inject_separated_frozen; et.
        - ii. eapply MAXSRC; ss.
      }
      { eapply inject_typify; eauto. }
    + refl.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss. inv MK. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto; try refl. econs; eauto.
  - left; i.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.

    esplits; eauto.
    { apply CsharpminorC.modsem_receptive. }
    inv MATCH. ii. hexploit (@transl_step_correct prog tprog TRANSL skenv_link skenv_link); eauto; ss.
    { eapply SkEnv.senv_genv_compat; ss. }
    { eapply SkEnv.senv_genv_compat; ss. }
    i; des.
    + esplits; eauto.
      * left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
      * econs; ss.
    + esplits; eauto.
      * right. subst tr. split. econs. eauto.
      * assert(MCOMPAT: CsharpminorC.get_mem st_src1 = SimMem.src sm1 /\ get_mem st_tgt0 = SimMem.tgt sm1).
        { inv H1; inv MCOMPAT; ss. }
        des. econs; eauto; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (CsharpminorC.module prog) (CminorC.module tprog) tt.

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. des_ifs. esplits; eauto. unfold transl_function in *. des_ifs.
      unfold transl_funbody in *. unfold bind in Heq. des_ifs.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. inv SIMSKENV. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
