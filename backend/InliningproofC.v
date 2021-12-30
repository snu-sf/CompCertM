Require Import FSets.
Require Import CoqlibC.
From compcertr Require Import
     Errors Ordered Maps Floats
     AST Linking
     Memory Events Smallstep
     Registers Op
     sflib.
Require Import IntegersC.
Require Import ValuesC GlobalenvsC.
Require Import RTLC.
From compcertr Require Import ValueDomain NeedDomain NeedOp Inlining.
Require Import ValueAnalysisC.
From compcertr Require SimMemInj.
(** newly added **)
From compcertr Require Export Inliningproof.
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
    (MATCHST: Inliningproof.match_states prog skenv_link skenv_link ge st_src0 st_tgt0 sm0)
    (MCOMPATIDX: idx = Inliningproof.measure st_src0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src)) (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - eapply Nat.lt_wf_0.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    inv INITTGT. des. inv SAFESRC. destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. exists sm_arg. esplits; eauto; try refl; econs; eauto.
    +  inv TYP. folder. ss.
       exploit (Genv.find_funct_match_genv SIMGE); eauto. intro FINDFTGT; des. ss.
       assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link)).
       { inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
         econs; eauto.
         + ii. ss. eapply Plt_Ple_trans. { genext. } ss. refl.
         + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
         + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
       }
       hexploit fsim_external_inject_eq; try apply FINDF0; et. i; clarify.
       rpapply match_call_states; ss; eauto.
       { i. inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
         econs; eauto.
         - eapply SimMemInjC.sim_skenv_symbols_inject; eauto.
         - etrans; try apply MWF. ss. etrans; try apply MWF. rewrite NBTGT. extlia.
       }
       { inv TYP0. eapply inject_list_typify_list; try apply VALS; eauto. }
       { apply MWF. }
       assert (fn_sig fd = fn_sig fd0).
       { unfold transf_function in *. unfold Errors.bind in *. des_ifs. }
       f_equal; eauto. f_equal; rewrite H; eauto.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR.
    unfold Errors.bind in *. unfold transf_function in *. des_ifs. inv TYP.
    esplits; eauto. econs; swap 1 2; eauto.
    + econs; eauto. erewrite <- inject_list_length; eauto.
    + erewrite <- inject_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss; cycle 1.
    { fold ge in EXTERNAL. clarify. }
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
        inv SIMSKENV. ss.
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
    inv MATCH; ss. inv MATCHST; ss; cycle 1.
    { inv HISTORY. inv CALLTGT. }
    inv HISTORY. ss. clear_tac. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. inv MLE0; ss. inv MCOMPAT. clear_tac.
      rpapply match_return_states; ss; eauto; ss.
      (* { clear - MWF. inv MWF. ii. apply TGTEXT in H. rr in H. des. ss. } *)
      { eapply match_stacks_le; eauto. eapply match_stacks_bound; cycle 1.
        { eapply Mem.unchanged_on_nextblock; eauto. }
        eapply match_stacks_extcall; try eapply MS; eauto.
        - eapply SkEnv.senv_genv_compat; eauto.
        - eapply SkEnv.senv_genv_compat; eauto.
        - ii. eapply MAXSRC; eauto.
        - ii. eapply MAXTGT; eauto.
        - eapply Mem.unchanged_on_implies; try eassumption. ii. rr. esplits; eauto.
        - eapply SimMemInj.inject_separated_frozen; et.
        - refl.
      }
      { eapply inject_rettypify; eauto. }
      { eapply MWFAFTR. }
    + refl.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss; cycle 1.
    { inv MS. clarify. }
    inv MS; cycle 1.
    { inv MS0; clarify. }
    inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto; try refl. econs; eauto.
  - (* step *)
    left; i.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii. hexploit (@step_simulation prog skenv_link skenv_link ge tge); eauto.
    { eapply SkEnv.senv_genv_compat; eauto. }
    { eapply SkEnv.senv_genv_compat; eauto. }
    { assert (SkEnv.genv_precise ge prog).
      { eapply SkEnv.project_revive_precise; et. eapply SkEnv.project_impl_spec; et. }
      inv H. econs; ii.
      - exploit P2GE; eauto. i. inv H0. des. exists x. split; eauto. des_ifs. ii. ss. bsimpl. congruence.
      - des. exploit GE2P; eauto. i; des. determ_tac Genv.genv_vars_inj.
    }
    i; des.
    + esplits; eauto.
      * left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
      * econs; ss.
    + esplits; eauto.
      * right. subst tr. split. econs. eauto.
      * assert(MCOMPAT: get_mem st_src1 = SimMem.src sm1 /\ get_mem st_tgt0 = SimMem.tgt sm1).
        { inv H1; inv MCOMPAT; ss. }
        des. econs; eauto; ss.
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
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold Errors.bind in MATCH. des_ifs. esplits; eauto. unfold transf_function in *. des_ifs.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. inv SIMSKENV. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
