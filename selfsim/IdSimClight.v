Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import MatchSimModSem.
Require Import ClightStepInj ClightStepExt.
Require Import IdSimExtra IdSimClightExtra.
Require Import CtypingC.
Require Import CopC.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Lemma clight_id
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>).
Proof.
  eapply any_id; eauto.
Qed.

Lemma clight_ext_unreach
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>).
Proof.
  eexists (ModPair.mk _ _ _); s. esplits; eauto. instantiate (1:=(SimSymbId.mk _ _)).
  econs; ss; i. destruct SIMSKENVLINK.
  exploit clight_unreach_local_preservation. i. des.
  eexists.
  eapply match_states_sim with (match_states := match_states_ext_clight); ss; eauto.
  - apply unit_ord_wf.
  - i. ss. inv INITTGT. inv SAFESRC. inv H.
    inv SIMARGS; ss.
    assert (FD: fd = fd0).
    { inv FPTR; ss. rewrite FINDF in FINDF0. clarify. }
    esplits; eauto.
    + econs; eauto.
    + ss. subst. econs 2; eauto.
      * inv TYP. inv TYP0. eapply lessdef_list_typify_list; et.
      * econs; et.
  - i. ss. des. inv SAFESRC. inv SIMARGS; ss. esplits. econs; ss.
    + inv FPTR; ss. eauto.
    + inv TYP. econs; ss; eauto.
      erewrite <- lessdef_list_length; eauto.
  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss. esplits; eauto.
    + des. inv INJ; ss; clarify. econs; ss; eauto.
    + econs; ss.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists sm_ret.
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto. inv SIMRET; ss.
    + inv SIMRET; ss.
      econs; eauto.
      eapply lessdef_typify; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT. esplits; eauto; econs; eauto.

  - left. i. split.
    { eapply modsem2_receptive. }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto. left. apply plus_one. econs; ss; eauto. eapply modsem2_determinate.
Unshelve.
  all: ss.
Qed.


Lemma clight_ext_top
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>).
Proof.
  eexists (ModPair.mk _ _ _); s. esplits; eauto. instantiate (1:=(SimSymbId.mk _ _)).
  econs; ss; i. destruct SIMSKENVLINK.
  eexists.
  eapply match_states_sim with (match_states := match_states_ext_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H.
    inv SIMARGS; ss.
    assert (FD: fd = fd0).
    { inv FPTR; ss. rewrite FINDF in FINDF0. clarify. }
    esplits; eauto.
    + econs; eauto.
    + ss. subst. econs; eauto.
      * inv TYP. inv TYP0. eapply lessdef_list_typify_list; eauto.
      * econs; eauto.
  - i. ss. des. inv SAFESRC. inv SIMARGS; ss. esplits. econs; ss.
    + inv FPTR; ss. eauto.
    + inv TYP. econs; ss; eauto.
      erewrite <- lessdef_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss.
    esplits; eauto.
    + des. inv INJ; ss; clarify. econs; ss; eauto.
    + econs; ss.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists sm_ret.
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto. inv SIMRET; ss.
    + inv SIMRET; ss.
      econs; eauto.
      eapply lessdef_typify; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT. esplits; eauto; econs; eauto.

  - left. i. split.
    { eapply modsem2_receptive. }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto. left. apply plus_one. econs; ss; eauto. eapply modsem2_determinate.
Unshelve.
  all: ss.
Qed.

Lemma clight_inj_drop_bot
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = (SimSymbDrop.mk bot1 (module2 clight) (module2 clight))>>).
Proof.
  eexists (ModPair.mk _ _ _); s. esplits; eauto. econs; ss; i.
  { econs; ss; i; clarify. inv WF. auto. }
  eexists.
  eapply match_states_sim with (match_states := match_states_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv INITTGT. inv SAFESRC. inv SIMARGS; ss. inv H. ss.
    exploit match_globals_find_funct; eauto.
    i. clarify. esplits; eauto; try refl; econs; eauto.
    + econs; eauto; try econs. inv TYP. inv TYP0. eapply inject_list_typify_list; eauto.

  - i. ss. exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv SIMARGS; ss. esplits. econs; ss.
    + eapply match_globals_find_funct; eauto.
    + inv TYP. econs; eauto. erewrite <- inject_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv MATCHST. inv SIMSKENV. ss. esplits; eauto; try refl.
    + econs; ss; eauto.
      * eapply SimSymbDrop_find_None; eauto. ii. clarify. ss. des. clarify.
      * des. clear EXTERNAL. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv INJ. inv SIMSKELINK. exploit SIMDEF; eauto. i. des. clarify. des_ifs. esplits; eauto.
    + econs; ss.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInj.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH. inv MATCHST.
    esplits; eauto.
    + econs; eauto. inv SIMRET; ss.
    + inv SIMRET; ss. econs; eauto. econs; eauto.
      { eapply inject_typify; et. }
      ss. eapply match_cont_incr; try eassumption.
      inv MLE. inv MLE0. etrans; eauto.
    + refl.

  - i. ss. inv FINALSRC. inv MATCH. inv MATCHST. inv CONT. esplits; eauto; try refl; econs; eauto.

  - left. i. split.
    + eapply modsem2_receptive.
    + ii. exploit clight_step_preserve_injection; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry2_inject. ss. }
      { inv SIMSKENV. ss. eapply SimSymbDrop_symbols_inject; eauto. }
      { inv SIMSKENV. ss. eapply SimSymbDrop_match_globals; eauto. }
      i. des. esplits; eauto. left. apply plus_one. econs; ss; eauto. eapply modsem2_determinate.
Unshelve.
  all: ss.
Qed.

Lemma clight_inj_drop
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>).
Proof.
  exploit clight_inj_drop_bot; eauto. i. des. eauto.
Qed.

Lemma clight_inj_id
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (module2 clight)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (module2 clight)>>).
Proof.
  eapply sim_inj_drop_bot_id. apply clight_inj_drop_bot; auto.
Qed.
