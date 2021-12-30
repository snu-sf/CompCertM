Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
From compcertr Require Import Cop Ctypes.
Require Import ClightC.
Require SimMemId SimMemExt.
From compcertr Require SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import MutrecABspec.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
From compcertr Require Import Events Integers Conventions.
Require Import Preservation.
Require Import LocationsC.

Require Import MatchSimModSem ModSemProps.
Require Import IdSimExtra.
Require Import CopC.
From compcertr Require Import sflib.

Require Import MutrecABspec.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Inductive match_states_ext_ab
  : unit -> state -> state -> SimMemExt.t' -> Prop :=
| match_ext_Callstate
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_ab
      tt
      (Callstate i m_src)
      (Callstate i m_tgt)
      sm0
| match_return_Callstate
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_ab
      tt
      (Returnstate i m_src)
      (Returnstate i m_tgt)
      sm0.

Section ABSOUNDSTATE.

  Variable skenv_link: SkEnv.t.
  Variable su: Sound.t.

  Inductive sound_state_ab
    : state -> Prop :=
  | sound_Callstate
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state_ab (Callstate i m)
  | sound_Returnstate
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state_ab (Returnstate i m)
  .

End ABSOUNDSTATE.


Section ABSOUND.

  Variable skenv_link: SkEnv.t.

  Lemma ab_unreach_local_preservation
    :
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link tt) sound_state>>
  .
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_spec with (lift := UnreachC.le') (sound_state := sound_state_ab skenv_link); eauto.
    econs; ss; i.
    { eapply UnreachC.liftspec; et. }
    - inv INIT. ss. unfold Sound.args in SUARG. des_ifs. des. esplits.
      + refl.
      + ss. econs; eauto. inv SKENV. ss.
      + instantiate (1:=get_mem). ss. refl.
    - inv STEP; inv SUST. esplits; eauto.
      + refl.
      + econs; eauto.
      + ss. refl.
    - inv FINAL; inv SUST. esplits; eauto.
      + refl.
      + econs; eauto. ss.
      + ss. refl.
  Qed.

End ABSOUND.

Inductive match_states_ab_internal:
  state -> state -> meminj -> mem -> mem -> Prop :=
| match_Callstate
    i m_src m_tgt j
  :
    match_states_ab_internal
      (Callstate i m_src)
      (Callstate i m_tgt)
      j m_src m_tgt
| match_Returnstate
    i m_src m_tgt j
  :
    match_states_ab_internal
      (Returnstate i m_src)
      (Returnstate i m_tgt)
      j m_src m_tgt
.

Inductive match_states_ab
  : unit -> state -> state -> SimMemInj.t' -> Prop :=
| match_states_ab_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWFINJ: j = sm0.(SimMemInj.inj))
    (MATCHST: match_states_ab_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMemInj.wf' sm0)
  :
    match_states_ab
      tt st_src st_tgt sm0
.

Lemma a_id
      (WF: Sk.wf MutrecABspec.module)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  eapply any_id; auto.
Qed.

Lemma a_ext_unreach
      (WF: Sk.wf MutrecABspec.module)
 :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbId.mk _ _).
  econs; ss; i.
  destruct SIMSKENVLINK.
  exploit ab_unreach_local_preservation. i. des.
  eapply match_states_sim with (match_states := match_states_ext_ab)
                               (match_states_at := top4); ss.
  - apply unit_ord_wf.
  - eauto.
  - i. ss. inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS; ss. esplits; eauto; ss.
    + econs; eauto.
    + assert (i = i0).
      { subst. inv VALS. inv H2. ss. }
      subst. econs; eauto. ss.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS; ss. inv FPTR; eauto. clarify.
    + instantiate (1:=i). inv SIMARGS; ss.
      rewrite VS in *. inv VALS. inv H3. inv H1. ss.
    + auto.

  - i. inv MATCH; auto.

  - i. ss. inv FINALSRC. inv MATCH.
    esplits; eauto.
    + econs.
    + econs; eauto. econs.

  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      * unfold ModSem.is_step. do 2 eexists. ss.
      * unfold safe_modsem in H.
        exploit H. eapply star_refl. ii. des; clarify. inv EVSTEP.
    + ii. inv STEPTGT; inv MATCH; ss.
      esplits; eauto.
      { left. eapply plus_one. econs. }
      econs; eauto.
Qed.

Lemma a_ext_top 
      (WF: Sk.wf MutrecABspec.module)
 :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbId.mk _ _).
  econs; ss; i.
  destruct SIMSKENVLINK.
  eapply match_states_sim with (match_states := match_states_ext_ab)
                               (match_states_at := top4); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss. inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS; ss. esplits; eauto; ss.
    + econs; eauto.
    + assert (i = i0).
      { subst. inv VALS. inv H2. ss. }
      subst. econs; eauto. ss.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS; ss. inv FPTR; eauto. clarify.
    + instantiate (1:=i). inv SIMARGS; ss.
      rewrite VS in *. inv VALS. inv H3. inv H1. ss.
    + auto.

  - i. inv MATCH; auto.

  - i. ss. inv FINALSRC. inv MATCH.
    esplits; eauto.
    + econs.
    + econs; eauto. econs.

  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      * unfold ModSem.is_step. do 2 eexists. ss.
      * unfold safe_modsem in H.
        exploit H. eapply star_refl. ii. des; clarify. inv EVSTEP.
    + ii. inv STEPTGT; inv MATCH; ss.
      esplits; eauto.
      { left. eapply plus_one. econs. }
      econs; eauto.
Qed.

Lemma ab_inj_drop_bot
      (WF: Sk.wf (MutrecABspec.module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = SimSymbDrop.mk bot1 (MutrecABspec.module) (MutrecABspec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with (match_states := match_states_ab)
                                 (match_states_at := top4); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. inv INITTGT. inv SAFESRC. inv SIMARGS; ss. inv H.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto.
      assert (i = i0).
      { subst. inv VALS. inv H2; ss. inv VS0. ss. }
      subst i0. econs.

  - i. des. inv SAFESRC. inv SIMARGS; ss.
    rewrite VS in *. inv VALS. inv H1. inv H3.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    inv SIMSKENV. ss. inv SIMSKE. ss. inv FPTR.  exploit SIMDEF; eauto.
    i. des. clarify. esplits; eauto. econs; ss; eauto.
    unfold Genv.find_funct_ptr. des_ifs.

  - i. inv MATCH; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv MATCHST. esplits; eauto.
    + econs.
    + econs; eauto. econs.
    + refl.

  - right. ii. des.
    esplits.
    + i. inv MATCH; inv MATCHST; ss.
      * unfold ModSem.is_step. do 2 eexists. ss.
      * unfold safe_modsem in H.
        exploit H. eapply star_refl. ii. des; clarify. inv EVSTEP.
    + ii. inv STEPTGT; inv MATCH; inv MATCHST; ss.
      esplits; eauto.
      { left. eapply plus_one. econs. }
      { refl. }
      econs; eauto. econs; eauto.
Qed.

Lemma ab_inj_drop
      (WF: Sk.wf (MutrecABspec.module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  exploit ab_inj_drop_bot; eauto. i. des. eauto.
Qed.

Lemma ab_inj_id
      (WF: Sk.wf (MutrecABspec.module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  eapply sim_inj_drop_bot_id. apply ab_inj_drop_bot; auto.
Qed.

Require Import IdSimInvExtra.

Section INJINV.

Local Existing Instance SimSymbDropInv.SimMemInvTop.
Local Existing Instance SimSymbDropInv.SimSymbDropInv.
Local Existing Instance SoundTop.Top.


Inductive match_states_ab_inv
  : unit -> state -> state -> SimMem.t -> Prop :=
| match_states_ab_inv_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MATCHST: match_states_ab_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_ab_inv
      tt st_src st_tgt sm0.


Lemma ab_inj_inv_id
      (WF: Sk.wf (MutrecABspec.module))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecABspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecABspec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbDropInv.mk bot1 _ _).
  econs; ss; i.
  { econs; ss; i; clarify. inv WF. eauto. }
  eapply match_states_sim with (match_states := match_states_ab_inv)
                               (match_states_at := top4); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. inv INITTGT. inv SAFESRC. inv SIMARGS; ss. inv H.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto.
      assert (i = i0).
      { subst. inv VALS. inv H2; ss. inv VS0. ss. }
      subst i0. econs.

  - i. des. inv SAFESRC. inv SIMARGS; ss.
    rewrite VS in *. inv VALS. inv H1. inv H3.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    inv SIMSKENV. ss. inv SIMSKE. ss. inv FPTR.  exploit SIMDEF; eauto.
    i. des. clarify. esplits; eauto. econs; ss; eauto.
    unfold Genv.find_funct_ptr. des_ifs.

  - i. inv MATCH; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv MATCHST. esplits; eauto.
    + econs.
    + econs; eauto. econs.
    + refl.

  - right. ii. des.
    esplits.
    + i. inv MATCH; inv MATCHST; ss.
      * unfold ModSem.is_step. do 2 eexists. ss.
      * unfold safe_modsem in H.
        exploit H. eapply star_refl. ii. des; clarify. inv EVSTEP.
    + ii. inv STEPTGT; inv MATCH; inv MATCHST; ss.
      esplits; eauto.
      { left. eapply plus_one. econs. }
      { refl. }
      econs; eauto. econs; eauto.
Qed.

End INJINV.
