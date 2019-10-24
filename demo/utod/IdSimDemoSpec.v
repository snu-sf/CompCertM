Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import DemoSpec.
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

Require Import MatchSimModSem ModSemProps.
Require Import IdSimExtra.
Require Import CtypingC.
Require Import CopC.
Require Import sflib.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Inductive match_states_ext_demo
  : unit -> state -> state -> SimMemExt.t' -> Prop :=
| match_ext
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_demo
      tt
      (mkstate i m_src)
      (mkstate i m_tgt)
      sm0
.

Section DEMOSOUNDSTATE.

  Variable skenv_link: SkEnv.t.
  Variable su: Sound.t.

  Inductive sound_state_demo
    : state -> Prop :=
  | sound_state
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (VALS: Sound.val su (Vlong i))
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state_demo (mkstate i m).

End DEMOSOUNDSTATE.

Section DEMOSOUND.

  Variable skenv_link: SkEnv.t.

  Lemma demo_unreach_local_preservation
    :
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link tt) sound_state>>
  .
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_spec with (lift := UnreachC.le') (sound_state := sound_state_demo skenv_link); eauto.
    econs; ss; i.
    { eapply UnreachC.liftspec; et. }
    - inv INIT. ss. unfold Sound.args in SUARG. des_ifs. des. esplits.
      + refl.
      + destruct st_init.
        econs; eauto; ss; inv SKENV; ss.
      + instantiate (1:=get_mem). ss. rewrite M. refl.
    - exists su0. esplits; eauto.
      + refl.
      + inv SUST. inv FINAL. ss. econs; eauto. ss. clarify.
      + inv SUST. inv FINAL. ss. refl.
  Qed.

End DEMOSOUND.

Inductive match_states_demo_internal:
  state -> state -> meminj -> mem -> mem -> Prop :=
| match_inj_internal
    i j m_src m_tgt
  :
    match_states_demo_internal
      (mkstate i m_src)
      (mkstate i m_tgt)
      j m_src m_tgt
.

Inductive match_states_demo
  : unit -> state -> state -> SimMemInj.t' -> Prop :=
| match_states_demo_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWFINJ: j = sm0.(SimMemInj.inj))
    (MATCHST: match_states_demo_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMemInj.wf' sm0)
  :
    match_states_demo
      tt st_src st_tgt sm0
.

Lemma demo_id
      (WF: Sk.wf DemoSpec.module)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  eapply any_id; eauto.
Qed.

Lemma demo_ext_unreach
      (WF: Sk.wf DemoSpec.module)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbId.mk _ _).
  econs; ss; i.
  destruct SIMSKENVLINK.
  exploit demo_unreach_local_preservation. i. des.
  eapply match_states_sim with (match_states := match_states_ext_demo); ss.
  - apply unit_ord_wf.
  - ss. eauto.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS. ss.
    esplits; eauto.
    + econs; eauto.
    + instantiate (2:=tt).
      destruct x, st_init_tgt. ss.
      rewrite VS, VS0 in VALS. inv VALS. inv H4. inv H2; ss.
    + ss.
  - i. ss. des. inv SAFESRC.
    set (sm_init_tgt := mkstate (get_arg st_init_src) (SimMemExt.tgt sm_arg)).
    exists sm_init_tgt.
    esplits. econs; ss.
    + inv SIMARGS; ss. rewrite VS in *. inv VALS. inv H1; inv H3. eauto.
    + inv SIMARGS; ss.
  - i. ss. inv MATCH; eauto.
  - i. ss. inv FINALSRC. inv MATCH.
    esplits; eauto.
    + econs. ss.
    + econs; eauto. ss. clarify.
  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      unfold safe_modsem in H.
      exploit H. eapply star_refl. ii. des; clarify.
    + ii. inv STEPTGT; inv MATCH; ss.
      Unshelve. ss. eapply bot4.
Qed.

Lemma demo_ext_top
      (WF: Sk.wf DemoSpec.module)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbId.mk _ _).
  econs; ss; i.
  destruct SIMSKENVLINK.
  eapply match_states_sim with (match_states := match_states_ext_demo); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS. ss.
    esplits; eauto.
    + econs; eauto.
    + instantiate (2:=tt).
      destruct x, st_init_tgt. ss.
      rewrite VS, VS0 in VALS. inv VALS. inv H4. inv H2; ss.
    + ss.
  - i. ss. des. inv SAFESRC.
    set (sm_init_tgt := mkstate (get_arg st_init_src) (SimMemExt.tgt sm_arg)).
    exists sm_init_tgt.
    esplits. econs; ss.
    + inv SIMARGS; ss. rewrite VS in *. inv VALS. inv H1; inv H3. eauto.
    + inv SIMARGS; ss.
  - i. ss. inv MATCH; eauto.
  - i. ss. inv FINALSRC. inv MATCH.
    esplits; eauto.
    + econs. ss.
    + econs; eauto. ss. clarify.
  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      unfold safe_modsem in H.
      exploit H. eapply star_refl. ii. des; clarify.
    + ii. inv STEPTGT; inv MATCH; ss.
      Unshelve. ss. eapply bot4.
Qed.

Lemma demo_inj_drop_bot
      (WF: Sk.wf DemoSpec.module)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = SimSymbDrop.mk bot1 (DemoSpec.module) (DemoSpec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with (match_states := match_states_demo); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS. ss.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + destruct x, st_init_tgt. ss.
      rewrite VS, VS0 in VALS. inv VALS. inv H4. inv H2; ss.
      econs; ss; eauto.
    + ss.
  - i. ss. des. inv SAFESRC.
    set (sm_init_tgt := mkstate (get_arg st_init_src) (SimMemInj.tgt sm_arg)).
    exists sm_init_tgt.
    esplits. econs; ss.
    + inv SIMARGS; ss. rewrite VS in *. inv VALS. inv H1; inv H3. eauto.
    + inv SIMARGS; ss.
  - i. ss. inv MATCH; eauto.
  - i. ss. inv FINALSRC. inv MATCH; inv MATCHST.
    esplits; eauto.
    + econs. ss.
    + econs; eauto; ss. clarify.
    + refl.
  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      unfold safe_modsem in H.
      exploit H. eapply star_refl. ii. des; clarify.
    + ii. inv STEPTGT; inv MATCH; ss.
      Unshelve. ss. eapply bot4.
Qed.

Lemma demo_inj_drop
      (WF: Sk.wf (DemoSpec.module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  exploit demo_inj_drop_bot; eauto. i. des. eauto.
Qed.

Lemma demo_inj_id
      (WF: Sk.wf (DemoSpec.module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  eapply sim_inj_drop_bot_id. apply demo_inj_drop_bot; auto.
Qed.

Require Import IdSimInvExtra.

Section INJINV.

Local Existing Instance SimSymbDropInv.SimMemInvTop.
Local Existing Instance SimSymbDropInv.SimSymbDropInv.
Local Existing Instance SoundTop.Top.


Inductive match_states_demo_inv
  : unit -> state -> state -> SimMem.t -> Prop :=
| match_states_demo_inv_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MATCHST: match_states_demo_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_demo_inv
      tt st_src st_tgt sm0
.

Lemma demo_inj_inv
      (WF: Sk.wf (DemoSpec.module))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (DemoSpec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (DemoSpec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimSymbDropInv.mk bot1 _ _).
  econs; ss; i.
  { econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with (match_states := match_states_demo_inv); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. clarify.
    inv SIMARGS. ss.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + destruct x, st_init_tgt. ss.
      rewrite VS, VS0 in VALS. inv VALS. inv H4. inv H2; ss.
      econs; ss; eauto.
    + ss.

  - i. ss. des. inv SAFESRC.
    inv MWF. ss. inv WF0. ss.
    set (sm_init_tgt := mkstate (get_arg st_init_src) (SimMemInj.tgt (SimMemInjInv.minj sm_arg))).
    exists sm_init_tgt.
    esplits. econs; ss.
    + inv SIMARGS; ss. rewrite VS in *. inv VALS. inv H1; inv H3. eauto.
    + inv SIMARGS; ss.
  - i. ss. inv MATCH; eauto.
  - i. ss. inv FINALSRC. inv MATCH; inv MATCHST.
    esplits; eauto.
    + econs. ss.
    + econs; eauto; ss. clarify.
    + refl.
  - right. ii. des.
    esplits.
    + i. inv MATCH; ss.
      unfold safe_modsem in H.
      exploit H. eapply star_refl. ii. des; clarify.
    + ii. inv STEPTGT; inv MATCH; ss.
      Unshelve. ss. eapply bot4.
Qed.

End INJINV.
