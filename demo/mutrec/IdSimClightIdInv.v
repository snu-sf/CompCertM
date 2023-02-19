Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
From compcertr Require Import Cop Ctypes.
Require Import ClightC.
Require Import AsmC.
Require SimMemInjInvC.
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
Require Import Conventions1C.

Require Import MatchSimModSem.
Require Import IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import CtypingC.
Require Import CopC.

Require Import MatchSimModSem.
Require Import Conventions1C.

Require Import ClightStepInj.
Require Import IdSimExtra IdSimInvExtra IdSimClightExtra.
Require Import mktac.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.

Local Existing Instance SoundTop.Top.

Inductive match_states_clight_inv
  : unit -> Clight.state -> Clight.state -> SimMem.t -> Prop :=
| match_states_clight_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = (SimMem.src sm0))
    (MWFTGT: m_tgt = (SimMem.tgt sm0))
    (MWFINJ: j = (SimMemInjInv.minj sm0).(SimMemInj.inj))
    (MATCHST: match_states_clight_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_clight_inv
      tt st_src st_tgt sm0
.

Lemma clight_inj_inv_id
      (clight: Clight.program)
      (WF: Sk.wf (module2 clight))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: (ModPair.src mp) = (module2 clight)>>)
      /\ (<<TGT: (ModPair.tgt mp) = (module2 clight)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s. instantiate (3:= (SimMemInjInvC.mk bot1 _ _)).
  esplits; eauto.
  econs; ss; i.
  { econs; ss; i; clarify. }
  eapply match_states_sim with (match_states := match_states_clight_inv); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv INITTGT. inv SAFESRC. inv SIMARGS; ss. inv H. ss.
    exploit match_globals_find_funct; eauto.
    i. clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto. econs; eauto.
      { inv TYP. inv TYP0. eapply inject_list_typify_list; eauto. }
      econs.

  - i. ss. exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv SIMARGS; ss. esplits. econs; ss.
    + eapply match_globals_find_funct; eauto.
    + inv TYP. econs; eauto.
      erewrite <- inject_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv MATCHST. inv SIMSKENV. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * eapply SimSymbIdInv_find_None; eauto.
        ii. clarify. ss. des. clarify.
      * des. clear EXTERNAL.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv INJ. inv SIMSKELINK. inv INJECT. exploit IMAGE; eauto.
        { left. eapply Genv.genv_defs_range; eauto. }
        { i. des. clarify. inv SIMSKENV. des_ifs. esplits; eauto. }
    + econs; ss.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInjInvC.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH. inv MATCHST.
    esplits; eauto.
    + econs; eauto. inv SIMRET; ss.
    + inv SIMRET; ss. econs; eauto. econs; eauto.
      { eapply inject_rettypify; et. }
      ss. eapply match_cont_incr; try eassumption.
      inv MLE. inv MLE1. inv MLE0. inv MLE. etrans; eauto.
    + refl.

  - i. ss. inv FINALSRC. inv MATCH. inv MATCHST. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.
    + refl.

  - left. i. split.
    + eapply modsem2_receptive.
    + ii. inv MATCH. destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
      cinv MWF. cinv WF0. ss.
      exploit clight_step_preserve_injection2; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry2_inject. ss. }
      { inv SIMSKENV. ss.
        exploit SimMemInjInvC.skenv_inject_symbols_inject; eauto. }
      { inv SIMSKENV. ss. exploit SimSymbIdInv_match_globals; eauto. } i. des.
      exploit SimMemInjC.parallel_gen; eauto. i. des.
      hexploit SimMemInjInv.le_inj_wf_wf; eauto.
      { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
        - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
        - eapply Mem.unchanged_on_implies; eauto.
          i. exploit INVRANGETGT; eauto. i. des. eauto. } intros MWFINV0.

      esplits; eauto.
      * left. apply plus_one. econs; ss; eauto.
        eapply modsem2_determinate.
      * instantiate (1:=SimMemInjInv.mk _ _ _). econs; ss; eauto.
      * econs; ss; eauto.
Unshelve. apply 0.
Qed.

End INJINV.
