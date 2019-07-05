Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require Import AsmC.
Require SimMemInjInvC SimSymbDropInv.
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
Require Import Conventions1C.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import StoreArguments.
Require Import AsmStepInj IntegersC.
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


Local Existing Instance SimSymbDropInv.SimMemInvTop.
Local Existing Instance SimSymbDropInv.SimSymbDropInv.
Local Existing Instance SoundTop.Top.

Inductive match_states_clight_inv (sm_arg: SimMem.t)
  : unit -> Clight.state -> Clight.state -> SimMem.t -> Prop :=
| match_states_clight_inv_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MATCHST: match_states_clight_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_clight_inv
      sm_arg tt st_src st_tgt sm0
.

Lemma clight_inj_inv_drop
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1). econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with (match_states := match_states_clight_inv); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. exploit SimSymbDropInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv INITTGT. inv SAFESRC. inv SIMARGS. inv H. ss.
    exploit match_globals_find_funct; eauto.
    i. clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto. econs; eauto.
      { inv TYP. inv TYP0. eapply inject_list_typify_list; eauto. }
      econs.

  - i. ss. exploit SimSymbDropInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv SIMARGS. esplits. econs; ss.
    + eapply match_globals_find_funct; eauto.
    + inv TYP. econs; eauto.
      erewrite <- inject_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv MATCHST. inv SIMSKENV. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * eapply SimSymbDropInv_find_None; eauto.
        ii. clarify. ss. des. clarify.
      * des. clear EXTERNAL.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv INJ. inv SIMSKELINK.
        exploit SIMDEF; eauto. i. des. clarify. des_ifs. esplits; eauto.
    + econs; ss.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInjInvC.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH. inv MATCHST.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. econs; eauto. econs; eauto.
      { eapply inject_typify; et. }
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
      { inv SIMSKENV. exploit SimSymbDropInv.sim_skenv_symbols_inject; eauto. }
      { inv SIMSKENV. rpapply SimSymbDropInv_match_globals; eauto. } i. des.
      exploit SimMemInjC.parallel_gen; eauto. i. des.
      hexploit SimMemInjInv.le_inj_wf_wf; eauto. intros MWFINV0.

      esplits; eauto.
      * left. apply plus_one. econs; ss; eauto.
        eapply modsem2_determinate.
      * instantiate (1:=SimMemInjInv.mk _ _ _). econs; ss; eauto.
      * econs; ss; eauto.
Qed.

End INJINV.
