Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require Import AsmC.
Require SimMemInjInvC.
Require Import MutrecA MutrecAspec MutrecAproof.
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

Require Import MatchSimModSem ModSemProps.
Require Import Conventions1C.

Require Import IdSimExtra IdSimInvExtra IdSimClightExtra.
Require Import mktac.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Inductive match_states_a_internal:
  state -> state -> meminj -> mem -> mem -> Prop :=
| match_Callstate
    i m_src m_tgt j
  :
    match_states_a_internal
      (Callstate i m_src)
      (Callstate i m_tgt)
      j m_src m_tgt
| match_Interstate
    i m_src m_tgt j
  :
    match_states_a_internal
      (Interstate i m_src)
      (Interstate i m_tgt)
      j m_src m_tgt
| match_Returnstate
    i m_src m_tgt j
  :
    match_states_a_internal
      (Returnstate i m_src)
      (Returnstate i m_tgt)
      j m_src m_tgt
.

Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.

Local Existing Instance SoundTop.Top.

Inductive match_states_a_inv (sm_arg: SimMem.t)
  : unit -> state -> state -> SimMem.t -> Prop :=
| match_states_a_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MATCHST: match_states_a_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_a_inv
      sm_arg tt st_src st_tgt sm0
.

Lemma a_inj_inv_id
      (WF: Sk.wf (MutrecAspec.module))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (MutrecAspec.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (MutrecAspec.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1). econs; ss; i; clarify. }
  eapply match_states_sim with (match_states := match_states_a_inv); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. }
    instantiate (1 := prog). intros GEMATCH.
    inv INITTGT. inv SAFESRC. inv SIMARGS. inv H. ss.
    inv GEMATCH. exploit SYMBLE; eauto. i. des.
    clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto.
      assert (i = i0).
      { subst. inv VALS. inv H2. ss. }
      subst. econs; eauto.
    + ss.

  - i. ss. exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. }
    instantiate (1 := prog). intros GEMATCH.
    des. inv SAFESRC. inv SIMARGS.
    inv GEMATCH. exploit SYMBLE; eauto. i. des; eauto.
    esplits. econs; ss; eauto.
    + clear -MWF INJ FPTR FPTR0.
      rewrite FPTR in FPTR0. inv FPTR0; ss.
      rewrite H1 in INJ. clarify.
    + rewrite VS in VALS. inv VALS; ss. inv H3. inv H1. auto.
    + ss.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv MATCHST. inversion SIMSKENV; subst. ss.
    i. ss. exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. }
    instantiate (2 := prog). intros GEMATCH.
    inv GEMATCH. exploit SYMBLE; eauto. i. des; eauto.
    esplits; eauto.
    + econs; ss; eauto.
    + econs; ss; econs; eauto.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInjInvC.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH. inv MATCHST.
    esplits; eauto.
    + econs; eauto. inv SIMRET; ss. rewrite INT in *. inv RETV. ss.
    + inv SIMRET; ss. econs; eauto. econs; eauto.
    + refl.

  - i. ss. inv FINALSRC. inv MATCH. inv MATCHST.
    esplits; eauto.
    + econs.
    + econs; eauto. econs.
    + refl.

  - right. ii. des.
    esplits.
    + i. inv MATCH. inv MATCHST.
      * unfold ModSem.is_step. do 2 eexists. ss. econs; eauto.
      * unfold safe_modsem in H.
        exploit H. eapply star_refl. ii. des; clarify. inv EVSTEP.
      * ss. exfalso. eapply NOTRET. econs. ss.
    + ii. inv STEPTGT; inv MATCH; inv MATCHST.
      * esplits; eauto.
        { left. eapply plus_one. econs. }
        refl.
        econs; eauto. econs.
      * esplits; eauto.
        { left. eapply plus_one. econs 2. eauto. }
        refl.
        econs; eauto. econs.
Qed.

End INJINV.
