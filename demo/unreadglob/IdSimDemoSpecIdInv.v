Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require Import AsmC.
Require SimMemInjInvC.
Require Import DemoSource DemoSpec DemoProof IdSimDemoSpec.
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

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.

Local Existing Instance SoundTop.Top.

Inductive match_states_demo_inv (sm_arg: SimMem.t)
  : unit -> state -> state -> SimMem.t -> Prop :=
| match_states_demo_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MATCHST: match_states_demo_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_demo_inv
      sm_arg tt st_src st_tgt sm0
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
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1). econs; ss; i; clarify. }
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
      rewrite MEMSRC, MEMTGT. ss.
  - i. ss. des. inv SAFESRC.
    inv MWF. ss. inv WF0. ss.
    set (sm_init_tgt := mkstate (get_arg st_init_src) (SimMemInj.tgt (SimMemInjInv.minj sm_arg))).
    exists sm_init_tgt.
    esplits. econs; ss.
    + inv SIMARGS. ss. rewrite VS in *. inv VALS. inv H2; inv H3. eauto.
    + inv SIMARGS. ss.
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
