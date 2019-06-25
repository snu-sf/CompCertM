Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
Require SimMemId SimMemExt SimMemInj SimMemInjInv.
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
Require Import ClightStepInj IdSimClight.
Require Import CtypingC.
Require Import CopC.
Require SoundTop.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Local Existing Instances SoundTop.Top.

Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInv.SimMemInjInv P.


Inductive match_states_clight_inv (sm_arg: SimMem.t)
  : unit -> Clight.state -> Clight.state -> SimMem.t -> Prop :=
| match_states_clight_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMem.src))
    (MWFTGT: m_tgt = sm0.(SimMem.tgt))
    (MWFINJ: j = sm0.(SimMemInjInv.inj))
    (MATCHST: match_states_clight_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMem.wf sm0)
  :
    match_states_clight_inv
      sm_arg tt st_src st_tgt sm0
.

Lemma clight_inj_inv
      (clight: Clight.program)
      (WF: Sk.wf clight.(module1))
  :
    exists mp,
      (<<SIM: ModPair.sim  mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module1)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module1)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1). econs; ss; i; clarify. }
  eapply match_states_sim with (match_states := match_states_clight_inv); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss.
    inv INITTGT. inv SAFESRC. inv SIMARGS. inv H. ss.
    assert (fd = fd0).
    { admit "genv". } clarify.
    esplits; eauto.
    + econs; eauto.
    + eapply SimMemInjInv.SimMemInjInv_obligation_1.
    + econs; eauto. econs; eauto. econs.

  - i. des. inv SAFESRC. inv SIMARGS. esplits. econs; ss.
    + instantiate (1:=fd). admit "genv".
    + inv TYP. econs; eauto.
      eapply vals_casted_inject; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv MATCHST. inv SIMSKENV. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * admit "genv".
      * admit "genv".
    + econs; ss.
    + eapply SimMemInjInv.SimMemInjInv_obligation_1.
    + instantiate (1:=top4). ss.

  - i. exists sm_ret.
    inv AFTERSRC. inv MATCH. inv MATCHST.
    exploit typify_c_inject; eauto.
    { inv SIMRET. ss. eauto. } i. des.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. econs; eauto. econs; eauto.
      ss. eapply match_cont_incr; try eassumption.
      inv MLE. inv MLE0. etrans; eauto.
    + eapply SimMemInjInv.SimMemInjInv_obligation_1.

  - i. inv FINALSRC. inv MATCH. inv MATCHST. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.
    + eapply SimMemInjInv.SimMemInjInv_obligation_1.

  - left. i. split.
    + eapply modsem1_receptive.
    + ii. inv MATCH. exploit clight_step_preserve_injection2; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry1_inject. ss. }
      { instantiate (1:=skenv_link_tgt).
        inv SIMSKENVLINK. ss. inv SIMSKENV0.
        (* TODO: make lemma *)
        econs; ss; i. splits; ss; i.
        - admit "".
        - admit "".
        - admit "".
      }
      { inv SIMSKENV. inv SIMSKE. inv INJECT. ss. rewrite SIMSKENV.
        inv SIMSKELINK. inv SIMSKENV0.
        split; ss; i.
        - exists d_src.
          destruct (classic (SimMemInjInv.mem_inv sm0 b_src)).
          + exploit NDOMAIN; eauto.
            { eapply Genv.genv_defs_range in FINDSRC. ss. }
            { ii. clarify. }
          + exploit DOMAIN; eauto.
            { eapply Genv.genv_defs_range in FINDSRC. ss. }
            { ii. clarify. }
        - esplits; eauto. eapply DOMAIN; eauto.
          + eapply Genv.genv_symb_range in FINDSRC. eauto.
          + ii. eapply INVCOMPAT in H; eauto. }
      { inv MWF. eauto. }
      { i. des. esplits.
        - left. econs.
          + econs; ss; eauto.
            eapply modsem1_determinate.
          + econs.
          + symmetry. eapply E0_right.
        - instantiate (1:=SimMemInjInv.mk m_src1 m_tgt1 j1 (SimMemInjInv.mem_inv sm0)).
          econs; ss; eauto.
          + eapply Mem.unchanged_on_nextblock; eauto.
          + eapply Mem.unchanged_on_nextblock; eauto.
        - econs; eauto. inv MWF.
          (* TODO: make lemma *)
          econs; ss; eauto.
          + eapply SimMemInjInv.unchanged_on_invariant; eauto.
            * ii. eapply INVRANGE; eauto. apply 0.
            * eapply Mem.unchanged_on_implies; eauto.
              i. eapply INVRANGE; eauto.
          + i. split.
            * ii. destruct ((SimMemInjInv.inj sm0) b0) as [[blk0 delta0]|]eqn:BLK.
              { dup BLK. eapply INCR in BLK. clarify.
                exploit INVRANGE; eauto. i. des.
                eapply H; eauto. eapply MAXSRC; eauto.
                eapply Mem.valid_block_inject_1; eauto. }
              { exploit SEP; eauto.
                i. des. eapply H2.
                eapply INVRANGE; eauto. }
            * eapply Mem.valid_block_unchanged_on; eauto.
              eapply INVRANGE; eauto. }
Qed.
