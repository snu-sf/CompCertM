Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import sflib.

Require Import MutrecHeader IntegersC.
Require Import StaticMutrecB StaticMutrecBspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SoundTop.
Require SimMemInjInv.
Require Import AsmC.

Set Implicit Arguments.


Definition memoized_inv: SimMemInjInv.memblk_invariant :=
  fun mem =>
    exists i,
      (<<VINDEX: mem Mint32 0 = Some (Vint i)>>) /\
      (<<VSUM: mem Mint32 (size_chunk Mint32) = Some (Vint (sum i))>>).

Local Instance SimMemMemoized: SimMem.class := SimMemInjInv.SimMemInjInv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Lemma memoized_inv_store_le i v_ind v_sum blk ofs0 ofs1 m_tgt0 m_tgt1
      (sm0 sm1: SimMemInjInv.t')
      (MWF: SimMem.wf sm0)
      (INVAR: sm0.(SimMemInjInv.mem_inv) blk)
      (OFSI: ofs0 = 0)
      (OFSV: ofs1 = size_chunk Mint32)
      (INDEX: v_ind = Vint i)
      (SUM: v_sum = Vint (sum i))
      (STR0: Mem.store Mint32 sm0.(SimMemInjInv.tgt) blk ofs0 v_ind = Some m_tgt0)
      (STR1: Mem.store Mint32 m_tgt0 blk ofs1 v_sum = Some m_tgt1)
      (MREL: sm1 = SimMemInjInv.mk sm0.(SimMemInjInv.src) m_tgt1 sm0.(SimMemInjInv.inj) sm0.(SimMemInjInv.mem_inv))
  :
    (<<MLE: SimMem.le sm0 sm1>>) /\
    (<<MWF: SimMem.wf sm1>>).
Proof.
  inv MWF. split.
  - econs; ss; eauto.
    + refl.
    + erewrite <- Mem.nextblock_store; eauto.
      erewrite <- Mem.nextblock_store; eauto. refl.
    + ii. clarify.
    + ii. eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_2; eauto.
  - econs; ss; eauto.
    + eapply MemoryC.private_unchanged_inject; eauto.
      * instantiate (1:=~2 loc_out_of_reach (SimMemInjInv.inj sm0) (SimMemInjInv.src sm0)).
        etrans.
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGE; eauto. }
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGE; eauto. }
      * auto.
      * symmetry.
        erewrite Mem.nextblock_store; try apply STR1; eauto.
        erewrite Mem.nextblock_store; try apply STR0; eauto.
    + ii. exploit SAT; eauto. i. inv H. des. des_ifs.
      * assert (Mem.valid_access m_tgt1 Mint32 blk0 0 Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto. }
        assert (Mem.valid_access m_tgt1 Mint32 blk0 (size_chunk Mint32) Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto. }
        destruct (peq blk blk0).
        { clarify. exists (i). des_ifs. split.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            + erewrite Mem.load_store_same; eauto. ss.
            + ss. right. left. refl.
          - erewrite Mem.load_store_same; eauto. ss. }
        { exists x. des_ifs. split.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            erewrite Mem.load_store_other; try apply STR0; eauto.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            erewrite Mem.load_store_other; try apply STR0; eauto. }
    + i. unfold Mem.valid_block in *.
      erewrite Mem.nextblock_store; try apply STR1; eauto.
      erewrite Mem.nextblock_store; try apply STR0; eauto.
Qed.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (StaticMutrecBspec.module).
Let md_tgt: Mod.t := (AsmC.module prog).
Hypothesis (INCL: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link md_src.(Mod.sk)).
Let tge := (SkEnv.project skenv_link md_tgt.(Mod.sk)).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) symbol_memoized sm_link.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  admit "TODO".
Qed.


End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (StaticMutrecBspec.module) (AsmC.module prog) symbol_memoized)
.
Proof.
  econs; ss.
  - econs; ss. i. inv SS. esplits; ss; eauto.
    + econs; ss.
      admit "fill definition".
    + ii. des; clarify.
    + ii. destruct H. eapply in_prog_defmap in PROG.
      ss. unfold update_snd in PROG. ss.
      des; clarify; inv DROP; ss.
      des; clarify.
  - ii. ss.
    inv SIMSKENVLINK. inv SIMSKENV.
    eapply sim_modsem; eauto.
Qed.
