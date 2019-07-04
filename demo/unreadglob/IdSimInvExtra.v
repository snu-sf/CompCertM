Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require SimMemInjInv.
Require SoundTop SimSymbId SimSymbDropInv.
Require Import CoqlibC.
Require Import ValuesC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import IdSimExtra.

Set Implicit Arguments.

Section INJINVDROP.

Local Instance SimMemTop: SimMem.class := SimMemInjInvC.SimMemInjInv top1 top1.
Local Instance SimSymbTop: SimSymb.class SimMemTop := SimSymbDropInv.SimSymbDrop.

Lemma SimSymbDropInv_match_globals F `{HasExternal F} V sm0 skenv_src skenv_tgt (p: AST.program F V)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 bot1 skenv_src skenv_tgt)
  :
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0.(SimMemInjInv.minj)).
Proof.
  inv SIMSKE. econs.
  - i. unfold SkEnv.revive in *. exists d_src.
    apply Genv_map_defs_def in FINDSRC. des.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
    des_ifs_safe.
    apply Genv.invert_find_symbol in Heq0.
    exploit SIMDEF; try apply FIND; eauto. i. des. clarify.
    esplits; eauto.
    exploit Genv_map_defs_def_inv; try apply DEFTGT.
    i. rewrite H0.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
    erewrite Genv.find_invert_symbol.
    + rewrite Heq1; eauto.
    + exploit SIMSYMB1; eauto. i. des. eauto.
  - i. unfold SkEnv.revive in *.
    rewrite Genv_map_defs_symb in FINDSRC.
    exploit SIMSYMB2; try apply FINDSRC; eauto.
Qed.

Lemma SimSymbDropInv_symbols_inject sm0 ss_link skenv_src skenv_tgt
      (SIMSKELINK: SimSymbDropInv.sim_skenv sm0 ss_link skenv_src skenv_tgt)
  :
    symbols_inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) skenv_src skenv_tgt.
Proof.
  inv SIMSKELINK. econs; esplits; ss; i.
  - unfold Genv.public_symbol, proj_sumbool.
    rewrite PUB in *. des_ifs; ss.
    + exploit SIMSYMB3; eauto. i. des. clarify.
    + exploit SIMSYMB2; eauto. i. des. clarify.
  - exploit SIMSYMB1; eauto. i. des. eauto.
  - exploit SIMSYMB2; eauto.
    { unfold Genv.public_symbol, proj_sumbool in *. des_ifs. eauto. }
    i. des. eauto.
  - unfold Genv.block_is_volatile, Genv.find_var_info.
    destruct (Genv.find_def skenv_src b1) eqn:DEQ.
    + exploit SIMDEF; eauto. i. des. clarify.
      rewrite DEFTGT. eauto.
    + des_ifs_safe. exfalso. exploit SIMDEFINV; eauto.
      i. des. clarify.
Qed.

Lemma SimSymbDropInv_find_None F `{HasExternal F} V (p: AST.program F V)
      sm0 skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 bot1 skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef)
  :
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. exfalso.
  unfold SkEnv.revive in *. ss.
  apply Genv_map_defs_def in Heq. des.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
  des_ifs_safe.
  apply Genv.invert_find_symbol in Heq0.
  inv SIMSKE. ss. inv FPTR; clarify.
  exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
  erewrite Integers.Ptrofs.add_zero in H4. clarify.
    exploit Genv_map_defs_def_inv; try apply DEFSRC.
  i. revert FINDSRC. rewrite H0.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
  erewrite Genv.find_invert_symbol.
  - rewrite Heq1; eauto. i. des_ifs.
  - exploit SIMSYMB3; eauto. i. des.
    assert (blk_src = b1).
    { exploit DISJ; eauto. }
    clarify.
Qed.

End INJINVDROP.

Section INJINVID.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv top1 P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.

Lemma SimSymbIdInv_match_globals F `{HasExternal F} V sm0 skenv_src skenv_tgt (p: AST.program F V)
      (SIMSKE: SimMemInjInvC.sim_skenv_inj sm0 bot1 skenv_src skenv_tgt)
  :
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0.(SimMemInjInv.minj)).
Proof.
  admit "".
Qed.

Lemma SimSymbIdInv_symbols_inject sm0 ss_link skenv_src skenv_tgt
      (SIMSKELINK: SimMemInjInvC.sim_skenv_inj sm0 ss_link skenv_src skenv_tgt)
  :
    symbols_inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) skenv_src skenv_tgt.
Proof.
  admit "".
Qed.

Lemma SimSymbIdInv_find_None F `{HasExternal F} V (p: AST.program F V)
      sm0 skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimMemInjInvC.sim_skenv_inj sm0 bot1 skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef)
  :
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  admit "".
Qed.

End INJINVID.


Require Import IdSimAsmExtra.
Require Import Integers.
Require Import mktac.


Section UNFREEPARALLEL.

Variable P_tgt : SimMemInjInv.memblk_invariant.

Local Instance SimMemTopP: SimMem.class := SimMemInjInvC.SimMemInjInv top1 P_tgt.

Lemma Mem_unfree_parallel
      (sm0 sm_arg sm_ret: SimMem.t) blk_src ofs_src ofs_tgt sz blk_tgt delta
      m_src1
      (DELTA: sm0.(SimMemInjInv.minj).(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
      (VAL: ofs_tgt = Ptrofs.add ofs_src (Ptrofs.repr delta))
      (MLE0: SimMemInjInv.le' sm0 sm_arg)
      (FREESRC: Mem.free
                  (SimMem.src sm0) blk_src
                  (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) =
                Some (SimMem.src sm_arg))
      (FREETGT: Mem.free
                  (SimMem.tgt sm0) blk_tgt
                  (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz) =
                Some (SimMem.tgt sm_arg))
      (MWF0: SimMem.wf sm0)
      (MWF1: SimMem.wf sm_arg)
      (MWF2: SimMem.wf sm_ret)
      (MLE1: SimMem.le (SimMem.lift sm_arg) sm_ret)
      (UNFREESRC: Mem_unfree
                    (SimMem.src sm_ret) blk_src
                    (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) =
                  Some m_src1)
  :
    exists sm1,
      (<<MSRC: sm1.(SimMem.src) = m_src1>>)
      /\ (<<MINJ: sm1.(SimMemInjInv.minj).(SimMemInj.inj) = sm_ret.(SimMemInjInv.minj).(SimMemInj.inj)>>)
      /\ (<<FREETGT: Mem_unfree
                       (SimMem.tgt sm_ret) blk_tgt
                       (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz)
                     = Some sm1.(SimMem.tgt)>>)
      /\ (<<MWF: SimMem.wf sm1>>)
      /\ (<<MLE: SimMem.le sm0 sm1>>).
Proof.
  ss.
  destruct sm0 as [sm0 mem_inv_src0 mem_inv_tgt0].
  destruct sm_arg as [sm_arg mem_inv_src_arg mem_inv_tgt_arg].
  destruct sm_ret as [sm_ret mem_inv_src_ret mem_inv_tgt_ret].
  destruct MWF0 as [MWF0 _ SATTGT0 INVRANGESRC0 INVRANGETGT0].
  destruct MWF1 as [MWF1 _ SATTGT1 INVRANGESRC1 INVRANGETGT1].
  destruct MWF2 as [MWF2 _ SATTGT2 INVRANGESRC2 INVRANGETGT2].
  destruct MLE0 as [MLE0 MINVEQSRC0 MINVEQTGT0].
  destruct MLE1 as [MLE1 MINVEQSRC1 MINVEQTGT1].
  ss. clarify.
  assert (DELTA0: SimMemInj.inj sm_ret blk_src = Some (blk_tgt, delta)).
  { inv MLE0. inv MLE1. ss. eapply INCR0. eapply INCR. eauto. }
  cinv MWF0. cinv MWF2. exploit Mem_unfree_parallel_inject; eauto.
  { ii. cinv PUBLIC. eapply Mem.mi_align; eauto.
    ii. exploit PERM; eauto. i. des.
    - eapply Mem.perm_cur. instantiate (1:=p). eapply Mem.perm_implies.
      + eapply Mem.free_range_perm; eauto.
      + econs.
    - eapply Mem.perm_free_3; eauto. inv MLE1. eapply MAXSRC; eauto.
      ss. eapply Mem.valid_block_free_1; eauto.
      eapply Mem.valid_block_inject_1; try apply DELTA; eauto. }
  { ii. inv MWF0. eapply Mem.mi_representable; eauto. inv MLE1. ss. des.
    - left. eapply Mem.perm_free_3; eauto. eapply MAXSRC; eauto.
      eapply Mem.valid_block_free_1; eauto.
      eapply Mem.valid_block_inject_1; try apply DELTA; eauto.
    - right. eapply Mem.perm_free_3; eauto. eapply MAXSRC; eauto.
      eapply Mem.valid_block_free_1; eauto.
      eapply Mem.valid_block_inject_1; try apply DELTA; eauto.
    - left. eapply Mem.perm_cur. eapply Mem.perm_implies.
      + eapply Mem.free_range_perm; eauto.
      + econs.
    - right. eapply Mem.perm_cur. eapply Mem.perm_implies.
      + eapply Mem.free_range_perm; eauto.
      + econs. }
  { ii. inv MLE1. ss. eapply MAXTGT in H.
    - eapply Mem_free_noperm; eauto.
    - eapply Mem.valid_block_free_1; eauto.
      eapply Mem.valid_block_inject_2; try apply DELTA; eauto. }
  { i. des. eexists (SimMemInjInv.mk (SimMemInjC.update sm0 _ _ _) mem_inv_src_ret mem_inv_tgt_ret).
    inv MLE0. inv MLE1. inv MWF1. inv MWF2. esplits; ss; eauto.
    - econs; ss; eauto; [econs; ss; eauto|..].
      + admit "".
      + admit "".
      + etrans; eauto.
        eapply Mem.unchanged_on_nextblock in SRCUNCHANGED0.
        eapply Mem.unchanged_on_nextblock in SRCUNCHANGED.
        etrans; eauto. etrans; eauto.
        eapply Mem_nextblock_unfree in UNFREESRC. rewrite UNFREESRC. refl.
      + etrans; eauto.
        eapply Mem.unchanged_on_nextblock in TGTUNCHANGED0.
        eapply Mem.unchanged_on_nextblock in TGTUNCHANGED.
        etrans; eauto. etrans; eauto.
        eapply Mem_nextblock_unfree in UNFREE. rewrite UNFREE. refl.
      + eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
        * ii. exploit INVRANGETGT2; eauto. i. des.
          unfold Mem.valid_block. eapply Plt_Ple_trans; eauto.
        * eapply Mem.unchanged_on_implies.
          { eapply Mem_unfree_unchanged_on; eauto. }
          { ii. exploit INVRANGETGT0; eauto. i. des.
            exfalso. destruct H1. clarify. eapply H2; eauto.
            eapply Mem.perm_cur. eapply Mem.perm_implies.
            - eapply Mem.free_range_perm; eauto.
              instantiate (1:=Ptrofs.unsigned ofs_src + delta). clear - a. lia.
            - econs. }
      + admit "".
      + admit "".
    - econs; ss; eauto. econs; ss; eauto.
      + etrans; eauto.
      + etrans; eauto. etrans; eauto.
        { rewrite SRCPARENTEQ in *.
          eapply Mem.unchanged_on_implies; eauto.
          ss. ii. admit "". }
        { eapply Mem.unchanged_on_implies.
          - eapply Mem_unfree_unchanged_on; eauto.
          - ss. ii. eapply SRCEXT in H. destruct H.
            unfold brange, loc_unmapped in *. des. clarify. }
      + etrans; eauto. etrans; eauto.
        { rewrite TGTPARENTEQ in *.
          eapply Mem.unchanged_on_implies; eauto.
          ss. ii. admit "". }
        { eapply Mem.unchanged_on_implies.
          - eapply Mem_unfree_unchanged_on; eauto.
          - ii. eapply TGTEXT in H. destruct H.
            unfold brange in *. destruct H1. clarify.
            eapply H; eauto. eapply Mem.perm_cur. eapply Mem.perm_implies.
            + eapply Mem.free_range_perm; eauto.
              erewrite Mem.address_inject in H3; try apply PUBLIC; eauto.
              * lia.
              * eapply Mem.free_range_perm; eauto. lia.
            + econs. }
      + admit "ez".
      + eapply Mem_unfree_perm_restore; try apply UNFREESRC; eauto.
        * ii. eapply MAXSRC0; eauto.
          unfold Mem.valid_block in *. erewrite Mem.nextblock_free; eauto.
        * eapply Mem.unchanged_on_nextblock; eauto.
      + eapply Mem_unfree_perm_restore; try apply UNFREE; eauto.
        * ii. eapply MAXTGT0; eauto.
          unfold Mem.valid_block in *. erewrite Mem.nextblock_free; eauto.
        * eapply Mem.unchanged_on_nextblock; eauto.
  }
  Unshelve. apply 0.
Qed.

End UNFREEPARALLEL.
