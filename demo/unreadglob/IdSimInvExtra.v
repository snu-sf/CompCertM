Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMemLift Sound SimSymb.
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

Local Existing Instance SimSymbDropInv.SimMemInvTop.
Local Existing Instance SimSymbDropInv.SimSymbDropInv.

Lemma SimSymbDropInv_match_globals F `{HasExternal F} V sm0 sk_src sk_tgt skenv_src skenv_tgt (p: AST.program F V)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 (SimSymbDropInv.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt)
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

Lemma SimSymbDropInv_find_None F `{HasExternal F} V (p: AST.program F V)
      sm0 sk_src sk_tgt skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 (SimSymbDropInv.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt)
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

Lemma SimSymbIdInv_match_globals F `{HasExternal F} V sm0 sk_src sk_tgt skenv_src skenv_tgt (p: AST.program F V)
      (SIMSKE: SimMemInjInvC.sim_skenv_inj sm0 (SimMemInjInvC.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt)
  :
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0.(SimMemInjInv.minj)).
Proof.
  inv SIMSKE. inv INJECT. inv SIMSKENV. econs; ss; eauto.
  - ii. exploit IMAGE; eauto.
    + left. eapply Genv.genv_defs_range in FINDSRC. eauto.
    + i. des. clarify. esplits; eauto.
  - i. exploit INVCOMPAT; eauto. i. des.
    exploit DOMAIN; eauto.
    eapply Genv.genv_symb_range in FINDSRC. eauto.
Qed.

Lemma SimSymbIdInv_find_None F `{HasExternal F} V (p: AST.program F V)
      sm0 sk_src sk_tgt skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimMemInjInvC.sim_skenv_inj sm0 (SimMemInjInvC.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef)
  :
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  destruct (Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt) eqn:FIND; auto.
  inv SIMSKE. inv SIMSKENV. inv INJECT. inv FPTR; eauto.
  - exploit IMAGE; eauto.
    + right. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      eapply Genv.genv_defs_range in Heq. ss.
    + i. des. clarify. erewrite Integers.Ptrofs.add_zero in FIND. clarify.
  - clarify.
Qed.

End INJINVID.


Require Import IdSimAsmExtra.
Require Import Integers.
Require Import mktac.


Section UNFREEPARALLEL.

Variable P_tgt : SimMemInjInv.memblk_invariant.

Local Instance SimMemInvP : SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P_tgt.

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
      (MLE1: SimMem.le (SimMemLift.lift sm_arg) sm_ret)
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
      + etrans. rewrite SRCPARENTEQ. eapply SRCEXT1.
        unfold SimMemInj.src_private, SimMemInj.valid_blocks in *. ss. ii; des. split.
        * eapply SimMemInj.loc_unmapped_frozen; eauto.
        * rewrite <- Mem_valid_block_unfree; try eapply UNFREESRC.
          eapply Mem.valid_block_unchanged_on; eauto.
      + unfold SimMemInj.tgt_private, SimMemInj.valid_blocks in *. ss. ii; des. split.
        * r. ii. destruct (eq_block b0 blk_src).
          { subst. clarify. eapply TGTEXT in PR. des. r in PR. eapply PR; et.
            eapply Mem_unfree_perm_restore; try eapply UNFREESRC; et.
            - ii. eapply MAXSRC0; et. eapply Mem.valid_block_free_1; et.
            - eapply Mem.unchanged_on_nextblock; et.
            - eapply Mem.valid_block_inject_1; try eapply PUBLIC; et.
          }
          { rewrite TGTPARENTEQ in PR. eapply TGTEXT1 in PR. des. r in PR. eapply PR; et.
            { eapply SimMemInj.frozen_preserves_tgt; et. }
            eapply MAXSRC0; et.
            { eapply Mem.valid_block_inject_1; try eapply PUBLIC1. eapply SimMemInj.frozen_preserves_tgt; et. }
            clear - H0 UNFREESRC n. unfold Mem_unfree, Mem.perm in *. des_ifs. ss. rewrite PMap.gso in H0; et.
          }
        * rewrite TGTPARENTEQ in PR. eapply TGTEXT1 in PR. des.
          rewrite <- Mem_valid_block_unfree; try eapply UNFREE.
          eapply Mem.valid_block_unchanged_on; eauto.
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
      + ii. exploit INVRANGESRC0; et. i; des. exploit INVRANGESRC2; et. i; des. esplits; et.
      + ii. exploit INVRANGETGT0; et. i; des. esplits; et. r. ii. destruct (eq_block b0 blk_src).
          { subst. clarify. r in H. eapply H; et.
            eapply Mem_unfree_perm_restore; try eapply UNFREESRC; et.
            - ii. eapply MAXSRC0; et. eapply Mem.valid_block_free_1; et.
            - eapply Mem.unchanged_on_nextblock; et.
            - eapply Mem.valid_block_inject_1; try eapply PUBLIC; et.
          }
          { exploit INVRANGETGT1; et. i; des. r in H4. eapply H4; et.
            { eapply SimMemInj.frozen_preserves_tgt; et. eapply Pos.lt_le_trans; et. }
            eapply MAXSRC0; et.
            { eapply Mem.valid_block_inject_1; try eapply PUBLIC1.
              eapply SimMemInj.frozen_preserves_tgt; et. eapply Pos.lt_le_trans; et. }
            clear - H0 UNFREESRC n. unfold Mem_unfree, Mem.perm in *. des_ifs. ss. rewrite PMap.gso in H3; et.
          }
    - econs; ss; eauto.
      assert(FROZENHI: SimMemInj.frozen (SimMemInj.inj sm0) (SimMemInj.inj sm_ret) (SimMemInj.src_parent_nb sm0)
                                        (SimMemInj.tgt_parent_nb sm0)).
      { + econs. ii. des. destruct (SimMemInj.inj sm_arg b_src) eqn: T.
          * destruct p. erewrite INCR0 in NEW0; et. clarify. eapply FROZEN. split; eauto.
          * eapply SimMemInj.inject_separated_frozen in FROZEN0. exploit FROZEN0; eauto. i. des.
            rewrite SRCPARENTEQNB, TGTPARENTEQNB. unfold Mem.valid_block in *. clear - H H0 SRCLE1 TGTLE1.
            assert(Ple (Mem.nextblock (SimMemInj.src sm_arg)) b_src) by xomega.
            assert(Ple (Mem.nextblock (SimMemInj.tgt sm_arg)) b_tgt) by xomega.
            split; eapply Pos.le_trans; eauto.
      }
      econs; ss; eauto.
      + etrans; eauto.
      + etrans; eauto. etrans; eauto.
        { rewrite SRCPARENTEQ in *.
          eapply Mem.unchanged_on_implies; eauto.
          ss. ii. split; et. ii. exploit INVRANGESRC0; et. i; des. et. }
        { eapply Mem.unchanged_on_implies.
          - eapply Mem_unfree_unchanged_on; eauto.
          - ss. ii. eapply SRCEXT in H. destruct H.
            unfold brange, loc_unmapped in *. des. clarify. }
      + etrans; eauto. etrans; eauto.
        { rewrite TGTPARENTEQ in *.
          eapply Mem.unchanged_on_implies; eauto.
          ss. ii. split; et. ii. exploit INVRANGETGT0; et. i; des. et. }
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
      + eapply SimMemInj.frozen_shortened; eauto.
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

Require Import AsmC.

Inductive match_states P0 P1
          (skenv_link_tgt: SkEnv.t)
          (ge_src ge_tgt: genv)
  : nat-> AsmC.state -> AsmC.state -> SimMemInjInv.t' -> Prop :=
| match_states_intro
    j init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : SimMemInjInv.t')
    (AGREE: AsmStepInj.agree j rs_src rs_tgt)
    (AGREEINIT: AsmStepInj.agree j init_rs_src init_rs_tgt)
    (MCOMPATSRC: m_src = sm0.(SimMemInjInv.minj).(SimMemInj.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMemInjInv.minj).(SimMemInj.tgt))
    (MCOMPATINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MWF: @SimMemInjInv.wf' P0 P1 sm0)
    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITRS: wf_init_rss fd.(fn_sig) init_rs_src init_rs_tgt)
    (RAWF: Genv.find_funct skenv_link_tgt (init_rs_tgt RA) = None)
    (RSPDELTA: forall (SIG: sig_cstyle fd.(fn_sig) = true)
                      blk_src ofs (RSPSRC: init_rs_src RSP = Vptr blk_src ofs),
        exists blk_tgt,
          (j blk_src = Some (blk_tgt, 0)))
  :
    match_states
      P0 P1
      skenv_link_tgt
      ge_src ge_tgt 0
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0
.
