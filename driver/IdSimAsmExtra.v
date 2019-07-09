Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
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

Require Import AsmregsC.
Require Import MatchSimModSemExcl2 MatchSimModSem.
Require Import StoreArguments StoreArgumentsProps.
Require Import AsmStepInj AsmStepExt IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import AsmExtra IdSimExtra.
Require Import Conventions1C.

Require Import mktac.


Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.


(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)


Lemma lessdef_commute j src0 src1 tgt0 tgt1
      (INJ0: Val.inject j src0 tgt0)
      (INJ1: Val.inject j src1 tgt1)
      (LESS: Val.lessdef src0 src1)
      (UNDEF: src0 = Vundef -> tgt0 = Vundef):
    Val.lessdef tgt0 tgt1.
Proof.
  inv LESS.
  - inv INJ0; inv INJ1; ss; try econs; clarify. rewrite UNDEF; auto.
  - rewrite UNDEF; auto.
Qed.

(* move it to MemoryC after stablizing *)
Section TOMEMORYC.

  Lemma Z2Nat_range n:
    Z.of_nat (Z.to_nat n) = if (zle 0 n) then n else 0.
  Proof.
    des_ifs.
    - rewrite Z2Nat.id; eauto.
    - unfold Z.to_nat. des_ifs.
  Qed.

  Theorem Mem_unfree_parallel_inject
          j m1 m2 b ofs_src ofs_tgt sz m1' b' delta
          (INJECT: Mem.inject j m1 m2)
          (UNFREE: Mem_unfree m1 b (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) = Some m1')
          (VAL: ofs_tgt = Ptrofs.add ofs_src (Ptrofs.repr delta))
          (DELTA: j b = Some (b', delta))
          (ALIGN: forall ofs chunk p (PERM: forall ofs0 (BOUND: ofs <= ofs0 < ofs + size_chunk chunk),
                                         (Ptrofs.unsigned ofs_src) <= ofs0 < (Ptrofs.unsigned ofs_src + sz) \/ Mem.perm m1 b ofs0 Max p),
              (align_chunk chunk | delta))
          (REPRESENTABLE: forall ofs (PERM: Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
                                            Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty \/
                                            (Ptrofs.unsigned ofs_src) <= Ptrofs.unsigned ofs < (Ptrofs.unsigned ofs_src + sz) \/
                                            (Ptrofs.unsigned ofs_src) <= Ptrofs.unsigned ofs - 1 < (Ptrofs.unsigned ofs_src + sz)),
              delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned)
          (NOPERM: Mem_range_noperm m2 b' (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz)):
      exists m2',
        (<<UNFREE: Mem_unfree m2 b' (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz) = Some m2'>>)
        /\ (<<INJECT: Mem.inject j m1' m2'>>).
  Proof.
    unfold Mem_unfree in UNFREE. des_ifs.
    assert (VALID: Plt b' (Mem.nextblock m2)).
    { exploit Mem.valid_block_inject_2; eauto. }
    unfold Mem_unfree in *. des_ifs. esplits; eauto. ss.
    assert (NOOVERLAP: forall b_src delta' ofs k p (DELTA: j b_src = Some (b', delta'))
                              (OFS: (Ptrofs.unsigned ofs_src) + delta <= ofs + delta' < Ptrofs.unsigned ofs_src + delta + sz)
                              (PERM: Mem.perm m1 b_src ofs k p),
               False).
    { i. exploit Mem.perm_inject; eauto. i. exploit NOPERM; eauto.
      - erewrite unsigned_add; eauto. eapply REPRESENTABLE; eauto. lia.
      - eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }

    econs; ss; eauto; i.

    - cinv (Mem.mi_inj _ _ _ INJECT).
      econs; ss; eauto; i.
      + destruct (peq b b1); clarify.
        * unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *. des_ifs_safe.
          des_ifs; clarify; eauto; try lia.
          { exploit Mem.perm_inject; eauto. i. exfalso. eapply NOPERM; eauto.
            eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }
          { exploit Mem.perm_inject; eauto. i. exfalso. eapply NOPERM; eauto.
            eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }
          { erewrite unsigned_add in *; try lia. eapply REPRESENTABLE; try lia. }
          { erewrite unsigned_add in *; try lia; eapply REPRESENTABLE; try lia. }
        * assert (Mem.perm m2 b2 (ofs + delta0) k p1).
          { exploit Mem.perm_inject; eauto. unfold Mem.perm in *. ss.
            rewrite PMap.gso in H0; eauto.
          }
          unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *.
          des_ifs. exfalso. exploit NOPERM; eauto.
          eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
      + ss. destruct (peq b1 b); clarify.
        { exploit ALIGN; eauto. i.
          exploit H0; eauto. unfold Mem.perm in *. ss. rewrite PMap.gss.
          unfold proj_sumbool. des_ifs; eauto. }
        { exploit Mem.mi_align; try eapply Mem.mi_inj; eauto.
          - ii. exploit H0; eauto. unfold Mem.perm. ss. rewrite PMap.gso; eauto. }
      + unfold Mem.perm, proj_sumbool in *. ss. repeat rewrite PMap.gsspec in *. des_ifs; eauto.
        * rewrite Mem_setN_in_repeat; eauto; [econs|]. rewrite Z2Nat.id; nia.
        * zsimpl. destruct (zlt 0 sz).
          { repeat rewrite Mem.setN_outside; cycle 1; eauto.
            { right. rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia. erewrite unsigned_add in *; eauto; try lia; eapply REPRESENTABLE; lia. }
            { rewrite length_list_repeat. rewrite Z2Nat_range. des_ifs; try lia. } }
          { repeat rewrite Mem.setN_outside; cycle 1; eauto; rewrite length_list_repeat; rewrite Z2Nat_range; des_ifs; try nia. }
        * zsimpl. destruct (zlt 0 sz).
          { repeat rewrite Mem.setN_outside; cycle 1; eauto.
            { left. erewrite unsigned_add in *; eauto; try lia; eapply REPRESENTABLE; lia. }
            { rewrite length_list_repeat. rewrite Z2Nat_range. des_ifs; try lia. } }
          { repeat rewrite Mem.setN_outside; cycle 1; eauto; rewrite length_list_repeat; rewrite Z2Nat_range; des_ifs; try nia. }
        * repeat rewrite Mem.setN_outside; cycle 1; eauto; rewrite length_list_repeat; rewrite Z2Nat_range; des_ifs; try nia.
        * repeat rewrite Mem.setN_outside; cycle 1; eauto. rewrite length_list_repeat. rewrite Z2Nat_range. des_ifs; try nia.
          apply NNPP. ii. exploit NOOVERLAP; eauto. erewrite unsigned_add in *; eauto; try lia; eapply REPRESENTABLE; lia.

    - exploit Mem.mi_freeblocks; eauto.
    - exploit Mem.mi_mappedblocks; eauto.
    - ii. unfold Mem.perm in *. ss. apply imply_to_or. i. clarify.
      rewrite PMap.gsspec in *. unfold proj_sumbool in *.
      des_ifs; ss; try (by exploit Mem.mi_no_overlap; try eapply H; eauto; i; des; clarify; eauto);
        try (ii; exploit NOOVERLAP; eauto; nia).
    - destruct (peq b0 b); clarify.
      + exploit REPRESENTABLE; eauto. unfold Mem.perm in *. ss. rewrite PMap.gss in *.
        unfold proj_sumbool in *. des_ifs; des; eauto; lia.
      + exploit Mem.mi_representable; eauto.
        unfold Mem.perm in *. ss. rewrite PMap.gso in *; eauto.
    - unfold Mem.perm, proj_sumbool in *. ss.
      rewrite PMap.gsspec in *.
      des_ifs; ss; eauto; (try by exploit Mem.mi_perm_inv; eauto); try by (left; try econs; try lia).
      { left. erewrite unsigned_add in *; eauto; try lia. eapply REPRESENTABLE; eauto. lia. }
      { destruct (zlt 0 sz); try lia. left. erewrite unsigned_add in *; eauto; try lia; eapply REPRESENTABLE; eauto; lia. }
      { right. ii. exploit Mem.perm_inject; eauto. i. eapply NOPERM; eauto. }
  Qed.

  Lemma Mem_unfree_perm_restore m0 m1 m2 m3 blk lo hi
        (FREE: Mem.free m0 blk lo hi = Some m1)
        (MAXPERM: forall b ofs
            (VALID: Mem.valid_block m0 b),
            <<MAX: Mem.perm m2 b ofs Max <1= Mem.perm m1 b ofs Max>>)
        (UNFREE: Mem_unfree m2 blk lo hi = Some m3)
        (NBLE: Ple (Mem.nextblock m1) (Mem.nextblock m2)):
      forall b ofs (VALID: Mem.valid_block m0 b),
        (<<MAX: Mem.perm m3 b ofs Max <1= Mem.perm m0 b ofs Max>>).
  Proof.
    ii. destruct (classic (brange blk lo hi b ofs)).
    - destruct H. clarify. eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply perm_F_any.
      eapply Mem.free_range_perm; eauto.
    - eapply Mem.perm_unchanged_on_2; auto.
      { eapply Mem.free_unchanged_on; eauto. instantiate (1:= ~2 brange blk lo hi). ii. eapply H1. splits; auto. }
      { auto. }
      eapply MAXPERM; eauto. eapply Mem.perm_unchanged_on_2; eauto.
      { eapply Mem_unfree_unchanged_on; eauto. }
      { auto. }
      { eapply Mem.nextblock_free in FREE. eapply Plt_Ple_trans; eauto. erewrite <- FREE. auto. }
  Qed.

  Lemma Mem_unfree_parallel
        sm0 sm_arg sm_ret blk_src ofs_src ofs_tgt sz blk_tgt delta m_src1
        (DELTA: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (VAL: ofs_tgt = Ptrofs.add ofs_src (Ptrofs.repr delta))
        (MLE0: SimMemInj.le' sm0 sm_arg)
        (FREESRC: Mem.free
                    (SimMemInj.src sm0) blk_src
                    (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) =
                  Some (SimMemInj.src sm_arg))
        (FREETGT: Mem.free
                    (SimMemInj.tgt sm0) blk_tgt
                    (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz) =
                  Some (SimMemInj.tgt sm_arg))
        (MWF0: SimMemInj.wf' sm0)
        (MWF1: SimMemInj.wf' sm_arg)
        (MWF2: SimMemInj.wf' sm_ret)
        (MLE1: SimMemInj.le' (SimMemInj.lift' sm_arg) sm_ret)
        (UNFREESRC: Mem_unfree
                      (SimMemInj.src sm_ret) blk_src
                      (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) =
                    Some m_src1):
      exists sm1,
        (<<MSRC: sm1.(SimMemInj.src) = m_src1>>)
        /\ (<<MINJ: sm1.(SimMemInj.inj) = sm_ret.(SimMemInj.inj)>>)
        /\ (<<FREETGT: Mem_unfree
                         (SimMemInj.tgt sm_ret) blk_tgt
                         (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz)
                       = Some sm1.(SimMemInj.tgt)>>)
        /\ (<<MWF: SimMemInj.wf' sm1>>)
        /\ (<<MLE: SimMemInj.le' sm0 sm1>>).
  Proof.
    assert (DELTA0: SimMemInj.inj sm_ret blk_src = Some (blk_tgt, delta)).
    { inv MLE0. inv MLE1. ss. eapply INCR0. eapply INCR. eauto. }
    cinv MWF0. cinv MWF2. exploit Mem_unfree_parallel_inject; eauto.
    { ii. cinv PUBLIC. eapply Mem.mi_align; eauto.
      ii. exploit PERM; eauto. i. des.
      - eapply Mem.perm_cur. instantiate (1:=p). eapply Mem.perm_implies; try eapply perm_F_any.
        eapply Mem.free_range_perm; eauto.
      - eapply Mem.perm_free_3; eauto. inv MLE1. eapply MAXSRC; eauto.
        ss. eapply Mem.valid_block_free_1; eauto.
        eapply Mem.valid_block_inject_1; try apply DELTA; eauto. }
    { ii. inv MWF0. eapply Mem.mi_representable; eauto. inv MLE1. ss. des.
      - left. eapply Mem.perm_free_3; eauto. eapply MAXSRC; eauto.
        eapply Mem.valid_block_free_1; eauto. eapply Mem.valid_block_inject_1; try apply DELTA; eauto.
      - right. eapply Mem.perm_free_3; eauto. eapply MAXSRC; eauto.
        eapply Mem.valid_block_free_1; eauto. eapply Mem.valid_block_inject_1; try apply DELTA; eauto.
      - left. eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply perm_F_any.
        eapply Mem.free_range_perm; eauto.
      - right. eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply perm_F_any.
        eapply Mem.free_range_perm; eauto. }
    { ii. inv MLE1. ss. eapply MAXTGT in H.
      - eapply Mem_free_noperm; eauto.
      - eapply Mem.valid_block_free_1; eauto. eapply Mem.valid_block_inject_2; try apply DELTA; eauto. }
    { i. des. eexists (SimMemInjC.update sm0 _ _ _). inv MLE0. inv MLE1. inv MWF1. esplits; ss; eauto.
      - econs; ss; eauto.
        + etrans. rewrite SRCPARENTEQ. eapply SRCEXT1.
          unfold SimMemInj.src_private, SimMemInj.valid_blocks in *. ss. ii; des. split.
          * eapply SimMemInj.loc_unmapped_frozen; eauto.
          * rewrite <- Mem_valid_block_unfree; try eapply UNFREESRC. eapply Mem.valid_block_unchanged_on; eauto.
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
            rewrite <- Mem_valid_block_unfree; try eapply UNFREE. eapply Mem.valid_block_unchanged_on; eauto.
        + etrans; eauto. eapply Mem.unchanged_on_nextblock in SRCUNCHANGED0.
          eapply Mem.unchanged_on_nextblock in SRCUNCHANGED. etrans; eauto. etrans; eauto.
          eapply Mem_nextblock_unfree in UNFREESRC. rewrite UNFREESRC. refl.
        + etrans; eauto. eapply Mem.unchanged_on_nextblock in TGTUNCHANGED0.
          eapply Mem.unchanged_on_nextblock in TGTUNCHANGED. etrans; eauto. etrans; eauto.
          eapply Mem_nextblock_unfree in UNFREE. rewrite UNFREE. refl.
      - assert(FROZENHI: SimMemInj.frozen (SimMemInj.inj sm0) (SimMemInj.inj sm_ret) (SimMemInj.src_parent_nb sm0) (SimMemInj.tgt_parent_nb sm0)).
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
          { rewrite SRCPARENTEQ in *. eapply Mem.unchanged_on_implies; eauto. }
          { eapply Mem.unchanged_on_implies.
            - eapply Mem_unfree_unchanged_on; eauto.
            - ii. eapply SRCEXT in H. destruct H. unfold brange, loc_unmapped in *. des. clarify. }
        + etrans; eauto. etrans; eauto.
          { rewrite TGTPARENTEQ in *. eapply Mem.unchanged_on_implies; eauto. }
          { eapply Mem.unchanged_on_implies.
            - eapply Mem_unfree_unchanged_on; eauto.
            - ii. eapply TGTEXT in H. destruct H. unfold brange in *. destruct H1. clarify.
              eapply H; eauto. eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply perm_F_any.
              + eapply Mem.free_range_perm; eauto.
                erewrite Mem.address_inject in H3; try apply PUBLIC; eauto; try lia.
                eapply Mem.free_range_perm; eauto. lia. }
        + eapply SimMemInj.frozen_shortened; eauto.
        + eapply Mem_unfree_perm_restore; try apply UNFREESRC; eauto.
          * ii. eapply MAXSRC0; eauto. unfold Mem.valid_block in *. erewrite Mem.nextblock_free; eauto.
          * eapply Mem.unchanged_on_nextblock; eauto.
        + eapply Mem_unfree_perm_restore; try apply UNFREE; eauto.
          * ii. eapply MAXTGT0; eauto. unfold Mem.valid_block in *. erewrite Mem.nextblock_free; eauto.
          * eapply Mem.unchanged_on_nextblock; eauto.
    }
  Qed.

End TOMEMORYC.

Definition junk_inj (m_src0 m_tgt0: mem) (j: meminj) (n: nat): meminj :=
  fun blk =>
    if plt blk (Mem.nextblock m_src0) then j blk
    else
      if plt blk (Mem.nextblock (JunkBlock.assign_junk_blocks m_src0 n)) then
        Some ((blk + (Mem.nextblock m_tgt0) - (Mem.nextblock m_src0))%positive, 0)
      else j blk.

Definition src_junk_val (m_src0 m_tgt0: mem) (n: nat) (v: val): val :=
  match v with
  | Vptr blk ofs =>
    if plt blk (Mem.nextblock m_tgt0) then Vundef
    else if plt blk (Mem.nextblock (JunkBlock.assign_junk_blocks m_tgt0 n)) then
           Vptr (blk + (Mem.nextblock m_src0) - (Mem.nextblock m_tgt0))%positive ofs
         else Vundef
  | _ => v
  end.

(* TODO: Move this lemmas *)
Lemma Plt_lemma a b c
      (LE: ~ Plt a b):
    ~ Plt (a + c - b) c.
Proof.
  ii. unfold Plt in *.
  erewrite <- Pos.compare_lt_iff in H. erewrite <- Pos.add_compare_mono_r in H. instantiate (1:=b) in H.
  erewrite Pos.sub_add in H; [|xomega]. rewrite Pos.add_comm in H. apply LE.
  erewrite -> Pos.compare_lt_iff in H. xomega.
Qed.

Lemma Plt_lemma2 a b c d
      (LE: ~ Plt a b)
      (LT: Plt a (b + d)):
    Plt (a + c - b) (c + d).
Proof.
  unfold Plt in *.
  erewrite <- Pos.compare_lt_iff in LT.
  erewrite <- Pos.add_compare_mono_r in LT. instantiate (1:=c) in LT.
  erewrite <- Pos.sub_compare_mono_r in LT.
  - instantiate (1:=b) in LT.
    erewrite -> Pos.compare_lt_iff in LT.
    rpapply LT. replace (b + d + c)%positive with (c + d + b)%positive.
    + rewrite Pos.add_sub. auto.
    + clear. xomega.
  - clear LT. xomega.
  - clear. xomega.
Qed.

Lemma src_junk_val_inj m_src0 m_tgt0 j n v
      (INJ: Mem.inject j m_src0 m_tgt0):
    Val.inject (junk_inj m_src0 m_tgt0 j n) (src_junk_val m_src0 m_tgt0 n v) v.
Proof.
  unfold src_junk_val. des_ifs; eauto. econs.
  - unfold junk_inj. des_ifs.
    + apply Plt_lemma in p0; eauto. clarify.
    + instantiate (1:=0).
      replace (b + Mem.nextblock m_src0 - Mem.nextblock m_tgt0 + Mem.nextblock m_tgt0 - Mem.nextblock m_src0)%positive with b; auto.
      clear - n0. rewrite Pos.sub_add; try xomega. rewrite Pos.add_sub. auto.
    + exfalso. rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs. apply n2. eapply Plt_lemma2 in p; eauto.
  - symmetry. eapply Ptrofs.add_zero.
Qed.

Lemma src_junk_val_junk m_src0 m_tgt0 n v
      (JUNK: JunkBlock.is_junk_value m_tgt0 (JunkBlock.assign_junk_blocks m_tgt0 n) v):
    JunkBlock.is_junk_value
      m_src0 (JunkBlock.assign_junk_blocks m_src0 n)
      (src_junk_val m_src0 m_tgt0 n v).
Proof.
  unfold JunkBlock.is_junk_value, src_junk_val in *. des_ifs. des. split.
  - ii. unfold Mem.valid_block in *. eapply Plt_lemma; eauto.
  - unfold Mem.valid_block. rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs. eapply Plt_lemma2; eauto.
Qed.

Definition set_regset_junk
           (m_src0 m_tgt0: mem) (n: nat)
           (rs0 rs1: Mach.regset) (sg: signature) (mr: mreg) : val :=
  if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
  then src_junk_val m_src0 m_tgt0 n (rs1 mr) else rs0 mr.

Lemma junk_inj_incr m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0):
    inject_incr j (junk_inj m_src0 m_tgt0 j n).
Proof.
  ii. unfold junk_inj. des_ifs. exfalso. eapply Mem.valid_block_inject_1 in H; eauto.
Qed.

Lemma assign_junk_blocks_parallel_inject m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0)
  :
    Mem.inject
      (junk_inj m_src0 m_tgt0 j n)
      (JunkBlock.assign_junk_blocks m_src0 n)
      (JunkBlock.assign_junk_blocks m_tgt0 n).
Proof.
  dup INJ. inv INJ. unfold junk_inj.
  econs; [inv mi_inj; econs|..]; i; repeat rewrite JunkBlock.assign_junk_blocks_perm in *.
  - des_ifs; eauto. eapply Mem.perm_valid_block in H0. exfalso. eauto.
  - unfold Mem.range_perm in *. repeat rewrite JunkBlock.assign_junk_blocks_perm in *. des_ifs; eauto. apply Z.divide_0_r.
  - des_ifs.
    + eapply memval_inject_incr; [..|eapply junk_inj_incr; eauto].
      exploit mi_memval; eauto. i. rpapply H1; eauto.
      * eapply Mem.unchanged_on_contents; eauto.
        { eapply JunkBlock.assign_junk_blocks_unchanged_on. } ss.
      * eapply Mem.unchanged_on_contents; eauto.
        { eapply JunkBlock.assign_junk_blocks_unchanged_on. } ss.
    + eapply Mem.perm_valid_block in H0. exfalso. eauto.
    + eapply Mem.perm_valid_block in H0. exfalso. eauto.
  - des_ifs.
    + exploit Mem.valid_block_unchanged_on; try apply JunkBlock.assign_junk_blocks_unchanged_on; eauto.
    + destruct (j b) as [[]|] eqn:DELTA; auto. exfalso. eapply Mem.valid_block_inject_1 in DELTA; try apply INJ0; eauto.
  - des_ifs.
    + eapply Mem.valid_block_unchanged_on;
        try apply JunkBlock.assign_junk_blocks_unchanged_on; eauto.
    + unfold Mem.valid_block. rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs. eapply Plt_lemma2; eauto.
    + exfalso. eapply Mem.valid_block_inject_1 in H; eauto.
  - ii. repeat rewrite JunkBlock.assign_junk_blocks_perm in *. des_ifs; eauto; exfalso; apply_all_once Mem.perm_valid_block; eauto.
  - set (Ptrofs.unsigned_range_2 ofs). des_ifs; des; eauto; lia.
  - des_ifs; eauto. zsimpl. exfalso. eapply Mem.perm_valid_block in H0.
    unfold Mem.valid_block in *. eapply Plt_lemma; eauto.
Qed.

Lemma junk_inj_separated m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0):
    inject_separated j (junk_inj m_src0 m_tgt0 j n) m_src0 m_tgt0.
Proof.
  unfold junk_inj. ii. des_ifs. split; auto. unfold Mem.valid_block. eapply Plt_lemma. auto.
Qed.

Lemma assign_junk_blocks_parallel n sm0
      (MWF: SimMemInj.wf' sm0):
    exists sm1,
      (<<MSRC: sm1.(SimMemInj.src) = JunkBlock.assign_junk_blocks (SimMemInj.src sm0) n>>)
      /\ (<<MTGT: sm1.(SimMemInj.tgt) = JunkBlock.assign_junk_blocks (SimMemInj.tgt sm0) n>>)
      /\ (<<MINJ: sm1.(SimMemInj.inj) = junk_inj (SimMemInj.src sm0) (SimMemInj.tgt sm0) (SimMemInj.inj sm0) n>>)
      /\ (<<MWF: SimMemInj.wf' sm1>>)
      /\ (<<MLE: SimMemInj.le' sm0 sm1>>)
.
Proof.
  cinv MWF.
  hexploit assign_junk_blocks_parallel_inject; eauto. intros INJ.
  exploit SimMemInjC.parallel_gen; eauto.
  - eapply junk_inj_incr; eauto.
  - eapply junk_inj_separated; eauto.
  - eapply Mem.unchanged_on_implies; try eapply JunkBlock.assign_junk_blocks_unchanged_on. ss.
  - eapply Mem.unchanged_on_implies; try eapply JunkBlock.assign_junk_blocks_unchanged_on. ss.
  - ii. erewrite <- JunkBlock.assign_junk_blocks_perm; eauto.
  - ii. erewrite <- JunkBlock.assign_junk_blocks_perm; eauto.
  - i. des. esplits; eauto; ss.
Qed.

Lemma store_arguments_nextblock
      m0 m1 rs vs sg
      (STORE: store_arguments m0 rs vs sg m1):
    Plt (Mem.nextblock m0) (Mem.nextblock m1).
Proof.
  inv STORE. rewrite <- NB. eapply Mem.nextblock_alloc in ALC. erewrite ALC. xomega.
Qed.

Lemma store_arguments_max_perm
      m0 m1 rs vs sg
      (STORE: store_arguments m0 rs vs sg m1)
      b ofs
      (VALID: Mem.valid_block m0 b):
    Mem.perm m1 b ofs <2= Mem.perm m0 b ofs.
Proof.
  inv STORE. ii. eapply Mem.perm_unchanged_on_2 in PR; try apply UNCH; eauto.
  - eapply Mem.perm_alloc_4; eauto. eapply Mem.alloc_result in ALC. ii. clarify. eapply Plt_strict; eauto.
  - ss. des_ifs. eapply Mem.alloc_result in ALC. ii. clarify. eapply Plt_strict; eauto.
  - eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma store_arguments_parallel
      sm0 m_tgt1 rs_tgt vs vs' sg
      (ARGSRC: store_arguments sm0.(SimMemInj.tgt) rs_tgt vs' sg m_tgt1)
      (TYP: Val.has_type_list vs' sg.(sig_args))
      (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (VALINJ: Val.inject_list sm0.(SimMemInj.inj) vs vs')
      (MWF: SimMemInj.wf' sm0):
    exists sm1 rs_src,
      (<<ARGTGT: store_arguments sm0.(SimMemInj.src) rs_src vs sg sm1.(SimMemInj.src)>>) /\
      (<<INJ: sm1.(SimMemInj.inj) = (update_meminj sm0.(SimMemInj.inj) (Mem.nextblock sm0.(SimMemInj.src)) (Mem.nextblock sm0.(SimMemInj.tgt)) 0)>>) /\
      (<<MWF: SimMemInj.wf' sm1>>) /\
      (<<MLE: SimMemInj.le' sm0 sm1>>) /\
      (<<MTGT: sm1.(SimMemInj.tgt) = m_tgt1>>) /\
      (<<AGREE: StoreArgumentsProps.agree
                  (update_meminj sm0.(SimMemInj.inj) (Mem.nextblock sm0.(SimMemInj.src)) (Mem.nextblock sm0.(SimMemInj.tgt)) 0)
                  rs_src
                  rs_tgt>>).
Proof.
  cinv MWF.
  exploit store_arguments_parallel_inject; eauto. i. des.
  exploit SimMemInjC.parallel_gen; eauto.
  - unfold update_meminj. ii. des_ifs.
    eapply Mem.valid_block_inject_1 in H; eauto. exfalso. eapply Plt_strict; eauto.
  - unfold update_meminj. ii. des_ifs. split; eapply Plt_strict.
  - eapply Mem.unchanged_on_implies; try eapply store_arguments_unchanged_on; eauto. ss.
  - eapply Mem.unchanged_on_implies; try eapply store_arguments_unchanged_on; eauto. ss.
  - ii. eapply store_arguments_max_perm; try apply ARGSRC; eauto.
  - ii. eapply store_arguments_max_perm; try apply ARGSRC; eauto.
  - i. des. esplits; eauto; ss.
Qed.


Definition undef_bisim (rs_src rs_tgt: regset): Prop :=
  forall (r: mreg) (IN: Conventions1.is_callee_save r = true) (UNDEF: rs_src (to_preg r) = Vundef),
    rs_tgt (to_preg r) = Vundef.

Inductive wf_init_rs (rs: regset): Prop :=
| wf_init_rs_intro
    (RSPDEF: rs RSP <> Vundef)
    (TPTR: Val.has_type (rs RA) Tptr)
    (RADEF: rs RA <> Vundef)
  :
    wf_init_rs rs.

Inductive wf_init_rs_asmstyle (rs: regset): Prop :=
| wf_init_rs_amstyle_intro
    (TPTR: Val.has_type (rs RA) Tptr)
    (RADEF: rs RA <> Vundef)
  :
    wf_init_rs_asmstyle rs
.

Inductive wf_init_rss: signature -> regset -> regset -> Prop :=
| wf_init_rss_intro
    sg init_rs_src init_rs_tgt
    (WFINITSRC: wf_init_rs init_rs_src)
    (WFINITTGT: wf_init_rs init_rs_tgt)
    (UNDEF: undef_bisim init_rs_src init_rs_tgt)
    (CSTYLE: sg.(sig_cstyle) = true)
  :
    wf_init_rss sg init_rs_src init_rs_tgt
| wf_init_rss_asmstyle
    sg init_rs_src init_rs_tgt
    (WFINITSRC: wf_init_rs_asmstyle init_rs_src)
    (WFINITTGT: wf_init_rs_asmstyle init_rs_tgt)
    (CSTYLE: sg.(sig_cstyle) = false)
  :
    wf_init_rss sg init_rs_src init_rs_tgt
.

Inductive match_states_ext
          (skenv_link_tgt : SkEnv.t)
          (ge_src ge_tgt: genv)
          (sm_init : @SimMem.t SimMemExt.SimMemExt)
  : unit -> AsmC.state -> AsmC.state -> (@SimMem.t SimMemExt.SimMemExt) -> Prop :=
| match_states_ext_intro
    init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : @SimMem.t SimMemExt.SimMemExt)
    (AGREE: AsmStepExt.agree rs_src rs_tgt)
    (AGREEINIT: AsmStepExt.agree init_rs_src init_rs_tgt)
    (* (INJ: Mem.extends m_src m_tgt) *)
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITRS: wf_init_rss fd.(fn_sig) init_rs_src init_rs_tgt)
    (RAWF: Genv.find_funct skenv_link_tgt (init_rs_tgt RA) = None)
  :
    match_states_ext
      skenv_link_tgt ge_src ge_tgt sm_init tt
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0.

Definition asm_init_rs (rs_src rs_tgt: Mach.regset)
           sg v_pc v_ra blk :=
  (((to_pregset (set_regset rs_src rs_tgt sg)) # PC <- v_pc)
     # RA <- v_ra)
    # RSP <- (Vptr blk Ptrofs.zero).

Lemma asm_init_rs_undef_bisim
      rs_src rs_tgt sg v_pc v_ra blk:
    undef_bisim (asm_init_rs rs_src (to_mregset rs_tgt) sg v_pc v_ra blk) rs_tgt.
Proof.
  ii. unfold asm_init_rs, to_pregset, set_regset, to_mregset, Pregmap.set, to_preg in *.
  des_ifs; try (by unfold preg_of in *; des_ifs).
  - rewrite to_preg_to_mreg in *. clarify. exfalso.
    exploit loc_args_callee_save_disjoint; eauto. apply NNPP. ii. rewrite <- loc_notin_not_in in H. eauto.
Qed.
