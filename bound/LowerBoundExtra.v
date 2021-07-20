Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC GlobalenvsC .
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import Lia LinkingC2 Conventions1C JunkBlock StoreArguments StoreArgumentsProps.

Set Implicit Arguments.

Local Opaque Z.mul.

Local Notation "a # b" := (PMap.get b a) (at level 1).
Local Ltac simp := repeat (bsimpl; des; des_sumbool; ss; clarify).

Require Import Coq.Classes.RelationClasses.

Inductive inj_same (j: meminj) v0 v1 : Prop :=
| inj_same_ptr
    blk0 blk1 blk delta0 delta1 ofs0 ofs1
    (VAL0: v0 = Vptr blk0 ofs0)
    (VAL1: v1 = Vptr blk1 ofs1)
    (INJ0: j blk0 = Some (blk, delta0))
    (INJ1: j blk1 = Some (blk, delta1))
    (DELTA: Ptrofs.unsigned ofs0 + delta0 = Ptrofs.unsigned ofs1 + delta1)
| inj_same_refl
    (EQ: v0 = v1).

Hint Constructors inj_same.

Program Instance inj_same_equivalence j: Equivalence (inj_same j).
Next Obligation. ii. inv H; eauto. Qed.
Next Obligation.
  ii. inv H; inv H0; eauto.
  inv VAL0. rewrite INJ1 in *. inv INJ2. econs; eauto. etrans; eauto.
Qed.

Lemma inj_same_inj j v0 v1 v_tgt
      (SAME: inj_same j v0 v1)
      (INJ: Val.inject j v1 v_tgt):
    Val.inject j v0 v_tgt.
Proof.
  inv SAME; eauto. inv INJ. rewrite H1 in *. inv INJ1.
  econs; eauto.
  erewrite <- (Ptrofs.repr_unsigned ofs1).
  erewrite <- (Ptrofs.repr_unsigned ofs0).
  repeat rewrite IntegersC.Ptrofs_add_repr.
  f_equal. auto.
Qed.

Lemma inj_same_incr j0 j1
      (INCR: inject_incr j0 j1):
  inj_same j0 <2= inj_same j1.
Proof.
  ii. inv PR; eauto.
Qed.

Lemma separated_out_of_reach j0 j1 m_src0 m_src1 m_tgt0 blk delta
      (INJ: Mem.inject j0 m_src0 m_tgt0)
      (INCR: inject_incr j0 j1)
      (SEPARATED: inject_separated j0 j1 m_src0 m_tgt0)
      (BOUND: Plt blk m_tgt0.(Mem.nextblock))
      (OUTOFREACH: loc_out_of_reach j0 m_src0 blk delta)
      (MAXPERM: forall b ofs p
                       (VALED: Mem.valid_block m_src0 b)
                       (PERM: Mem.perm m_src1 b ofs Max p),
          Mem.perm m_src0 b ofs Max p):
  loc_out_of_reach j1 m_src1 blk delta.
Proof.
  ii. unfold inject_separated in *.
  destruct (j0 b0) eqn:EQ.
  - destruct p. specialize (INCR _ _ _ EQ). clarify.
    eapply OUTOFREACH; eauto. eapply MAXPERM; eauto.
    apply NNPP. intro N.
    eapply Mem.mi_freeblocks in N; eauto. clarify.
  - specialize (SEPARATED _ _ _ EQ H). des.
    apply SEPARATED0. eauto.
Qed.

Record freed_from m0 m1 blk lo hi : Prop :=
  mk_freed_from
    { freed_from_unchanged: Mem.unchanged_on
                              (fun blk' ofs =>
                                 if eq_block blk' blk
                                 then ~ (lo <= ofs < hi)
                                 else True)
                              m0 m1;
      freed_from_nextblock: m1.(Mem.nextblock) = m0.(Mem.nextblock);
      freed_from_perm: Mem.range_perm m0 blk lo hi Cur Freeable;
      freed_from_noperm: Mem_range_noperm m1 blk lo hi;
      freed_from_contents: forall ofs (IN: lo <= ofs < hi),
          ZMap.get ofs (Mem.mem_contents m0) !! blk =
          ZMap.get ofs (Mem.mem_contents m1) !! blk; }.

Lemma freed_from_perm_le m_src0 m_src1 blk lo hi blk' ofs k p
      (FREED: freed_from m_src0 m_src1 blk lo hi)
      (PERM: Mem.perm m_src1 blk' ofs k p):
    Mem.perm m_src0 blk' ofs k p.
Proof.
  destruct (eq_block blk' blk).
  - clarify. destruct (classic (lo <= ofs < hi)).
    + exfalso. eapply freed_from_noperm; eauto.
      eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
    + eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
      des_ifs; eauto. eapply Mem.perm_valid_block in PERM.
      unfold Mem.valid_block in *. erewrite <- freed_from_nextblock; eauto.
  - eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
    des_ifs; eauto. eapply Mem.perm_valid_block in PERM.
    unfold Mem.valid_block in *. erewrite <- freed_from_nextblock; eauto.
Qed.

Lemma freed_from_inject j m_src0 m_src1 m_tgt blk lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (FREED: freed_from m_src0 m_src1 blk lo hi):
    Mem.inject j m_src1 m_tgt.
Proof.
  eapply Mem.extends_inject_compose; eauto.
  econs.
  - eapply freed_from_nextblock; eauto.
  - econs; i; unfold inject_id in *; clarify; try rewrite Z.add_0_r.
    + eapply freed_from_perm_le; eauto.
    + eapply Z.divide_0_r.
    + destruct (eq_block b2 blk).
      * clarify. destruct (classic (lo <= ofs < hi)).
        -- erewrite <- freed_from_contents; eauto. refl.
        -- erewrite (Mem.unchanged_on_contents _ _ _ (freed_from_unchanged FREED)); auto.
           refl.
           des_ifs; eauto.
           eapply freed_from_perm_le; eauto.
      * erewrite (Mem.unchanged_on_contents _ _ _ (freed_from_unchanged FREED)); auto.
        refl.
        des_ifs; eauto.
        eapply freed_from_perm_le; eauto.
  - i. destruct (eq_block b blk).
    + clarify. destruct (classic (lo <= ofs < hi)).
      * right. eapply freed_from_noperm; eauto.
      * left. eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
        des_ifs; eauto. eapply Mem.perm_valid_block; eauto.
    + left. eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
      des_ifs; eauto. eapply Mem.perm_valid_block; eauto.
Qed.

Lemma freed_from_out_of_reach j m_src0 m_src1 m_tgt blk lo hi blk' delta ofs
      (INJECT: Mem.inject j m_src0 m_tgt)
      (FREED: freed_from m_src0 m_src1 blk lo hi)
      (DELTA: j blk = Some (blk', delta))
      (IN: lo + delta <= ofs < hi + delta):
    loc_out_of_reach j m_src1 blk' ofs.
Proof.
  ii. destruct (eq_block b0 blk).
  - clarify. eapply freed_from_noperm; eauto. omega.
  - exploit Mem.inject_no_overlap; eauto.
    + eapply freed_from_perm_le; eauto.
    + eapply Mem.perm_cur.
      eapply Mem.perm_implies.
      eapply freed_from_perm; eauto.
      instantiate (1 := ofs - delta). omega. econs.
    + i. des; eauto. omega.
Qed.

Lemma freed_from_perm_greater m0 m1 blk lo hi
      (FREE: freed_from m0 m1 blk lo hi):
    Mem.perm m1 <4= Mem.perm m0.
Proof.
  ii. inv FREE. inv freed_from_unchanged0.
  specialize (unchanged_on_perm x0 x1 x2 x3).
  des_ifs; [destruct (zle lo x1); destruct (zlt x1 hi)|];
    [exploit freed_from_perm0; eauto;
     i; eapply Mem.perm_cur;
     eapply Mem.perm_implies; eauto; econs | ..];
    eapply unchanged_on_perm; eauto with lia;
      eapply Mem.perm_valid_block in PR; ii;
        unfold Mem.valid_block; rewrite <- freed_from_nextblock0; auto.
Qed.

Lemma free_freed_from m0 m1 blk lo hi
      (FREE: Mem.free m0 blk lo hi = Some m1):
    freed_from m0 m1 blk lo hi.
Proof.
  econs.
  - eapply Mem.free_unchanged_on; eauto.
    i. des_ifs.
  - eapply Mem.nextblock_free; eauto.
  - eapply Mem.free_range_perm; eauto.
  - eapply Mem_free_noperm; eauto.
  - i. Local Transparent Mem.free. unfold Mem.free in *.
    des_ifs.
Qed.

Lemma init_mem_freed_from m_init:
    freed_from m_init m_init 1%positive 0 0.
Proof.
  econs; ii; auto; try omega.
  econs; eauto. refl.
Qed.

Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj) (m: mem) : Prop :=
| sken_inject_intro
    (DOMAIN: forall b, Plt b ge.(Genv.genv_next) -> j b = Some(b, 0))
    (IMAGE: forall b1 b2 delta (INJ: j b1 = Some(b2, delta))
                   (PERM: Senv.block_is_volatile ge b1 = true \/ exists ofs, Mem.perm m b1 ofs Max Nonempty),
        Senv.block_is_volatile ge b2 = Senv.block_is_volatile ge b1).

Lemma skenv_inject_max_perm {F V} (genv: Genv.t F V) (j: meminj) (m0 m1 m_tgt: mem)
      (INJ: Mem.inject j m0 m_tgt)
      (MAXPERM: forall b ofs p (VALID: Mem.valid_block m0 b) (PERM: Mem.perm m1 b ofs Max p),
          Mem.perm m0 b ofs Max p)
      (SYMB: skenv_inject genv j m0):
    skenv_inject genv j m1.
Proof.
  inv SYMB. econs; eauto. i. eapply IMAGE; eauto.
  unfold symbols_inject_weak in *. des. splits; auto.
  right. exists ofs. eapply MAXPERM; eauto.
  eapply Mem.valid_block_inject_1; eauto.
Qed.

Section INJRANGEWF.

Variable F V: Type.
Variable ge: Genv.t F V.

Inductive inj_range_block_wf (j: meminj) (m: mem) blk_src
          (P: Z -> Prop) : Prop :=
| inj_range_wf_empty
    (REACH: j blk_src = None)
    (BOT: P <1= bot1)
| inj_range_wf_intro
    blk_tgt delta
    (DELTA: j blk_src = Some (blk_tgt, delta))
    (ALIGN: forall chunk ofs k p, (range ofs (ofs + size_chunk chunk) <1= ((fun ofs => Mem.perm m blk_src ofs k p) \1/ P)) -> (align_chunk chunk | delta))
    (RANGE: forall ofs,
        (P (Ptrofs.unsigned ofs) \/
         P (Ptrofs.unsigned ofs - 1) ->
         delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned))
    (VOLATILE: forall
        ofs
        (VOL: Senv.block_is_volatile ge blk_src = false)
        (IN: P ofs), Senv.block_is_volatile ge blk_tgt = Senv.block_is_volatile ge blk_src).

Definition inj_range_wf (j: meminj) (m: mem) (P: Values.block -> Z -> Prop) :=
  forall blk, inj_range_block_wf j m blk (P blk).

Lemma inj_range_wf_le j m P0 P1
      (INJWF: inj_range_wf j m P0)
      (PLE: P1 <2= P0):
    inj_range_wf j m P1.
Proof.
  ii. destruct (INJWF blk).
  - econs 1; eauto.
  - econs 2; eauto; ii.
    + eapply ALIGN. ii. eapply H in PR. des; eauto.
    + eapply RANGE. des; eauto.
Qed.

Lemma private_unfree_symbols_inject
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (SYMB: skenv_inject ge j m_src0)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src):
    <<SYMB: skenv_inject ge j m_src1>>
.
Proof.
  inv SYMB. econs; auto. i.
  destruct (WFINJ b1); clarify. des.
  - exploit IMAGE; eauto.
  - destruct (classic (brange blk_src lo hi b1 ofs)).
    + destruct (Senv.block_is_volatile ge b1) eqn:VEQ.
      * exploit IMAGE; eauto.
      * unfold brange in *. des. clarify.
        exploit VOLATILE; eauto.
    + exploit IMAGE; eauto. right. exists ofs.
      eapply Mem.unchanged_on_perm; try apply Mem_unfree_unchanged_on; eauto.
      eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma private_unfree_inj_wf
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src):
  <<WFINJ: inj_range_wf j m_src1 P>>.
Proof.
  ii. destruct (WFINJ blk).
  - econs 1; eauto.
  - econs 2; eauto. ii.
    eapply ALIGN. ii. eapply H in PR. des; eauto.
    eapply Mem_unfree_unchanged_on in UNFREE; eauto.
    inv UNFREE. specialize (unchanged_on_perm blk x0 k p).
    destruct (classic (brange blk_src lo hi blk x0)).
    + right. inv H0. eauto.
    + left. eapply unchanged_on_perm; eauto.
      eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma private_unfree_inj
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src):
  <<INJ: Mem.inject j m_src1 m_tgt>>.
Proof.
  unfold Mem.inject in *.
  unfold Mem_unfree in *. des_ifs.
  inv INJ.
  econs; eauto.
  - inv mi_inj. econs; ii; ss; eauto.
    + unfold Mem.perm, Mem.perm_order' in H0. ss. des_ifs_safe.
      rewrite PMap.gsspec in *.
      destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify; cycle 1.
      * eapply mi_perm; eauto. unfold Mem.perm. bsimpl.
        assert(((Mem.mem_access m_src0) # b1) ofs k = Some p1).
        { des_ifs; simp. }
        rewrite H1; ss.
      * des_ifs; simp.
        eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem.
        eapply PERM; eauto with extlia.
    + destruct (WFINJ b1); clarify.
      destruct (eq_block b1 blk_src); clarify.
      { eapply ALIGN.
        instantiate (1:=p0). instantiate (1:=Max). instantiate (1:=ofs). ii.
        unfold Mem.range_perm, Mem.perm in *. ss.
        rewrite PMap.gss in H0; eauto.
        specialize (H0 _ PR). unfold proj_sumbool in *. des_ifs; ss; eauto. }
      * assert (Mem.range_perm m_src0 b1 ofs (ofs + size_chunk chunk) Max p0).
        { unfold Mem.range_perm, Mem.perm in *. ss.
          i. specialize (H0 ofs0 H).
          rewrite PMap.gso in H0; eauto. } clear H0.
        eapply mi_align; eauto.
    + unfold Mem.range_perm, Mem.perm in H0; ss.
      destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify; cycle 1.
      * assert(Mem.perm m_src0 b1 ofs Cur Readable).
        { rewrite PMap.gsspec in H0. des_ifs; simp. }
        clear H0. rewrite PMap.gsspec.
        des_ifs; ss; cycle 1.
        { eapply mi_memval; eauto. }
        destruct (classic (0 <= hi - lo)); cycle 1.
        { assert(NEG: exists n, hi - lo = Z.neg n).
          { assert(Z.sgn (hi - lo) = - 1).
            { eapply Z.sgn_neg. extlia. }
            unfold Z.sgn in *. des_ifs. eauto. }
          des. rewrite NEG. rewrite Z2Nat.inj_neg. ss.
          eapply mi_memval; eauto. }
        rewrite Mem.setN_other; ss.
        { eapply mi_memval; eauto. }
        ii. rewrite repeat_length in *. simp.
        { rewrite Z2Nat.id in *; ss. extlia. }
      * simp. rewrite PMap.gsspec. des_ifs.
        destruct (classic (0 <= hi - lo)); cycle 1.
        { rewrite PMap.gsspec in *. des_ifs; simp. extlia. }
        rewrite Mem_setN_in_repeat; ss.
        { econs; eauto. }
        rewrite Z2Nat.id; ss. extlia.
  - clear_until mi_no_overlap.
    rr. unfold Mem.perm; ss. ii.
    destruct (peq b1 blk_src && zle lo ofs1 && zlt ofs1 hi) eqn:T1; clarify.
    { simp. clear mi_no_overlap.
      rewrite PMap.gss in *. des_ifs; simp. clear H2.
      rewrite PMap.gso in *; cycle 1.
      { ii; clarify. }
      eapply not_and_or. ii. des. clarify.
      eapply PRVT; try apply H1; eauto; cycle 1.
      { instantiate (1:= ofs2 + delta2). zsimpl. eauto. }
      { rr. extlia. } }
    destruct (peq b2 blk_src && zle lo ofs2 && zlt ofs2 hi) eqn:T2; clarify.
    { sguard in T1. simp. clear mi_no_overlap.
      rewrite PMap.gss in *. des_ifs; simp. clear H3.
      rewrite PMap.gso in *; cycle 1.
      { ii; clarify. }
      eapply not_and_or. ii. des. clarify.
      eapply PRVT; try apply H0; eauto; cycle 1.
      { instantiate (1:= ofs1 + delta1). zsimpl. eauto. }
      { rr. extlia. }
    }
    specialize (mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2).
    do 3 (hexploit1 mi_no_overlap; ss).
    eapply mi_no_overlap.
    + rewrite PMap.gsspec in H2. des_ifs; simp.
    + rewrite PMap.gsspec in H3. des_ifs; simp.
  - i. ss. destruct (WFINJ b); clarify.
   destruct (eq_block b blk_src). subst.
    + des; unfold Mem.perm in *; ss; rewrite PMap.gss in H0.
      * unfold proj_sumbool in *; des_ifs; eauto 6.
      * unfold proj_sumbool in *; des_ifs; eauto 6.
    + assert (Mem.perm m_src0 b (Ptrofs.unsigned ofs) Max Nonempty \/
              Mem.perm m_src0 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
      { unfold Mem.range_perm, Mem.perm in *. ss.
        rewrite PMap.gso in H0; eauto. } clear H0.
      eapply mi_representable; eauto.
  - unfold Mem.perm. ss. ii.
    exploit mi_perm_inv; eauto. i.
    destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify.
    + bsimpl. des_safe. des_sumbool. rewrite PMap.gsspec. des_ifs_safe. ss. left. eauto with mem.
    + rewrite PMap.gsspec. des_ifs_safe. left. ss. eauto with mem.
Qed.

Lemma private_unfree_inj_inj_wf
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (SYMB: skenv_inject ge j m_src0)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src):
    (<<INJ: Mem.inject j m_src1 m_tgt>>) /\
    (<<WFINJ: inj_range_wf j m_src1 P>>) /\
    (<<SYMB: skenv_inject ge j m_src1>>).
Proof.
  splits.
  - eapply private_unfree_inj; eauto.
  - eapply private_unfree_inj_wf; eauto.
  - eapply private_unfree_symbols_inject; eauto.
Qed.

Lemma unfree_free_inj_inj_wf P j (m_src0 m_src1 m_src2 m_tgt: mem)
      blk0 blk1 delta1 delta2 ofs1 ofs2 size
      (DELTA1: delta1 = Ptrofs.unsigned ofs1)
      (DELTA2: delta2 = Ptrofs.unsigned ofs2)
      (FREE: Mem.free m_src0 blk0 delta1 (delta1 + size) = Some m_src1)
      (UNFREE: Mem_unfree m_src1 blk1 delta2 (delta2 + size) = Some m_src2)
      (SYMB: skenv_inject ge j m_src0)
      (SAME: inj_same j (Vptr blk1 ofs2) (Vptr blk0 ofs1))
      (MAPPED: j blk1 <> None)
      (INJ: Mem.inject j m_src0 m_tgt)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range delta2 (delta2 + size) <1= P blk1):
    (<<INJ: Mem.inject j m_src2 m_tgt>>) /\
    (<<WFINJ: inj_range_wf j m_src2 P>>) /\
    (<<SYMB: skenv_inject ge j m_src2>>).
Proof.
  subst. destruct (j blk1) as [[]|] eqn:BEQ; clarify; cycle 1.
  assert (SAME0: j blk0 = Some (b, z - Ptrofs.unsigned ofs1 + Ptrofs.unsigned ofs2)).
  { inv SAME.
    - inv VAL0. inv VAL1. rewrite BEQ in *. inv INJ0. rewrite INJ1.
      repeat f_equal. lia.
    - inv EQ. rewrite BEQ. repeat f_equal. lia. }
  eapply private_unfree_inj_inj_wf; cycle 4; eauto.
  - eapply skenv_inject_max_perm; eauto.
    i. eapply Mem.perm_free_3; eauto.
  - ii. destruct (WFINJ blk).
    +  econs 1; eauto.
    + econs 2; eauto.
      i. eapply ALIGN. ii. eapply H in PR. des; eauto.
      left. eapply Mem.perm_free_3; eauto.
  - eapply Mem.free_left_inject; eauto.
  - hexploit Mem.free_range_perm; eauto. i.
    eapply Mem.range_perm_inj in H; try apply INJ; eauto.
    replace (z + Ptrofs.unsigned ofs2) with
        (Ptrofs.unsigned ofs1 + (z - Ptrofs.unsigned ofs1 + Ptrofs.unsigned ofs2)); [|lia].
    replace (z + (Ptrofs.unsigned ofs2 + size)) with
        (Ptrofs.unsigned ofs1 + size + (z - Ptrofs.unsigned ofs1 + Ptrofs.unsigned ofs2)); [|lia].
    auto.
  - intros delta' RANGE0 blk' ofs' INJECT. unfold range in *.
    destruct (eq_block blk' blk0); clarify.
    + eapply Mem.perm_free_2; eauto. lia.
    + intros PERM. eapply Mem.perm_free_3 in PERM; eauto.
      eapply Mem.free_range_perm in FREE.
      exploit Mem.inject_no_overlap; eauto.
      * eapply Mem.perm_max; eauto.
        eapply Mem.perm_implies; try eapply FREE; [|econs].
        instantiate (1:=delta' - z + Ptrofs.unsigned ofs1 - Ptrofs.unsigned ofs2). lia.
      * ii. des; clarify. zsimpl. lia.
Qed.

End INJRANGEWF.
