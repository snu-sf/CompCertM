Require Import Zwf.
Require Import Axioms.
Require Import CoqlibC.
Require Intv.
Require Import MapsC.
Require Archi.
Require Import ASTC.
Require Import IntegersC.
Require Import Floats.
Require Import ValuesC.
Require Export Memdata MemdataC.
Require Export Memtype.
Require Import sflib.
Require Import Lia.
Require Import Events.
Require Import Classical_Pred_Type.
Require Import Coq.Logic.FunctionalExtensionality.


Local Notation "a # b" := (PMap.get b a) (at level 1).
(** Above is exactly copied from Memory.v **)

(* newly added *)
Require Export Memory.






Global Program Instance mem_unchanged_on_PreOrder P: RelationClasses.PreOrder (Mem.unchanged_on P).
Next Obligation. ii; ss. eapply Mem.unchanged_on_refl. Qed.
Next Obligation. ii; ss. eapply Mem.unchanged_on_trans; eauto. Qed.


Lemma Mem_unchanged_on_trans_strong
      P m0 m1 m2
      (UNCH0: Mem.unchanged_on P m0 m1)
      (UNCH1: Mem.unchanged_on (P /2\ (fun b _ => Mem.valid_block m0 b)) m1 m2):
    <<UNCH2: Mem.unchanged_on P m0 m2>>.
Proof.
  inv UNCH0. inv UNCH1. econs; i; try xomega.
  - etransitivity.
    { eapply unchanged_on_perm; eauto. }
    eapply unchanged_on_perm0; eauto.
    { unfold Mem.valid_block in *. xomega. }
  - erewrite <- unchanged_on_contents; eauto.
    dup H0. apply Mem.perm_valid_block in H1. unfold Mem.valid_block in *.
    erewrite <- unchanged_on_contents0; eauto. eapply unchanged_on_perm; eauto.
Qed.

Lemma Mem_alloc_range_perm
      m0 lo hi m1 blk
      (ALLOC: Mem.alloc m0 lo hi = (m1, blk)):
    <<PERM: Mem.range_perm m1 blk lo hi Cur Freeable>>.
Proof. ii. eapply Mem.perm_alloc_2; eauto. Qed.

Hint Resolve Mem_alloc_range_perm : mem.

Definition dead_block (m: mem) (b: block): Prop := forall ofs, ~Mem.perm m b ofs Cur Nonempty.

Inductive mem_equiv (m0 m1: mem): Prop :=
| mem_equiv_intro
    (UNCH: Mem.unchanged_on top2 m0 m1)
    (DEAD: forall b (BETWEEN: (m0.(Mem.nextblock) <= b < m1.(Mem.nextblock))%positive), dead_block m1 b).

Definition update_meminj (F: meminj) (blk_src blk_tgt: block) (delta: Z): meminj :=
  fun blk: block => if eq_block blk blk_src then Some (blk_tgt, delta) else F blk.
Hint Unfold update_meminj.

Lemma no_overlap_equiv
      F m0 m1
      (PERM: all4 (Mem.perm m0 <4> Mem.perm m1))
      (OVERLAP: Mem.meminj_no_overlap F m0):
    <<OVERLAP: Mem.meminj_no_overlap F m1>>.
Proof. ii; ss. eapply OVERLAP; eauto; eapply PERM; eauto. Qed.

Lemma Mem_alloc_fresh_perm
      m0 lo hi blk m1
      (ALLOC: Mem.alloc m0 lo hi = (m1, blk)):
    <<NOPERM: forall ofs p k, ~Mem.perm m0 blk ofs p k>>
    /\ <<NOPERM: forall ofs (OUTSIDE: ~ lo <= ofs < hi) p k, ~Mem.perm m1 blk ofs p k>>.
Proof.
  ii. exploit Mem.alloc_result; eauto. i; clarify. esplits; eauto.
  - ii. exploit (Mem.nextblock_noaccess m0 m0.(Mem.nextblock)); eauto with mem; try xomega.
    i. unfold Mem.perm in *. rewrite H0 in *. ss.
  - ii. exploit (Mem.nextblock_noaccess m0 m0.(Mem.nextblock)); eauto with mem.
Unshelve.
  all: ss.
Qed.

Lemma update_no_overlap
      F m0 sz blk_src blk_tgt delta m1
      (OVERLAP: Mem.meminj_no_overlap F m0)
      (ALLOC: Mem.alloc m0 0 sz = (m1, blk_src))
      (PRIVTGT: forall ofs
          (SZ: 0 <= ofs < sz),
          loc_out_of_reach F m0 blk_tgt (ofs + delta)):
    <<OVERLAP: Mem.meminj_no_overlap
                 (update_meminj F blk_src blk_tgt delta)
                 (* (fun blk: block => if eq_block blk_src blk then Some (blk_tgt, delta) else F blk) *)
                 m1>>.
Proof.
  u. hnf. ii; ss. destruct (classic (b1' = b2')); cycle 1.
  { left; ss. }
  right. clarify. exploit Mem.alloc_result; eauto. i; clarify. des_ifs; ss; cycle 1.
  - ii. exploit Mem.perm_alloc_3; eauto. i.
    exploit PRIVTGT; try apply H3; eauto; cycle 1.
    replace (ofs2 + delta2 - delta1) with ofs1 by xomega. eauto with mem.
  - exploit OVERLAP; [|apply H0|apply H1|..]; eauto with mem. ii; des; ss.
  - ii. exploit Mem.perm_alloc_3; eauto. i.
    exploit PRIVTGT; try apply H3; eauto; cycle 1.
    replace (ofs1 + delta1 - delta2) with ofs2 by xomega. eauto with mem.
Qed.


Section INJECT.

Lemma private_unchanged_inject
      F m_src m_tgt0 m_tgt1 P
      (INJ: Mem.inject F m_src m_tgt0)
      (UNCH: Mem.unchanged_on P m_tgt0 m_tgt1)
      (PRIV: ~2 loc_out_of_reach F m_src <2= P):
  <<INJ: Mem.inject F m_src m_tgt1>>.
Proof.
  inv UNCH. econs; eauto; try (by ii; eapply INJ; eauto with mem congruence).
  - econs; cycle 1; try (apply INJ; eauto).
    + ii. destruct (classic (P b2 (ofs + delta))).
      * (* publics *)
        erewrite unchanged_on_contents; eauto.
        { eapply INJ; eauto with mem. }
        { inv INJ. inv mi_inj. eauto. }
      * (* privs *)
        assert(loc_out_of_reach F m_src b2 (ofs + delta)).
        { ii. hnf in PRIV. exploit PRIV.
          { unfold loc_out_of_reach. ii. exploit H4; eauto. }
          i. ss.
        }
        unfold loc_out_of_reach in H2. exfalso. eapply H2; eauto.
        replace (ofs + delta - delta) with ofs by lia. eauto with mem.
    + ii. destruct (classic (P b2 (ofs + delta) /\ Mem.valid_block m_tgt0 b2)).
      * (* publics *)
        des. erewrite <- unchanged_on_perm; eauto. eapply INJ; eauto with mem.
      * (* privs *)
        apply not_and_or in H1. des; exfalso; cycle 1.
        { inv INJ. exploit mi_mappedblocks; eauto. }
        apply H1. apply PRIV. unfold loc_out_of_reach. ii. exploit H2; eauto.
        replace (ofs + delta - delta) with ofs by lia. eauto with mem.
  - ii. eapply Plt_Ple_trans; eauto. eapply Mem.valid_block_inject_2; eauto.
  - ii. destruct (classic (P b2 (ofs + delta) /\ Mem.valid_block m_tgt0 b2)).
    + (* publics *)
      des. eapply INJ; eauto. eapply unchanged_on_perm; eauto with mem congruence.
    + (* privs *)
      apply not_and_or in H1. des; cycle 1.
      { exfalso. inv INJ. exploit mi_mappedblocks; eauto. }
      right. ii. apply H1. apply PRIV. ii. exploit H3; eauto.
      replace (ofs + delta - delta) with ofs by lia. eauto with mem.
Qed.

End INJECT.



Section ARGPASSING.

Import Mem.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f', inject f' m1' m2
        /\ inject_incr f f'
        /\ f' b1 = Some(b2, delta)
        /\ (forall b, b <> b1 -> f' b = f b)
        /\ f' = fun b => if eq_block b b1 then Some(b2, delta) else f b.
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence. auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1); eauto.
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1); eauto.
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1); eauto; try congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. omega.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. omega.
(* representable *)
  unfold f'; intros. destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    { generalize (Ptrofs.unsigned_range_2 ofs). i.
      exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto. i.
      omega. }
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   { generalize (Ptrofs.unsigned_range_2 ofs). i.
     exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto. i.
     omega. }
  eapply mi_representable0; try eassumption.
  destruct H10; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by omega.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  split; auto.
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Lemma Mem_alloc_left_inject
      j0 m_src0 m_src1 m_tgt sz blk_src blk_tgt
      (INJ: Mem.inject j0 m_src0 m_tgt)
      (ALLOC: Mem.alloc m_src0 0 sz = (m_src1, blk_src))
      (VALID: Mem.valid_block m_tgt blk_tgt)
      (TGTPRIV: forall ofs (BOUND: 0 <= ofs < sz), loc_out_of_reach j0 m_src0 blk_tgt ofs)
      (TGTPERM: forall ofs k p (BOUND: 0 <= ofs < sz), Mem.perm m_tgt blk_tgt ofs k p):
    Mem.inject (fun blk => if eq_block blk blk_src
                           then Some (blk_tgt, 0)
                           else j0 blk) m_src1 m_tgt.
Proof.
  exploit alloc_left_mapped_inject; eauto.
  { split; try xomega. eapply max_unsigned_zero. }
  { ii. rewrite Z.add_0_r. eapply TGTPERM; eauto. }
  { hnf. ii. apply Z.divide_0_r. }
  { ii. rewrite ! Z.add_0_r in *. eapply TGTPRIV; eauto. rewrite Z.add_simpl_r. eauto with mem. }
  i; des. clarify.
Qed.


Lemma Mem_alloc_left_inject_empty
      j0 m_src0 m_src1 m_tgt blk_src blk_tgt delta
      (INJ: Mem.inject j0 m_src0 m_tgt)
      (ALLOC: Mem.alloc m_src0 0 0 = (m_src1, blk_src))
      (VALID: Mem.valid_block m_tgt blk_tgt):
      (* (DELTABD: 0 <= delta <= Ptrofs.max_unsigned) *)
    Mem.inject (fun blk => if eq_block blk blk_src
                           then Some (blk_tgt, delta)
                           else j0 blk) m_src1 m_tgt.
Proof.
(* NOTE: "alloc_left_mapped_inject" is not good enough. *)
  assert(NOPERM: forall ofs p k, ~Mem.perm m_src1 blk_src ofs k p).
  { ii; clarify. exploit Mem.perm_alloc_3; eauto. i; xomega. }

  assert(PERM: all4 (Mem.perm m_src0 -4> Mem.perm m_src1) /\ all4 (Mem.perm m_src1 -4> Mem.perm m_src0)).
  { split; ii.
    - eapply Mem.perm_alloc_1; eauto.
    - eapply Mem.perm_alloc_4; eauto. ii; clarify. eapply NOPERM; eauto.
  } ss; des.

  assert(INCR: inject_incr j0 (fun blk => if eq_block blk blk_src then Some (blk_tgt, delta) else j0 blk)).
  { ii; des_ifs. inv INJ. exfalso. exploit mi_freeblocks0; eauto with mem. i; ss. clarify. }
  econs; try eapply INJ.
  - econs; try eapply INJ.
    + ii. des_ifs; try (eapply INJ; eauto). exfalso. eapply NOPERM; eauto.
    + ii. des_ifs; eauto.
      { exfalso. eapply NOPERM. eapply H0; eauto. instantiate (1:= ofs).
        generalize (size_chunk_pos chunk); intro. xomega. }
      eapply INJ; eauto. ii. apply PERM0. eapply H0; eauto.
    + ii. des_ifs; eauto.
      { exfalso. eapply NOPERM; eauto. }
      (* it should only inject more. not less *)
      inv INJ. clear_until mi_inj0. inv mi_inj0.
      exploit mi_memval0; eauto. i.
      eapply memval_inject_incr; eauto; cycle 1.
Local Transparent Mem.alloc.
      exploit alloc_result; eauto. i; clarify.
      clear - n H1 ALLOC. unfold alloc in *. clarify; ss. rewrite PMap.gsspec. des_ifs.
Local Opaque Mem.alloc.
  - ii. des_ifs; try eapply INJ; eauto with mem.
    { exfalso. eapply H. eapply valid_new_block. eauto. }
  - ii. des_ifs; try eapply INJ; eauto with mem.
  - ii. des_ifs; try (by exploit NOPERM; eauto). eapply INJ; [apply H|..]; eauto.
  - ii. des_ifs.
    { des; try (by exploit NOPERM; eauto). }
    eapply INJ; [apply H|..]; eauto. des; eauto.
  - ii. des_ifs; try eapply INJ; eauto. inv INJ. exploit mi_perm_inv0; eauto. i; des; eauto.
Qed.


Lemma Mem_store_perm_iff
      chunk m0 blk ofs v m1
      (STORE: Mem.store chunk m0 blk ofs v = Some m1):
    <<EQ: all4 (Mem.perm m0 <4> Mem.perm m1)>>.
Proof. ii; split; ss; eauto with mem. Qed.

Lemma Mem_store_perm_eq
      chunk m0 blk ofs v m1
      (STORE: Mem.store chunk m0 blk ofs v = Some m1):
    <<EQ: all4 (Mem.perm m0 =4= Mem.perm m1)>>.
Proof. eapply prop_ext4. eapply Mem_store_perm_iff; eauto. Qed.

End ARGPASSING.









Definition brange (blk: block) (lo hi: Z): block -> Z -> Prop := fun b ofs => b= blk /\ lo <= ofs < hi. (* TODO: Use Notation instead *)
Hint Unfold brange.

(*** TODO: move to proper place ***)
Lemma brange_shorten
      blk lo0 hi0 lo1 hi1
      (LO: lo1 <= lo0)
      (HI: hi0 <= hi1)
  :
    <<SHORT: brange blk lo0 hi0 <2= brange blk lo1 hi1>>
.
Proof.
  u. ii; des; esplits; et; xomega.
Qed.

Section UNFREE.

Definition Mem_range_noperm (m: mem) (b: block) (lo hi: Z) :=
  forall ofs (BDD: lo <= ofs < hi), ~ Mem.perm m b ofs Max Nonempty.
Hint Unfold Mem_range_noperm.

Lemma Mem_unchanged_noperm
      P m0 m1 blk lo hi
      (UNCH: Mem.unchanged_on P m0 m1)
      (VALID: Mem.valid_block m0 blk)
      (NOPERM: Mem_range_noperm m0 blk lo hi)
      (RANGE: brange blk lo hi <2= P):
    <<NOPERM: Mem_range_noperm m1 blk lo hi>>.
Proof.
  ii. eapply NOPERM; eauto. inv UNCH. eapply unchanged_on_perm; eauto.
Qed.

Lemma Mem_free_noperm
      m0 blk lo hi m1
      (FREE: Mem.free m0 blk lo hi = Some m1):
    <<NOPERM: Mem_range_noperm m1 blk lo hi>>.
Proof.
  Local Transparent Mem.free.
  unfold Mem.free in *. des_ifs. unfold Mem.unchecked_free. ss. ii; ss. unfold Mem.perm in *. ss.
  rewrite PMap.gsspec in *. des_ifs. simpl_bool. des; des_sumbool; clarify.
  Local Opaque Mem.free.
Qed.

Program Definition Mem_unfree (m: mem) (b: block) (lo hi: Z): option mem :=
  if plt b m.(Mem.nextblock)
  then Some (Mem.mkmem
               (PMap.set b (Mem.setN (list_repeat (Z.to_nat (hi-lo)) Undef) lo ((Mem.mem_contents m) # b))
                         (Mem.mem_contents m))
               (PMap.set b
                         (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else m.(Mem.mem_access)#b ofs k)
                      m.(Mem.mem_access))
            m.(Mem.nextblock) _ _ _)
  else None.
Next Obligation.
  generalize (Mem.access_max m). intro PERM.
  unfold Mem.perm_order'' in *. rewrite ! PMap.gsspec in *.
  des_ifs; simpl_bool; des; des_sumbool; eauto with mem;
    try (by specialize (PERM b ofs); des_ifs); try (by specialize (PERM b0 ofs); des_ifs).
Defined.
Next Obligation.
  rewrite ! PMap.gsspec in *. generalize (Mem.nextblock_noaccess m); eauto. i.
  des_ifs; simpl_bool; des; des_sumbool; eauto with mem.
Defined.
Next Obligation.
  generalize (Mem.contents_default m); eauto. i.
  rewrite ! PMap.gsspec in *. des_ifs; ss. rewrite Mem.setN_default. ss.
Defined.

Lemma Mem_nextblock_unfree
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1):
    m0.(Mem.nextblock) = m1.(Mem.nextblock).
Proof. unfold Mem_unfree in *. des_ifs; ss. Qed.

Lemma Mem_valid_block_unfree
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1):
    all1 ((Mem.valid_block m0) <1> (Mem.valid_block m1)).
Proof. unfold Mem_unfree in *. des_ifs; ss. Qed.

Lemma Mem_unfree_unchanged_on0
      m0 m1 blk lo hi P
      (UNFR: Mem_unfree m0 blk lo hi = Some m1)
      (RANGE: brange blk lo hi <2= ~2 P):
    <<UNCH: Mem.unchanged_on P m0 m1>>.
Proof.
  unfold Mem_unfree in *. des_ifs; ss. econs; ss; eauto; try refl.
  - ii. unfold Mem.perm. ss. rewrite PMap.gsspec. des_ifs. exfalso. simpl_bool. des. des_sumbool. eapply RANGE; eauto.
  - ii. rewrite PMap.gsspec. des_ifs. rewrite Mem.setN_outside; ss. rewrite length_list_repeat.
    apply NNPP; ii. apply not_or_and in H1. des. eapply RANGE; eauto.
    u. esplits; eauto; try lia. destruct (classic (0 <= hi - lo)).
    + rewrite Z2Nat.id in *; ss. xomega.
    + abstr (hi - lo) x. destruct x; try xomega. rewrite Z2Nat.inj_neg in *. xomega.
Qed.

Lemma Mem_unfree_unchanged_on
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1):
    <<UNCH: Mem.unchanged_on (~2 brange blk lo hi) m0 m1>>.
Proof. exploit Mem_unfree_unchanged_on0; et. ii. tauto. Qed.

Lemma Mem_unfree_perm
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1):
    <<PERM: forall k p, Mem.range_perm m1 blk lo hi k p>>.
Proof.
  ii. unfold Mem_unfree in *. des_ifs. unfold Mem.perm. ss. rewrite PMap.gss. des_ifs.
  - ss. eauto with mem.
  - bsimpl. des; des_sumbool; try xomega.
Qed.

Lemma Mem_unfree_suceeds
      m0 blk lo hi
      (VALID: Mem.valid_block m0 blk):
    exists m1, <<UNFR: Mem_unfree m0 blk lo hi = Some m1>>.
Proof. unfold Mem_unfree. des_ifs. esplits; eauto. Qed.

Lemma Mem_unfree_extends
      m0 m1 blk lo hi
      (NOPERM: Mem_range_noperm m0 blk lo hi)
      (UNFR: Mem_unfree m0 blk lo hi = Some m1):
    <<EXT: Mem.extends m0 m1>>.
Proof.
  unfold Mem_unfree in *. des_ifs. econs; unfold Mem.perm in *; ss; eauto.
  - unfold inject_id. econs; unfold Mem.perm in *; ii; ss; clarify; eauto with mem.
    + rewrite PMap.gsspec. zsimpl. des_ifs; bsimpl; des; ss; des_sumbool; clarify; eauto with mem.
    + eapply Z.divide_0_r.
    + zsimpl. rewrite PMap.gsspec. des_ifs; try refl. destruct (classic (lo <= ofs < hi)).
      * exfalso. red in H0. des_ifs. eapply NOPERM; eauto. eapply Mem.perm_cur_max; eauto.
        unfold Mem.perm. rewrite Heq. econs; eauto.
      * rewrite Mem.setN_other; try refl. ii. rewrite length_list_repeat in *. clarify.
        destruct (classic (0 <= hi - lo)).
        { rewrite Z2Nat.id in *; ss. xomega. }
        { abstr (hi - lo) x. destruct x; try xomega. rewrite Z2Nat.inj_neg in *. xomega. }
  - ii. rewrite PMap.gsspec in *. des_ifs; bsimpl; des; ss; des_sumbool; clarify; eauto with mem.
Qed.

Lemma Mem_unfree_right_inject
      F m_src0 m_tgt0 blk lo hi m_tgt1
      (INJ: Mem.inject F m_src0 m_tgt0)
      (NOPERM: Mem_range_noperm m_tgt0 blk lo hi)
      (UNFR: Mem_unfree m_tgt0 blk lo hi = Some m_tgt1):
    <<INJ: Mem.inject F m_src0 m_tgt1>>.
Proof. eapply Mem.inject_extends_compose; eauto. eapply Mem_unfree_extends; eauto. Qed.

Local Ltac simp := repeat (bsimpl; des; des_sumbool; ss; clarify).

Lemma Mem_setN_in_repeat
      n v p q c
      (IN: p <= q < p + (Z.of_nat n)):
    (ZMap.get q (Mem.setN (list_repeat n v) p c)) = v.
Proof.
  exploit (Mem.setN_in (list_repeat n v) p q c); eauto.
  { ss. rewrite length_list_repeat. ss. }
  i. apply in_list_repeat in H. ss.
Qed.

Theorem Mem_unfree_parallel_extends m1 m2 b lo hi m1'
        (EXTEND: Mem.extends m1 m2)
        (UNFREE: Mem_unfree m1 b lo hi = Some m1'):
    exists m2',
      (<<UNFREE: Mem_unfree m2 b lo hi = Some m2'>>)
      /\ (<<EXTEND: Mem.extends m1' m2'>>).
Proof.
  unfold Mem_unfree in UNFREE. des_ifs. dup p. erewrite Mem.mext_next in *; eauto.
  unfold Mem_unfree. des_ifs. esplits; eauto. econs; ss; eauto; i.
  - eapply Mem.mext_next; eauto.
  - set (INJ:= Mem.mext_inj _ _ EXTEND). inv INJ. econs; ss; i.
    + unfold Mem.perm, proj_sumbool, inject_id in *. ss. clarify. zsimpl.
      rewrite PMap.gsspec in *. des_ifs; exploit Mem.perm_extends; eauto.
    + unfold inject_id in *. clarify. apply Z.divide_0_r.
    + unfold Mem.perm, proj_sumbool, inject_id in *. ss. clarify. zsimpl.
      repeat rewrite PMap.gsspec in *. des_ifs.
      * rewrite Mem_setN_in_repeat; eauto; [econs|]. rewrite Z2Nat.id; nia.
      * repeat rewrite Mem.setN_outside; try (by right; rewrite length_list_repeat; rewrite Z2Nat_range; des_ifs; try nia).
        exploit mi_memval; eauto; i; zsimpl; ss.
      * repeat rewrite Mem.setN_outside; try (by left; nia). exploit mi_memval; eauto; i; zsimpl; ss.
      * repeat rewrite Mem.setN_outside; try by (left; nia). exploit mi_memval; eauto; i; zsimpl; ss.
      * exploit mi_memval; eauto; i; zsimpl; ss.
  - unfold Mem.perm, proj_sumbool, inject_id in *. ss.
    rewrite PMap.gsspec in *. des_ifs; eauto; exploit Mem.mext_perm_inv; eauto.
Qed.

End UNFREE.


Ltac perm_impl_tac := eapply Mem.perm_implies with Freeable; [|eauto with mem].

Lemma delta_range
      F m_src m_tgt blk_src blk_tgt delta sz
      (INJECT: Mem.inject F m_src m_tgt)
      (INJVAL: F blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_src blk_src 0 sz Cur Freeable)
      (SIZEARG: 0 < sz <= Ptrofs.max_unsigned):
   <<DELTA: 0 <= delta <= Ptrofs.max_unsigned>> /\
   <<DELTA: sz + delta <= Ptrofs.max_unsigned>>.
Proof.
  unfold NW. split.
  - exploit Mem.mi_representable; eauto; cycle 1.
    { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. }
    left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max. perm_impl_tac. eapply PERM. split; try xomega.
  - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1.
    { instantiate (1:= (Ptrofs.repr sz)). rewrite Ptrofs.unsigned_repr; try xomega. }
    right. rewrite Ptrofs.unsigned_repr; try xomega.
    eapply Mem.perm_cur_max. perm_impl_tac. eapply PERM. split; try xomega.
Qed.

Lemma Mem_unchanged_on_bot
      m0 m1
      (NB: ((Mem.nextblock m0) <= (Mem.nextblock m1))%positive):
    Mem.unchanged_on bot2 m0 m1.
Proof. econs; ss; eauto. Qed.

Hint Resolve Mem.unchanged_on_nextblock: mem.

Lemma Mem_loadbytes_succeeds
      m0 blk ofs mv
      (PERM: Mem.perm m0 blk ofs Cur Readable)
      (MV: ZMap.get ofs (Mem.mem_contents m0) # blk = mv):
    Mem.loadbytes m0 blk ofs 1 = Some [mv].
Proof.
  Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes. des_ifs. exfalso. apply n. r. ii. assert(ofs0 = ofs) by xomega. clarify.
  Local Opaque Mem.loadbytes.
Qed.

Lemma Mem_equal_iff m0 m1
      (CONTENTS: Mem.mem_contents m0 = Mem.mem_contents m1)
      (PERM: Mem.mem_access m0 = Mem.mem_access m1)
      (NEXT: Mem.nextblock m0 = Mem.nextblock m1):
    m0 = m1.
Proof.
  destruct m0, m1. ss. subst. f_equal; apply proof_irrelevance.
Qed.

Lemma Mem_unchanged_on_strengthen P m0 m1:
    Mem.unchanged_on P m0 m1 <-> Mem.unchanged_on ((fun blk _ => Mem.valid_block m0 blk)/2\ P) m0 m1.
Proof.
  split; i; eapply Mem.unchanged_on_implies; eauto; ss. i. des. auto.
Qed.

Lemma Mem_free_zero_same m b lo0 hi0 lo1 hi1
      (SZ0: hi0 <= lo0)
      (SZ1: hi1 <= lo1):
    Mem.free m b lo0 hi0 = Mem.free m b lo1 hi1.
Proof.
  Local Transparent Mem.free. unfold Mem.free. des_ifs; try (exfalso; eapply n; ii; lia).
  f_equal. apply Mem_equal_iff; ss. f_equal.
  extensionality ofs. extensionality k. unfold proj_sumbool. des_ifs; exfalso; lia.
Qed.

Theorem Mem_free_parallel_inject'
        f m1 m2 blk_src blk_tgt ofs_src ofs_tgt sz m1'
        (INJ: Mem.inject f m1 m2)
        (VAL: Val.inject f (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
        (FREE: Mem.free m1 blk_src (Ptrofs.unsigned ofs_src) ((Ptrofs.unsigned ofs_src) + sz) = Some m1'):
    exists m2',
      (<<FREE: Mem.free m2 blk_tgt (Ptrofs.unsigned ofs_tgt) ((Ptrofs.unsigned ofs_tgt) + sz) = Some m2'>>)
      /\ (<<INJ: Mem.inject f m1' m2'>>).
Proof.
  inv VAL. destruct (zlt 0 sz).
  - exploit Mem.free_parallel_inject; eauto. i. des. esplits; eauto.
    erewrite Mem.address_inject; try apply INJ; eauto.
    + replace (Ptrofs.unsigned ofs_src + delta + sz) with
          (Ptrofs.unsigned ofs_src + sz + delta); [eauto|lia].
    + eapply Mem.free_range_perm; eauto. lia.
  - exploit Mem.free_parallel_inject; eauto. i. des.
    esplits; eauto. erewrite Mem_free_zero_same; eauto; lia.
Qed.

Lemma brange_split
      blk lo mid hi
      (RANGE: lo <= mid < hi):
    brange blk lo hi = brange blk lo mid \2/ brange blk mid hi.
Proof.
  apply func_ext1; i. apply func_ext1; i.
  apply AxiomsC.prop_ext. unfold brange. split.
  - ii. des; clarify. destruct (classic (x1 < mid)).
    + left. esplits; et.
    + right. esplits; et. xomega.
  - ii. des; clarify; esplits; et; xomega.
Qed.

Lemma Mem_valid_access_unchanged_on
      m0 m1 chunk b ofs perm
      (VA: Mem.valid_access m0 chunk b ofs perm)
      (UNCH: Mem.unchanged_on (brange b ofs (ofs + size_chunk chunk)) m0 m1)
  :
    (<<VA: Mem.valid_access m1 chunk b ofs perm>>)
.
Proof.
  rr in VA. des.
  rr. esplits; et.
  ii. exploit VA; et. intro T.
  eapply Mem.perm_unchanged_on; et.
Qed.

Lemma Mem_load_valid_block
      chunk m b ofs v
      (LOAD: Mem.load chunk m b ofs = Some v)
  :
    <<VALID: Mem.valid_block m b>>
.
Proof.
  eapply Mem.load_valid_access in LOAD. rr in LOAD. des. specialize (LOAD ofs). exploit LOAD; eauto.
  { generalize (size_chunk_pos chunk); i. xomega. }
  intro T. eapply Mem.perm_valid_block; et.
Qed.

Lemma Mem_range_noperm_split
      m b lo mid hi
      (PERM: Mem_range_noperm m b lo hi)
      (LO: lo <= mid)
      (HI: mid <= hi)
  :
    (<<PERM: Mem_range_noperm m b lo mid>>) /\
    (<<PERM: Mem_range_noperm m b mid hi>>)
.
Proof.
  esplits; et.
  - ii. eapply (PERM ofs); et. xomega.
  - ii. eapply (PERM ofs); et. xomega.
Qed.

(** TODO: move to proper place: MemoryC **)
Lemma Mem_unfree_left_extends
      m_src0 m_src1 blk lo hi m_tgt0
      (EXT: Mem.extends m_src0 m_tgt0)
      (UNFREESRC: Mem_unfree m_src0 blk lo hi = Some m_src1)
      (PERMTGT: Mem.range_perm m_tgt0 blk lo hi Cur Freeable)
  :
    <<EXT: Mem.extends m_src1 m_tgt0>>
.
Proof.
  unfold Mem_unfree in *. ss. des_ifs.
  inv EXT; ss. econs; ss; et.
  - econs; ss; et.
    + inv mext_inj. ii. unfold Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * ss.
        bsimpl. des. des_sumbool.
        exploit PERMTGT; et. intro T. unfold Mem.perm in T.
        unfold inject_id in *. clarify. zsimpl.
        clear - H0 T.
        eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto.
      * exploit mi_perm; et.
      * exploit mi_perm; et.
    + inv mext_inj. ii. unfold Mem.range_perm, Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * unfold inject_id in *. clarify. exists 0. xomega.
      * exploit mi_align; et.
    + inv mext_inj. ii. unfold Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * ss.
        bsimpl. des. des_sumbool.
        exploit PERMTGT; et. intro T. unfold Mem.perm in T.
        unfold inject_id in *. clarify. zsimpl.
        rewrite Mem_setN_in_repeat; ss.
        { econs; et. }
        { rewrite Z2Nat_range. des_ifs; try xomega. }
      * rewrite Mem.setN_outside; eauto.
        bsimpl. unfold inject_id in *. clarify.
        rewrite length_list_repeat.
        rewrite Z2Nat_range. des_ifs; try xomega.
        des; des_sumbool; try xomega.
      * unfold inject_id in *. clarify. exploit mi_memval; et.
  - ii.
    exploit mext_perm_inv; et. intro T. des.
    + left.
      unfold Mem.perm. ss.
      rewrite PMap.gsspec in *. des_ifs. bsimpl. des. des_sumbool. ss. econs; et.
    + destruct (classic (b = blk /\ lo <= ofs < hi)).
      * left.
        unfold Mem.perm. ss.
        rewrite PMap.gsspec in *. des_ifs; bsimpl; des; des_sumbool; ss. econs; et.
      * right.
        unfold Mem.perm. ss.
        rewrite PMap.gsspec in *. des_ifs. bsimpl. des. des_sumbool. ss. ii.
        apply not_and_or in H0. des; ss. xomega.
Qed.

Local Transparent Mem.loadbytes.
Lemma Mem_unfree_loadbytes
      m0 blk lo hi m1
      (UNFREE: Mem_unfree m0 blk lo hi = Some m1)
  :
    <<UNDEF: Mem.loadbytes m1 blk lo (hi - lo) = Some (list_repeat (Z.to_nat (hi - lo)) Undef)>>
.
Proof.
  hexploit Mem_unfree_perm; eauto. intro PERM.
  unfold Mem_unfree in *. des_ifs.
  unfold Mem.loadbytes. ss. des_ifs; cycle 1.
  { contradict n. ii.
    exploit (PERM Cur Readable ofs); eauto; ss.
    xomega.
  }
  r. f_equal.
  rewrite PMap.gsspec. des_ifs.
  rp; try rewrite Mem.getN_setN_same; eauto.
  rewrite length_list_repeat. ss.
Qed.
Local Opaque Mem.loadbytes.

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => (Mem.valid_block m) b.
Hint Unfold valid_blocks.
Hint Unfold loc_out_of_bounds.

Lemma Mem_setN_getN_same_aux
      n p c0 c1
      ofs
      (SAME: ZMap.get ofs c0 = ZMap.get ofs c1)
  :
    <<SAME: ZMap.get ofs (Mem.setN (Mem.getN n p c0) p c1) = ZMap.get ofs c0>>
.
Proof.
  ginduction n; ii; ss. des.
  erewrite IHn; ss.
  ii. rewrite ZMap.gsspec. des_ifs.
Qed.

Lemma Mem_setN_getN_same2
      n p c0 c1
      ofs
      (RANGE: p <= ofs < p + Z.of_nat n)
  :
    <<SAME: ZMap.get ofs (Mem.setN (Mem.getN n p c0) p c1) = ZMap.get ofs c0>>
.
Proof.
  ginduction n; ii; ss.
  { xomega. }
  des.
  destruct (classic (ofs = p)).
  - clarify. r. rewrite Mem.setN_outside; ss.
    { rewrite ZMap.gsspec. des_ifs. }
    left. xomega.
  - erewrite IHn; ss.
    xomega.
Qed.

Lemma Mem_setN_getN_same
      n p c
  :
    <<SAME: forall ofs, ZMap.get ofs (Mem.setN (Mem.getN n p c) p c) = ZMap.get ofs c>>
.
Proof.
  ii.
  eapply Mem_setN_getN_same_aux; eauto.
Qed.

Inductive Mem_stored (chunk: memory_chunk) (m0: mem) (b: block) (ofs: Z) (v: val) (m1: mem): Prop :=
| Mem_stored_intro
    (NB: Mem.nextblock m0 = Mem.nextblock m1)
    (UNCH: Mem.unchanged_on (~2 brange b ofs (ofs + (size_chunk chunk))) m0 m1)
    (STORED: Mem.load chunk m1 b ofs = Some v)
    (* (PERM: forall mid (OFS: ofs <= mid < ofs + (size_chunk chunk)) k p, *)
    (*     Mem.perm m0 b mid k p <-> Mem.perm m1 b mid k p) *)
    (PERM: forall b0 ofs0 k p,
        Mem.perm m0 b0 ofs0 k p <-> Mem.perm m1 b0 ofs0 k p)
.



Local Transparent Mem.load Mem.loadbytes Mem.storebytes.
Lemma extends_load_right_stored_left
      m_src0 m_tgt0
      chunk v b ofs
      (EXT: Mem.extends m_src0 m_tgt0)
      (LDTGT: Mem.load chunk m_tgt0 b ofs = Some v)
      (VALID: Mem.valid_access m_src0 chunk b ofs Writable)
      (* (PERM: Mem.range_perm m_src0 b ofs (ofs + (size_chunk chunk)) Cur Writable) *)
  :
    exists m_src1, (<<STRSRC: Mem_stored chunk m_src0 b ofs v m_src1>>)
                   /\ (<<EXT: Mem.extends m_src1 m_tgt0>>)
.
Proof.
  rr in VALID. des.
  hexploit (Mem.range_perm_loadbytes m_tgt0 b ofs).
  { ii. eapply Mem.perm_extends; eauto. eapply Mem.perm_implies with Writable; eauto with mem. }
  intro LDBYTES. des.
  exploit Mem.loadbytes_length; et. intro LEN.
  generalize (size_chunk_pos chunk); intro SZC.
  hexploit (Mem.range_perm_storebytes m_src0 b ofs bytes); eauto.
  { ii. eapply VALID. rewrite LEN in *. rewrite Z2Nat.id in *; try xomega. }
  intro STRBYTES. destruct STRBYTES as [m_src1 STRBYTES].
  exists m_src1.
  (* inv EXT. *)
  (* dup LDTGT. unfold Mem.load in LDTGT. des_ifs. *)
  (* edestruct (Mem.range_perm_storebytes . *)
  (* esplits. *)
  (* { econs. et. *)
  (* } *)
  dsplits.
  - econs; eauto with mem.
    + exploit Mem.nextblock_storebytes; et.
    + eapply Mem.storebytes_unchanged_on; et. i. intro U. apply U; clear U.
      rr. esplits; ss; try xomega. rewrite LEN in *. rewrite Z2Nat.id in *; try xomega.
    + exploit Mem.loadbytes_storebytes_same; eauto. intro LDB.
      rewrite LEN in *. rewrite Z2Nat.id in *; try xomega.
      exploit Mem.loadbytes_load; try apply LDB; et. intro LDSRC.
      exploit Mem.loadbytes_load; try apply LDBYTES; et. intro LDTGT0.
      clarify.
  - inv EXT. inv SPLITHINT.
    econs; et.
    + congruence.
    + unfold inject_id in *.
      inv mext_inj.
      econs; et.
      * ii. clarify. eapply mi_perm; eauto. eapply PERM; eauto.
      * ii. clarify. eapply mi_align; eauto. ii. exploit H0; eauto. intro T. eapply PERM; eauto.
      * ii; clarify.
        exploit mi_memval; eauto.
        { eapply PERM; eauto. }
        intro INJ.
        destruct (classic (b2 = b /\ ofs <= ofs0 < ofs + size_chunk chunk)).
        { (* stored regoion *)
          rename H into RANGE.
          des. clarify.
          unfold Mem.storebytes in STRBYTES. des_ifs. ss.
          rewrite PMap.gsspec. des_ifs.
          clear - SZC RANGE0 RANGE1 INJ LDBYTES. unfold Mem.loadbytes in LDBYTES. des_ifs.
          zsimpl.
          erewrite Mem_setN_getN_same2; eauto.
          { refl. }
          rewrite Z2Nat.id in *; try xomega.
        }
        { (* not stored regoion *)
          inv UNCH.
          assert(INJ0: memval_inject inject_id (ZMap.get ofs0 (Mem.mem_contents m_src1) !! b2)
                                     (ZMap.get ofs0 (Mem.mem_contents m_src0) !! b2)).
          {
            erewrite unchanged_on_contents; eauto.
            { refl. }
            eapply PERM; eauto.
          }
          exploit memval_inject_compose; eauto.
        }
    + ii. exploit mext_perm_inv; eauto.
      i; des; eauto.
      * left. eapply PERM; eauto.
      * right. ii. eapply H0. eapply PERM; eauto.
Qed.
Local Opaque Mem.load Mem.loadbytes Mem.storebytes.

