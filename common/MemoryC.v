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
Require Export Memdata.
Require Export Memtype.
Require Import sflib.
Require Import Lia.
Require Import Events.
Require Import Classical_Pred_Type.


Local Notation "a # b" := (PMap.get b a) (at level 1).
(** Above is exactly copied from Memory.v **)

(* newly added *)
Require Export Memory.




Section FROZEN.
  
(* Copied from CRELLVM *)
Inductive frozen (f_old f_new: meminj) (bound_src bound_tgt: block): Prop :=
| frozen_intro
    (NEW_IMPLIES_OUTSIDE:
       forall b_src b_tgt delta
              (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
         <<OUTSIDE_SRC: (bound_src <= b_src)%positive>> /\ <<OUTSIDE_TGT: (bound_tgt <= b_tgt)%positive>>)
.

Remark inject_separated_frozen
       f_old f_new m_src m_tgt
  :
    Events.inject_separated f_old f_new m_src m_tgt <->
    frozen f_old f_new m_src.(Mem.nextblock) m_tgt.(Mem.nextblock)
.
Proof.
  unfold Events.inject_separated in *.
  unfold Mem.valid_block in *.
  split; i.
  - econs; eauto.
    i. des.
    hexploit H; eauto. i; des.
    splits; xomega.
  - inv H.
    exploit NEW_IMPLIES_OUTSIDE; eauto.
    i; des.
    split; xomega.
Qed.

Lemma frozen_preserves_src
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_src
      (INSIDE: (b_src < bound_src)%positive)
  :
    <<PRESERVED: f_old b_src = f_new b_src>>
.
Proof.
  inv FROZEN.
  destruct (f_old b_src) eqn:T0; ss;
    destruct (f_new b_src) eqn:T1; ss.
  - destruct p, p0; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    exfalso.
    xomega.
Qed.

Lemma frozen_preserves_tgt
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_tgt
      (INSIDE: (b_tgt < bound_tgt)%positive)
  :
    <<PRESERVED: forall b_src delta (NOW: f_new b_src = Some (b_tgt, delta)),
      <<OLD: f_old b_src = Some (b_tgt, delta)>> >>
.
Proof.
  inv FROZEN.
  ii.
  destruct (f_old b_src) eqn:T; ss.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - exfalso.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    xomega.
Qed.

Lemma frozen_shortened
      f_old f_new
      bd_src0 bd_tgt0
      (FROZEN: frozen f_old f_new bd_src0 bd_tgt0)
      bd_src1 bd_tgt1
      (SHORT_SRC: (bd_src1 <= bd_src0)%positive)
      (SHORT_TGT: (bd_tgt1 <= bd_tgt0)%positive)
  :
    <<FROZEN: frozen f_old f_new bd_src1 bd_tgt1>>
.
Proof.
  inv FROZEN.
  econs; eauto.
  ii. des.
  hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
  split; ss.
  - red. etransitivity; eauto.
  - red. etransitivity; eauto.
Qed.

Lemma frozen_refl
      f
      bound_src bound_tgt
  :
    <<FROZEN: frozen f f bound_src bound_tgt>>
.
Proof.
  econs; eauto. i; des. clarify.
Qed.

Lemma loc_unmapped_frozen
      F F'
      fbound_src fbound_tgt
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_src)
      (UNMAPPED: loc_unmapped F b ofs)
  :
    loc_unmapped F' b ofs
.
Proof.
  unfold loc_unmapped in *.
  destruct (F' b) eqn:T; ss.
  destruct p; ss.
  inv FROZEN.
  exploit NEW_IMPLIES_OUTSIDE; eauto.
  i; des. xomega.
Qed.

Lemma loc_out_of_reach_frozen
      F F'
      fbound_src fbound_tgt
      (INCR: inject_incr F F')
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_tgt)
      m0 m1
      (UNMAPPED: loc_out_of_reach F m0 b ofs)
      (UNCHANGED: forall k p b0 delta (MAPPED: F b0 = Some (b, delta)),
          Mem.perm m0 b0 (ofs - delta) k p <-> Mem.perm m1 b0 (ofs - delta) k p)
  :
    loc_out_of_reach F' m1 b ofs
.
Proof.
  unfold loc_out_of_reach in *.
  i.
  exploit frozen_preserves_tgt; eauto.
  i. des.
  hexploit UNMAPPED; eauto. i.
  ii.
  contradict H1.
  eapply UNCHANGED; eauto.
Qed.

End FROZEN.





(* TODO: Move to MemdataC *)
Program Instance memval_inject_Reflexive: RelationClasses.Reflexive (@memval_inject Val.mi_normal inject_id).
Next Obligation.
  destruct x; ss; econs; eauto.
  apply val_inject_id. ss.
Qed.



Global Program Instance mem_unchanged_on_PreOrder P: RelationClasses.PreOrder (Mem.unchanged_on P).
Next Obligation. ii; ss. eapply Mem.unchanged_on_refl. Qed.
Next Obligation. ii; ss. eapply Mem.unchanged_on_trans; eauto. Qed.


Lemma Mem_unchanged_on_trans_strong
      P m0 m1 m2
      (UNCH0: Mem.unchanged_on P m0 m1)
      (UNCH1: Mem.unchanged_on (P /2\ (fun b _ => Mem.valid_block m0 b)) m1 m2)
  :
    <<UNCH2: Mem.unchanged_on P m0 m2>>
.
Proof.
  inv UNCH0. inv UNCH1.
  econs; i.
  - xomega.
  - etransitivity.
    { eapply unchanged_on_perm; eauto. }
    eapply unchanged_on_perm0; eauto.
    { unfold Mem.valid_block in *. xomega. }
  - erewrite <- unchanged_on_contents; eauto.
    dup H0. apply Mem.perm_valid_block in H1. unfold Mem.valid_block in *.
    erewrite <- unchanged_on_contents0; eauto.
    eapply unchanged_on_perm; eauto.
Qed.

Lemma Mem_alloc_range_perm
      m0 lo hi m1 blk
      (ALLOC: Mem.alloc m0 lo hi = (m1, blk))
  :
    <<PERM: Mem.range_perm m1 blk lo hi Cur Freeable>>
.
Proof.
  ii. eapply Mem.perm_alloc_2; eauto.
Qed.

Hint Resolve Mem_alloc_range_perm : mem.

Definition dead_block (m: mem) (b: block): Prop := forall ofs, ~Mem.perm m b ofs Cur Nonempty.

Inductive mem_equiv (m0 m1: mem): Prop :=
| mem_equiv_intro
    (UNCH: Mem.unchanged_on top2 m0 m1)
    (DEAD: forall b (BETWEEN: (m0.(Mem.nextblock) <= b < m1.(Mem.nextblock))%positive), dead_block m1 b)
.

Definition update_meminj (F: meminj) (blk_src blk_tgt: block) (delta: Z): meminj :=
  fun blk: block => if eq_block blk blk_src then Some (blk_tgt, delta) else F blk
.
Hint Unfold update_meminj.

Lemma no_overlap_equiv
      F m0 m1
      (PERM: all4 (Mem.perm m0 <4> Mem.perm m1))
      (OVERLAP: Mem.meminj_no_overlap F m0)
  :
    <<OVERLAP: Mem.meminj_no_overlap F m1>>
.
Proof.
  ii; ss. eapply OVERLAP; eauto; eapply PERM; eauto.
Qed.

Lemma Mem_alloc_fresh_perm
      m0 lo hi blk m1
      (ALLOC: Mem.alloc m0 lo hi = (m1, blk))
  :
    <<NOPERM: forall ofs p k, ~Mem.perm m0 blk ofs p k>>
     /\
    <<NOPERM: forall ofs (OUTSIDE: ~ lo <= ofs < hi) p k, ~Mem.perm m1 blk ofs p k>>
.
Proof.
  ii.
  exploit Mem.alloc_result; eauto. i; clarify.
  esplits; eauto.
  - ii.
    exploit (Mem.nextblock_noaccess m0 m0.(Mem.nextblock)); eauto with mem.
    { ii. xomega. }
    i. unfold Mem.perm in *.
    rewrite H0 in *. ss.
  - ii.
    exploit (Mem.nextblock_noaccess m0 m0.(Mem.nextblock)); eauto with mem.
Unshelve.
  all: ss.
Qed.

Lemma update_no_overlap
      F m0
      (OVERLAP: Mem.meminj_no_overlap F m0)
      sz blk_src blk_tgt delta m1
      (ALLOC: Mem.alloc m0 0 sz = (m1, blk_src))
      (PRIVTGT: forall
          ofs
          (SZ: 0 <= ofs < sz)
        ,
          loc_out_of_reach F m0 blk_tgt (ofs + delta))
  :
    <<OVERLAP: Mem.meminj_no_overlap
                 (update_meminj F blk_src blk_tgt delta)
                 (* (fun blk: block => if eq_block blk_src blk then Some (blk_tgt, delta) else F blk) *)
                 m1>>
.
Proof.
  u.
  hnf. ii; ss.
  destruct (classic (b1' = b2')); cycle 1.
  { left; ss. }
  right. clarify.
  exploit Mem.alloc_result; eauto. i; clarify.
  des_ifs; ss; cycle 1.
  - ii.
    exploit Mem.perm_alloc_3; eauto. i.
    exploit PRIVTGT; try apply H3; eauto; cycle 1.
    replace (ofs2 + delta2 - delta1) with ofs1 by xomega.
    eauto with mem.
  - exploit OVERLAP; [|apply H0|apply H1|..]; eauto with mem. ii; des; ss.
  - ii.
    exploit Mem.perm_alloc_3; eauto. i.
    exploit PRIVTGT; try apply H3; eauto; cycle 1.
    replace (ofs1 + delta1 - delta2) with ofs2 by xomega.
    eauto with mem.
Qed.


Section INJECT.

Context `{CTX: Val.meminj_ctx}.

Lemma private_unchanged_inject
      F m_src m_tgt0 m_tgt1
      P
      (INJ: Mem.inject F m_src m_tgt0)
      (UNCH: Mem.unchanged_on P m_tgt0 m_tgt1)
      (PRIV: ~2 loc_out_of_reach F m_src <2= P)
      (NB: (Mem.nextblock m_tgt0) = (Mem.nextblock m_tgt1))
  :
    <<INJ: Mem.inject F m_src m_tgt1>>
.
Proof.
  inv UNCH.
  econs; eauto.
  - econs; cycle 1.
    + apply INJ; eauto.
    + ii.
      destruct (classic (P b2 (ofs + delta))).
      * (* publics *)
        erewrite unchanged_on_contents; eauto.
        { eapply INJ; eauto with mem. }
        { inv INJ. inv mi_inj. eauto. }
      * (* privs *)
        assert(loc_out_of_reach F m_src b2 (ofs + delta)).
        { ii. hnf in PRIV.
          exploit PRIV.
          { unfold loc_out_of_reach. ii. exploit H4; eauto. }
          i. ss.
        }
        unfold loc_out_of_reach in H2.
        exploit H2; eauto.
        { replace (ofs + delta - delta) with ofs by lia. eauto with mem. }
        i; ss.
    + ii.
      destruct (classic (P b2 (ofs + delta) /\ Mem.valid_block m_tgt1 b2)).
      * (* publics *)
        des.
        erewrite <- unchanged_on_perm; eauto.
        { eapply INJ; eauto with mem. }
        { eauto with congruence. }
      * (* privs *)
        apply not_and_or in H1. des; cycle 1.
        { exfalso. inv INJ.
          exploit mi_mappedblocks; eauto. i. eauto with congruence. }
        exfalso.
        apply H1. apply PRIV. unfold loc_out_of_reach. ii. exploit H2; eauto.
        replace (ofs + delta - delta) with ofs by lia.
        eauto with mem.
  - ii. eapply INJ; eauto with mem congruence.
  - ii. unfold Mem.valid_block. rewrite <- NB.
    eapply INJ; eauto with mem congruence.
  - ii. eapply INJ; eauto with mem congruence.
  - ii. eapply INJ; eauto with mem congruence.
  - ii.
    destruct (classic (P b2 (ofs + delta) /\ Mem.valid_block m_tgt1 b2)).
    + (* publics *)
      des.
      eapply INJ; eauto.
      eapply unchanged_on_perm; eauto with mem congruence.
    + (* privs *)
      apply not_and_or in H1. des; cycle 1.
      { exfalso. inv INJ.
        exploit mi_mappedblocks; eauto. i. eauto with congruence. }
      assert(~ Mem.perm m_src b1 ofs Max Nonempty).
      { ii. apply H1. apply PRIV. ii. exploit H3; eauto.
        replace (ofs + delta - delta) with ofs by lia.
        eauto with mem.
      }
      eauto.
Qed.

End INJECT.



Section ARGPASSING.

Context `{CTX: Val.meminj_ctx}.
(* Local Existing Instance Val.mi_normal. *)

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
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b)
  /\ f' = fun b => if eq_block b b1 then Some(b2, delta) else f b.
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. omega.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. omega.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    {
      generalize (Ptrofs.unsigned_range_2 ofs). i.
      exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto. i.
      omega. }
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   {
   generalize (Ptrofs.unsigned_range_2 ofs). i.
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
      j0
      m_src0 m_src1 m_tgt sz blk_src
      (INJ: Mem.inject j0 m_src0 m_tgt)
      (ALLOC: Mem.alloc m_src0 0 sz = (m_src1, blk_src))
      blk_tgt
      (VALID: Mem.valid_block m_tgt blk_tgt)
      (TGTPRIV: forall ofs (BOUND: 0 <= ofs < sz), loc_out_of_reach j0 m_src0 blk_tgt ofs)
      (TGTPERM: forall ofs k p (BOUND: 0 <= ofs < sz), Mem.perm m_tgt blk_tgt ofs k p)
  :
    Mem.inject (fun blk => if eq_block blk blk_src
                           then Some (blk_tgt, 0)
                           else j0 blk) m_src1 m_tgt
.
Proof.
  exploit alloc_left_mapped_inject; eauto.
  { split; try xomega. eapply max_unsigned_zero. }
  { ii. rewrite Z.add_0_r. eapply TGTPERM; eauto. }
  { hnf. ii. apply Z.divide_0_r. }
  { ii. rewrite ! Z.add_0_r in *. eapply TGTPRIV; eauto. rewrite Z.add_simpl_r. eauto with mem. }
  i; des. clarify.
Qed.


Lemma Mem_alloc_left_inject_empty
      j0
      m_src0 m_src1 m_tgt blk_src
      (INJ: Mem.inject j0 m_src0 m_tgt)
      (ALLOC: Mem.alloc m_src0 0 0 = (m_src1, blk_src))
      blk_tgt delta
      (VALID: Mem.valid_block m_tgt blk_tgt)
      (* (DELTABD: 0 <= delta <= Ptrofs.max_unsigned) *)
  :
    Mem.inject (fun blk => if eq_block blk blk_src
                           then Some (blk_tgt, delta)
                           else j0 blk) m_src1 m_tgt
.
Proof.
(* NOTE: "alloc_left_mapped_inject" is not good enough. *)
  assert(NOPERM: forall ofs p k, ~Mem.perm m_src1 blk_src ofs k p).
  {
    ii; clarify.
    exploit Mem.perm_alloc_3; eauto. i; xomega.
  }

  assert(PERM: all4 (Mem.perm m_src0 -4> Mem.perm m_src1) /\ all4 (Mem.perm m_src1 -4> Mem.perm m_src0)).
  { split; ii.
    - eapply Mem.perm_alloc_1; eauto.
    - eapply Mem.perm_alloc_4; eauto.
      ii; clarify. eapply NOPERM; eauto.
  } ss; des.

  assert(INCR: inject_incr j0 (fun blk => if eq_block blk blk_src then Some (blk_tgt, delta) else j0 blk)).
  { ii; des_ifs. inv INJ. exfalso. exploit mi_freeblocks0; eauto with mem. i; ss. clarify. }
  econs; try eapply INJ.
  - econs; try eapply INJ.
    + ii. des_ifs; eauto.
      { exfalso. eapply NOPERM; eauto. }
      eapply INJ; eauto.
    + ii. des_ifs; eauto.
      { exfalso. eapply NOPERM. eapply H0; eauto. instantiate (1:= ofs).
        generalize (size_chunk_pos chunk); intro. xomega. }
      eapply INJ; eauto.
      ii. apply PERM0. eapply H0; eauto.
    + ii. des_ifs; eauto.
      { exfalso. eapply NOPERM; eauto. }
      (* it should only inject more. not less *)
      inv INJ. clear_until mi_inj0. inv mi_inj0.
      exploit mi_memval0; eauto. i.
      eapply memval_inject_incr; eauto; cycle 1.
Local Transparent Mem.alloc.
      exploit alloc_result; eauto. i; clarify.
      clear - n H1 ALLOC.
      unfold alloc in *. clarify; ss.
      rewrite PMap.gsspec. des_ifs.
Local Opaque Mem.alloc.
  - ii. des_ifs; try eapply INJ; eauto with mem.
    { admit "ez". }
  - ii. des_ifs; try eapply INJ; eauto with mem.
  - ii. des_ifs; try (by exploit NOPERM; eauto).
    eapply INJ; [apply H|..]; eauto.
  - ii. des_ifs.
    { des; try (by exploit NOPERM; eauto). }
    eapply INJ; [apply H|..]; eauto.
    des; eauto.
  - ii. des_ifs; try eapply INJ; eauto.
    inv INJ. exploit mi_perm_inv0; eauto.
    i; des; eauto.
Qed.


Lemma Mem_store_perm_iff
      chunk m0 blk ofs v m1
      (STORE: Mem.store chunk m0 blk ofs v = Some m1)
  :
    <<EQ: all4 (Mem.perm m0 <4> Mem.perm m1)>>
.
Proof.
  ii; split; ss.
  - eapply Mem.perm_store_1; eauto.
  - eapply Mem.perm_store_2; eauto.
Qed.

Lemma Mem_store_perm_eq
      chunk m0 blk ofs v m1
      (STORE: Mem.store chunk m0 blk ofs v = Some m1)
  :
    <<EQ: all4 (Mem.perm m0 =4= Mem.perm m1)>>
.
Proof.
  eapply prop_ext4. eapply Mem_store_perm_iff; eauto.
Qed.

Local Transparent store.
Lemma Mem_store_mapped_inject_undef
      f m1 m2 b1 ofs chunk n1
      (INJ: Mem.inject f m1 m2)
      (STORESRC: Mem.store chunk m1 b1 ofs Vundef = Some n1)
  :
    inject f n1 m2
.
Proof.
  hexploit Mem_store_perm_iff; eauto. intro PERM. des.
  econs; try apply INJ; eauto.
  - econs; eauto.
    + ii; clarify. eapply INJ; eauto. eapply PERM; eauto.
    + ii; clarify. eapply INJ; eauto. ii. eapply PERM; eauto.
    + ii; clarify.
      unfold store in *.
      Local Opaque encode_val.
      des_ifs. ss.
      unfold ZMap.get; rewrite PMap.gsspec. des_ifs; cycle 1.
      { eapply INJ; eauto. }
      unfold perm in *. ss.
      (* inv INJ. clear_until mi_inj0. inv mi_inj0. clear mi_perm0 mi_align0. *)
      Local Transparent encode_val.
      destruct chunk; ss; repeat (unfold ZMap.set in *; rewrite PMap.gsspec; des_ifs; [econs; eauto|]);
        eapply INJ; eauto.
 - admit "ez".
 - admit "ez".
 - admit "ez".
 - admit "ez".
Qed.

End ARGPASSING.









Definition brange (blk: block) (lo hi: Z): block -> Z -> Prop := fun b ofs => b= blk /\ lo <= ofs < hi. (* TODO: Use Notation instead *)
Hint Unfold brange.

Section UNFREE.

Definition Mem_range_noperm (m: mem) (b: block) (lo hi: Z) :=
  forall ofs (BDD: lo <= ofs < hi), ~ Mem.perm m b ofs Max Nonempty
.
Hint Unfold Mem_range_noperm.

Lemma Mem_unchanged_noperm
      P m0 m1 blk lo hi
      (UNCH: Mem.unchanged_on P m0 m1)
      (VALID: Mem.valid_block m0 blk)
      (NOPERM: Mem_range_noperm m0 blk lo hi)
      (RANGE: brange blk lo hi <2= P)
  :
    <<NOPERM: Mem_range_noperm m1 blk lo hi>>
.
Proof.
  ii. eapply NOPERM; eauto. inv UNCH. eapply unchanged_on_perm; eauto.
Qed.

Lemma Mem_range_noperm_dec:
  forall m b lo hi, {Mem_range_noperm m b lo hi} + {~ Mem_range_noperm m b lo hi}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi); cycle 1.
  { left; red; intros. omegaContradiction. }
  destruct (Mem.perm_dec m b lo Max Nonempty).
  { right. ii. eapply H0; eauto. xomega. }
  destruct (H (lo + 1)).
  { red. omega. }
  - left; red; intros. destruct (zeq lo ofs). congruence. apply m0. omega.
  - right; red; intros. elim n0. red; intros; apply H0; omega.
Defined.

Lemma Mem_free_noperm
      m0 blk lo hi m1
      (FREE: Mem.free m0 blk lo hi = Some m1)
  :
    <<NOPERM: Mem_range_noperm m1 blk lo hi>>
.
Proof.
  Local Transparent Mem.free.
  unfold Mem.free in *. des_ifs.
  unfold Mem.unchecked_free. ss. ii; ss. unfold Mem.perm in *. ss.
  rewrite PMap.gsspec in *. des_ifs.
  simpl_bool. des; des_sumbool; clarify.
  Local Opaque Mem.free.
Qed.

Program Definition Mem_unfree (m: mem) (b: block) (lo hi: Z): option mem :=
  if plt b m.(Mem.nextblock)
  then
    if Mem_range_noperm_dec m b lo hi
    then
      Some (Mem.mkmem
              (PMap.set b (Mem.setN (list_repeat (hi-lo).(Z.to_nat) Undef) lo ((Mem.mem_contents m) # b))
                        (Mem.mem_contents m))
              (PMap.set b
                        (fun ofs k =>
                           if zle lo ofs && zlt ofs hi
                           then Some Freeable
                           else m.(Mem.mem_access)#b ofs k)
                        m.(Mem.mem_access))
              m.(Mem.nextblock) _ _ _)
    else None
  else None
.
Next Obligation.
  generalize (Mem.access_max m). intro PERM.
  unfold Mem.perm_order'' in *.
  rewrite ! PMap.gsspec in *.
  des_ifs; simpl_bool; des; des_sumbool; eauto with mem.
  - specialize (PERM b ofs). des_ifs.
  - specialize (PERM b ofs). des_ifs.
  - specialize (PERM b0 ofs). des_ifs.
  - specialize (PERM b ofs). des_ifs.
  - specialize (PERM b ofs). des_ifs.
  - specialize (PERM b0 ofs). des_ifs.
Defined.
Next Obligation.
  rewrite ! PMap.gsspec in *.
  generalize (Mem.nextblock_noaccess m); eauto. i.
  des_ifs; simpl_bool; des; des_sumbool; eauto with mem.
Defined.
Next Obligation.
  generalize (Mem.contents_default m); eauto. i.
  rewrite ! PMap.gsspec in *.
  des_ifs; ss.
  rewrite Mem.setN_default. ss.
Defined.

Lemma Mem_nextblock_unfree
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1)
  :
    m0.(Mem.nextblock) = m1.(Mem.nextblock)
.
Proof. unfold Mem_unfree in *. des_ifs; ss. Qed.

Lemma Mem_valid_block_unfree
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1)
  :
    all1 (m0.(Mem.valid_block) <1> m1.(Mem.valid_block))
.
Proof. unfold Mem_unfree in *. des_ifs; ss. Qed.

Lemma Mem_unfree_unchanged_on
      m0 m1 blk lo hi P
      (UNFR: Mem_unfree m0 blk lo hi = Some m1)
      (RANGE: brange blk lo hi <2= ~2 P)
  :
    <<UNCH: Mem.unchanged_on P m0 m1>>
.
Proof.
  unfold Mem_unfree in *. des_ifs; ss.
  econs; ss; eauto.
  - refl.
  - ii. unfold Mem.perm. ss.
    rewrite PMap.gsspec. des_ifs. exfalso. simpl_bool. des. des_sumbool.
    eapply RANGE; eauto.
  - ii. rewrite PMap.gsspec. des_ifs. rewrite Mem.setN_outside; ss. rewrite length_list_repeat.
    apply NNPP; ii. apply not_or_and in H1. des. eapply RANGE; eauto.
    u. esplits; eauto; try lia.
    destruct (classic (0 <= hi - lo)).
    + rewrite Z2Nat.id in *; ss. xomega.
    + abstr (hi - lo) x. destruct x; try xomega. rewrite Z2Nat.inj_neg in *. xomega.
Qed.

Context `{CTX: Val.meminj_ctx}.

Lemma Mem_unfree_suceeds
      m0 blk lo hi
      (VALID: Mem.valid_block m0 blk)
      (NOPERM: Mem_range_noperm m0 blk lo hi)
  :
    exists m1, <<UNFR: Mem_unfree m0 blk lo hi = Some m1>>
.
Proof.
  unfold Mem_unfree. des_ifs. esplits; eauto.
Qed.

Lemma Mem_unfree_extends
      m0 m1 blk lo hi
      (UNFR: Mem_unfree m0 blk lo hi = Some m1)
  :
    <<EXT: Mem.extends m0 m1>>
.
Proof.
  unfold Mem_unfree in *. des_ifs.
  econs; unfold Mem.perm in *; ss; eauto.
  - unfold inject_id.
    econs; unfold Mem.perm in *; ii; ss; clarify; eauto with mem.
    + rewrite PMap.gsspec. zsimpl. des_ifs; bsimpl; des; ss; des_sumbool; clarify; eauto with mem.
    + eapply Z.divide_0_r.
    + zsimpl. rewrite PMap.gsspec. des_ifs; cycle 1.
      { refl. }
      destruct (classic (lo <= ofs < hi)).
      * exfalso. red in H0. des_ifs. eapply m; eauto. eapply Mem.perm_cur_max; eauto.
        unfold Mem.perm. rewrite Heq. econs; eauto.
      * rewrite Mem.setN_other; cycle 1.
        { ii. rewrite length_list_repeat in *. clarify.
          destruct (classic (0 <= hi - lo)).
          - rewrite Z2Nat.id in *; ss. xomega.
          - abstr (hi - lo) x. destruct x; try xomega. rewrite Z2Nat.inj_neg in *. xomega.
        }
        refl.
  - ii. rewrite PMap.gsspec in *. des_ifs; bsimpl; des; ss; des_sumbool; clarify; eauto with mem.
Qed.

Lemma Mem_unfree_right_inject
      F m_src0 m_tgt0 blk lo hi m_tgt1
      (INJ: Mem.inject F m_src0 m_tgt0)
      (UNFR: Mem_unfree m_tgt0 blk lo hi = Some m_tgt1)
  :
    <<INJ: Mem.inject F m_src0 m_tgt1>>
.
Proof. eapply Mem.inject_extends_compose; eauto. eapply Mem_unfree_extends; eauto. Qed.

End UNFREE.


Ltac perm_impl_tac := eapply Mem.perm_implies with Freeable; [|eauto with mem].

Lemma delta_range
      `{Val.meminj_ctx}
      F m_src m_tgt
      (INJECT: Mem.inject F m_src m_tgt)
      blk_src blk_tgt delta
      (INJVAL: F blk_src = Some (blk_tgt, delta))
      sz
      (PERM: Mem.range_perm m_src blk_src 0 sz Cur Freeable)
      (SIZEARG: 0 < sz <= Ptrofs.max_unsigned)
  :
   <<DELTA: 0 <= delta <= Ptrofs.max_unsigned>> /\
   <<DELTA: sz + delta <= Ptrofs.max_unsigned>>
.
Proof.
  unfold NW.
  split.
  - exploit Mem.mi_representable; eauto; cycle 1.
    { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. }
    left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max.
    perm_impl_tac. eapply PERM. split; try xomega.
  - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1.
    { instantiate (1:= sz.(Ptrofs.repr)).
      rewrite Ptrofs.unsigned_repr; cycle 1.
      { split; try xomega. }
      i. des. xomega.
    }
    right.
    rewrite Ptrofs.unsigned_repr; cycle 1.
    { split; try xomega. }
    eapply Mem.perm_cur_max. perm_impl_tac.
    eapply PERM. split; try xomega.
Qed.

(* TODO: Move to MemoryC *)
Lemma Mem_unchanged_on_bot
      m0 m1
      (NB: ((Mem.nextblock m0) <= (Mem.nextblock m1))%positive)
  :
    Mem.unchanged_on bot2 m0 m1
.
Proof. econs; ss; eauto. Qed.
