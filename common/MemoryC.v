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


Local Notation "a # b" := (PMap.get b a) (at level 1).
(** Above is exactly copied from Memory.v **)

(* newly added *)
Require Export Memory.






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










Section UNFREE.

Program Definition Mem_unfree (m: mem) (b: block) (lo hi: Z): option mem :=
  if plt b m.(Mem.nextblock)
  then
    Some (Mem.mkmem
            (PMap.set b (Mem.setN (list_repeat (hi-lo+1).(Z.to_nat) Undef) lo ((Mem.mem_contents m) # b))
                      (Mem.mem_contents m))
            (PMap.set b
                      (fun ofs k =>
                         if zle lo ofs && zlt ofs hi
                         then Some Freeable
                         else m.(Mem.mem_access)#b ofs k)
                      m.(Mem.mem_access))
            m.(Mem.nextblock) _ _ _)
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

