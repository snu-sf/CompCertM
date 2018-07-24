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

Program Definition Mem_drop_perm_none (m: mem) (b: block) (lo hi: Z): mem :=
  (Mem.mkmem m.(Mem.mem_contents)
                 (PMap.set b
                           (fun ofs k =>
                              if zle lo ofs && zlt ofs hi
                              then None
                              else m.(Mem.mem_access)#b ofs k)
                           m.(Mem.mem_access))
                 m.(Mem.nextblock) _ _ _)
.
Next Obligation.
  repeat rewrite PMap.gsspec.
  destruct (peq b0 b); cycle 1.
  { apply Mem.access_max. }
  subst.
  des_ifs.
  - apply Mem.access_max.
Qed.
Next Obligation.
  hexploit Mem.nextblock_noaccess; eauto; []; i; des.
  rewrite PMap.gsspec.
  des_ifs; eauto.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.

Lemma Mem_drop_perm_none_spec
      m0 blk0 lo hi m1
      (DROP: Mem_drop_perm_none m0 blk0 lo hi = m1)
  :
    (<<NB: Mem.nextblock m0 = Mem.nextblock m1>>)
    /\
    (<<UNCH: Mem.unchanged_on (fun blk1 ofs => blk0 <> blk1 \/ ofs < lo \/ hi <= ofs) m0 m1>>)
    /\
    (<<INSIDE: forall
        ofs
        (INSIDE: lo <= ofs < hi)
    ,
      all2 ~2 Mem.perm m1 blk0 ofs>>)
.
Proof.
  ii.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
  splits; ii; ss.
  - econs; ss; eauto.
    { reflexivity. }
    ii.
    unfold Mem.perm. cbn. rewrite ! PMap.gsspec in *. des_ifs. simpl_bool.
    des; ss; des_sumbool; try lia.
  - des_ifs. simpl_bool. des; des_sumbool; lia.
Qed.

Lemma Mem_set_perm_none_impl
      m0 blk lo hi m1
      (DROP: Mem_drop_perm_none m0 blk lo hi = m1)
  :
    <<PERM: Mem.perm m1 <4= Mem.perm m0>>
.
Proof.
  ii.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
Qed.

Lemma Mem_set_perm_none_left_inject
      `{Val.meminj_ctx}
      j m_src0 m_tgt0
      (INJ: Mem.inject j m_src0 m_tgt0)
      blk lo hi m_src1
      (DROP: Mem_drop_perm_none m_src0 blk lo hi = m_src1)
  :
    <<INJ: Mem.inject j m_src1 m_tgt0>>
.
Proof.
  hexploit Mem_set_perm_none_impl; eauto. intro IMPL; des.
  inv INJ.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in IMPL. ss.
  econs; ss; eauto.
  - inv mi_inj.
    econs; i; ss; eauto.
    + exploit mi_perm; eauto.
      eapply IMPL; eauto.
    + eapply mi_align; eauto.
      ii.
      eapply IMPL; eauto. eapply H1; eauto.
    + exploit mi_memval; eauto.
      eapply IMPL; eauto.
  - ii. unfold Mem.perm in *. ss. eapply mi_no_overlap; eauto; eapply IMPL; eauto.
  - unfold Mem.perm. ss.
    ii. eapply mi_representable; eauto.
    des.
    + left. eapply IMPL; eauto.
    + right. eapply IMPL; eauto.
  - ii. hexploit mi_perm_inv; eauto.
    unfold Mem.perm. ss. unfold Mem.perm in H1.
    i; des.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
Qed.

Global Opaque Mem_drop_perm_none.








Module DEPRECATED.

Program Definition Mem_set_perm (m: mem) (b: block) (lo hi: Z) (op: option permission): option mem :=
  match op with
    | Some p =>
      if (Mem.range_perm_dec m b lo hi Max p) then
        if (plt b m.(Mem.nextblock)) then
          Some (Mem.mkmem m.(Mem.mem_contents)
                          (PMap.set b
                                    (fun ofs k =>
                                       match k with
                                         | Cur =>
                                           if zle lo ofs && zlt ofs hi
                                           then Some p
                                           else m.(Mem.mem_access)#b ofs k
                                         | Max => m.(Mem.mem_access)#b ofs k
                                       end
                                    )
                                    m.(Mem.mem_access))
                          m.(Mem.nextblock) _ _ _)
        else None
      else None
    | None =>
      Some (Mem.mkmem m.(Mem.mem_contents)
                      (PMap.set b
                                (fun ofs k =>
                                   if zle lo ofs && zlt ofs hi
                                   then None
                                   else m.(Mem.mem_access)#b ofs k)
                                m.(Mem.mem_access))
                      m.(Mem.nextblock) _ _ _)
  end.
Next Obligation.
  repeat rewrite PMap.gsspec.
  destruct (peq b0 b); cycle 1.
  { apply Mem.access_max. }
  subst.
  des_ifs.
  - simpl_bool; des; des_sumbool.
    exploit H; eauto.
  - apply Mem.access_max.
Qed.
Next Obligation.
  specialize (Mem.nextblock_noaccess m b0 ofs k H1). intros.
  rewrite PMap.gsspec.
  des_ifs.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply Mem.access_max.
  apply Mem.access_max.
Qed.
Next Obligation.
  hexploit Mem.nextblock_noaccess; eauto; []; i; des.
  rewrite PMap.gsspec.
  des_ifs; eauto.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.

Lemma Mem_set_perm_none_spec
      m0 blk0 lo hi m1
      (DROP: Mem_set_perm m0 blk0 lo hi None = Some m1)
  :
    (<<OUTSIDE: forall
      blk1 ofs
      (DISJOINT: blk0 <> blk1 \/ ofs < lo \/ hi <= ofs)
    ,
      all2 (Mem.perm m0 blk1 ofs <2> Mem.perm m1 blk1 ofs)>>)
    /\
    (<<INSIDE: forall
        ofs
        (INSIDE: lo <= ofs < hi)
    ,
      all2 ~2 Mem.perm m1 blk0 ofs>>)
.
Proof.
  ii.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
  split; ii; ss.
  - rewrite PMap.gsspec.
    des_ifs. simpl_bool. des_safe. des_sumbool. admit "IDK WHY BUT IT MAKES xomega SLOW IN STACKINGPROOFC1.v!!!!!! des; try xomega".
  - des_ifs. simpl_bool. des_safe. admit "des; des_sumbool; try xomega".
Qed.

Lemma Mem_set_perm_none_impl
      m0 blk lo hi m1
      (DROP: Mem_set_perm m0 blk lo hi None = Some m1)
  :
    <<PERM: Mem.perm m1 <4= Mem.perm m0>>
.
Proof.
  ii.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
Qed.

Lemma Mem_set_perm_none_left_inject
      `{Val.meminj_ctx}
      j m_src0 m_tgt0
      (INJ: Mem.inject j m_src0 m_tgt0)
      blk lo hi m_src1
      (DROP: Mem_set_perm m_src0 blk lo hi None = Some m_src1)
  :
    <<INJ: Mem.inject j m_src1 m_tgt0>>
.
Proof.
  hexploit Mem_set_perm_none_impl; eauto. intro IMPL; des.
  inv INJ.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in IMPL. ss.
  econs; ss; eauto.
  - inv mi_inj.
    econs; i; ss; eauto.
    + exploit mi_perm; eauto.
      eapply IMPL; eauto.
    + eapply mi_align; eauto.
      ii.
      eapply IMPL; eauto. eapply H1; eauto.
    + exploit mi_memval; eauto.
      eapply IMPL; eauto.
  - ii. unfold Mem.perm in *. ss. eapply mi_no_overlap; eauto; eapply IMPL; eauto.
  - unfold Mem.perm. ss.
    ii. eapply mi_representable; eauto.
    des.
    + left. eapply IMPL; eauto.
    + right. eapply IMPL; eauto.
  - ii. hexploit mi_perm_inv; eauto.
    unfold Mem.perm. ss. unfold Mem.perm in H1.
    i; des.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
Qed.

Global Opaque Mem_set_perm.

(* heap(malloc) has permission on (b, -1) *)
(* TODO: Name is not precise... malloc && drop_perm will satsify this condition. *)
Definition is_stack_block (m: mem) (blk: block): Prop := forall
    ofs kind perm
    (PERM: Mem.perm m blk ofs kind perm)
  ,
    <<POS: 0 <= ofs>>
.
Hint Unfold is_stack_block.

End DEPRECATED.

Definition dead_block (m: mem) (b: block): Prop := forall ofs, ~Mem.perm m b ofs Cur Nonempty.

Inductive mem_equiv (m0 m1: mem): Prop :=
| mem_equiv_intro
    (UNCH: Mem.unchanged_on top2 m0 m1)
    (DEAD: forall b (BETWEEN: (m0.(Mem.nextblock) <= b < m1.(Mem.nextblock))%positive), dead_block m1 b)
.

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

Lemma drop_perm_none_dead_block
      m0 blk lo hi
      (INSIDE: forall ofs k p (PERM: Mem.perm m0 blk ofs k p), lo <= ofs < hi)
  :
    dead_block (Mem_drop_perm_none m0 blk lo hi) blk
.
Proof.
  ii.
  exploit (Mem_drop_perm_none_spec m0 blk lo hi); eauto. i; des.
  destruct (classic (lo <= ofs < hi)).
  - eapply INSIDE0; eauto.
  - inv UNCH.
    erewrite <- unchanged_on_perm in *; ss.
    + eapply INSIDE in H. xomega.
    + right. xomega.
    + unfold Mem.valid_block. rewrite NB.
      eapply Mem.perm_valid_block; eauto.
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



Inductive future_imm (m0 m1: mem): Prop :=
| future_imm_alloc
    blk lo hi
    (FREE: Mem.alloc m0 lo hi = (m1, blk))
| future_imm_store
    chunk blk ofs v
    (STORE: Mem.store chunk m0 blk ofs v = Some m1)
| future_imm_storebytes
    ofs blk mvs
    (STOREB: Mem.storebytes m0 blk ofs mvs = Some m1)
| future_imm_free
    blk lo hi
    (FREE: Mem.free m0 blk lo hi = Some m1)
| future_imm_drop_perm_none
    blk lo hi
    (DROPN: Mem_drop_perm_none m0 blk lo hi = m1)
(* TODO: drop_perm? *)
.
Hint Constructors future_imm.

Definition future: mem -> mem -> Prop := rtc future_imm.
Hint Unfold future.






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




Section STORED.

Inductive Mem_stored (chunk: memory_chunk) (m0: mem) (b: block) (ofs: Z) (v: val): Prop :=
| stored_intro
    (STORED: (Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b m0.(Mem.mem_contents)))
             = (encode_val chunk v))
    (WRITABLE: Mem.valid_access m0 chunk b ofs Writable)
.

Definition Mem_storedv chunk m addr v: Prop :=
  match addr with
  | Vptr b ofs true => Mem_stored chunk m b (Ptrofs.unsigned ofs) v
  | _ => False
  end
.

Theorem Mem_store_stored
        chunk m0 b ofs v m1
        (STORE: Mem.store chunk m0 b ofs v = Some m1)
  :
    <<STORED: Mem_stored chunk m1 b ofs v>>
.
Proof.
  econs; eauto with mem.
  erewrite Mem.store_mem_contents; eauto.
  rewrite Maps.PMap.gsspec. des_ifs.
  erewrite <- encode_val_length; eauto.
  rewrite Mem.getN_setN_same. ss.
Qed.

(* Local Transparent Mem.load. *)
(* Lemma Mem_stored_load *)
(*       chunk m0 b ofs v *)
(*       (STORE: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     <<LOAD: Mem.load chunk m0 b ofs = Some v>> *)
(* . *)
(* Proof. *)
(*   inv STORE. *)
(*   unfold Mem.load. des_ifs; cycle 1. *)
(*   { exfalso. eapply n. eauto with mem. } *)
(*   red. f_equal. *)
(*   destruct chunk; ss; des_ifs. *)
(*   - unfold encode_val in *. *)
(*   destruct chunk; ss. *)
(*   - unfold Maps.PMap.get. des_ifs. econs; eauto. *)
(* Qed. *)
(* Local Opaque Mem.load. *)

(* Local Transparent Mem.store. *)

(* Definition ZMap_equal {X} (eqX: X -> X -> Prop) (EQUIV: RelationClasses.Equivalence eqX) *)
(*            (zm0 zm1: Maps.ZMap.t X): Prop := *)
(*   zm0.(fst) = zm1.(fst) /\ Maps.PTree_Properties.Equal EQUIV zm0.(snd) zm1.(snd) *)
(* . *)

(* Inductive Mem_equal (m0 m1: mem): Prop := *)
(* | equal_intro *)
(*       (EQ0: m0.(Mem.mem_contents).(fst) = m1.(Mem.mem_contents).(fst)) *)
(*       (EQ1: @Maps.PTree_Properties.Equal _ (ZMap_equal eq (@Eqsth _)) *)
(*                                          (admit "") *)
(*                                          m0.(Mem.mem_contents).(snd) m1.(Mem.mem_contents).(snd)) *)
(*       (EQ2: m0.(Mem.mem_access) = m1.(Mem.mem_access)) *)
(*       (EQ3: m0.(Mem.nextblock) = m1.(Mem.nextblock)) *)
(* . *)

(* Theorem Mem_stored_store *)
(*         chunk m0 b ofs v *)
(*         (STORED: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     exists m1, <<STORE: Mem.store chunk m0 b ofs v = Some m1>> /\ *)
(*                         <<EQUIV: Mem_equal m0 m1>> *)
(* . *)
(* Proof. *)
(*   inv STORED. *)
(*   unfold Mem.store. des_ifs. destruct m0; ss. *)
(*   esplits; eauto. *)
(*   econs; eauto. cbn. *)
(*   destruct mem_contents; ss. *)
(*   hnf. ii; ss. *)
(*   destruct (Maps.PTree.get x t0) eqn:T. *)
(*   - rewrite Maps.PTree.gsspec. rewrite T. *)
(*     unfold Maps.PMap.get in *. ss. des_ifs; try reflexivity. *)
(*     econs; ss. *)
(*     { rewrite Mem.setN_default. ss. } *)
(*     hnf. ii. *)
(*     destruct (Maps.PTree.get x (snd t1)) eqn:U. *)
(*     + *)
(*     des_ifs. *)
(*     rewrite <- STORED0. erewrite <- encode_val_length with (v:=v); eauto. *)
(*     rewrite Mem.getN_setN_same. ss. *)
(*     econs; eauto. *)
(*   unfold Maps.PMap.set. ss. f_equal. *)
(*   Maps.PTree_Properties.Equal *)
(*   assert(forall i, Maps.PTree.set b (Mem.setN (encode_val chunk v) ofs (Maps.PMap.get b (t, t0))) t0 *)
(*   rewrite Maps.PTree.gsspec. *)
(*   eapply Axioms.functional_extensionality. *)
(*   cbn. *)
(*   Set Printing All. *)
(*   rewrite Maps.PMap.gsspec. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(*   econs; eauto. *)
(*   econs; eauto with mem. *)
(*   erewrite Mem.store_mem_contents; eauto. *)
(*   rewrite Maps.PMap.gsspec. des_ifs. *)
(*   erewrite <- encode_val_length; eauto. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(* Qed. *)


(* Lemma Mem_equal_proof_irr *)
(*       m0 m1 *)
(*       (EQ0: m0.(Mem.mem_contents) = m1.(Mem.mem_contents)) *)
(*       (EQ1: m0.(Mem.mem_access) = m1.(Mem.mem_access)) *)
(*       (EQ2: m0.(Mem.nextblock) = m1.(Mem.nextblock)) *)
(*   : *)
(*     m0 = m1 *)
(* . *)
(* Proof. *)
(*   destruct m0, m1; ss. clarify. *)
(*   f_equal; eapply Axioms.proof_irr. *)
(* Qed. *)

(* Theorem Mem_stored_store *)
(*         chunk m0 b ofs v *)
(*         (STORED: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     exists m1, <<STORE: Mem.store chunk m0 b ofs v = Some m1>> /\ *)
(*                         <<EQUIV: m0 = m1>> *)
(* . *)
(* Proof. *)
(*   inv STORED. *)
(*   unfold Mem.store. des_ifs. destruct m0; ss. *)
(*   esplits; eauto. cbn. *)
(*   f_equal. eapply Mem_equal_proof_irr; eauto. *)
(*   ss. *)
(*   destruct mem_contents; ss. *)
(*   unfold Maps.PMap.set. ss. f_equal. *)
(*   Maps.PTree_Properties.Equal *)
(*   assert(forall i, Maps.PTree.set b (Mem.setN (encode_val chunk v) ofs (Maps.PMap.get b (t, t0))) t0 *)
(*   rewrite Maps.PTree.gsspec. *)
(*   eapply Axioms.functional_extensionality. *)
(*   cbn. *)
(*   Set Printing All. *)
(*   rewrite Maps.PMap.gsspec. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(*   econs; eauto. *)
(*   econs; eauto with mem. *)
(*   erewrite Mem.store_mem_contents; eauto. *)
(*   rewrite Maps.PMap.gsspec. des_ifs. *)
(*   erewrite <- encode_val_length; eauto. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(* Qed. *)


Context `{CTX: Val.meminj_ctx}.

Lemma memval_inject_refl
      mv
  :
    @memval_inject Val.mi_normal (fun b0 : block => Some (b0, 0)) mv mv
.
Proof.
  destruct mv; ss; econs; eauto.
  apply val_inject_id. ss.
Qed.

Lemma store_stored_extends
      m0 m1
      chunk rsp pos v
      (STORED: Mem_stored chunk m0 rsp pos v)
      (STORE: Mem.store chunk m0 rsp pos v = Some m1)
  :
    <<EXTENDS: Mem.extends m1 m0>>
.
Proof.
Local Transparent Mem.store.
  hexploit Mem_store_perm_eq; eauto. intro PERM. des.
  unfold Mem.store in *. inv STORE. des_ifs.
  econs; eauto.
  unfold inject_id.
  econs; ss; eauto.
  - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss.
  - ii; clarify. unfold Mem.range_perm, Mem.perm in *. ss. rewrite Z.divide_0_r. reflexivity.
  - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss.
    rewrite Maps.PMap.gsspec. des_ifs; cycle 1.
    { apply memval_inject_refl. }
    inv STORED.
    rewrite <- STORED0.
    destruct chunk; ss; rewrite ! Maps.ZMap.gsspec; des_ifs; try apply memval_inject_refl.
Local Opaque Mem.store.
Qed.

Lemma store_stored_inject
      j0 m_src0 m_src1 m_tgt
      (INJ: Mem.inject j0 m_src0 m_tgt)
      v_src v_tgt
      (INJV: Val.inject j0 v_src v_tgt) 
      ty rsp_src rsp_tgt rspdelta ofs
      (SRC: Mem.storev (chunk_of_type ty) m_src0 (Vptr rsp_src ofs true) v_src = Some m_src1)
      (TGT: Mem_stored (chunk_of_type ty) m_tgt rsp_tgt (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) v_tgt)
      (INJRSP: j0 rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned)))
      (BOUND: Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta <= Ptrofs.max_unsigned)
  :
    <<INJ: Mem.inject j0 m_src1 m_tgt>>
.
Proof.
  ss. red.
  exploit Mem.store_mapped_inject; eauto. i; des.
  eapply Mem.inject_extends_compose; eauto.
  eapply store_stored_extends; try apply SRC; eauto.
  rpapply H. f_equal.
  rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; ss. split; try xomega.
  hexploit (Ptrofs.unsigned_range ofs); eauto. i.
  hexploit (Ptrofs.unsigned_range rspdelta); eauto. i.
  xomega.
Qed.

Lemma Mem_stored_unchanged_on
      P m0 m1
      (UNCH: Mem.unchanged_on P m0 m1)
      b ofs v chunk
      (INSIDE: forall i : Z, ofs <= i < ofs + size_chunk chunk -> P b i)
      (STORED: Mem_stored chunk m0 b ofs v)
  :
    <<STORED: Mem_stored chunk m1 b ofs v>>
.
Proof.
  inv UNCH.
  inv STORED. econs; eauto.
  - erewrite <- STORED0.
    unfold Mem.valid_access in *. ss. des; ss.
    apply Mem.range_perm_implies with (p2:= Readable) in WRITABLE; eauto with mem.
    destruct chunk; ss; rewrite ! unchanged_on_contents; eauto with lia.
  - hnf in WRITABLE. des.
    hnf. splits; eauto. ii. eapply unchanged_on_perm; eauto.
    eauto with mem.
Qed.



Goal forall ty, type_of_chunk (chunk_of_type ty) = ty.
Proof. i; destruct ty; ss. Qed.

Goal forall chunk, (chunk_of_type (type_of_chunk chunk)) = chunk.
Proof. i. destruct chunk; ss. Abort.

Lemma float32_eq
      f0 f1
      (EQ: Float32.to_bits f0 = Float32.to_bits f1)
  :
    f0 = f1
.
Proof.
  rewrite <- Float32.of_to_bits. symmetry. rewrite <- Float32.of_to_bits.
  rewrite EQ. ss.
Qed.

Lemma float_eq
      f0 f1
      (EQ: Float.to_bits f0 = Float.to_bits f1)
  :
    f0 = f1
.
Proof.
  rewrite <- Float.of_to_bits. symmetry. rewrite <- Float.of_to_bits.
  rewrite EQ. ss.
Qed.

Lemma mod_eq
      x y
      A
      (EQ0: x mod A = y mod A)
      (EQ1: x / A = y / A)
      (BOUND: 0 < A)
  :
    x = y
.
Proof.
  des. try lia. try xomega.
  rewrite Z_div_mod_eq with (b:=A); try lia.
  symmetry.
  rewrite Z_div_mod_eq with (b:=A); try lia.
  congruence.
Qed.

Lemma Mem_stored_dtm
      ty m b ofs v0 v1
      (* (TY0: Val.has_type v0 ty) *)
      (* (TY1: Val.has_type v1 ty) *)
      (WELLDEF0: ~ In Undef (encode_val (chunk_of_type ty) v0))
      (WELLDEF1: ~ In Undef (encode_val (chunk_of_type ty) v0))
      (STORED0: Mem_stored (chunk_of_type ty) m b ofs v0)
      (STORED1: Mem_stored (chunk_of_type ty) m b ofs v1)
  :
    v0 = v1
.
Proof.
Local Transparent Byte.repr.
  inv STORED0. inv STORED1.
  clear WRITABLE WRITABLE0.
  clear_tac.
  rewrite STORED in *. clear STORED. clear_tac.
  unfold encode_val in *; ss.
  pose v0 as X. pose v1 as Y. pose ty as TY.
  unfold inj_bytes, encode_int, rev_if_be in *.
  destruct Archi.big_endian eqn:T; ss.
  assert(BYTE: Byte.modulus = 256).
  { unfold Byte.modulus in *. unfold Byte.wordsize. ss. }
  destruct ty; ss.
  - des_ifs; ss; try (by exfalso; eauto).
    unfold Byte.repr in *. ss. clarify.
    f_equal.
    destruct i, i0; ss.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    eapply Int.mkint_eq.
    { unfold Int.modulus in *. unfold two_power_nat in *. ss.
      do 4 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    apply float_eq.
    abstr (Float.to_bits f) F0.
    abstr (Float.to_bits f0) F1.
    destruct F0, F1; ss.
    eapply Int64.mkint_eq.
    { unfold Int64.modulus in *. unfold two_power_nat in *. ss.
      do 8 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    destruct i, i0; ss.
    eapply Int64.mkint_eq.
    { unfold Int64.modulus in *. unfold two_power_nat in *. ss.
      do 8 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    apply float32_eq.
    abstr (Float32.to_bits f) F0.
    abstr (Float32.to_bits f0) F1.
    destruct F0, F1; ss.
    eapply Int.mkint_eq.
    { unfold Int.modulus in *. unfold two_power_nat in *. ss.
      do 4 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs.
  - des_ifs.
Qed.

End STORED.





Section LOADABLE.

Inductive Mem_loadable (chunk: memory_chunk) (m0: mem) (b: block) (ofs: Z) (v: val): Prop :=
| loadable_intro
    (LOADABLE: Mem.load chunk m0 b ofs = Some v)
.

End LOADABLE.




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

