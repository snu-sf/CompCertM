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


Require Export Memory.

Module Mem.
  Include Memory.Mem.
  Local Transparent load.
  Local Transparent loadbytes.

  Definition perm_kind_dec (k0 k1: perm_kind): {k0 = k1} + {k0 <> k1}.
    decide equality.
  Defined.

  Section FREEWEAK.
    Program Definition unchecked_free_weak (m: mem) (b: block) (lo hi: Z): mem :=
      Mem.mkmem m.(Mem.mem_contents)
                    (PMap.set b
                              (fun ofs k => if zle lo ofs && zlt ofs hi && perm_kind_dec k Cur
                                            then None
                                            else m.(Mem.mem_access)#b ofs k)
                              m.(Mem.mem_access))
                    m.(Mem.nextblock) _ _ _.
    Next Obligation.
      repeat rewrite PMap.gsspec. destruct (peq b0 b).
      - r. des_ifs; bsimpl; des; des_sumbool; ss.
        + exploit Mem.access_max; eauto. rewrite Heq. rewrite Heq0. ii; ss.
        + exploit Mem.access_max; eauto. rewrite Heq. rewrite Heq0. ii; ss.
        + exploit Mem.access_max; eauto. rewrite Heq. rewrite Heq0. ii; ss.
        + exploit Mem.access_max; eauto. rewrite Heq. rewrite Heq0. ii; ss.
      - apply Mem.access_max.
    Qed.
    Next Obligation.
      repeat rewrite PMap.gsspec. destruct (peq b0 b).
      - subst.
        des_ifs; auto. apply Mem.nextblock_noaccess; auto.
      - apply Mem.nextblock_noaccess; auto.
    Qed.
    Next Obligation.
      apply Mem.contents_default.
    Qed.
    Definition free_weak (m: mem) (b: block) (lo hi: Z): option mem :=
      if Mem.range_perm_dec m b lo hi Cur Freeable
      then Some(unchecked_free_weak m b lo hi)
      else None.
  End FREEWEAK.

  Theorem range_perm_free_weak:
    forall m1 b lo hi,
      range_perm m1 b lo hi Cur Freeable ->
      { m2: mem | free_weak m1 b lo hi = Some m2 }.
  Proof.
    intros; unfold free_weak. rewrite pred_dec_true; auto. econstructor; eauto.
  Defined.

  Section FREE_WEAK.

    Variable m1: mem.
    Variable bf: block.
    Variables lo hi: Z.
    Variable m2: mem.
    Hypothesis FREE_WEAK: free_weak m1 bf lo hi = Some m2.

    Theorem free_weak_range_perm:
      range_perm m1 bf lo hi Cur Freeable.
    Proof.
      unfold free_weak in FREE_WEAK. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
      congruence.
    Qed.

    Lemma free_weak_result:
      m2 = unchecked_free_weak m1 bf lo hi.
    Proof.
      unfold free_weak in FREE_WEAK. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
      congruence. congruence.
    Qed.

    Theorem nextblock_free_weak:
      nextblock m2 = nextblock m1.
    Proof.
      rewrite free_weak_result; reflexivity.
    Qed.

    Theorem valid_block_free_weak_1:
      forall b, valid_block m1 b -> valid_block m2 b.
    Proof.
      intros. rewrite free_weak_result. assumption.
    Qed.

    Theorem valid_block_free_weak_2:
      forall b, valid_block m2 b -> valid_block m1 b.
    Proof.
      intros. rewrite free_weak_result in H. assumption.
    Qed.

    Local Hint Resolve valid_block_free_weak_1 valid_block_free_weak_2: mem.

    Theorem perm_free_weak_1:
      forall b ofs k p,
        b <> bf \/ ofs < lo \/ hi <= ofs ->
        perm m1 b ofs k p ->
        perm m2 b ofs k p.
    Proof.
      intros. rewrite free_weak_result. unfold perm, unchecked_free_weak; simpl.
      rewrite PMap.gsspec. destruct (peq b bf). subst b.
      destruct (zle lo ofs); simpl.
      destruct (zlt ofs hi); simpl.
      elimtype False; intuition.
      auto. auto.
      auto.
    Qed.

    Theorem perm_free_weak_2:
      forall ofs p, lo <= ofs < hi -> ~ perm m2 bf ofs Cur p.
    Proof.
      intros. rewrite free_weak_result. unfold perm, unchecked_free_weak; simpl.
      rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
      simpl. tauto. omega. omega.
    Qed.

    Theorem perm_free_weak_3:
      forall b ofs k p,
        perm m2 b ofs k p -> perm m1 b ofs k p.
    Proof.
      intros until p. rewrite free_weak_result. unfold perm, unchecked_free_weak; simpl.
      rewrite PMap.gsspec. destruct (peq b bf). subst b.
      destruct (zle lo ofs); simpl.
      destruct (zlt ofs hi); simpl. des_ifs.
      auto. auto. auto.
    Qed.

    Theorem perm_free_weak_inv:
      forall b ofs k p,
        perm m1 b ofs k p ->
        (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
    Proof.
      intros. rewrite free_weak_result. unfold perm, unchecked_free_weak; simpl.
      rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
      destruct (zle lo ofs); simpl; auto.
      destruct (zlt ofs hi); simpl; auto.
    Qed.

    Theorem valid_access_free_weak_1:
      forall chunk b ofs p,
        valid_access m1 chunk b ofs p ->
        b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
        valid_access m2 chunk b ofs p.
    Proof.
      intros. inv H. constructor; auto with mem.
      red; intros. eapply perm_free_weak_1; eauto.
      destruct (zlt lo hi). intuition. right. omega.
    Qed.

    Theorem valid_access_free_weak_2:
      forall chunk ofs p,
        lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
        ~(valid_access m2 chunk bf ofs p).
    Proof.
      intros; red; intros. inv H2.
      generalize (size_chunk_pos chunk); intros.
      destruct (zlt ofs lo).
      elim (perm_free_weak_2 lo p).
      omega. apply H3. omega.
      elim (perm_free_weak_2 ofs p).
      omega. apply H3. omega.
    Qed.

    Theorem valid_access_free_weak_inv_1:
      forall chunk b ofs p,
        valid_access m2 chunk b ofs p ->
        valid_access m1 chunk b ofs p.
    Proof.
      intros. destruct H. split; auto.
      red; intros. generalize (H ofs0 H1).
      rewrite free_weak_result. unfold perm, unchecked_free_weak; simpl.
      rewrite PMap.gsspec. destruct (peq b bf). subst b.
      destruct (zle lo ofs0); simpl.
      destruct (zlt ofs0 hi); simpl.
      tauto. auto. auto. auto.
    Qed.

    Theorem valid_access_free_weak_inv_2:
      forall chunk ofs p,
        valid_access m2 chunk bf ofs p ->
        lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
    Proof.
      intros.
      destruct (zlt lo hi); auto.
      destruct (zle (ofs + size_chunk chunk) lo); auto.
      destruct (zle hi ofs); auto.
      elim (valid_access_free_weak_2 chunk ofs p); auto. omega.
    Qed.

    Theorem load_free_weak:
      forall chunk b ofs,
        b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
        load chunk m2 b ofs = load chunk m1 b ofs.
    Proof.
      intros. unfold load.
      destruct (valid_access_dec m2 chunk b ofs Readable).
      rewrite pred_dec_true.
      rewrite free_weak_result; auto.
      eapply valid_access_free_weak_inv_1; eauto.
      rewrite pred_dec_false; auto.
      red; intro; elim n. eapply valid_access_free_weak_1; eauto.
    Qed.

    Theorem load_free_weak_2:
      forall chunk b ofs v,
        load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
    Proof.
      intros. unfold load. rewrite pred_dec_true.
      rewrite (load_result _ _ _ _ _ H). rewrite free_weak_result; auto.
      apply valid_access_free_weak_inv_1. eauto with mem.
    Qed.

    Theorem loadbytes_free_weak:
      forall b ofs n,
        b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
        loadbytes m2 b ofs n = loadbytes m1 b ofs n.
    Proof.
      intros. unfold loadbytes.
      destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
      rewrite pred_dec_true.
      rewrite free_weak_result; auto.
      red; intros. eapply perm_free_weak_3; eauto.
      rewrite pred_dec_false; auto.
      red; intros. elim n0; red; intros.
      eapply perm_free_weak_1; eauto. destruct H; auto. right; omega.
    Qed.

    Theorem loadbytes_free_weak_2:
      forall b ofs n bytes,
        loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
    Proof.
      intros. unfold loadbytes in *.
      destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
      rewrite pred_dec_true. rewrite free_weak_result; auto.
      red; intros. apply perm_free_weak_3; auto.
    Qed.

  End FREE_WEAK.

  Local Hint Resolve valid_block_free_weak_1 valid_block_free_weak_2
        perm_free_weak_1 perm_free_weak_2 perm_free_weak_3
        valid_access_free_weak_1 valid_access_free_weak_inv_1: mem.

  Lemma free_weak_left_inj:
    forall f m1 m2 b lo hi m1',
      mem_inj f m1 m2 ->
      free_weak m1 b lo hi = Some m1' ->
      mem_inj f m1' m2.
  Proof.
    intros. exploit free_weak_result; eauto. intro FREE_WEAK. inversion H. constructor.
    (* perm *)
    intros. eauto with mem.
    (* align *)
    intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros; eapply perm_free_weak_3; eauto.
    (* mem_contents *)
    intros. rewrite FREE_WEAK; simpl. eauto with mem.
  Qed.

  Lemma free_weak_right_inj:
    forall f m1 m2 b lo hi m2',
      mem_inj f m1 m2 ->
      free_weak m2 b lo hi = Some m2' ->
      (forall b' delta ofs k p,
          f b' = Some(b, delta) ->
          perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
      mem_inj f m1 m2'.
  Proof.
    intros. exploit free_weak_result; eauto. intro FREE_WEAK. inversion H.
    assert (PERM:
              forall b1 b2 delta ofs k p,
                f b1 = Some (b2, delta) ->
                perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
    intros.
    intros. eapply perm_free_weak_1; eauto.
    destruct (eq_block b2 b); auto. subst b. right.
    assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
    omega.
    constructor.
    (* perm *)
    auto.
    (* align *)
    eapply mi_align0; eauto.
    (* mem_contents *)
    intros. rewrite FREE_WEAK; simpl. eauto.
  Qed.

  (* Theorem free_weak_left_extends: *)
  (*   forall m1 m2 b lo hi m1', *)
  (*     extends m1 m2 -> *)
  (*     free_weak m1 b lo hi = Some m1' -> *)
  (*     extends m1' m2. *)
  (* Proof. *)
  (*   intros. inv H. constructor. *)
  (*   rewrite (nextblock_free_weak _ _ _ _ _ H0). auto. *)
  (*   eapply free_weak_left_inj; eauto. *)
  (*   intros. exploit mext_perm_inv0; eauto. intros [A|A]. *)
  (*   eapply perm_free_weak_inv in A; eauto. destruct A as [[A B]|A]; auto. *)
  (*   subst b0. right; eapply perm_free_weak_2; eauto. *)
  (*   intuition eauto using perm_free_weak_3. *)
  (* Qed. *)

  Theorem free_weak_right_extends:
    forall m1 m2 b lo hi m2',
      extends m1 m2 ->
      free_weak m2 b lo hi = Some m2' ->
      (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
      extends m1 m2'.
  Proof.
    intros. inv H. constructor.
    rewrite (nextblock_free_weak _ _ _ _ _ H0). auto.
    eapply free_weak_right_inj; eauto.
    unfold inject_id; intros. inv H. eapply H1; eauto. omega.
    intros. eauto using perm_free_weak_3.
  Qed.

  Theorem free_weak_parallel_extends:
    forall m1 m2 b lo hi m1',
      extends m1 m2 ->
      free_weak m1 b lo hi = Some m1' ->
      exists m2',
        free_weak m2 b lo hi = Some m2'
        /\ extends m1' m2'.
  Proof.
    intros. inversion H.
    assert ({ m2': mem | free_weak m2 b lo hi = Some m2' }).
    apply range_perm_free_weak. red; intros.
    replace ofs with (ofs + 0) by omega.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_weak_range_perm; eauto.
    destruct X as [m2' FREE_WEAK]. exists m2'; split; auto.
    constructor.
    rewrite (nextblock_free_weak _ _ _ _ _ H0).
    rewrite (nextblock_free_weak _ _ _ _ _ FREE_WEAK). auto.
    eapply free_weak_right_inj with (m1 := m1'); eauto.
    eapply free_weak_left_inj; eauto.
    unfold inject_id; intros. inv H1.
    eapply perm_free_weak_2. eexact H0. instantiate (1 := ofs); omega. eauto.
    intros. exploit mext_perm_inv0; eauto using perm_free_weak_3. intros [A|A].
    eapply perm_free_weak_inv in A; eauto. destruct A as [[A B]|A]; auto.
    subst b0. right; eapply perm_free_weak_2; eauto.
    right; intuition eauto using perm_free_weak_3.
  Qed.

  Lemma free_weak_left_inject:
    forall f m1 m2 b lo hi m1',
      inject f m1 m2 ->
      free_weak m1 b lo hi = Some m1' ->
      inject f m1' m2.
  Proof.
    intros. inversion H. constructor.
    (* inj *)
    eapply free_weak_left_inj; eauto.
    (* free_weakblocks *)
    eauto with mem.
    (* mappedblocks *)
    auto.
    (* no overlap *)
    red; intros. eauto with mem.
    (* representable *)
    intros. eapply mi_representable0; try eassumption.
    destruct H2; eauto with mem.
    (* perm inv *)
    intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_weak_3.
    eapply perm_free_weak_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
    subst b1. right; eapply perm_free_weak_2; eauto.
  Qed.

  Lemma free_weak_right_inject:
    forall f m1 m2 b lo hi m2',
      inject f m1 m2 ->
      free_weak m2 b lo hi = Some m2' ->
      (forall b1 delta ofs k p,
          f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
          lo <= ofs + delta < hi -> False) ->
      inject f m1 m2'.
  Proof.
    intros. inversion H. constructor.
    (* inj *)
    eapply free_weak_right_inj; eauto.
    (* free_weakblocks *)
    auto.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    auto.
    (* representable *)
    auto.
    (* perm inv *)
    intros. eauto using perm_free_weak_3.
  Qed.

  Theorem free_weak_inject:
    forall f m1 l m1' m2 b lo hi m2',
      inject f m1 m2 ->
      free_weak_list m1 l = Some m1' ->
      free_weak m2 b lo hi = Some m2' ->
      (forall b1 delta ofs k p,
          f b1 = Some(b, delta) ->
          perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
          exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
      inject f m1' m2'.
  Proof.
    intros.
    eapply free_weak_right_inject; eauto.
    eapply free_weak_list_left_inject; eauto.
    intros. exploit perm_free_weak_list; eauto. intros [A B].
    exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
  Qed.

  Theorem free_weak_parallel_inject:
    forall f m1 m2 b lo hi m1' b' delta,
      inject f m1 m2 ->
      free_weak m1 b lo hi = Some m1' ->
      f b = Some(b', delta) ->
      exists m2',
        free_weak m2 b' (lo + delta) (hi + delta) = Some m2'
        /\ inject f m1' m2'.
  Proof.
    intros.
    destruct (range_perm_free_weak m2 b' (lo + delta) (hi + delta)) as [m2' FREE_WEAK].
    eapply range_perm_inject; eauto. eapply free_weak_range_perm; eauto.
    exists m2'; split; auto.
    eapply free_weak_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
    simpl; rewrite H0; auto.
    intros. destruct (eq_block b1 b).
    subst b1. rewrite H1 in H2; inv H2.
    exists lo, hi; split; auto with coqlib. omega.
    exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
    eapply perm_max. eapply perm_implies. eauto. auto with mem.
    instantiate (1 := ofs + delta0 - delta).
    apply perm_cur_max. apply perm_implies with Free_Weakable; auto with mem.
    eapply free_weak_range_perm; eauto. omega.
    intros [A|A]. congruence. omega.
  Qed.

  Lemma free_weak_unchanged_on:
    forall m b lo hi m',
      free_weak m b lo hi = Some m' ->
      (forall i, lo <= i < hi -> ~ P b i) ->
      unchanged_on m m'.
  Proof.
    intros; constructor; intros.
    - rewrite (nextblock_free_weak _ _ _ _ _ H). apply Ple_refl.
    - split; intros.
      eapply perm_free_weak_1; eauto.
      destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
      subst b0. elim (H0 ofs). omega. auto.
      eapply perm_free_weak_3; eauto.
    - unfold free_weak in H. destruct (range_perm_dec m b lo hi Cur Free_Weakable); inv H.
      simpl. auto.
  Qed.

Global Opaque Mem.alloc Mem.free_weak Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free_weak
  Mem.free_weak_range_perm
  Mem.nextblock_free_weak
  Mem.valid_block_free_weak_1
  Mem.valid_block_free_weak_2
  Mem.perm_free_weak_1
  Mem.perm_free_weak_2
  Mem.perm_free_weak_3
  Mem.valid_access_free_weak_1
  Mem.valid_access_free_weak_2
  Mem.valid_access_free_weak_inv_1
  Mem.valid_access_free_weak_inv_2
  Mem.unchanged_on_refl
: mem.
