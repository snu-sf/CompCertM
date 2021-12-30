Require Import Setoid Program.Basics.
Require Import CoqlibC.
From compcertr Require Import
     Decidableplus
     AST
     Integers
     Values
     Events
     Globalenvs.
Require Import MemoryC.
(** newly added **)
Require Import AxiomsC.
From compcertr Require Export Separation.
Require Import JunkBlock.

Local Open Scope sep_scope.


Ltac sep_split := econs; [|split]; swap 2 3.

Global Program Instance disjoint_footprint_sym: Symmetric disjoint_footprint.
Next Obligation. ii. eapply H; eauto. Qed.


Lemma separation_private
      m_src m_tgt F P
      (MATCH: m_tgt |= P ** minjection F m_src)
  :
     P.(m_footprint) <2= loc_out_of_reach F m_src.
Proof.
  inv MATCH. des; ss.
  ii. unfold disjoint_footprint in *. ss.
  eapply H1; eauto.
Qed.

Lemma disjoint_footprint_drop_empty
      P Q0 Q1
      (EMPTY: Q0.(m_footprint) <2= bot2)
      (DISJ: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (Q0 ** Q1)>>.
Proof.
  ii. ss. unfold disjoint_footprint in *. des; eauto.
  eapply EMPTY; eauto.
Qed.

(* Lemma disjoint_footprint_mconj *)
(*       P Q0 Q1 *)
(*       (DISJ0: disjoint_footprint P Q0) *)
(*       (DISJ1: disjoint_footprint P Q1) *)
(*   : *)
(*     <<DISJ: disjoint_footprint P (mconj Q0 Q1)>> *)
(* . *)
(* Proof. *)
(*   ii. ss. unfold disjoint_footprint in *. des; eauto. *)
(* Qed. *)

Lemma disjoint_footprint_mconj
      P Q0 Q1
  :
    <<DISJ: disjoint_footprint P (mconj Q0 Q1)>>
    <-> <<DISJ0: disjoint_footprint P Q0>> /\ <<DISJ1: disjoint_footprint P Q1>>.
Proof.
  split; ii; ss; unfold disjoint_footprint in *; des; eauto.
  esplits; ii; ss; eauto.
Qed.

Lemma disjoint_footprint_sepconj
      P Q0 Q1
  :
    (<<DISJ0: disjoint_footprint P Q0>>) /\ (<<DISJ1: disjoint_footprint P Q1>>)
    <-> (<<DISJ: disjoint_footprint P (Q0 ** Q1)>>).
Proof.
  unfold disjoint_footprint in *.
  split; esplits; ii; ss; des; eauto.
Qed.

(* Lemma mconj_sym *)
(*       P Q *)
(*   : *)
(*     <<EQ: massert_eqv (mconj P Q) (mconj Q P)>> *)
(* . *)
(* Proof. *)
(*   red. *)
(*   split; ii. *)
(*   - econs. *)
(*     + ii. unfold mconj in *. ss. des; ss. *)
(*     + ii. ss. des; eauto. *)
(*   - econs. *)
(*     + ii. unfold mconj in *. ss. des; ss. *)
(*     + ii. ss. des; eauto. *)
(* Qed. *)

Lemma massert_eq
      pred0 footprint0 INVAR0 VALID0
      pred1 footprint1 INVAR1 VALID1
      (EQ0: pred0 = pred1)
      (EQ1: footprint0 = footprint1)
  :
    Build_massert pred0 footprint0 INVAR0 VALID0 = Build_massert pred1 footprint1 INVAR1 VALID1.
Proof.
  clarify.
  f_equal.
  apply Axioms.proof_irr.
  apply Axioms.proof_irr.
Qed.

Lemma mconj_sym
      P Q
  :
    <<EQ: (mconj P Q) = (mconj Q P)>>.
Proof.
  apply massert_eq; ss.
  - apply Axioms.functional_extensionality. ii; ss.
    apply prop_ext.
    split; i; des; split; ss.
  - apply Axioms.functional_extensionality. ii; ss.
    apply Axioms.functional_extensionality. ii; ss.
    apply prop_ext.
    split; i; des; eauto.
Qed.

Lemma sepconj_sym
      P Q
  :
    <<EQ: (sepconj P Q) = (sepconj Q P)>>.
Proof.
  apply massert_eq; ss.
  - apply Axioms.functional_extensionality. ii; ss.
    apply prop_ext.
    split; i; des; esplits; ss.
    + sym; ss.
    + sym; ss.
  - apply Axioms.functional_extensionality. ii; ss.
    apply Axioms.functional_extensionality. ii; ss.
    apply prop_ext.
    split; i; des; eauto.
Qed.

Local Transparent sepconj.

Lemma sep_drop_tail3
      P Q R
  :
    massert_imp (P ** Q ** R) (P ** Q).
Proof.
  unfold massert_imp. ss. split; ii; eauto.
  - des; esplits; eauto. apply disjoint_footprint_sepconj in H1. des; ss.
  - ss. des; eauto.
Qed.

Lemma sepconj_isolated_mutation0
      m0 m1 P Q
      (SEP: m0 |= P ** Q)
      (* (UNCH: Mem.unchanged_on (~2 P.(m_footprint)) m0 m1) *)
      (UNCH: Mem.unchanged_on (fun blk ofs => ~ P.(m_footprint) blk ofs /\ Mem.valid_block m0 blk) m0 m1)
  :
    <<SEP: m1 |= Q>>.
Proof.
  destruct SEP as (A & B & C).
  eapply m_invar; eauto.
  eapply Mem.unchanged_on_implies; eauto. ii. ss. esplits; eauto.
Qed.

Lemma sepconj_isolated_mutation1
      m0 m1 P Q
      (SEP: m0 |= P ** Q)
      (UNCH: Mem.unchanged_on (~2 P.(m_footprint)) m0 m1)
  :
    <<SEP: m1 |= Q>>.
Proof.
  eapply sepconj_isolated_mutation0; eauto.
  eapply Mem.unchanged_on_implies; eauto. ii. des; ss.
Qed.

Lemma sepconj_isolated_mutation_strong
      m0 m1 P0 P1 Q
      (SEP: m0 |= P0)
      (UNCH: Mem.unchanged_on Q m0 m1)
      (IMP: massert_imp P0 P1)
      (FOOT: P1.(m_footprint) <2= Q)
  :
    <<SEP: m1 |= P1>>.
Proof.
  hnf in IMP. des.
  eapply m_invar; eauto.
  eapply Mem.unchanged_on_implies; eauto.
Qed.

Lemma sepconj_isolated_mutation_stronger
      m0 m1 P0 P1 CTX CHNG
      (SEP: m0 |= P0 ** CTX)
      (UNCH: Mem.unchanged_on (~2 CHNG) m0 m1)
      (IMP: massert_imp P0 P1)
      (ISOL0: CHNG <2= P0.(m_footprint))
      (ISOL1: P1.(m_footprint) <2= ~2 CHNG)
  :
    <<SEP: m1 |= P1 ** CTX>>.
Proof.
  destruct SEP as (A & B & C).
  hnf in IMP. des.
  sep_split; eauto.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. eapply ISOL1; eauto.
  - ii. eapply C; eauto.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. apply ISOL0 in H1. eauto.
Qed.

Lemma globalenv_inject_incr_strong
      j j' m_src m_tgt0 m_tgt1 F V (ge: Genv.t F V)
      (INCR: inject_incr j j')
      (INJ: inject_separated j j' m_src m_tgt0)
      (SEP: m_tgt0 |= globalenv_inject ge j)
      (MLE: (m_tgt0.(Mem.nextblock) <= m_tgt1.(Mem.nextblock))%positive)
  :
    <<SEP: m_tgt1 |= globalenv_inject ge j'>>.
Proof.
  assert(m_tgt0 |= globalenv_inject ge j').
  { ss. des. esplits; eauto. inv SEP0. econs; eauto. ii. eapply IMAGE; eauto.
    rr in INJ. destruct (j b1) eqn:T.
    - destruct p; ss. exploit INCR; eauto. i; clarify.
    - exploit INJ; eauto. i; des. exfalso.
      eapply H2. r. eapply Plt_Ple_trans; eauto.
  }
  eapply m_invar; eauto.
  ss.
Qed.

Lemma disjoint_footprint_sep
      A WALL B
      (DISJ0: A.(m_footprint) <2= WALL)
      (DISJ1: B.(m_footprint) <2= ~2 WALL)
  :
    <<DISJ: disjoint_footprint A B>>.
Proof.
  ii. apply DISJ0 in H. apply DISJ1 in H0. ss.
Qed.

Program Definition freed_range (b: block) (lo hi: Z): massert := {|
  m_pred := fun m =>
              <<RANGE: 0 <= lo /\ hi <= Ptrofs.modulus>> /\ <<VALID: lo < hi -> (Mem.valid_block m) b>>
  ;
  m_footprint := brange b lo hi
  ;
|}.
Next Obligation. des. esplits; eauto. i. eapply Mem.valid_block_unchanged_on; eauto. Qed.
Next Obligation. hnf in H0. des; clarify. eapply H1. lia. Qed.

Hint Unfold freed_range.

Lemma add_pure_r
      m P
  :
    <<SEP: m |= P>> <-> <<SEP: m |= P ** pure True>>.
Proof. split; ii. - sep_split; ss. - destruct H. ss. Qed.

Lemma range_split0
      b lo mid hi
      (RANEG: lo <= mid <= hi)
  :
    massert_imp (range b lo hi) (range b lo mid ** range b mid hi).
Proof.
  econs; ii.
  - apply add_pure_r. apply add_pure_r in H. r. rewrite sep_assoc. eapply range_split; eauto.
  - ss. des; esplits; eauto; try lia.
Qed.

Lemma range_freed_range
      sp lo hi
  :
    massert_imp (range sp lo hi) (freed_range sp lo hi).
Proof.
  econs; ii; ss.
  des; esplits; eauto. i. specialize (H1 lo).
  exploit H1; eauto with mem lia.
Unshelve.
  all: econs.
Qed.

Lemma add_pure_r_eq
      P
  :
    P = P ** pure True.
Proof.
  destruct P; ss. unfold sepconj. ss.
  eapply massert_eq.
  - apply functional_extensionality. ii; ss.
    apply prop_ext. split; ii; des; esplits; ss.
  - repeat (apply functional_extensionality; ii; ss).
    apply prop_ext. split; ii; des; ss; eauto.
Qed.

Lemma mconj_distr
      m P Q CTX
  :
    <<SEP: m |= (mconj P Q) ** CTX>> <-> <<SEP: m |= P ** CTX>> /\ <<SEP: m |= Q ** CTX>>.
Proof.
  split; ii.
  - destruct H as (A & B & C). ss. des. sym in C. apply disjoint_footprint_mconj in C. des.
    esplits; eauto.
    + sym; ss.
    + sym; ss.
  - des. destruct SEP. destruct SEP0. des.
    sep_split; ss.
    sym. apply disjoint_footprint_mconj. esplits; eauto.
    + sym; ss.
    + sym; ss.
Qed.

Lemma range_nonnil_valid_block
      m b lo hi
      (SEP: m |= range b lo hi)
      (RANGE: lo < hi)
  :
    <<VALID: (Mem.valid_block m) b>>.
Proof.
  ss. des. specialize (SEP1 lo). exploit SEP1; eauto. { lia. } i. eapply Mem.perm_valid_block; eauto.
Unshelve.
  all: econs.
Qed.

Lemma sepconj_isolated_mutation_strongest
      m0 m1 P P0 P1 CTX CHNG
      (SEP: m0 |= P ** CTX)
      (UNCH: Mem.unchanged_on (~2 CHNG) m0 m1)
      (IMP: massert_imp P P1)
      (PRED: m1 |= P0)
      (ISOL: CHNG <2= P.(m_footprint))
      (ISOL0: P0.(m_footprint) <2= CHNG)
      (ISOL1: P1.(m_footprint) <2= ~2 CHNG)
      (DISJ: disjoint_footprint P0 P1)
  :
    <<SEP: m1 |= P0 ** P1 ** CTX>>.
Proof.
  destruct SEP as (A & B & C).
  hnf in IMP. des.
  sep_split; eauto.
  { apply disjoint_footprint_sepconj. split; ss. ii. eapply C; eauto. }
  sep_split.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. eapply ISOL1; eauto.
  - ii. eapply C; eauto.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. apply ISOL in H1. eauto.
Qed.

Lemma sepconj_isolated_mutation_revisited
      m0 m1 P0 P1 CTX CHNG
      (SEP: m0 |= P0 ** CTX)
      (UNCH: Mem.unchanged_on (~2 CHNG) m0 m1)
      (ISOL: CHNG <2= P0.(m_footprint))
      (PRED: m1 |= P1)
      (FOOT: P1.(m_footprint) <2= P0.(m_footprint))
  :
    <<SEP: m1 |= P1 ** CTX>>.
Proof.
  destruct SEP as (A & B & C).
  sep_split; eauto.
  { ii. et. }
  eapply m_invar; et.
  eapply Mem.unchanged_on_implies; eauto.
  ii. eapply ISOL in H1. rr in C. et.
Qed.

Lemma mconj_footprint_le
      A0 B0 A1 B1
      (LEA: A0.(m_footprint) <2= A1.(m_footprint))
      (LEB: B0.(m_footprint) <2= B1.(m_footprint))
  :
    (mconj A0 B0).(m_footprint) <2= (mconj A1 B1).(m_footprint).
Proof.
  ss. ii. des; et.
Qed.

Lemma sepconj_footprint_le
      A0 B0 A1 B1
      (LEA: A0.(m_footprint) <2= A1.(m_footprint))
      (LEB: B0.(m_footprint) <2= B1.(m_footprint))
  :
    (sepconj A0 B0).(m_footprint) <2= (sepconj A1 B1).(m_footprint).
Proof.
Local Transparent sepconj.
  ss. ii. des; et.
Local Opaque sepconj.
Qed.

Local Transparent sepconj.
Lemma m_footprint_sepconj_le
      P0 Q0 P1 Q1
      (LEP: P0.(m_footprint) <2= P1.(m_footprint))
      (LEQ: Q0.(m_footprint) <2= Q1.(m_footprint))
  :
    <<LE: (P0 ** Q0).(m_footprint) <2= (P1 ** Q1).(m_footprint)>>.
Proof. ii; ss. des; ss; eauto. Qed.

Lemma sep_assoc_footprint
      P Q R
  :
    ((P ** Q) ** R).(m_footprint) =
    (P ** Q ** R).(m_footprint).
Proof.
  ss.
  apply func_ext2. ii; ss. apply prop_ext.
  split; ii; ss; des; et.
Qed.

Lemma unfree_freed_range
      sp m0 m1 lo mid hi
      (SEP: m0 |= freed_range sp lo mid ** range sp mid hi)
      (UNFREE: Mem_unfree m0 sp lo mid = Some m1):
    <<SEP: m1 |= range sp lo hi>>.
Proof.
  ss. des. esplits; et. ii.
  hexploit Mem_unfree_unchanged_on; et. intro UNCH; des.
  destruct (classic (i < mid)).
  - eapply Mem_unfree_perm; et.
  - eapply Mem.perm_unchanged_on; et.
    + u. ii. des. extlia.
    + eapply SEP3; et. extlia.
Qed.

Local Opaque sepconj.

Lemma assign_junk_blocks_rule
      P m_src0
      (PRED: m_src0 |= P)
      n
  :
    (assign_junk_blocks m_src0 n) |= P.
Proof.
  destruct P; ss.
  eapply m_invar; eauto.
  eapply Mem.unchanged_on_implies.
  { eapply assign_junk_blocks_unchanged_on; eauto. }
  ss.
Qed.

