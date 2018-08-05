Require Import Setoid Program.Basics.
Require Import CoqlibC Decidableplus.
Require Import AST Integers Values Memory Events Globalenvs.
(** newly added **)
Require Import AxiomsC.
Require Export Separation.

Local Open Scope sep_scope.


Ltac sep_split := econs; [|split]; swap 2 3.


Section INJ.

Context `{Val.meminj_ctx}.

Lemma separation_private
      m_src m_tgt F P
      (MATCH: m_tgt |= P ** minjection F m_src)
  :
     P.(m_footprint) <2= loc_out_of_reach F m_src
.
Proof.
  inv MATCH. des; ss.
  ii. unfold disjoint_footprint in *. ss.
  eapply H2; eauto.
Qed.

End INJ.

Lemma disjoint_footprint_drop_empty
      P Q0 Q1
      (EMPTY: Q0.(m_footprint) <2= bot2)
      (DISJ: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (Q0 ** Q1)>>
.
Proof.
  ii. ss. unfold disjoint_footprint in *. des; eauto.
  eapply EMPTY; eauto.
Qed.

Lemma disjoint_footprint_mconj
      P Q0 Q1
      (DISJ0: disjoint_footprint P Q0)
      (DISJ1: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (mconj Q0 Q1)>>
.
Proof.
  ii. ss. unfold disjoint_footprint in *. des; eauto.
Qed.

Lemma disjoint_footprint_sepconj
      P Q0 Q1
  :
    (<<DISJ0: disjoint_footprint P Q0>>) /\ (<<DISJ1: disjoint_footprint P Q1>>)
    <->
    (<<DISJ: disjoint_footprint P (Q0 ** Q1)>>)
.
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
    Build_massert pred0 footprint0 INVAR0 VALID0 = Build_massert pred1 footprint1 INVAR1 VALID1
.
Proof.
  clarify.
  f_equal.
  apply Axioms.proof_irr.
  apply Axioms.proof_irr.
Qed.

Lemma mconj_sym
      P Q
  :
    <<EQ: (mconj P Q) = (mconj Q P)>>
.
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

Local Transparent sepconj.

Lemma sep_drop_tail3
      P Q R
  :
    massert_imp (P ** Q ** R) (P ** Q)
.
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
    <<SEP: m1 |= Q>>
.
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
    <<SEP: m1 |= Q>>
.
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
    <<SEP: m1 |= P1>>
.
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
    <<SEP: m1 |= P1 ** CTX>>
.
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

