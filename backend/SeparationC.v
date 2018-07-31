Require Import Setoid Program.Basics.
Require Import CoqlibC Decidableplus.
Require Import AST Integers Values Memory Events Globalenvs.
(** newly added **)
Require Import AxiomsC.
Require Export Separation.

Local Open Scope sep_scope.




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

