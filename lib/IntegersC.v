Require Import Eqdep_dec Zquot Zwf.
Require Import CoqlibC.
Require Archi.
(** newly added **)
Require Export Integers.

Lemma Ptrofs_add_repr: forall x y,
    <<EQ: (Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y)) = Ptrofs.repr (x + y)>>.
Proof.
  i. apply Ptrofs.eqm_repr_eq. eapply Ptrofs.eqm_sym. eapply Ptrofs.eqm_trans.
  - apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr.
  - apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma max_unsigned_zero: 0 <= Ptrofs.max_unsigned.
Proof.
  etransitivity; try unshelve apply Ptrofs.unsigned_range_2. apply Ptrofs.zero.
Qed.

Lemma mul_le_div
      a b
      (LE: 4 * a <= b):
    <<LE: a <= b / 4>>.
Proof.
  red.
  assert(4 * a / 4 = a).
  { rewrite Z.mul_comm. rewrite Z.div_mul; ss. }
  rewrite <- H. eapply Z_div_le; eauto. xomega.
Qed.

Lemma Z2Nat_range n:
  Z.of_nat (Z.to_nat n) = if (zle 0 n) then n else 0.
Proof. destruct n; ss; try nia. Qed.

Hint Rewrite Ptrofs.unsigned_zero Ptrofs.add_zero Ptrofs.add_zero_l
     Ptrofs.repr_unsigned Ptrofs_add_repr : psimpl.

Ltac psimpl := repeat (autorewrite with psimpl in *;
                       try (rewrite Ptrofs.unsigned_repr in *; ss; try xomega; [])).
