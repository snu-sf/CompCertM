Require Import Eqdep_dec Zquot Zwf.
Require Import CoqlibC.
Require Archi.
(** newly added **)
Require Export Integers.

Lemma Ptrofs_add_repr
      x y
  :
    <<EQ: (Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y)) = Ptrofs.repr (x + y)>>
.
Proof.
  apply Ptrofs.eqm_repr_eq.
  eapply Ptrofs.eqm_sym.
  eapply Ptrofs.eqm_trans.
  - apply Ptrofs.eqm_sym. apply Ptrofs.eqm_unsigned_repr.
  - apply Ptrofs.eqm_add.
    + apply Ptrofs.eqm_unsigned_repr.
    + apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma max_unsigned_zero
  :
    0 <= Ptrofs.max_unsigned
.
Proof.
  etransitivity; try unshelve apply Ptrofs.unsigned_range_2.
  apply Ptrofs.zero.
Qed.


Hint Rewrite Ptrofs.unsigned_zero Ptrofs.add_zero Ptrofs.add_zero_l
     Ptrofs.repr_unsigned Ptrofs_add_repr : psimpl
.

Ltac psimpl := repeat (autorewrite with psimpl in *;
                       try (rewrite Ptrofs.unsigned_repr in *; ss; try xomega; []))
.
