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

