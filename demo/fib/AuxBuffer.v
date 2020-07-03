Require Import CoqlibC Maps.
Require Import ASTC IntegersC ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
(* Require Import Clightdefs. *)

Set Implicit Arguments.




(*** nat ***)
Lemma succ_pred
      x y
  :
    <<SUCC: x = S y>> <-> <<PRED: (x - 1)%nat = y /\ (1 <= x)%nat>>
.
Proof.
  {
    split.
    - ginduction x; ii; des; ss. clarify. split; try xomega.
    - ginduction x; ii; des; clarify; ss; try xomega. f_equal. rewrite Nat.sub_0_r. ss.
  }
Qed.





(*** int ***)
Lemma eta
      i j
      (EQ: i.(Int.intval) = j.(Int.intval))
  :
    <<EQ: i = j>>
.
Proof.
  r. destruct i, j; ss. clarify. f_equal. eapply Axioms.proof_irr.
Qed.

Lemma Int_add_repr: forall x y,
    <<EQ: (Int.add (Int.repr x) (Int.repr y)) = Int.repr (x + y)>>.
Proof.
  i. apply Int.eqm_repr_eq. eapply Int.eqm_sym. eapply Int.eqm_trans.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_add; apply Int.eqm_unsigned_repr.
Qed.

Lemma Int_sub_repr: forall x y,
    <<EQ: (Int.sub (Int.repr x) (Int.repr y)) = Int.repr (x - y)>>.
Proof.
  i. apply Int.eqm_repr_eq. eapply Int.eqm_sym. eapply Int.eqm_trans.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_sub; apply Int.eqm_unsigned_repr.
Qed.







(*** nat && int ***)
Definition to_nat (i: int): nat := Z.to_nat (Int.signed i).
Definition of_nat (n: nat): int := Int.repr (Z.of_nat n).

Definition to_nat_opt (i: int): option nat :=
  if zle 0 (Int.signed i)
  then Some (Z.to_nat (Int.signed i))
  else None
.

Definition of_nat_opt (n: nat): option int :=
  if zlt (Z.of_nat n) Int.modulus
  then Some (Int.repr (Z.of_nat n))
  else None
.
Hint Unfold of_nat to_nat of_nat_opt to_nat_opt.

Lemma range_to_nat
      x
      (RANGE: Z.of_nat x <= Int.max_signed)
  :
    to_nat_opt (of_nat x) = Some x
.
Proof.
  { i. unfold to_nat_opt, of_nat.
    generalize Int.min_signed_neg; i.
    generalize (Int.signed_range (Int.repr (Z.of_nat x))); i.
    rewrite Int.signed_repr in *; try lia. des_ifs; try lia.
    rewrite Nat2Z.id; ss.
  }
Qed.




(*** option ***)
Definition option_rel A B (r: A -> B -> Prop): option A -> option B -> Prop :=
  fun oa ob =>
    match oa, ob with
    | Some a, Some b => <<REL: r a b>>
    | None, None => True
    | _, _ => False
    end
.
