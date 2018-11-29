Require Import CoqlibC.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes.
Require Archi.
(** newly added **)
Require Export Cop.
Require Import sflib.
Require Conventions1.



Fixpoint typelist_to_listtype (tys: typelist): list type :=
  match tys with
  | Tnil => []
  | Tcons hd tl => hd :: typelist_to_listtype tl
  end
.

Inductive typecheck (vs: list val) (tys: typelist): Prop :=
| typecheck_intro
    (TYP: Forall2 (val_casted) vs (typelist_to_listtype tys))
    (NVOID: Forall (fun ty => ty <> Tvoid) (typelist_to_listtype tys))
    (SZ: 4 * Conventions1.size_arguments_64 (typlist_of_typelist tys) 0 0 0 <= Ptrofs.max_unsigned)
.

Lemma val_casted_has_type
      v ty
      (WT: val_casted v ty)
      (NVOID: ty <> Tvoid)
  :
    Val.has_type v ty.(typ_of_type)
.
Proof.
  inv WT; ss.
Qed.

