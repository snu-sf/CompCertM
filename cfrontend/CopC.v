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
  end.

Inductive typecheck (vs: list val) (tys: typelist): Prop :=
| typecheck_intro
    (TYP: Forall2 (val_casted) vs (typelist_to_listtype tys))
    (NVOID: Forall (fun ty => ty <> Tvoid) (typelist_to_listtype tys))
    (SZ: 4 * Conventions1.size_arguments_64 (typlist_of_typelist tys) 0 0 0 <= Ptrofs.max_unsigned).

Lemma val_casted_has_type
      v ty
      (WT: val_casted v ty)
      (NVOID: ty <> Tvoid):
    Val.has_type v ty.(typ_of_type).
Proof. inv WT; ss. Qed.

Lemma val_casted_has_type_list
      vs tys
      (WT: Forall2 val_casted vs (typelist_to_listtype tys))
      (NVOID: Forall (fun ty => ty <> Tvoid) (typelist_to_listtype tys)):
    Val.has_type_list vs (typlist_of_typelist tys).
Proof.
  ginduction vs; destruct tys; ii; ss; inv WT; inv NVOID; ii; ss.
  esplits; eauto.
  eapply val_casted_has_type; eauto.
Qed.

Lemma typlist_of_typelist_eq: forall itys,
    typlist_of_typelist (type_of_params itys) = (map typ_of_type (map snd itys)).
Proof. i. ginduction itys; ii; ss; des_ifs; ss. f_equal. ss. Qed.

Lemma typelist_to_listtype_length: forall itys,
    length (typelist_to_listtype (type_of_params itys)) = length (map typ_of_type (map snd itys)).
Proof. i. ginduction itys; ii; ss; des_ifs; ss. xomega. Qed.


