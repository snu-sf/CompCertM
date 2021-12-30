Require Import CoqlibC.
From compcertr Require Import
     AST
     Integers
     Floats
     Values
     Memory
     Ctypes.
From compcertr Require Archi.
(** newly added **)
From compcertr Require Export Cop.
From compcertr Require Import sflib.
From compcertr Require Conventions Conventions1.


Inductive typecheck (vs: list val) (tys: typelist): Prop :=
| typecheck_intro
    (TYP: Forall2 (val_casted) vs (typelist_to_listtype tys))
    (NVOID: Forall (fun ty => ty <> Tvoid) (typelist_to_listtype tys))
    (SZ: 4 * Conventions.size_arguments (signature_of_type tys Tvoid cc_default) <= Ptrofs.max_unsigned).

Lemma val_casted_has_type
      v ty
      (WT: val_casted v ty)
      (NVOID: ty <> Tvoid):
    Val.has_type v (typ_of_type ty).
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
Proof. i. ginduction itys; ii; ss; des_ifs; ss. extlia. Qed.
