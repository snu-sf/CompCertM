(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import CoqlibC.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import sflib.
(** newly added **)
Require Export Values.
Require Import Conventions1.

Set Implicit Arguments.


Global Program Instance inject_incr_PreOrder: PreOrder inject_incr.
Next Obligation.
  ii. eapply inject_incr_trans; eauto.
Qed.



(* From stdpp Require Import list. *)
Section TYPIFY.

  Lemma Val_has_type_dec
        v ty
  :
    {Val.has_type v ty} + {~ Val.has_type v ty}
  .
  Proof.
    destruct v, ty; ss; eauto.
  Qed.

  Definition typify (v: val) (ty: typ): val :=
    if Val_has_type_dec v ty
    then v
    else Vundef
  .

  (* Definition typify' (v: val) (ty: option typ): val := *)
  (*   match ty with *)
  (*   | None => Vundef *)
  (*   | Some ty => typify v ty *)
  (*   end *)
  (* . *)

  Lemma typify_has_type
        v ty
    :
      <<TYP: Val.has_type (typify v ty) ty>>
  .
  Proof.
    unfold typify. des_ifs.
  Qed.

  Definition typify_list (vs: list val) (tys: list typ): list val :=
    zip typify vs tys
  .

  (* Definition typify_list (vs: list val) (tys: list typ): option (list val) := *)
  (*   if Nat.eqb vs.(length) tys.(length) *)
  (*   then Some (zip typify vs tys) *)
  (*   else None *)
  (* . *)

  (* Definition typify_opt (v: val) (ty: option typ): val := *)
  (*   match ty with *)
  (*   | None => v *)
  (*   | Some ty => typify v ty *)
  (*   end *)
  (* . *)

  Lemma typify_list_length
        vs tys
    :
      length (typify_list vs tys) = Nat.min (length vs) (length tys)
  .
  Proof.
    ginduction vs; ii; ss. destruct tys; ss. rewrite IHvs; ss.
  Qed.

End TYPIFY.

Hint Unfold typify typify_list.
(* Hint Unfold typify_. *)

Lemma lessdef_typify
      x y ty
      (LD: Val.lessdef x y)
  :
    <<LD: Val.lessdef (typify x ty) (typify y ty)>>
.
Proof.
  unfold typify. des_ifs.
  inv LD; ss.
Qed.

Lemma inject_typify
      j x y ty
      (INJ: Val.inject j x y)
  :
    <<INJ: Val.inject j (typify x ty) (typify y ty)>>
.
Proof.
  unfold typify. des_ifs.
  inv INJ; ss.
Qed.

Lemma lessdef_list_typify_list
      xs ys tys
      (LEN: length tys = length xs)
      (LD: Val.lessdef_list xs ys)
  :
    <<LD: Val.lessdef_list (typify_list xs tys) (typify_list ys tys)>>
.
Proof.
  ginduction LD; ii; ss.
  unfold typify_list. ss. des_ifs. ss.
  econs; eauto.
  - eapply lessdef_typify; eauto.
  - eapply IHLD; eauto.
Qed.

(* Lemma lessdef_typify_opt *)
(*       x y ty *)
(*       (LD: Val.lessdef x y) *)
(*   : *)
(*     <<LD: Val.lessdef (typify_opt x ty) (typify_opt y ty)>> *)
(* . *)
(* Proof. *)
(*   unfold typify_opt. des_ifs. eapply lessdef_typify; ss. *)
(* Qed. *)

(* Lemma inject_typify_opt *)
(*       `{Val.meminj_ctx} *)
(*       j x y ty *)
(*       (INJ: Val.inject j x y) *)
(*   : *)
(*     <<INJ: Val.inject j (typify_opt x ty) (typify_opt y ty)>> *)
(* . *)
(* Proof. *)
(*   unfold typify_opt. des_ifs. eapply inject_typify; ss. *)
(* Qed. *)



Lemma lessdef_list_length
      xs ys
      (LD: Val.lessdef_list xs ys)
  :
    <<LEN: xs.(length) = ys.(length)>>
.
Proof.
  ginduction LD; ii; ss.
  des. red. xomega.
Qed.

Lemma inject_list_typify_list
      inj xs ys tys
      (LEN: length tys = length xs)
      (LD: Val.inject_list inj xs ys)
  :
    <<LD: Val.inject_list inj (typify_list xs tys) (typify_list ys tys)>>
.
Proof.
  ginduction LD; ii; ss.
  unfold typify_list. ss. des_ifs. ss.
  econs; eauto.
  - eapply inject_typify; eauto.
  - eapply IHLD; eauto.
Qed.

Lemma inject_list_length
      j xs ys
      (INJ: Val.inject_list j xs ys)
  :
    <<LEN: xs.(length) = ys.(length)>>
.
Proof.
  ginduction INJ; ii; ss.
  des. red. xomega.
Qed.

Lemma typify_has_type_list
      vs tys
      (LEN: length vs = length tys)
  :
    <<TYS: Val.has_type_list (typify_list vs tys) tys>>
.
Proof.
  ginduction vs; ii; ss.
  { des_ifs. }
  destruct tys; ss.
  clarify.
  esplits; eauto.
  - eapply typify_has_type.
  - eapply IHvs; eauto.
Qed.


Lemma has_type_typify
      v ty
      (TY: Val.has_type v ty)
  :
    <<TY: (typify v ty) = v>>
.
Proof.
  rr. unfold typify. des_ifs.
Qed.

Lemma has_type_list_typify
      vs tys
      (TYS: Val.has_type_list vs tys)
  :
    <<TYS: (typify_list vs tys) = vs>>
.
Proof.
  ginduction vs; ii; ss.
  destruct tys; ss.
  des. unfold typify_list. ss. r. f_equal.
  - eapply has_type_typify; et.
  - eapply IHvs; et.
Qed.

Inductive typecheck (vs: list val) (sg: signature) (tvs: list val): Prop :=
| typecheck_intro
    (LEN: length vs = length sg.(sig_args))
    (TYP: typify_list vs sg.(sig_args) = tvs)
    (* (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
.

Lemma Val_hiword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.hiword (Val.longofwords vhi vlo)) = vhi>>
.
Proof.
  u.
  unfold Val.longofwords, Val.hiword. des_ifs; ss; eauto.
  rewrite Int64.hi_ofwords. ss.
Qed.

Lemma Val_loword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.loword (Val.longofwords vhi vlo)) = vlo>>
.
Proof.
  u.
  unfold Val.longofwords, Val.loword. des_ifs; ss; eauto.
  rewrite Int64.lo_ofwords. ss.
Qed.
