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

Set Implicit Arguments.


Definition is_ptr (v: val): bool :=
  match v with
  | Vptr _ _ _ => true
  | _ => false
  end
.

Hint Unfold is_ptr.

Definition is_real_ptr (v: val): bool :=
  match v with
  | Vptr _ _ true => true
  | _ => false
  end
.
Hint Unfold is_real_ptr.

Definition is_fake_ptr (v: val): bool :=
  match v with
  | Vptr _ _ false => true
  | _ => false
  end
.
Hint Unfold is_fake_ptr.

Definition to_fake (v: val): val :=
  match v with
  | Vptr blk ofs true => Vptr blk ofs false
  | _ => v
  end
.


(* Definition is_real_fptr (v: val): bool := *)
(*   match v with *)
(*   | Vptr _ ofs true => if (Ptrofs.eq ofs Ptrofs.zero) then true else false *)
(*   | _ => false *)
(*   end *)
(* . *)
(* Hint Unfold is_real_fptr. *)

Definition fake_ptr_one: val := Vptr 1%positive Ptrofs.zero false.

Section INJECTNORMAL.

Local Existing Instance Val.mi_normal.

Lemma fakeptr_inject_id
      F fptr
      (FAKE: ~ is_real_ptr fptr)
  :
    <<INJECT: Val.inject F fptr fptr>>
.
Proof. destruct fptr; ss. des_ifs. econs; eauto. Qed.

End INJECTNORMAL.

Global Program Instance inject_incr_PreOrder: PreOrder inject_incr.
Next Obligation.
  ii. eapply inject_incr_trans; eauto.
Qed.



(* Fixpoint zip X Y Z (f: option X -> option Y -> Z) (xs: list X) (ys: list Y): list Z := *)
(*   match xs, ys with *)
(*   | [], [] => [] *)
(*   | xhd :: xtl, [] => f (Some xhd) None :: zip f xtl [] *)
(*   | [], yhd :: ytl => f None (Some yhd) :: zip f [] ytl *)
(*   | xhd :: xtl, yhd :: ytl => f (Some xhd) (Some yhd) :: zip f xtl ytl *)
(*   end *)
(* . *)

Fixpoint zip X Y Z (f: X -> Y -> Z) (xs: list X) (ys: list Y): list Z :=
  match xs, ys with
  | xhd :: xtl, yhd :: ytl => f xhd yhd :: zip f xtl ytl
  | _, _ => []
  end
.

Lemma zip_length
      X Y Z (f: X -> Y -> Z) xs ys
  :
    length (zip f xs ys) = min xs.(length) ys.(length)
.
Proof.
  ginduction xs; ii; ss.
  des_ifs.
  ss. rewrite IHxs. xomega.
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

End TYPIFY.

Hint Unfold typify typify_list.
(* Hint Unfold typify_. *)

