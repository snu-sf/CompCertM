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
      `{Val.meminj_ctx}
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
      `{Val.meminj_ctx}
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
      `{Val.meminj_ctx}
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
    (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
.
