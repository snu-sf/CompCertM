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

