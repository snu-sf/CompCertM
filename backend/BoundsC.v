(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Computation of resource bounds for Linear code. *)

Require Import FSets FSetAVL.
Require Import CoqlibC Ordered.
Require Intv.
Require Import ASTC.
Require Import Op.
Require Import Machregs Locations.
Require Import LinearC.
Require Import Conventions.

(** newly added **)
Require Export Bounds.


Section BOUNDS.

Variable sg: signature.
Let f := (dummy_function sg).

Compute (RegSet.elements (record_regs_of_function f)).
Compute (max_over_slots_of_funct f local_slot).
Compute (max_over_slots_of_funct f outgoing_slot).
Compute (f.(fn_stacksize)).

Lemma function_bounds_dummy_spec
  :
    (<<CALLEESAVE: f.(function_bounds).(used_callee_save) = []>>)
    /\
    (<<LOCAL: f.(function_bounds).(bound_local) = 0>>)
    /\
    (<<OUTGOING: f.(function_bounds).(bound_outgoing) = size_arguments sg>>)
    /\
    (<<STACKDATA: f.(function_bounds).(bound_stack_data) = 0>>)
.
Proof.
  subst f.
  cbn.
  esplits; eauto.
  generalize (size_arguments_above sg). i. xomega.
Qed.

End BOUNDS.


