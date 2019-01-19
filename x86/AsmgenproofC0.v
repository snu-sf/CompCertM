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

(** Correctness proof for Asm generation: machine-independent framework *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import MachC Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import sflib Asmgenproof0 Skeleton.

(** * Processor registers and register states *)

Section MATCH_STACK.

Variable ske: SkEnv.t.
Variable ge: Mach.genv.

Variable initial_parent_sp : val.
Hypothesis initial_parent_ptr : ValuesC.is_real_ptr (initial_parent_sp).
Variable initial_parent_ra : val.
Hypothesis initial_parent_ra_ptr : Val.has_type initial_parent_ra Tptr.
Hypothesis initial_parent_ra_fake : ~ ValuesC.is_real_ptr initial_parent_ra.

Inductive match_stack: list Mach.stackframe -> Prop :=
| match_stack_dummy
  :
    match_stack ((dummy_stack initial_parent_sp initial_parent_ra)::[])
| match_stack_cons: forall fb sp ra c s f tf tc,
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    transl_code_at_pc ge ra fb f c false tf tc ->
    ValuesC.is_real_ptr sp ->
    (* sp <> Vundef -> *)
    match_stack s ->
    (* forall (NOTVOL: not_volatile sp), *)
      match_stack (Stackframe fb sp ra c :: s).

Lemma parent_sp_ptr: forall s, match_stack s -> ValuesC.is_real_ptr (parent_sp s).
Proof.
  induction 1; auto.
Qed.

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof.
  intros s MATCH. apply parent_sp_ptr in MATCH.
  unfold ValuesC.is_real_ptr in MATCH. des_ifs; ss.
Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

End MATCH_STACK.
