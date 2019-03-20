Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Smallstep.
Require Import Csem.
Require Import sflib.
Require Import CsemC Mod.
Require Import Header.

Definition x : ident := 53%positive.

Definition code: statement := (Sreturn (Some (Evar x (Tlong Unsigned noattr)))).
Program Definition func: function := {|
  fn_return := Tfloat F32 noattr;
  fn_callconv := cc_default;
  fn_params := ((x, Tlong Unsigned noattr) :: nil);
  fn_vars := nil;
  fn_body := code;
|}.

Program Definition prog: program :=
  @Build_program function [(func_id, (Gfun (Internal func)))] [func_id ; main_id] main_id [] (@PTree.empty _) _.

Definition md: Mod.t := module prog.

Hint Unfold md prog func code.