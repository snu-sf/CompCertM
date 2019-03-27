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
Require Import Cminor.
Require Import sflib.
Require Import CminorC Mod.
Require Import DemoHeader.

Definition x : ident := 53%positive.
Definition code: stmt := (Sreturn (Some (Eunop Ofloatoflongu (Evar x)))).
Program Definition func: function := {|
  fn_sig := {| sig_args := [AST.Tlong]; sig_res := Some AST.Tfloat; sig_cc := cc_default |};
  fn_params := (x :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body := code;
|}.

Program Definition prog: program :=
  @mkprogram _ _ [(func_id, (Gfun (AST.Internal func)))] [func_id ; main_id] main_id.

Definition md: Mod.t := module prog.

Hint Unfold md prog func code.