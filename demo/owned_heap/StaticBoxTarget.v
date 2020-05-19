From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition __val : ident := 54%positive.
Definition _get : ident := 53%positive.
Definition _main : ident := 56%positive.
Definition _set : ident := 55%positive.
Definition _val : ident := 52%positive.

Definition v_val := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Evar _val tint)))
|}.

Definition f_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__val, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign (Evar _val tint) (Etempvar __val tint))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_val, Gvar v_val) :: (_get, Gfun(Internal f_get)) ::
 (_set, Gfun(Internal f_set)) :: nil).

Definition public_idents : list ident :=
(_set :: _get :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


