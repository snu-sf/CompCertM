From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Mod ClightC CoqlibC.
Local Open Scope Z_scope.

Definition _get : ident := 54%positive.
Definition _incr : ident := 55%positive.
Definition _main : ident := 56%positive.
Definition _x : ident := 53%positive.

Definition v_x := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
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
(Sifthenelse (Ebinop Oge (Evar _x tint) (Econst_int (Int.repr 0) tint) tint)
  (Sreturn (Some (Evar _x tint)))
  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_incr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign (Evar _x tint)
  (Ebinop Omod
    (Ebinop Oadd (Evar _x tint) (Econst_int (Int.repr 1) tint) tint)
    (Econst_int (Int.repr 10) tint) tint))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
(
 (_x, Gvar v_x) :: (_get, Gfun(Internal f_get)) ::
 (_incr, Gfun(Internal f_incr)) :: nil
).

Definition public_idents : list ident :=
(_incr :: _get :: nil).

Definition prog : Clight.program :=
  mkprogram composites global_definitions public_idents _main Logic.I.

Definition module: Mod.t := module2_mi prog (Some "SV").
