(** Generated from Clightgen, then trimed **)
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _f : ident := 57%positive.
Definition _g : ident := 55%positive.
Definition _in : ident := 53%positive.
Definition _main : ident := 58%positive.
Definition _out : ident := 54%positive.
Definition _x : ident := 56%positive.
Definition _t'1 : ident := 59%positive.

Definition v_in := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_out := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_f := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _x tint) (Evar _in tint) tint)
    (Ssequence
      (Sassign (Evar _in tint) (Etempvar _x tint))
      (Sassign (Evar _out tint)
        (Ebinop Omul (Etempvar _x tint) (Etempvar _x tint) tint)))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _g (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Evar _out tint) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_in, Gvar v_in) :: (_out, Gvar v_out) ::
 (_g,
   Gfun(External (EF_external "g"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) :: (_f, Gfun(Internal f_f)) :: nil).

Definition public_idents : list ident :=
(_f :: _g :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


