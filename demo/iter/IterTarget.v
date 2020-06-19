From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _fptr : ident := 53%positive.
Definition _iter : ident := 56%positive.
Definition _main : ident := 57%positive.
Definition _n : ident := 54%positive.
Definition _x : ident := 55%positive.
Definition _t'1 : ident := 58%positive.
Definition _t'2 : ident := 59%positive.

Definition f_iter := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_fptr, (tptr (Tfunction (Tcons tint Tnil) tint cc_default))) ::
                (_n, tint) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Etempvar _x tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Etempvar _fptr (tptr (Tfunction (Tcons tint Tnil) tint cc_default)))
        ((Etempvar _x tint) :: nil))
      (Scall (Some _t'2)
        (Evar _iter (Tfunction
                      (Tcons
                        (tptr (Tfunction (Tcons tint Tnil) tint cc_default))
                        (Tcons tint (Tcons tint Tnil))) tint cc_default))
        ((Etempvar _fptr (tptr (Tfunction (Tcons tint Tnil) tint cc_default))) ::
         (Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint) tint) ::
         (Etempvar _t'1 tint) :: nil)))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_iter, Gfun(Internal f_iter)) :: nil).

Definition public_idents : list ident :=
(_iter :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.

Require Import Mod ClightC.

Definition module: Mod.t := module2_mi prog (Some "iter"%string).
