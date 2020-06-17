From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _fib : ident := 56%positive.
Definition _main : ident := 57%positive.
Definition _n : ident := 53%positive.
Definition _y1 : ident := 54%positive.
Definition _y2 : ident := 55%positive.
Definition _t'1 : ident := 58%positive.
Definition _t'2 : ident := 59%positive.

Definition f_fib := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_y1, tint) :: (_y2, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _n tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _fib (Tfunction (Tcons tint Tnil) tint cc_default))
          ((Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 2) tint)
             tint) :: nil))
        (Sset _y1 (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _fib (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
               tint) :: nil))
          (Sset _y2 (Etempvar _t'2 tint)))
        (Sreturn (Some (Ebinop Oadd (Etempvar _y1 tint) (Etempvar _y2 tint)
                         tint)))))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_fib, Gfun(Internal f_fib)) :: nil).

Definition public_idents : list ident :=
(_fib :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.

Require Import Mod ClightC.

Definition module: Mod.t := module2_mi prog (Some "fib"%string).
