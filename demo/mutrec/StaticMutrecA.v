From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import StaticMutrecHeader.

Local Open Scope Z_scope.

Definition _x : ident := 55%positive.
Definition _t'1 : ident := 58%positive.

Definition v_memoized := {|
  gvar_info := (tarray tint 10);
  gvar_init := (Init_int32 (Int.repr (-1)) :: Init_int32 (Int.repr (-1)) ::
                Init_int32 (Int.repr (-1)) :: Init_int32 (Int.repr (-1)) ::
                Init_int32 (Int.repr (-1)) :: Init_int32 (Int.repr (-1)) ::
                Init_int32 (Int.repr (-1)) :: Init_int32 (Int.repr (-1)) ::
                Init_int32 (Int.repr (-1)) :: Init_int32 (Int.repr (-1)) ::
                nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition func_f := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _x tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Olt
                   (Ederef
                     (Ebinop Oadd (Evar _memoized (tarray tint 10))
                       (Etempvar _x tint) (tptr tint)) tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _g (Tfunction (Tcons tint Tnil) tint cc_default))
          ((Ebinop Osub (Etempvar _x tint) (Econst_int (Int.repr 1) tint)
             tint) :: nil))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _memoized (tarray tint 10)) (Etempvar _x tint)
              (tptr tint)) tint)
          (Ebinop Osub
            (Ebinop Oadd (Etempvar _t'1 tint) (Etempvar _x tint) tint)
            (Econst_int (Int.repr 1) tint) tint)))
      Sskip)
    (Sreturn (Some (Ederef
                     (Ebinop Oadd (Evar _memoized (tarray tint 10))
                       (Etempvar _x tint) (tptr tint)) tint)))))
|}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((g_id,
   Gfun(External (EF_external "g"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) :: (_memoized, Gvar v_memoized) ::
 (f_id, Gfun(Internal func_f)) :: nil).

Definition public_idents : list ident :=
(f_id :: g_id :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents main_id Logic.I.


