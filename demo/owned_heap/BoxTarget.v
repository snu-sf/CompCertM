From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "Box.c"%string.
  Definition normalized := false.
End Info.

Definition _delete : ident := 60%positive.
Definition _free : ident := 53%positive.
Definition _from_raw : ident := 62%positive.
Definition _get : ident := 57%positive.
Definition _into_raw : ident := 63%positive.
Definition _key : ident := 55%positive.
Definition _main : ident := 64%positive.
Definition _malloc : ident := 52%positive.
Definition _new : ident := 56%positive.
Definition _ptr : ident := 61%positive.
Definition _set : ident := 59%positive.
Definition _v : ident := 54%positive.
Definition _val : ident := 58%positive.
Definition _t'1 : ident := 65%positive.

Definition f_new := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_v, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_key, (tptr tint)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof tint tulong) :: nil))
    (Sset _key (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign (Ederef (Etempvar _key (tptr tint)) tint) (Etempvar _v tint))
    (Sreturn (Some (Etempvar _key (tptr tint))))))
|}.

Definition f_get := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef (Ecast (Etempvar _key (tptr tvoid)) (tptr tint)) tint)))
|}.

Definition f_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tvoid)) :: (_val, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign (Ederef (Ecast (Etempvar _key (tptr tvoid)) (tptr tint)) tint)
  (Etempvar _val tint))
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _key (tptr tvoid)) :: nil))
|}.

Definition f_from_raw := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _ptr (tptr tvoid))))
|}.

Definition f_into_raw := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _key (tptr tvoid))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_new, Gfun(Internal f_new)) :: (_get, Gfun(Internal f_get)) ::
 (_set, Gfun(Internal f_set)) :: (_delete, Gfun(Internal f_delete)) ::
 (_from_raw, Gfun(Internal f_from_raw)) ::
 (_into_raw, Gfun(Internal f_into_raw)) :: nil).

Definition public_idents : list ident :=
(_into_raw :: _from_raw :: _delete :: _set :: _get :: _new :: _free :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.

Require Import Mod ClightC.

Definition module: Mod.t := module2_mi prog (Some "OHAlloc"%string).
