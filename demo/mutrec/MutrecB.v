Require Import List ZArith.
Require Import CoqlibC Integers Floats AST Cop Asm.
Require Import MutrecHeader.

Set Implicit Arguments.

Local Open Scope Z_scope.

Definition func_g: function := (admit "").

Definition global_definitions : list (ident * globdef fundef unit) :=
((f_id,
   Gfun(External (EF_external "f"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))))
   :: (g_id, Gfun(Internal func_g)) :: nil).

Definition public_idents : list ident :=
(f_id :: g_id :: nil).

Definition prog : Asm.program := 
  mkprogram global_definitions public_idents main_id.


