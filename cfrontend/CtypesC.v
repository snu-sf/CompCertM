Require Import Axioms CoqlibC Maps Errors.
Require Import AST Linking.
Require Archi.

Require Export Ctypes.

Set Implicit Arguments.

Definition fundef_of_fundef F (f: fundef F): AST.fundef F :=
  match f with
  | Internal f => AST.Internal f
  | External ef _ _ _ => AST.External ef
  end
.

Coercion fundef_of_fundef: fundef >-> AST.fundef.
