Require Export AST.
Require Export Globalenvs.
Require Import Memory.

Set Implicit Arguments.


(* Skeleton Genv *)
Module SkEnv.

  Definition t := Genv.t (fundef (option signature)) unit.

End SkEnv.

(* Skeleton *)
Module Sk.

  Definition t := AST.program (fundef (option signature)) unit.

  Definition load_skenv: t -> SkEnv.t := @Genv.globalenv (fundef (option signature)) unit.
  (* No coercion! *)

  Definition load_mem: t -> option mem := @Genv.init_mem (fundef (option signature)) unit.
  (* No coercion! *)

End Sk.

