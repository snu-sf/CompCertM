Require Import CoqlibC.
Require Export Globalenvs.
Require Import Memory.
Require Import Ctypes.
Require Export AST.

Set Implicit Arguments.

(* I don't want it to be "AST.program"-dependent, because of Ctypes.program *)
(* TODO: In high level, prog_public can be dropped, as the data is already linked. Is it really so? *)
(* Definition flesh F V := list (ident * globdef F V)%type. *)

(* Skeleton Genv *)
Module SkEnv.

  (* TODO: Fix properly to cope with Ctypes.fundef *)
  Definition t := Genv.t (AST.fundef (option signature)) unit.

  (* Definition project F V (skenv: t) (fl: flesh F V): option (Genv.t F V). *)
  (*   admit "". *)
  (* Defined. *)

  (* TODO: Is it OK to define it in Prop? I just need backward simulation of this. *)
  Inductive project (skenv: t) (ids: ident -> Prop) (skenv_proj: t): Prop :=
  | project_intro
      (PUBLIC: skenv_proj.(Genv.genv_public) = [])
      (* TODO: is this OK? Check if this info affects semantics except for linking *)
      (NEXT: skenv.(Genv.genv_next) = skenv_proj.(Genv.genv_next))
      (PROJ: forall
          id
          (IN: ids id)
        ,
          (<<SYMB: skenv.(Genv.find_symbol) id = skenv_proj.(Genv.find_symbol) id>>))
      (* TODO: I don't need def here. IT will be overwritten. *)
      (NPROJ: forall
          id
          (NIN: ~ ids id)
        ,
          <<NONE: skenv_proj.(Genv.find_symbol) id = None>>)
  .

  (* Definition project (skenv: t) (ids: list ident): option SkEnv.t. *)
  (*   admit "". *)
  (* Defined. *)

End SkEnv.

(* Skeleton *)
Module Sk.

  Definition t := AST.program (AST.fundef (option signature)) unit.

  Definition load_skenv: t -> SkEnv.t := @Genv.globalenv (AST.fundef (option signature)) unit.
  (* No coercion! *)

  Definition load_mem: t -> option mem := @Genv.init_mem (AST.fundef (option signature)) unit.
  (* No coercion! *)

End Sk.

