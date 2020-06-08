Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import IterTarget.
Require Import SIR0.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.

Definition c_iter (vs: list val): itree (E owned_heap) val :=
  m0 <- trigger (Get _) ;; oh0 <- trigger (Get _) ;;
  match vs with
  | [fptr ; Vint n ; x] =>
    if Int.eq n Int.zero
    then triggerDone x 
    else `rv: val <- triggerECall fptr [x] ;;
         trigger (ICall _iter [fptr ; Vint (Int.sub n Int.one) ; rv])
  | _ => triggerUB "signature"
  end
.

Definition f_iter: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_iter) c_iter.

Definition global_definitions: list (ident * globdef (fundef (function owned_heap)) unit) :=
((_iter, Gfun(Internal f_iter)) ::
 nil
)
.

Definition prog: program owned_heap := mkprogram global_definitions public_idents _main.

Definition module: Mod.t := module prog "iter"%string initial_owned_heap.
