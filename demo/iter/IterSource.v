Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import IterTarget.
Require Import SIRmini_eutt.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.

Definition c_iter (oh0: owned_heap) (m0: mem) (vs: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  match vs with
  | [fptr ; Vint n ; x] =>
    x <- unwrapU (Cop.sem_cast x Clightdefs.tint Clightdefs.tint m0) ;;
    if Int.eq n Int.zero
    then Ret (oh0, (m0, x))
             (* triggerDone oh0 m0 x *)
    else '(oh1, (m1, rv)) <- trigger (ECall fptr oh0 m0 [x]) ;;
         trigger (ICall _iter oh1 m1 [fptr ; Vint (Int.sub n Int.one) ; rv])
  | _ => triggerUB (owned_heap := owned_heap)
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
