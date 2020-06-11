Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import FibTarget.
Require Import SIRmini_quotient.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.

Definition c_fib (oh0: owned_heap) (m0: mem) (vs: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  match vs with
  | [Vint n] =>
    if Int.eq n Int.zero
    then Ret (oh0, (m0, (Vint Int.zero)))
    else
      if Int.eq n Int.one
      then Ret (oh0, (m0, (Vint Int.one)))
      else
        '(oh1, (m1, y1)) <- trigger (ICall _fib oh0 m0 [Vint (Int.sub n (Int.repr 2))]) ;;
        '(oh2, (m2, y2)) <- trigger (ICall _fib oh0 m0 [Vint (Int.sub n (Int.repr 1))]) ;;
        Ret (oh2, (m2, Val.add y1 y2))
  | _ => triggerUB (owned_heap := owned_heap)
  end
.

Definition f_fib: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_fib)
             (fun oh0 m0 vs => trigger (EBP _) ;; c_fib oh0 m0 vs).

Definition global_definitions: list (ident * globdef (fundef (function owned_heap)) unit) :=
((_fib, Gfun(Internal f_fib)) ::
 nil
)
.

Definition prog: program owned_heap := mkprogram global_definitions public_idents _main.

Definition module: Mod.t := module prog "fib"%string initial_owned_heap.
