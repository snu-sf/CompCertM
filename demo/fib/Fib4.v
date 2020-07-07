Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import FibHeader.
Require Import Fib0.
Require Import SIR.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition f_fib_ru (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  `n: nat <- (unwrapN (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in

      '(oh1, (m1, y1)) <- trigger (ICall _fib_ru oh0 m0 vs0) ;;
      (guarantee (postcond oh0 m0 vs0 (oh1, (m1, y1)))) ;;

      let vs1 := [Vint (of_nat (S m))] in

      '(oh2, (m2, y2)) <- trigger (ICall _fib_ru oh1 m1 vs1) ;;
      (guarantee (postcond oh1 m1 vs1 (oh2, (m2, y2)))) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
    end
.

Definition f_fib (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  assume (precond oh0 m0 vs0) ;;
  trigger (ICall _fib_ru oh0 m0 vs0)
  >>= guaranteeK (postcond oh0 m0 vs0)
.

Definition prog: program owned_heap :=
  (Maps.add _fib_ru f_fib_ru (Maps.add _fib f_fib Maps.empty)).

Definition module: Mod.t := module (Fib0.module) prog "fib"%string initial_owned_heap.
