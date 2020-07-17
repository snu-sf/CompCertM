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
  match vs0 with
  | [Vint n] =>
    if Int.eq n Int.zero
    then Ret (oh0, (m0, (Vint Int.zero)))
    else
      if Int.eq n Int.one
      then Ret (oh0, (m0, (Vint Int.one)))
      else
        let vs0 := [Vint (Int.sub n (Int.repr 2))] in
        guarantee (Int.lt (Int.sub n (Int.repr 2)) n) ;;
        '(oh1, (m1, y1)) <- trigger (ICall _fib_ru oh0 m0 vs0) ;;

        let vs1 := [Vint (Int.sub n (Int.repr 1))] in
        guarantee (Int.lt (Int.sub n (Int.repr 1)) n) ;;
        '(oh2, (m2, y2)) <- trigger (ICall _fib_ru oh1 m1 vs1) ;;
        Ret (oh2, (m2, Val.add y1 y2))
  | _ => triggerNB
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


Program Definition module: SMod.t _ := SMod.mk (Fib0.module) prog "fib"%string initial_owned_heap _.
