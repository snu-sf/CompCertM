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



Definition f_fib (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  assume (precond oh0 m0 vs0) ;;
  ohmv <- trigger (EChoose { ohmv: (owned_heap * (mem * val)) | postcond oh0 m0 vs0 ohmv }) ;;
  Ret (proj1_sig ohmv)
.

Definition prog: program owned_heap :=
  (Maps.add _fib f_fib Maps.empty).

Program Definition module: SMod.t _ := SMod.mk (Fib0.module) prog "fib"%string initial_owned_heap _.
