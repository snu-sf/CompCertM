Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import UnionFind0.
Require Import SIR.
Require Export AuxBuffer.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.

(*** TODO: move to CoqlibC ***)
Coercion is_some_coercion {X}: (option X) -> bool := is_some.

(*** TODO: move to more root ***)
Global Opaque ident_eq.
Global Opaque Z.of_nat.

(*** TODO: move to better place ***)
Definition unblock (v: val): option block :=
  match v with
  | Vptr x ofs =>
    if Ptrofs.eq_dec ofs Ptrofs.zero
    then Some x
    else None
  | _ => None
  end
.

Definition malloc (m0: mem) (sz: ptrofs): option (mem * block) :=
  let (m1, b) := Mem.alloc m0 (-8) (Ptrofs.unsigned sz) in
  do m2 <- Mem.store Mptr m1 b (-8) (Vptrofs sz) ; Some (m2, b)
.

Definition parg_new (vs0: list val): option unit :=
  match vs0 with
  | [] => Some tt
  | _ => None
  end
.

Definition parg_find (vs0: list val): option block :=
  match vs0 with
  | [v] => unblock v
  | _ => None
  end
.

Definition parg_union (vs0: list val): option (block * block) :=
  match vs0 with
  | [x ; y] =>
    match unblock x, unblock y with
    | Some x, Some y => Some (x, y)
    | _, _ => None
    end
  | _ => None
  end
.

Global Obligation Tactic := sk_incl_tac.
