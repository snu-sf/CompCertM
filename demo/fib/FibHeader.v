Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import Fib0.
Require Import SIR.
Require Export AuxBuffer.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.

Fixpoint fib_nat (n: nat): nat :=
  match n with
  | 0%nat => 0%nat
  | S n' =>
    match n' with
    | 0%nat => 1%nat
    | S n'' => fib_nat n'' + fib_nat n'
    end
  end.
Lemma fib_nat_0: (fib_nat 0 = 0)%nat. Proof. ss. Qed.
Lemma fib_nat_1: (fib_nat 1 = 1)%nat. Proof. ss. Qed.
Lemma fib_nat_recurse: forall n, ((fib_nat (S (S n))) = (fib_nat n) + fib_nat (S n))%nat.
Proof. reflexivity. Qed.
Global Opaque fib_nat.

(*** TODO: compare with VST (compile it!) ***)
(***
Definition fib_spec fun_id :=
 DECLARE fun_id
  WITH n : Z
  PRE  [ _n OF tint ]
     PROP (0 <= n < 45) (* 50th term is too large to be a 32bit int *)
     LOCAL (temp _n (Vint (Int.repr n)))
     SEP ()
  POST [ tint ]
     PROP () LOCAL (temp ret_temp (Vint (Int.repr (fib_of_Z n))))
     SEP ().
***)

Definition parse_arg (oh0: owned_heap) (m0: mem) (vs0: list val): option nat :=
  match vs0 with
  | [Vint n] => (to_nat_opt n)
  | _ => None
  end
.
Hint Unfold parse_arg.

(*** TODO: move to CoqlibC ***)
Coercion is_some_coercion {X}: (option X) -> bool := is_some.
Definition precond (oh0: owned_heap) (m0: mem) (vs0: list val) := exists n, parse_arg oh0 m0 vs0 = Some n.

Definition postcond (oh0: owned_heap) (m0: mem) (vs0: list val): (owned_heap * (mem * val)) -> Prop :=
  fun '(ohr, (mr, vr)) => 
    match parse_arg oh0 m0 vs0 with
    | Some n => (<<OH: oh0 = ohr>> /\ <<M: m0 = mr>> /\ <<V: vr = Vint (of_nat (fib_nat n))>>)
    | _ => False
    end
.
Hint Unfold postcond.

(*** TODO: move to more root ***)
Global Opaque ident_eq.
Global Opaque Z.of_nat.


(* Definition _fib_ru := 57%positive. *)

Global Obligation Tactic := sk_incl_tac.
