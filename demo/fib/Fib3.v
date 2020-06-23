Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import Fib0.
Require Import SIRmini.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Definition owned_heap: Type := unit.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt.


(* Definition to_nat (i: int): nat := Z.to_nat (Int.unsigned i). *)
Definition to_nat (i: int): nat := Z.to_nat (Int.signed i).
Definition of_nat (n: nat): int := Int.repr (Z.of_nat n).

Definition to_nat_opt (i: int): option nat :=
  if zle 0 (Int.signed i)
  then Some (Z.to_nat (Int.signed i))
  else None
.

Definition of_nat_opt (n: nat): option int :=
  if zlt (Z.of_nat n) Int.modulus
  then Some (Int.repr (Z.of_nat n))
  else None
.

(* Goal forall x y (POS: Int.signed x + Int.signed y <= Int.max_signed) (POS: Int.signed x >= 0) (POS: Int.signed y >= 0), to_nat (Int.add x y) = Nat.add (to_nat x) (to_nat y). *)
(* Proof. *)
(*   i. unfold to_nat. *)
(*   rewrite <- Z2Nat.inj_add; eauto with xomega. rewrite Int.add_signed. rewrite Int.signed_repr; ss. *)
(*   split; try xomega. *)
(*   - generalize Int.min_signed_neg; i. xomega. *)
(* Qed. *)
Fixpoint fib_nat (n: nat): nat :=
  match n with
  | 0%nat => 0%nat
  | S n' =>
    match n' with
    | 0%nat => 1%nat
    | S n'' => fib_nat n'' + fib_nat n'
    end
  end.

(***
precondition: exists n, vs = [Vint n]
postcondition: OH unchanged && M unchanged && rv = of_nat (fib(n))
***)

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

Definition precond (vs: list val): option nat :=
  match vs with
  | [Vint n] => (to_nat_opt n)
  | _ => None
  end
.
Hint Unfold precond.
Coercion is_some_coercion {X}: (option X) -> bool := is_some.

Definition f_fib (oh0: owned_heap) (m0: mem) (vs: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  tau;;
  n <- (unwrapU (precond vs)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      (* '(oh1, (m1, y1)) <- trigger (ICall _fib oh0 m0 [Vint (of_nat m)]) ;; *)
      let vs0 := [Vint (of_nat m)] in
      unwrapN (precond vs0) ;;
      '(oh1, (m1, y1)) <- trigger (ICall _fib oh0 m0 vs0) ;;
      (assume (<<OH: oh0 = oh1>> /\ <<M: m0 = m1>> /\ <<V: y1 = Vint (of_nat (fib_nat m))>>)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      unwrapN (precond vs1) ;;
      '(oh2, (m2, y2)) <- trigger (ICall _fib oh1 m1 vs1) ;;
      (assume (<<OH: oh1 = oh2>> /\ <<M: m1 = m2>> /\ <<V: y2 = Vint (of_nat (fib_nat (S m)))>>)) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
      (* match y1, y2 with *)
      (* | Vint y1, Vint y2 => Ret (oh2, (m2, Vint (of_nat (Nat.add (to_nat y1) (to_nat y2))))) *)
      (* | _, _ => triggerUB *)
      (* end *)
    end
  >>=
  guaranteeK (fun '(ohr, (mr, vr)) => (<<OH: oh0 = ohr>> /\ <<M: m0 = mr>> /\ <<V: vr = Vint (of_nat (fib_nat n))>>))
.
(*     else *)
(*       if Nat.eqb n 0%nat *)
(* Definition f_fib (oh0: owned_heap) (m0: mem) (vs: list val): *)
(*   itree (E owned_heap) (owned_heap * (mem * val)) := *)
(*   tau;; *)
(*   match vs with *)
(*   | [Vint n] => *)
(*     if Int.eq n Int.zero *)
(*     then Ret (oh0, (m0, (Vint Int.zero))) *)
(*     else *)
(*       if Int.eq n Int.one *)
(*       then Ret (oh0, (m0, (Vint Int.one))) *)
(*       else *)
(*         (* guarantee (Int_le n Int.zero) ;; *) *)
(*         guarantee True ;; *)
(*         '(oh1, (m1, y1)) <- trigger (ICall _fib oh0 m0 [Vint (Int.sub n (Int.repr 2))]) ;; *)
(*         (assume (fun _ => <<OH: oh0 = oh1>> /\ <<M: m0 = m1 >> /\ <<V: y1 = fib (Int.sub n (Int.repr 2))>>) tt) ;; *)

(*         guarantee True ;; *)
(*         '(oh2, (m2, y2)) <- trigger (ICall _fib oh1 m1 [Vint (Int.sub n (Int.repr 1))]) ;; *)
(*         assume (<<OH: oh1 = oh2>> /\ <<M: m1 = m2 >> /\ <<V: y2 = fib (Int.sub n (Int.repr 1))>>) ;; *)
(*         Ret (oh2, (m2, Val.add y1 y2)) *)
(*   | _ => triggerUB *)
(*   end *)
(*   >>= *)
(*   (fun '(ohr, (mr, vr)) => guarantee(<<OH: oh0 = ohr>> /\ <<M: m0 = mr>> /\ <<V: True>>) ;; Ret (ohr, (mr, vr))) *)
(* . *)

Definition prog: program owned_heap := (Maps.add _fib f_fib Maps.empty).

Definition module: Mod.t := module (Fib0.module) prog "fib"%string initial_owned_heap.
