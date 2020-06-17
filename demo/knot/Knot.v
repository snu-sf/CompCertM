Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import SIRmini.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)




(* Set Printing Universes. *)
(* Record my_mod: Type := mk { *)
(*   datatype: Type; *)
(* }. *)
(* Definition my_mods_uses_option (md: option my_mod): option my_mod := option_map id md. *)
(* Polymorphic Variant void1 : Type -> Type := . *)
(* Definition boo: my_mod := mk (itree void1 unit). *)

(* my_mod.u0 < option_map.u0 <= option.u0 = ITree.Core.ITreeDefinition.2 *)

(* Found: ITree.Core.ITreeDefinition.1 = sum1.u0 <= interleaved.u2 <= bind_tau.u0 <= bind_tau_.u0 <= option.u0 = owned_heap.u0  *)

(* Record my_record: Type := mk { *)
(*   my_ty: Type; *)
(* } *)
(* . *)
(* Definition foo: my_record := mk (option nat). *)
(* Definition bar: Type := (itree void1 my_record). *)
(* Definition baz: option my_record := Some (mk Empty_set). *)
(* Definition dog (mr: my_record): option Type := Some mr.(my_ty). *)

(* itree > option *)






(* Section TTTTTTTTTT. *)
(*   Definition owned_heap: Type := itree EventE nat. *)
(*   Set Printing Universes. *)
(*   Print Universes. *)
(*   (* Definition ok: itree EventE (itree void1 nat) := *) *)
(*   (*   Tau (Ret (Ret 0%nat)) *) *)
(*   (* . *) *)
(*   (* Definition ok: itree EventE (itree void1 nat) := *) *)
(*   (*   triggerUB *) *)
(*   (* . *) *)
(*   Definition not_ok: itree EventE (itree void1 owned_heap) := *)
(*     (triggerUB) *)
(*     (* vis (ENB) (fun v => match v: void with end) *) *)
(*     (* vis (EUB) (fun _ => (Ret (Ret 0%nat))) *) *)
(*   . *)
(*   Set Printing Universes. *)
(*   Print Universes. *)
(* End TTTTTTTTTT. *)







(* From ITree Require Export *)
(*      Events.State *)
(*      Events.StateFacts *)
(* . *)



(* let r: ((int -> int) ref) = ref (fun x -> assert false) *)
Definition owned_heap: Type := ktree EventE nat nat.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => fun _ => triggerUB.
(* Definition owned_heap: Type := unit. *)
(* Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => tt. *)



(*** our "val" does not support a value of type "ktree EventE nat nat -> ktree EventE nat nat" ***)
(***
FUTURE WORK: We already checked that "Vabs (a: Any)" approach is at least well-defined.
We can use it and generalize "ICall" event so that we don't need this "CallKnotE"
 ***)


(* Definition bc E R (t: itree E (itree E R)): itree E R := x <- t ;; x. *)
Variant CallKnotE: Type -> Type :=
(*** it has universe inconsistency in:
       ktr <- trigger (CallKnot g oh0) ;; ktr ***)
(* | CallKnot *)
(*     (g: ktree EventE nat nat -> ktree EventE nat nat) (oh: owned_heap): *)
(*     CallKnotE (owned_heap * (ktree EventE nat nat)) *)
| CallKnot
    (g: ktree EventE nat nat -> ktree EventE nat nat) (oh: owned_heap) (v: nat):
    CallKnotE (owned_heap * nat)
.



(* let landins_knot (g: (int -> int) -> (int -> int)): int -> int = *)
(*   r := g (fun x -> !r x); !r *)
Definition _knot := 100%positive.
Definition knot (g: ktree EventE nat nat -> ktree EventE nat nat)
           (oh0: owned_heap): ktree EventE nat (owned_heap * nat) :=
  let oh1: owned_heap := g (fun x => oh0 x) in
  (fun x => rv <- oh1 x ;; Ret (oh1, rv))
.

(* let factorial: int -> int = *)
(*   let g f x = *)
(*     if x = 0 then *)
(*       1 *)
(*     else *)
(*       x * f (x - 1) *)
(*   in *)
(*   landins_knot g *)
Definition _factorial := 150%positive.
Set Printing Universes.
(* Print Universes. *)
Definition factorial (oh0: owned_heap): ktree EventE nat (owned_heap * nat) :=
  let g: ktree EventE nat nat -> ktree EventE nat nat
      := fun f x =>
           match x with
           | O => Ret 1%nat
           | S y => y' <- f y ;; Ret (x * y')%nat
           end
  in
  fun x => trigger (CallKnot g oh0 x)
.

let main = print_endline (string_of_int (factorial 5));
Definition c_knot (oh0: owned_heap) (m0: mem) (vs: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  match vs with
  | [fptr ; Vint n ; x] =>
    x <- unwrapU (Cop.sem_cast x Clightdefs.tint Clightdefs.tint m0) ;;
    if Int.eq n Int.zero
    then Ret (oh0, (m0, x))
             (* triggerDone oh0 m0 x *)
    else '(oh1, (m1, rv)) <- trigger (ECall sg fptr oh0 m0 [x]) ;;
         trigger (ICall _iter oh1 m1 [fptr ; Vint (Int.sub n Int.one) ; rv])
  | _ => triggerUB (owned_heap := owned_heap)
  end
.

let factorial: int -> int =
  let g f x =
    if x = 0 then
      1
    else
      x * f (x - 1)
  in
  landins_knot g

let main =
  print_endline (string_of_int (factorial 5));

Definition c_iter (oh0: owned_heap) (m0: mem) (vs: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  match vs with
  | [fptr ; Vint n ; x] =>
    x <- unwrapU (Cop.sem_cast x Clightdefs.tint Clightdefs.tint m0) ;;
    if Int.eq n Int.zero
    then Ret (oh0, (m0, x))
             (* triggerDone oh0 m0 x *)
    else '(oh1, (m1, rv)) <- trigger (ECall sg fptr oh0 m0 [x]) ;;
         trigger (ICall _iter oh1 m1 [fptr ; Vint (Int.sub n Int.one) ; rv])
  | _ => triggerUB (owned_heap := owned_heap)
  end
.
Compute (burn 100 (c_iter tt Mem.empty [Vint (Int.zero); Vint (Int.zero); Vint (Int.zero)])).
Compute (burn 100 (c_iter tt Mem.empty [Vint (Int.one); Vint (Int.one); Vint (Int.one)])).
Compute (burn 100 ((fun oh0 m0 vs => trigger (EBP _) ;; c_iter oh0 m0 vs) tt Mem.empty [Vint (Int.zero); Vint (Int.zero); Vint (Int.zero)])).
Compute (burn 100 ((fun oh0 m0 vs => trigger (EBP _) ;; c_iter oh0 m0 vs) tt Mem.empty [Vint (Int.one); Vint (Int.one); Vint (Int.one)])).

Definition f_iter: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_iter)
             (fun oh0 m0 vs => trigger (EBP _) ;; c_iter oh0 m0 vs).

Definition global_definitions: list (ident * globdef (fundef (function owned_heap)) unit) :=
((_iter, Gfun(Internal f_iter)) ::
 nil
)
.

Definition prog: program owned_heap := mkprogram global_definitions public_idents _main.

Definition module: Mod.t := module prog "iter"%string initial_owned_heap.
