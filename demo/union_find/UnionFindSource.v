Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import UnionFindTarget.
Require Import SIR.

(* Require Import Clightdefs. *)

From ExtLib Require Import
     OptionMonad
     Functor FunctorLaws
     Structures.Maps
.

Set Implicit Arguments.


Import FunctorNotation.
Local Open Scope monad_scope.
Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 61, t at next level, t1 at next level, x ident, right associativity) : itree_scope.


Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.

Program Instance function_MapOk (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}):
  MapOk eq (function_Map V dec) (K := K) := {| mapsto := fun k v m => m k = Some v |}.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.

Definition assume oh (P: Prop): itree (E oh) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerUB "assume"
.
  
Definition guarantee oh (P: Prop): itree (E oh) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerNB "guarantee"
.

Definition unblock (v: val): option block :=
  match v with
  | Vptr blk ofs =>
    if Ptrofs.eq_dec ofs Ptrofs.zero
    then Some blk
    else None
  | _ => None
  end
.




Definition owned_heap: Type := block -> option (block * int).
Instance owned_heap_Map: (Map _ _ owned_heap) := function_Map _ eq_block.
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => Maps.empty.

Definition c_makeSet (vs: list val): itree (E owned_heap) val :=
  m0 <- trigger (Get _) ;; oh0 <- trigger (Get _) ;;
  let '(m1, blk) := (Mem.alloc m0 0%Z 0%Z) in
  let oh1: owned_heap := Maps.add blk (blk, Int.zero) oh0 in
  trigger (Put _ m1) ;; trigger (Put _ oh1) ;;
  Ret (Vptr blk Ptrofs.zero)
.

Definition c_makeSet_old (oh0: owned_heap) (vs: list val) (m0: mem):
  itree (E owned_heap) (owned_heap * mem * val) :=
  let '(m1, blk) := (Mem.alloc m0 0%Z 0%Z) in
  let oh1 := Maps.add blk (blk, Int.zero) oh0 in
  Ret (oh1, m1, (Vptr blk Ptrofs.zero))
.

Definition f_makeSet: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_makeSet) c_makeSet.

Definition c_find (vs: list val): itree (E owned_heap) val :=
  oh0 <- trigger (Get _) ;;
  x <- unwrapU ((hd_error vs) >>= unblock) ;;
  '(p, rk) <- unwrapU (Maps.lookup x oh0) ;; trigger (LPut _p (Vptr p Ptrofs.zero)) ;;
  (if negb (eq_block p x)
   then `p0: block <- (unblock <$> (trigger (ICall _find [Vptr p Ptrofs.zero])) >>= unwrapN) ;;
        trigger (LPut _p (Vptr p0 Ptrofs.zero)) ;;
        let oh1 := Maps.add x (p0, rk) oh0 in
        trigger (Put _ oh1)
   else Ret tt) ;;
  trigger (LGet _p) >>= ret
.

Definition f_find: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_find) c_find.

Definition global_definitions: list (ident * globdef (fundef (SIR.function owned_heap)) unit) :=
((_malloc, Gfun(External EF_malloc)) ::
 (_makeSet, Gfun(Internal f_makeSet)) :: (_find, Gfun(Internal f_find)) ::
 (* (_unionS, Gfun(Internal f_unionS)) :: *)
 (* (_same_set, Gfun(Internal f_same_set)) :: *)
 nil
)
.

Definition prog: SIR.program owned_heap := mkprogram global_definitions public_idents _main.

Definition module: Mod.t := SIR.module prog "UF"%string initial_owned_heap.

(* void unionS(struct Node* x, struct Node* y) { *)
(*   struct Node *xRoot, *yRoot; *)
(*   unsigned int xRank, yRank; *)
(*   xRoot = find(x); *)
(*   yRoot = find(y); *)
(*   if (xRoot == yRoot) { *)
(*     return; *)
(*   } *)
(*   xRank = xRoot -> rank; *)
(*   yRank = yRoot -> rank; *)
(*   if (xRank < yRank) { *)
(*     xRoot -> parent = yRoot; *)
(*   } else if (xRank > yRank) { *)
(*     yRoot -> parent = xRoot; *)
(*   } else { *)
(*     yRoot -> parent = xRoot; *)
(*     xRoot -> rank = xRank + 1; *)
(*   } *)
(* }; *)

(* ///////////////////////////////////////////////// *)

(* int same_set(struct Node* x, struct Node *y) { *)
(*   return (find(x) == find(y)); *)
(* } *)
