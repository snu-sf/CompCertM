From Coq Require Import
     Arith.PeanoNat
     (* Strings.String *)
     Lists.List
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Require Import Program.
Require Import Simulation.
Require Import AxiomsC.

Set Implicit Arguments.
Set Universe Polymorphism.



(*** TODO: move to CoqlibC ***)
Global Unset Transparent Obligations.
Add Search Blacklist "_obligation_".

From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     (* OptionMonad *)
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Open Scope monad_scope.
Open Scope itree_scope.
(* Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2)) *)
(*   (at level 61, t at next level, t1 at next level, x ident, right associativity) : itree_scope. *)




Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end)
.


Lemma eq_eutt
      E R
      (a b: itree E R)
      (EQ: a = b)
  :
    eutt eq a b
.
Proof. i. clarify. refl. Qed.

Lemma vis_not_ret
      E R (r: R) X (e: E X) k
      (EUTT: Vis e k ≈ Ret r)
  :
    False
.
Proof. ii. punfold EUTT. inv EUTT. Qed.

(* Lemma eqit_inv_vis {E R1 R2 RR} b1 b2 {u1 u2} (e1: E u1) (e2: E u2) *)
(*       (k1: u1 -> itree E R1) (k2: u2 -> itree E R2) : *)
(*   eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2) -> *)
(*   u1 = u2 /\ e1 ~= e2 /\ (forall u1 u2 (EQ: u1 ~= u2), eqit RR b1 b2 (k1 u1) (k2 u2)). *)
(* Proof. *)
(*   intros. punfold H. repeat red in H. simpl in H. *)
(*   dependent destruction H. pclearbot. esplits; eauto. *)
(*   ii. apply JMeq_eq in EQ. clarify. *)
(* Qed. *)

Fail Lemma empty_nonempty
      (T: Type)
      (EQ: void = T)
      (INHAB: inhabited T)
  :
    False
.
(* Proof. *)
(*   inversion INHAB. rewrite <- EQ in H. inv H. *)
(* Qed. *)








Section OWNEDHEAP.

Variable owned_heap: Type.





Section EFF.

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (oh: owned_heap) (m: mem) (vs: list val):
      InternalCallE (owned_heap * (mem * val))
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (sg: signature) (fptr: val)
          (oh: owned_heap) (m: mem) (vs: list val): ExternalCallE (owned_heap * (mem * val))
  .

  Variant EventE: Type -> Type :=
  | ENB: EventE void
  | EUB: EventE void
  | EChoose (X: Type): EventE X
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' EventE.
  Definition eff1: Type -> Type := Eval compute in InternalCallE +' eff0.
  Definition E := Eval compute in eff1.

End EFF.

(* Q: Why manually match "void" type, not using "embed" or "trigger"?
   A: It returns arbitrary type "A", not "void" *)
Definition triggerUB {E A} `{EventE -< E}: itree E A :=
  vis (EUB) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E}: itree E A :=
  vis (ENB) (fun v => match v: void with end)
.
(* Definition triggerDone {E A} `{EventE -< E} (oh: owned_heap) (m: mem) (v: val): itree E A := *)
(*   vis (EDone oh m v) (fun v => match v: void with end) *)
(* . *)

Definition unwrapN {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB
  end.

Definition unwrapU {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB
  end.

(* Record function : Type := mkfunction *)
(*   { fn_sig: signature; *)
(*     fn_code: (forall (oh: owned_heap) (m: mem) (vs: list val), *)
(*                  itree E (owned_heap * (mem * val))); } *)
(* . *)

(* Definition program: Type := AST.program (fundef function) unit. *)
Definition function: Type := (forall (oh: owned_heap) (m: mem) (vs: list val),
                                 itree E (owned_heap * (mem * val))).
Definition program: Type := ident -> option function.

Global Instance program_Map: (Map _ _ _) := (@function_Map ident function ident_eq).




Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition interp_function: (InternalCallE ~> itree E) :=
    fun T ei =>
      let '(ICall func_name oh m vs) := ei in
      match (p func_name) with
      | Some (f) => (f oh m vs)
      | _ => triggerNB
      end
  .

  Definition interp_program0:
    (forall T, InternalCallE T -> itree eff0 T) :=
    fun _ ic =>
      let sem0: itree eff0 _ := (mrec interp_function) _ ic in
      sem0
  .

End DENOTE.






Section TEST.

Definition _sum := 55%positive.

Definition c_sum (oh: owned_heap) (m: mem) (vs: list val): itree E (owned_heap * (mem * val)) :=
  match vs with
  | [Vint n] =>
    if Int.eq n Int.zero
    then Ret (oh, (m, (Vint Int.zero)))
    else '(oh, (m, s)) <- trigger (ICall _sum oh m [Vint (Int.sub n Int.one)]) ;;
         Ret (oh, (m, (Val.add s (Vint n))))
  | _ => triggerUB
  end
.

Definition f_sum: function := c_sum.

Definition global_definitions: list (ident * globdef (fundef (function)) unit) :=
  ((_sum, Gfun(Internal f_sum)) :: nil)
.

Definition p: program := Maps.add _sum c_sum (Maps.empty).

Variable initial_oh: owned_heap.
Let one := (interp_program0 p (ICall _sum initial_oh Mem.empty [Vint (Int.repr 1%Z)])).
(* Compute (burn 1 one). *)

Lemma one_spec
  :
    one ≈ Ret (initial_oh, (Mem.empty, Vint (Int.repr 1%Z)))
.
Proof.
  subst one. unfold interp_program0. ss.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  replace (Int.add Int.zero (Int.repr 1)) with (Int.repr 1); cycle 1.
  { refl. }
  refl.
Qed.

End TEST.

End OWNEDHEAP.



Lemma eq_is_bisim: forall E R (t1 t2 : itree E R), t1 = t2 -> t1 ≅ t2.
Proof. ii. clarify. reflexivity. Qed.
Lemma bisim_is_eq: forall E R (t1 t2 : itree E R), t1 ≅ t2 -> t1 = t2.
Proof. ii. eapply bisimulation_is_eq; eauto. Qed.



Ltac f := first [eapply bisim_is_eq|eapply eq_is_bisim].
Tactic Notation "f" "in" hyp(H) := first [eapply bisim_is_eq in H|eapply eq_is_bisim in H].
Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  sym in T; apply simpobs in T; apply bisim_is_eq in T; rewrite T in *; clarify.
Ltac csc := clarify; simpl_depind; clarify.

Notation "tau ;; t2" := (Tau t2)
  (at level 61, right associativity) : itree_scope.



(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
Lemma eutt_eq_bind : forall E R U (t1 t2: itree E U) (k1 k2: U -> itree E R), t1 ≈ t2 -> (forall u, k1 u ≈ k2 u) -> ITree.bind t1 k1 ≈ ITree.bind t2 k2.
Proof.
  intros.
  eapply eutt_clo_bind with (UU := Logic.eq); [eauto |].
  intros ? ? ->. apply H0.
Qed.
Ltac f_equiv := first [eapply eutt_eq_bind|eapply eqit_VisF|Morphisms.f_equiv].
(* eapply eqit_bind'| *)

Hint Rewrite @bind_trigger : itree.
Hint Rewrite @tau_eutt : itree.
Hint Rewrite @bind_tau : itree.

Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree; cbn).

(*** TODO: IDK why but (1) ?UNUSNED is needed (2) "fold" tactic does not work. WHY????? ***)
Ltac fold_eutt :=
  repeat multimatch goal with
         | [ H: eqit eq true true ?A ?B |- ?UNUSED ] =>
           let name := fresh "tmp" in
           assert(tmp: eutt eq A B) by apply H; clear H; rename tmp into H
         end
.

Lemma bind_ret_map {E R1 R2} (u : itree E R1) (f : R1 -> R2) :
  (r <- u ;; Ret (f r)) ≅ f <$> u.
Proof.
  rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_Ret. auto.
  - rewrite bind_ret_r. reflexivity.
Qed.

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) ≅ Vis e (fun x => f <$> (k x)).
Proof.
  cbn.
  unfold ITree.map.
  autorewrite with itree. refl.
Qed.

