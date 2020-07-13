From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
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
From Coq Require Import
     Arith.PeanoNat
     (* Strings.String *)
     Lists.List
     Morphisms
     Setoid
     RelationClasses
.
Require Import CoqlibC.
Require Import Program.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.


Set Implicit Arguments.


Definition hrespectful A0 A1 B0 B1 (RA: A0 -> A1 -> Prop) (RB: B0 -> B1 -> Prop):
  (A0 -> B0) -> (A1 -> B1) -> Prop :=
  fun f0 f1 => forall a0 a1, RA a0 a1 -> RB (f0 a0) (f1 a1)
.

Definition hrespectful_respectful A B (RA: relation A) (RB: relation B):
  @hrespectful A A B B RA RB = @respectful A B RA RB.
Proof. ss. Qed.

Notation " R !-> R' " := (@hrespectful _ _ _ _ (R%signature) (R'%signature))
                           (right associativity, at level 55).
                         (* : signature_scope. *)

Class HProper A0 A1 (R : A0 -> A1 -> Prop) (a0: A0) (a1: A1) : Prop := hproper_prf : R a0 a1.

Program Instance HProper_Proper A RA (a: A) (P: HProper RA a a): Proper RA a.

Hint Unfold hrespectful.
Hint Unfold HProper.





Global Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
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

(* Lemma eq_eutt *)
(*       E R *)
(*       (a b: itree E R) *)
(*       (EQ: a = b) *)
(*   : *)
(*     eutt eq a b *)
(* . *)
(* Proof. i. clarify. refl. Qed. *)

(* Lemma vis_not_ret *)
(*       E R (r: R) X (e: E X) k *)
(*       (EUTT: Vis e k ≈ Ret r) *)
(*   : *)
(*     False *)
(* . *)
(* Proof. ii. punfold EUTT. inv EUTT. Qed. *)













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

Notation "tau;; t2" := (Tau t2)
  (at level 200, right associativity) : itree_scope.



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

(* Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree in H; cbn in H). *)
(* Tactic Notation "irw" := repeat (autorewrite with itree; cbn). *)

(*** TODO: IDK why but (1) ?UNUSNED is needed (2) "fold" tactic does not work. WHY????? ***)
Ltac fold_eutt :=
  repeat multimatch goal with
         | [ H: eqit eq true true ?A ?B |- ?UNUSED ] =>
           let name := fresh "tmp" in
           assert(tmp: eutt eq A B) by apply H; clear H; rename tmp into H
         end
.

Lemma bind_ret_map {E R1 R2} (u : itree E R1) (f : R1 -> R2) :
  (r <- u ;; Ret (f r)) = f <$> u.
Proof.
  f.
  rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_Ret. auto.
  - rewrite bind_ret_r. reflexivity.
Qed.

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) = Vis e (fun x => f <$> (k x)).
Proof.
  f.
  cbn.
  unfold ITree.map.
  autorewrite with itree. refl.
Qed.




(*** TODO: move to SIRCommon ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; et.
Qed.

Lemma bind_ret_l : forall (E : Type -> Type) (R S : Type) (r : R) (k : R -> itree E S),
    ` x : _ <- Ret r;; k x = k r.
Proof.
  i. f. eapply bind_ret_l.
Qed.

Lemma bind_ret_r : forall (E : Type -> Type) (R : Type) (s : itree E R), ` x : R <- s;; Ret x = s.
Proof.
  i. f. eapply bind_ret_r.
Qed.

Lemma bind_tau : forall (E : Type -> Type) (R U : Type) (t : itree E U) (k : U -> itree E R),
  ` x : _ <- Tau t;; k x = Tau (` x : _ <- t;; k x).
Proof.
  i. f. eapply bind_tau.
Qed.

Lemma bind_vis: forall (E : Type -> Type) (R U V : Type) (e : E V) (ek : V -> itree E U) (k : U -> itree E R),
  ` x : _ <- Vis e ek;; k x = Vis e (fun x : V => ` x : _ <- ek x;; k x).
Proof.
  i. f. eapply bind_vis.
Qed.

Lemma bind_trigger: forall (E : Type -> Type) (R U : Type) (e : E U) (k : U -> itree E R),
    ` x : _ <- ITree.trigger e;; k x = Vis e (fun x : U => k x).
Proof. i. f. eapply bind_trigger. Qed.

Lemma bind_bind : forall (E : Type -> Type) (R S T : Type) (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ` x : _ <- (` x : _ <- s;; k x);; h x = ` r : R <- s;; ` x : _ <- k r;; h x.
Proof. i. f. eapply bind_bind. Qed.

Lemma unfold_bind :
forall (E : Type -> Type) (R S : Type) (t : itree E R) (k : R -> itree E S),
` x : _ <- t;; k x = ITree._bind k (fun t0 : itree E R => ` x : _ <- t0;; k x) (observe t).
Proof. i. f. apply unfold_bind. Qed.



Hint Rewrite unfold_interp_mrec : itree_axiom.
Hint Rewrite bind_ret_l : itree_axiom.
Hint Rewrite bind_ret_r : itree_axiom.
Hint Rewrite bind_tau : itree_axiom.
Hint Rewrite bind_vis : itree_axiom.
Hint Rewrite bind_trigger : itree_axiom.
Hint Rewrite bind_bind : itree_axiom.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom; cbn).

Ltac iby TAC :=
  first [
      instantiate (1:= fun _ _ _ => _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- _ ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- _ ;; _) ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); irw; TAC|
      fail
    ]
.
