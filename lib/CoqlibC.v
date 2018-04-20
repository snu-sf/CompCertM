(** copied && added "C" **)
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

(** newly added **)
Require Export Coqlib.
Require Export sflib.
From Paco Require Export paco.
Require Export Basics.

Require Import Relations.
Require Import RelationClasses.
Require Import Wellfounded.

Set Implicit Arguments.



Ltac determ_tac LEMMA :=
  let tac := eauto in
  let x := rev_all ltac:(fun f => apply f) in
  let y := all ltac:(fun f => apply f) in
  first[
      exploit LEMMA; [x|y|]
    | exploit LEMMA; [tac|x|y|]
    | exploit LEMMA; [tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|tac|x|y|]
    ]
  ;
  i; des; clarify
.

(* TODO: if it is mature enough, move it to sflib & remove this file *)

Definition update_fst {A B C: Type} (f: A -> C) (ab: A * B): C * B := (f ab.(fst), ab.(snd)).

Definition update_snd {A B C: Type} (f: B -> C) (ab: A * B): A * C := (ab.(fst), f ab.(snd)).

Lemma dep_split_right
      (A B: Prop)
      (PA: A)
      (PB: <<LEFT: A>> -> B)
  :
    <<SPLIT: A /\ B>>
.
Proof.
  split; eauto.
Qed.

Lemma dep_split_left
      (A B: Prop)
      (PA: <<RIGHT: B>> -> A)
      (PB: B)
  :
    A /\ B
.
Proof.
  split; eauto.
Qed.

Lemma list_forall2_map
      X Y (f: X -> Y) xs
  :
    list_forall2 (fun x0 x1 => x1 = f x0) xs (map f xs)
.
Proof.
  ginduction xs; ii; ss.
  - econs; eauto.
  - econs; eauto.
Qed.


Lemma list_forall2_map_right
      X Y (f: X -> Y) xs
  :
    list_forall2 (fun x0 x1 => x0 = f x1) (map f xs) xs
.
Proof.
  ginduction xs; ii; ss.
  - econs; eauto.
  - econs; eauto.
Qed.

(* Lemma list_forall2_flip *)
(*       X Y (P: X -> Y -> Prop) xs ys *)
(*       (FORALL2: list_forall2 P xs ys) *)
(*   : *)
(*     <<FORALL2: list_forall2 (Basics.flip P) ys xs>> *)
(* . *)
(* Proof. *)
(*   ginduction FORALL2; ii; ss. *)
(*   - econs; eauto. *)
(*   - econs; eauto. *)
(* Qed. *)

Lemma list_forall2_stronger
      X Y xs ys (P: X -> Y -> Prop)
      (FORALL2: list_forall2 P xs ys)
      Q
      (STRONGER: P <2= Q)
  :
    <<FORALL2: list_forall2 Q xs ys>>
.
Proof.
  ginduction FORALL2; ii; ss.
  - econs; eauto.
  - econs; eauto.
    eapply IHFORALL2; eauto.
Qed.

Global Program Instance incl_PreOrder {A}: PreOrder (@incl A).
Next Obligation.
  ii. ss.
Qed.
Next Obligation.
  ii.
  eauto.
Qed.

(* is_Some & is_None? a bit harder to type *)
Definition is_some {X} (x: option X): bool :=
  match x with
  | Some _ => true
  | _ => false
  end
.

Definition is_none {X} := negb <*> (@is_some X).

Hint Unfold is_some is_none.



Notation "x $" := (x.(proj1_sig)) (at level 50, no associativity (* , only parsing *)).

Notation " ~1 p" := (fun x0 => ~ (p x0)) (at level 50, no associativity).

Notation "p /1\ q" := (fun x0 => and (p x0) (q x0)) (at level 50, no associativity).

Definition less1 X0 (p q: X0 -> Prop) := (forall x0 (PR: p x0 : Prop), q x0 : Prop).
Hint Unfold less1.
Notation "p <1= q" := (less1 p q) (at level 50).

(* Originally in sflib, (t):Prop *)
(* Removed it for use in "privs" of ASTM *)
(* Notation "<< x : t >>" := (NW (fun x => (t))) (at level 80, x ident, no associativity). *)


Global Program Instance less1_PreOrder X0: PreOrder (@less1 X0).

Print Ltac uf.
Ltac u := repeat (autounfold with * in *; cbn in *).
(* TODO add in sflib *)

Hint Unfold Basics.compose.


(* Note: not clos_refl_trans. That is not well-founded.. *)
Lemma well_founded_clos_trans
      index
      (order: index -> index -> Prop)
      (WF: well_founded order)
  :
    <<WF: well_founded (clos_trans index order)>>
.
Proof.
  hnf in WF.
  hnf.
  i.
  eapply Acc_clos_trans. eauto.
Qed.
