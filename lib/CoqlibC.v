(** copied && added "C" **)
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

(** newly added **)
Require Export Coqlib.
Ltac check_safe := let n := numgoals in guard n < 2.
Require Export sflib.
From Paco Require Export paco.
Require Export Basics.

Require Import Relations.
Require Import RelationClasses.
Require Import Wellfounded.
Require Export Classical_Prop.
Require Import AxiomsC.

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

Notation top1 := (fun _ => True).
Notation top2 := (fun _ _ => True).
Notation top3 := (fun _ _ _ => True).
Notation top4 := (fun _ _ _ => True).

Notation " 'all1' p" := (forall x0, p x0) (at level 50, no associativity).
Notation " 'all2' p" := (forall x0 x1, p x0 x1) (at level 50, no associativity).
Notation " 'all3' p" := (forall x0 x1 x2, p x0 x1 x2) (at level 50, no associativity).
Notation " 'all4' p" := (forall x0 x1 x2 x3, p x0 x1 x2 x3) (at level 50, no associativity).

Notation " ~1 p" := (fun x0 => ~ (p x0)) (at level 50, no associativity).
Notation " ~2 p" := (fun x0 x1 => ~ (p x0 x1)) (at level 50, no associativity).
Notation " ~3 p" := (fun x0 x1 x2 => ~ (p x0 x1 x2)) (at level 50, no associativity).
Notation " ~4 p" := (fun x0 x1 x2 x3 => ~ (p x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p /1\ q" := (fun x0 => and (p x0) (q x0)) (at level 50, no associativity).
Notation "p /2\ q" := (fun x0 x1 => and (p x0 x1) (q x0 x1)) (at level 50, no associativity).
Notation "p /3\ q" := (fun x0 x1 x2 => and (p x0 x1 x2) (q x0 x1 x2)) (at level 50, no associativity).
Notation "p /4\ q" := (fun x0 x1 x2 x3 => and (p x0 x1 x2 x3) (q x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p -1> q" := (fun x0 => (forall (PR: p x0: Prop), q x0): Prop) (at level 50, no associativity).
Notation "p -2> q" := (fun x0 x1 => (forall (PR: p x0 x1: Prop), q x0 x1): Prop) (at level 50, no associativity).
Notation "p -3> q" := (fun x0 x1 x2 => ((forall (PR: p x0 x1 x2: Prop), q x0 x1 x2): Prop)) (at level 50, no associativity).
Notation "p -4> q" := (fun x0 x1 x2 x3 => (forall (PR: p x0 x1 x2 x3: Prop), q x0 x1 x2 x3): Prop) (at level 50, no associativity).

Goal all1 ((bot1: unit -> Prop) -1> top1). ii. ss. Qed.
Goal ((bot1: unit -> Prop) <1= top1). ii. ss. Qed.
Goal (bot2: unit -> unit -> Prop) <2= top2. ii. ss. Qed.


Definition less1 X0 (p q: X0 -> Prop) := (forall x0 (PR: p x0 : Prop), q x0 : Prop).
Definition less2 X0 X1 (p q: X0 -> X1 -> Prop) := (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop).
Definition less3 X0 X1 X2 (p q: X0 -> X1 -> X2 -> Prop) := (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop).
Definition less4 X0 X1 X2 X3 (p q: X0 -> X1 -> X2 -> X3 -> Prop) := (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop).

Notation "p <1= q" := (less1 p q) (at level 50).
Notation "p <2= q" := (less2 p q) (at level 50).
Notation "p <3= q" := (less3 p q) (at level 50).
Notation "p <4= q" := (less4 p q) (at level 50).

Global Program Instance less1_PreOrder X0: PreOrder (@less1 X0).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less2_PreOrder X0 X1: PreOrder (@less2 X0 X1).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less3_PreOrder X0 X1 X2: PreOrder (@less3 X0 X1 X2).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less4_PreOrder X0 X1 X2 X3 : PreOrder (@less4 X0 X1 X2 X3).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Hint Unfold less1 less2 less3 less4.

Goal ((bot1: unit -> Prop) <1= top1). ii. ss. Qed.
Goal (bot2: unit -> unit -> Prop) <2= top2. ii. ss. Qed.

(* Notation "p =1= q" := (forall x0, eq (p x0) (q x0)) (at level 50, no associativity). *)
Notation "p =1= q" := (fun x0 => eq (p x0) (q x0)) (at level 50, no associativity).
Notation "p =2= q" := (fun x0 x1 => eq (p x0 x1) (q x0 x1)) (at level 50, no associativity).
Notation "p =3= q" := (fun x0 x1 x2 => eq (p x0 x1 x2) (q x0 x1 x2)) (at level 50, no associativity).
Notation "p =4= q" := (fun x0 x1 x2 x3 => eq (p x0 x1 x2 x3) (q x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p <1> q" := (fun x0 => iff (p x0) (q x0)) (at level 50, no associativity).
Notation "p <2> q" := (fun x0 x1 => iff (p x0 x1) (q x0 x1)) (at level 50, no associativity).
Notation "p <3> q" := (fun x0 x1 x2 => iff (p x0 x1 x2) (q x0 x1 x2)) (at level 50, no associativity).
Notation "p <4> q" := (fun x0 x1 x2 x3 => iff (p x0 x1 x2 x3) (q x0 x1 x2 x3)) (at level 50, no associativity).

Lemma prop_ext1
      X0
      (P Q: X0 -> Prop)
      (IFF: all1 (P <1> Q))
  :
    <<EQ: all1 (P =1= Q)>>
.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext2
      X0 X1
      (P Q: X0 -> X1 -> Prop)
      (IFF: all2 (P <2> Q))
  :
    <<EQ: all2 (P =2= Q)>>
.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext3
      X0 X1 X2
      (P Q: X0 -> X1 -> X2 -> Prop)
      (IFF: all3 (P <3> Q))
  :
    <<EQ: all3 (P =3= Q)>>
.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext4
      X0 X1 X2 X3
      (P Q: X0 -> X1 -> X2 -> X3 -> Prop)
      (IFF: all4 (P <4> Q))
  :
    <<EQ: all4 (P =4= Q)>>
.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

(* Originally in sflib, (t):Prop *)
(* Removed it for use in "privs" of ASTM *)
(* Notation "<< x : t >>" := (NW (fun x => (t))) (at level 80, x ident, no associativity). *)


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

Lemma Forall2_impl
      X Y
      (xs: list X) (ys: list Y)
      (P Q: X -> Y -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <2= Q))
      (FORALL: Forall2 P xs ys)
  :
    <<FORALL: Forall2 Q xs ys>>
.
Proof.
  admit "easy".
Qed.

Inductive Forall3 X Y Z (R: X -> Y -> Z -> Prop): list X -> list Y -> list Z -> Prop :=
| Forall3_nil: Forall3 R [] [] []
| Forall3_cons
    x y z
    xs ys zs
    (TAIL: Forall3 R xs ys zs)
  :
    Forall3 R (x :: xs) (y :: ys) (z :: zs)
.

Lemma Forall3_impl
      X Y Z
      (xs: list X) (ys: list Y) (zs: list Z)
      (P Q: X -> Y -> Z -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <3= Q))
      (FORALL: Forall3 P xs ys zs)
  :
    <<FORALL: Forall3 Q xs ys zs>>
.
Proof.
  admit "easy".
Qed.


Definition o_map A B (oa: option A) (f: A -> B): option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end
.

Definition o_join A (a: option (option A)): option A :=
  match a with
  | Some a => a
  | None => None
  end
.

Definition o_bind A B (oa: option A) (f: A -> option B): option B := o_join (o_map oa f).
Hint Unfold o_map o_join o_bind.

Definition curry2 A B C (f: A -> B -> C): (A * B) -> C := fun ab => f ab.(fst) ab.(snd).

Definition o_bind2 A B C (oab: option (A * B)) (f: A -> B -> option C) : option C :=
o_join (o_map oab f.(curry2)).

(* Notation "o >>= f" := (o_bind o f) (at level 50, no associativity) : option_monad_scope. *)

(* Copied from Errors.v *)

Notation "'do' X <- A ; B" := (o_bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200)
 : o_monad_scope.


Notation "'do' ( X , Y ) <- A ; B" := (o_bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : o_monad_scope.

Notation "'assertion' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200, only parsing)
  : o_monad_scope.

Open Scope o_monad_scope.

Ltac subst_locals := all ltac:(fun H => is_local_definition H; subst H).

Hint Unfold flip.

Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Print Ltac uf.
Tactic Notation "u" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Tactic Notation "u" := repeat (autounfold with *; cbn).
Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in *).

Lemma dependent_split_right
      (A B: Prop)
      (PA: A)
      (PB: <<HINTLEFT: A>> -> B)
  :
    <<PAB: A /\ B>>
.
Proof. eauto. Qed.

Lemma dependent_split_left
      (A B: Prop)
      (PA: <<HINTRIGHT: B>> -> A)
      (PB: B)
  :
    <<PAB: A /\ B>>
.
Proof. eauto. Qed.

Ltac dsplit_r := eapply dependent_split_right.
Ltac dsplit_l := eapply dependent_split_left.
Ltac dsplits :=
  repeat (let NAME := fresh "SPLITHINT" in try (dsplit_r; [|intro NAME]))
.

Locate des_sumbool.
(* TODO: Update Coqlib *)
Lemma proj_sumbool_is_false
      P
      (a: {P} + {~ P})
      (FALSE: ~ P)
  :
    <<FALSE: proj_sumbool a = false>>
.
Proof. unfold proj_sumbool. des_ifs. Qed.

Ltac des_sumbool :=
  repeat
    match goal with
    | [ H: proj_sumbool ?x = true |- _ ] => apply proj_sumbool_true in H
    | [ H: proj_sumbool ?x = false |- _ ] => apply proj_sumbool_false in H
    | [ H: true = proj_sumbool ?x |- _ ] => symmetry in H; apply proj_sumbool_true in H
    | [ H: false = proj_sumbool ?x |- _ ] => symmetry in H; apply proj_sumbool_false in H

    | [ |- proj_sumbool ?x = true ] => apply proj_sumbool_is_true
    | [ |- proj_sumbool ?x = false ] => apply proj_sumbool_is_false
    | [ |- true = proj_sumbool ?x ] => symmetry; apply proj_sumbool_is_true
    | [ |- false = proj_sumbool ?x ] => symmetry; apply proj_sumbool_is_false
    end
.

Ltac is_prop H :=
  let ty := type of H in
  match type of ty with
  | Prop => idtac
  | _ => fail 1
  end
.

Ltac all_prop TAC := all ltac:(fun H => tryif is_prop H then TAC H else idtac).

Ltac all_prop_inv := all_prop inv.
(* TODO: infinite loop when inv-ing "a+b = c+d". "progress" tactic does not help here. *)
(* TODO: add all_once, which captures only current hypotheses and apply TAC *)

Ltac all_rewrite := all ltac:(fun H => rewrite_all H).

Definition bar_True: Type := True.
Global Opaque bar_True.
Ltac bar :=
  let NAME := fresh
                "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT"
  in
  assert(NAME: bar_True) by ss
.

Ltac clear_until id :=
  on_last_hyp ltac:(fun id' => match id' with
                               | id => idtac
                               | _ => clear id'; clear_until id
                               end)
.

Ltac clear_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => clear id'; clear_until_bar
                               end)
.

Goal True -> True -> False.
  intro. bar. intro.
  clear_until H0. clear_until H. Undo 2.
  clear_until_bar.
  clear_tac.
Abort.

