(** copied && added "C" **)
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

(** newly added **)
From compcertr Require Export Coqlib.
Ltac check_safe := let n := numgoals in guard n < 2.
From compcertr Require Export sflib.
From Paco Require Export paco.
Require Export Basics.

Require Import Relations.
Require Export RelationClasses.
Require Import Wellfounded.
Require Export Classical_Prop.
Require Export Lia.
Require Import AxiomsC.
Require Import Relation_Operators.
Require Export List.

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
    ];
  i; des; clarify.

(* TODO: if it is mature enough, move it to sflib & remove this file *)

Definition update_fst {A B C: Type} (f: A -> C) (ab: A * B): C * B := (f (fst ab), (snd ab)).

Definition update_snd {A B C: Type} (f: B -> C) (ab: A * B): A * C := ((fst ab), f (snd ab)).

Lemma dep_split_right
      (A B: Prop) (PA: A)
      (PB: <<LEFT: A>> -> B):
    <<SPLIT: A /\ B>>.
Proof. split; eauto. Qed.

Lemma dep_split_left
      (A B: Prop)
      (PA: <<RIGHT: B>> -> A)
      (PB: B):
    A /\ B.
Proof. split; eauto. Qed.

Lemma list_forall2_map
      X Y (f: X -> Y) xs:
    list_forall2 (fun x0 x1 => x1 = f x0) xs (map f xs).
Proof. ginduction xs; ii; ss; econs; eauto. Qed.


Lemma list_forall2_map_right
      X Y (f: X -> Y) xs:
    list_forall2 (fun x0 x1 => x0 = f x1) (map f xs) xs.
Proof. ginduction xs; ii; ss; econs; eauto. Qed.

Lemma Forall_app A P (l0 l1: list A)
      (FORALL0: Forall P l0)
      (FORALL1: Forall P l1):
    Forall P (l0 ++ l1).
Proof. ginduction l0; i; ss. inv FORALL0. econs; eauto. Qed.

Lemma list_forall2_stronger
      X Y xs ys (P: X -> Y -> Prop) Q
      (FORALL2: list_forall2 P xs ys)
      (STRONGER: P <2= Q):
    <<FORALL2: list_forall2 Q xs ys>>.
Proof. ginduction FORALL2; ii; ss; econs; eauto. eapply IHFORALL2; eauto. Qed.

Global Program Instance incl_PreOrder {A}: PreOrder (@incl A).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

(* is_Some & is_None? a bit harder to type *)
Definition is_some {X} (x: option X): bool :=
  match x with
  | Some _ => true
  | _ => false
  end.

Definition is_none {X} := negb <*> (@is_some X).

Hint Unfold is_some is_none.


Notation "x $" := ((proj1_sig x)) (at level 50, no associativity (* , only parsing *)).

Notation top1 := (fun _ => True).
Notation top2 := (fun _ _ => True).
Notation top3 := (fun _ _ _ => True).
Notation top4 := (fun _ _ _ _ => True).
Notation top5 := (fun _ _ _ _ _ => True).
Notation top6 := (fun _ _ _ _ _ _ => True).

Notation " 'all1' p" := (forall x0, p x0) (at level 50, no associativity, only parsing).
Notation " 'all2' p" := (forall x0 x1, p x0 x1) (at level 50, no associativity, only parsing).
Notation " 'all3' p" := (forall x0 x1 x2, p x0 x1 x2) (at level 50, no associativity, only parsing).
Notation " 'all4' p" := (forall x0 x1 x2 x3, p x0 x1 x2 x3) (at level 50, no associativity, only parsing).

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
      (IFF: all1 (P <1> Q)):
    <<EQ: all1 (P =1= Q)>>.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext2
      X0 X1
      (P Q: X0 -> X1 -> Prop)
      (IFF: all2 (P <2> Q)):
    <<EQ: all2 (P =2= Q)>>.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext3
      X0 X1 X2
      (P Q: X0 -> X1 -> X2 -> Prop)
      (IFF: all3 (P <3> Q)):
    <<EQ: all3 (P =3= Q)>>.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma prop_ext4
      X0 X1 X2 X3
      (P Q: X0 -> X1 -> X2 -> X3 -> Prop)
      (IFF: all4 (P <4> Q)):
    <<EQ: all4 (P =4= Q)>>.
Proof. ss. ii. eapply prop_ext; eauto. Qed.

Lemma func_ext1
      X0 Y0
      (P Q: X0 -> Y0)
      (EQ: all1 (P =1= Q)):
    <<EQ: P = Q>>.
Proof. apply Axioms.functional_extensionality. ii; ss. Qed.

Lemma func_ext2
      X Y Z
      (P Q: X -> Y -> Z)
      (EQ: all2 (P =2= Q)):
    <<EQ: P = Q>>.
Proof. apply func_ext1; ss. i. apply func_ext1; ss. Qed.

Lemma func_ext3
      X Y Z W
      (P Q: X -> Y -> Z -> W)
      (EQ: all3 (P =3= Q)):
    <<EQ: P = Q>>.
Proof. apply func_ext2; ss. i. apply func_ext1; ss. Qed.

(* Originally in sflib, (t):Prop *)
(* Removed it for use in "privs" of ASTM *)
(* Notation "<< x : t >>" := (NW (fun x => (t))) (at level 80, x ident, no associativity). *)


Hint Unfold Basics.compose.


(* Note: not clos_refl_trans. That is not well-founded.. *)
Lemma well_founded_clos_trans
      index
      (order: index -> index -> Prop)
      (WF: well_founded order):
    <<WF: well_founded (clos_trans index order)>>.
Proof. hnf in WF. hnf. i. eapply Acc_clos_trans. eauto. Qed.

Lemma Forall2_impl
      X Y
      (xs: list X) (ys: list Y)
      (P Q: X -> Y -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <2= Q))
      (FORALL: Forall2 P xs ys):
    <<FORALL: Forall2 Q xs ys>>.
Proof. induction FORALL; econs; eauto. Qed.

Inductive Forall3 X Y Z (R: X -> Y -> Z -> Prop): list X -> list Y -> list Z -> Prop :=
| Forall3_nil: Forall3 R [] [] []
| Forall3_cons
    x y z xs ys zs
    (TAIL: Forall3 R xs ys zs):
    Forall3 R (x :: xs) (y :: ys) (z :: zs).

Lemma Forall3_impl
      X Y Z
      (xs: list X) (ys: list Y) (zs: list Z)
      (P Q: X -> Y -> Z -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <3= Q))
      (FORALL: Forall3 P xs ys zs):
    <<FORALL: Forall3 Q xs ys zs>>.
Proof. induction FORALL; econs; eauto. Qed.


Definition o_map A B (oa: option A) (f: A -> B): option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end.

Definition o_join A (a: option (option A)): option A :=
  match a with
  | Some a => a
  | None => None
  end.

Definition o_bind A B (oa: option A) (f: A -> option B): option B := o_join (o_map oa f).
Hint Unfold o_map o_join o_bind.

Definition curry2 A B C (f: A -> B -> C): (A * B) -> C := fun ab => f (fst ab) (snd ab).

Definition o_bind2 A B C (oab: option (A * B)) (f: A -> B -> option C) : option C :=
o_join (o_map oab (curry2 f)).

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

Lemma o_bind_ignore
      X Y
      (x: option X) (y: option Y):
    (do _ <- x ; y) = assertion(x) ; y.
Proof. des_ifs. Qed.

Ltac subst_locals := all ltac:(fun H => is_local_definition H; subst H).

Hint Unfold flip.

Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Tactic Notation "u" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Tactic Notation "u" := repeat (autounfold with *; cbn).
Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in *).

Lemma dependent_split_right
      (A B: Prop)
      (PA: A)
      (PB: <<HINTLEFT: A>> -> B):
    <<PAB: A /\ B>>.
Proof. eauto. Qed.

Lemma dependent_split_left
      (A B: Prop)
      (PA: <<HINTRIGHT: B>> -> A)
      (PB: B):
    <<PAB: A /\ B>>.
Proof. eauto. Qed.

Ltac dsplit_r := eapply dependent_split_right.
Ltac dsplit_l := eapply dependent_split_left.
Ltac dsplits :=
  repeat (let NAME := fresh "SPLITHINT" in try (dsplit_r; [|intro NAME])).

Locate des_sumbool.
(* TODO: Update Coqlib *)
Lemma proj_sumbool_is_false
      P
      (a: {P} + {~ P})
      (FALSE: ~ P):
    <<FALSE: proj_sumbool a = false>>.
Proof. unfold proj_sumbool. des_ifs. Qed.

Ltac des_sumbool :=
  repeat
    (unfold Datatypes.is_true, is_true in *;
     match goal with
     | [ H: proj_sumbool ?x = true |- _ ] => apply proj_sumbool_true in H
     | [ H: proj_sumbool ?x = false |- _ ] => apply proj_sumbool_false in H
     | [ H: true = proj_sumbool ?x |- _ ] => symmetry in H; apply proj_sumbool_true in H
     | [ H: false = proj_sumbool ?x |- _ ] => symmetry in H; apply proj_sumbool_false in H

     | [ |- proj_sumbool ?x = true ] => apply proj_sumbool_is_true
     | [ |- proj_sumbool ?x = false ] => apply proj_sumbool_is_false
     | [ |- true = proj_sumbool ?x ] => symmetry; apply proj_sumbool_is_true
     | [ |- false = proj_sumbool ?x ] => symmetry; apply proj_sumbool_is_false
     end).

Ltac is_prop H :=
  let ty := type of H in
  match type of ty with
  | Prop => idtac
  | _ => fail 1
  end.

Ltac all_prop TAC := all ltac:(fun H => tryif is_prop H then TAC H else idtac).

Ltac all_prop_inv := all_prop inv.
(* TODO: infinite loop when inv-ing "a+b = c+d". "progress" tactic does not help here. *)
(* TODO: add all_once, which captures only current hypotheses and apply TAC *)

Ltac all_rewrite := all ltac:(fun H => rewrite_all H).

Definition bar_True: Type := True.
Global Opaque bar_True.
Ltac bar :=
  let NAME := fresh
                "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" in
  assert(NAME: bar_True) by ss.

Ltac clear_until id :=
  on_last_hyp ltac:(fun id' => match id' with
                               | id => idtac
                               | _ => clear id'; clear_until id
                               end).

Ltac clear_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => clear id'; clear_until_bar
                               end).

Goal True -> True -> False.
  intro. bar. intro. clear_until H0. clear_until H. Undo 2. clear_until_bar. clear_tac.
Abort.



Definition aof_true: Type := True.
Global Opaque aof_true.

Ltac all_once_fast TAC :=
  generalize (I: aof_true);
  let name := fresh "bar" in
  assert(name: aof_true) by constructor; move name at top; revert_until name;
  repeat
    match goal with
    | [ |- aof_true -> _ ] => fail 1
    | _ => intro; on_last_hyp TAC
    end;
  intro; on_last_hyp ltac:(fun H => clear H);
  clear name.

Goal forall (a b c d e: bool) f,
    (negb true = false) -> (* IT SHOULD NOT RUN INF LOOP *)
    (negb false = true) ->
    (negb a = true) ->
    (negb b = true) ->
    (negb c = true) ->
    True -> (* SHOULD IGNORE THIS *)
    (negb d = true) ->
    (negb e = true) ->
    (0 :: 2 :: nil = f) -> (* SHOULD IGNORE THIS *)
    (negb (true && false) = true) -> True -> False.
Proof.
  i. revert H9. all_once_fast ltac:(fun H => try apply negb_true_iff in H).
Abort.

Ltac spc H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
    | [a0: A, a1: A, a2: A, a3: A |- _] => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
    | [a0: A, a1: A, a2: A |- _] => fail 2 "3 candidates!" a0 "," a1 "," a2
    | [a0: A, a1: A |- _] => fail 2 "2 candidates!" a0 "," a1
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

Ltac spcN n H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match type of n with
  | Z => idtac
  | _ => fail "second argument should be 'Z'"
  end;
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] =>
      match n with
      | - 5 => specialize (H a1)
      | - 4 => specialize (H a2)
      | - 3 => specialize (H a3)
      | - 2 => specialize (H a4)
      | - 1 => specialize (H a5)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | 4%Z => specialize (H a4)
      | 5%Z => specialize (H a5)
      | _ => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
      end
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] =>
      match n with
      | - 4 => specialize (H a1)
      | - 3 => specialize (H a2)
      | - 2 => specialize (H a3)
      | - 1 => specialize (H a4)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | 4%Z => specialize (H a4)
      | _ => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
      end
    | [a0: A, a1: A, a2: A, a3: A |- _] =>
      match n with
      | - 3 => specialize (H a1)
      | - 2 => specialize (H a2)
      | - 1 => specialize (H a3)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | _ => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
      end
    | [a0: A, a1: A, a2: A |- _] =>
      match n with
      | - 2 => specialize (H a1)
      | - 1 => specialize (H a2)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | _ => fail 2 "3 candidates!" a0 "," a1 "," a2
      end
    | [a0: A, a1: A |- _] =>
      match n with
      | - 1 => specialize (H a1)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | _ => fail 2 "2 candidates!" a0 "," a1
      end
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

Goal let my_nat := nat in
     let my_f := my_nat -> Prop in
     forall (f: my_f) (g: nat -> Prop) (x: nat) (y: my_nat), False.
  i. spc f. spc g.
Abort.

Lemma map_ext_strong
      X Y (f g: X -> Y) xs
      (EXT: forall x (IN: In x xs), f x = g x):
    map f xs = map g xs.
Proof.
  ginduction xs; ii; ss. exploit EXT; eauto. i; des.
  f_equal; ss. eapply IHxs; eauto.
Qed.

(* copied from : https://robbertkrebbers.nl/research/ch2o/tactics.html *)
Hint Extern 998 (_ = _) => f_equal : f_equal.
Hint Extern 999 => congruence : congruence.
Hint Extern 1000 => lia : lia.



Section ALIGN.

  Lemma align_refl
        x
        (NONNEG: x >= 0):
    <<ALIGN: align x x = x>>.
  Proof.
    destruct (Z.eqb x 0) eqn: T.
    { rewrite Z.eqb_eq in T. clarify. }
    rewrite Z.eqb_neq in T. red. unfold align.
    replace ((x + x - 1) / x) with 1.
    { extlia. }
    replace (x + x - 1) with (1 * x + (1 * x + (- 1))); cycle 1.
    { extlia. }
    rewrite Z.div_add_l; try eassumption.
    rewrite Z.div_add_l; try eassumption.
    replace (Z.div (Zneg xH) x) with (Zneg xH).
    { extlia. }
    destruct x; ss. clear - p. unfold Z.div. des_ifs. ginduction p; i; ss; des_ifs.
  Qed.

  Lemma align_zero: forall x, <<ALIGN: align x 0 = 0>>.
  Proof. i. unfold align. red. ss. extlia. Qed.

  Lemma align_divisible
        z y
        (DIV: (y | z))
        (NONNEG: y > 0):
      <<ALIGN: align z y = z>>.
  Proof.
    red. unfold align.
    replace ((z + y - 1) / y) with (z / y + (y - 1) / y); cycle 1.
    { unfold Z.divide in *. des. clarify. rewrite Z_div_mult; ss.
      replace (z0 * y + y - 1) with (z0 * y + (y - 1)); cycle 1.
      { extlia. }
      rewrite Z.div_add_l with (b := y); ss. extlia.
    }
    replace ((y - 1) / y) with 0; cycle 1.
    { erewrite Zdiv_small; ss. extlia. }
    unfold Z.divide in *. des. clarify. rewrite Z_div_mult; ss. rewrite Z.add_0_r. extlia.
  Qed.

  Lemma align_idempotence
        x y
        (NONNEG: y > 0):
      <<ALIGN: align (align x y) y = align x y>>.
  Proof. apply align_divisible; ss. apply align_divides; ss. Qed.

End ALIGN.

Hint Rewrite align_refl: align.
Hint Rewrite align_zero: align.
Hint Rewrite align_idempotence: align.

Ltac inv_all_once := all_once_fast ltac:(fun H => try inv H).
Ltac apply_all_once LEMMA :=  all_once_fast ltac:(fun H => try apply LEMMA in H).

Lemma find_map
      X Y (f: Y -> bool) (x2y: X -> Y) xs:
    find f (map x2y xs) = o_map (find (f <*> x2y) xs) x2y.
Proof. u. ginduction xs; ii; ss. des_ifs; ss. Qed.

Ltac revert_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => revert id'; revert_until_bar
                               end).

(* Ltac folder := all_once_fast ltac:(fun H => try (is_local_definition H; fold_all H)). *)
Ltac folder :=
  repeat multimatch goal with
         | [ H: _ |- _ ] => is_local_definition H; fold_all H
         end.

(* copied from promising/lib/Basic.v *)

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.

Notation rtc := (clos_refl_trans_1n _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt1n_refl rt1n_trans t_step.

Program Instance rtc_PreOrder A (R:A -> A -> Prop): PreOrder (rtc R).
Next Obligation.
  ii. revert H0. induction H; auto. i. exploit IHclos_refl_trans_1n; eauto.
Qed.

Lemma rtc_tail A R
      (a1 a3:A)
      (REL: rtc R a1 a3):
  (exists a2, rtc R a1 a2 /\ R a2 a3) \/
  (a1 = a3).
Proof.
  induction REL; auto. des; subst; left; eexists; splits; [|eauto| | eauto]; econs; eauto.
Qed.

Lemma rtc_implies A (R1 R2: A -> A -> Prop)
      (IMPL: R1 <2= R2):
  rtc R1 <2= rtc R2.
Proof.
  ii. induction PR; eauto. etrans; [|eauto]. econs 2; [|econs 1]. apply IMPL. auto.
Qed.

Lemma rtc_refl
      A R (a b:A)
      (EQ: a = b):
  rtc R a b.
Proof. subst. econs. Qed.

Lemma rtc_n1
      A R (a b c:A)
      (AB: rtc R a b)
      (BC: R b c):
  rtc R a c.
Proof. etrans; eauto. econs 2; eauto. Qed.

Lemma rtc_reverse
      A R (a b:A)
      (RTC: rtc R a b):
  rtc (fun x y => R y x) b a.
Proof. induction RTC; eauto. etrans; eauto. econs 2; eauto. Qed.

Lemma rtc_once
      A (R: A -> A -> Prop) a b
      (ONCE: R a b):
    rtc R a b.
Proof. econs; eauto. Qed.

Lemma Forall2_length
      X Y (P: X -> Y -> Prop) xs ys
      (FORALL2: Forall2 P xs ys):
    length xs = length ys.
Proof. ginduction FORALL2; ii; ss. extlia. Qed.

Ltac hexpl_aux H NAME :=
  let n := fresh NAME in
  first[hexploit H; eauto; check_safe; repeat intro n; des].
Tactic Notation "hexpl" constr(H) := hexpl_aux H H.
(* Tactic Notation "hexpl" constr(H) tactic(TAC) := hexpl_aux H TAC. *)
Tactic Notation "hexpl" constr(H) ident(NAME) := hexpl_aux H NAME.

(* 0 goal *)
Goal forall (mytt: unit) (H: unit -> False), False.
  i. hexpl H.
Qed.

(* 1 goal *)
Goal forall (H: nat -> False), False.
  i. hexpl H.
Abort.

Goal forall (H: nat -> nat -> False), False.
  i. Fail hexpl H.
Abort.

(* name *)
Goal forall (mytt: unit) (HH: unit -> (True -> True /\ True)), False.
  i. hexpl HH ABC. hexpl HH.
Abort.

Hint Extern 997 => extlia : extlia.

Hint Rewrite
     Z.add_0_l Z.add_0_r Z.add_assoc Z.add_simpl_l Z.add_simpl_r Z.add_opp_r Z.add_opp_l
     Z.mul_0_l Z.mul_0_r Z.mul_assoc
     Z.sub_0_r Z.sub_diag Z.sub_simpl_l Z.sub_simpl_r Z.sub_0_l
     Z.div_0_l Zdiv_0_r Z.div_1_r
     Z.mod_1_r Z.mod_0_l Z.mod_same Z.mod_mul Z.mod_mod
     Z.sub_add
  : zsimpl.

Ltac zsimpl := repeat autorewrite with zsimpl in *.

Ltac rp := first [erewrite f_equal8|
                  erewrite f_equal7|
                  erewrite f_equal6|
                  erewrite f_equal5|
                  erewrite f_equal4|
                  erewrite f_equal3|
                  erewrite f_equal2|
                  erewrite f_equal|
                  fail].

Ltac align_bool :=
  (repeat match goal with
          | [ H: true <> true |- _ ] => tauto
          | [ H: false <> false |- _ ] => tauto
          | [ H: true <> _ |- _ ] => symmetry in H
          | [ H: false <> _ |- _ ] => symmetry in H
          | [ H: _ <> true |- _ ] => apply not_true_is_false in H
          | [ H: _ <> false |- _ ] => apply not_false_is_true in H
          end).
Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Definition range (lo hi: Z): Z -> Prop := fun x => lo <= x < hi. (* TODO: Use Notation instead *)
Hint Unfold range.

Ltac sym := symmetry.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.

Ltac eapply_all_once LEMMA :=
  all_once_fast ltac:(fun H => try eapply LEMMA in H; try eassumption; check_safe).

Ltac Nsimpl := all_once_fast ltac:(fun H => try apply NNPP in H; try apply not_and_or in H; try apply not_or_and in H).

Ltac hexploit1 H :=
  match goal with
  | [ H: ?A -> ?B |- _ ] =>
    apply (@mp B); [apply H|clear H; intro H]
  end.

Lemma rev_nil
      X (xs: list X)
      (NIL: rev xs = []):
    xs = [].
Proof.
  generalize (f_equal (@length _) NIL). i. ss. destruct xs; ss. rewrite app_length in *. ss. extlia.
Qed.

Fixpoint last_opt X (xs: list X): option X :=
  match xs with
  | [] => None
  | [hd] => Some hd
  | hd :: tl => last_opt tl
  end.

Lemma last_none
      X (xs: list X)
      (NONE: last_opt xs = None):
    xs = [].
Proof. ginduction xs; ii; ss. des_ifs. spc IHxs. ss. Qed.

Lemma last_some
      X (xs: list X) x
      (SOME: last_opt xs = Some x):
    exists hds, xs = hds ++ [x].
Proof.
  ginduction xs; ii; ss. des_ifs.
  { exists nil. ss. }
  exploit IHxs; eauto. i; des. rewrite H. exists (a :: hds). ss.
Qed.

Lemma forall2_eq
      X Y (P: X -> Y -> Prop) xs ys:
    list_forall2 P xs ys <-> Forall2 P xs ys.
Proof. split; i; ginduction xs; ii; ss; inv H; ss; econs; eauto. Qed.

(* Fixpoint zip X Y Z (f: option X -> option Y -> Z) (xs: list X) (ys: list Y): list Z := *)
(*   match xs, ys with *)
(*   | [], [] => [] *)
(*   | xhd :: xtl, [] => f (Some xhd) None :: zip f xtl [] *)
(*   | [], yhd :: ytl => f None (Some yhd) :: zip f [] ytl *)
(*   | xhd :: xtl, yhd :: ytl => f (Some xhd) (Some yhd) :: zip f xtl ytl *)
(*   end *)
(* . *)

Fixpoint zip X Y Z (f: X -> Y -> Z) (xs: list X) (ys: list Y): list Z :=
  match xs, ys with
  | xhd :: xtl, yhd :: ytl => f xhd yhd :: zip f xtl ytl
  | _, _ => []
  end.

Lemma zip_length
      X Y Z (f: X -> Y -> Z) xs ys:
    length (zip f xs ys) = min (length xs) (length ys).
Proof. ginduction xs; ii; ss. des_ifs. ss. rewrite IHxs. extlia. Qed.

Lemma in_zip_iff
      X Y Z (f: X -> Y -> Z) xs ys z:
    (<<ZIP: In z (zip f xs ys)>>)
    <-> (exists x y, <<F: f x y = z>> /\ exists n, <<X: nth_error xs n = Some x>> /\ <<Y: nth_error ys n = Some y>>).
Proof.
  split; ii.
  - ginduction xs; ii; ss. des_ifs. ss. des; ss.
    + esplits; eauto; try instantiate (1 := 0%nat); ss.
    + exploit IHxs; eauto. i; des. esplits; eauto; try instantiate (1:= (1+n)%nat); ss.
  - des. ginduction n; ii; ss.
    { des_ifs. ss. left; ss. }
    des_ifs. ss. exploit (@IHn _ _ _ f); eauto.
Qed.

Global Opaque Z.mul.

Lemma unit_ord_wf: well_founded (bot2: unit -> unit -> Prop).
Proof. ii. induction a; ii; ss. Qed.

Ltac et:= eauto.

Require Import Program.

Lemma f_equal_h
      X1 X2 Y1 Y2 (f1: X1 -> Y1) (f2: X2 -> Y2) x1 x2
      (TYPX: X1 = X2)
      (FUNC: f1 ~= f2)
      (ARG: x1 ~= x2)
      (TYPY: Y1 = Y2): (* Do we need this? *)
    f1 x1 ~= f2 x2.
Proof. subst. subst. ss. Qed.

Lemma f_equal_hr
      X1 X2 Y (f1: X1 -> Y) (f2: X2 -> Y) x1 x2
      (FUNC: f1 ~= f2)
      (TYP: X1 = X2)
      (ARG: x1 ~= x2):
    f1 x1 = f2 x2.
Proof. eapply JMeq_eq. eapply f_equal_h; eauto. Qed.

Lemma f_equal_rh
      X Y1 Y2 (f1: X -> Y1) (f2: X -> Y2) x
      (FUNC: f1 ~= f2)
      (TYP: Y1 = Y2):
    f1 x ~= f2 x.
Proof. eapply f_equal_h; eauto. Qed.

Lemma cons_app
      X xhd (xtl: list X):
    xhd :: xtl = [xhd] ++ xtl.
Proof. ss. Qed.

Lemma list_map_injective A B (f: A -> B)
      (INJECTIVE: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
      l0 l1
      (LEQ: map f l0 = map f l1):
    l0 = l1.
Proof.
  revert l1 LEQ. induction l0; i; ss; destruct l1; ss. inv LEQ. f_equal; eauto.
Qed.

Lemma Forall_in_map A B al (R: B -> Prop) (f: A -> B)
      (RMAP: forall a (IN: In a al), R (f a)):
    Forall R (map f al).
Proof. induction al; econs; ss; eauto. Qed.

Lemma Forall2_in_map A B al (R: B -> A -> Prop) (f: A -> B)
      (RMAP: forall a (IN: In a al), R (f a) a):
    list_forall2 R (map f al) al.
Proof. induction al; econs; ss; eauto. Qed.

Lemma eq_Forall2_eq A (al0 al1 : list A):
    list_forall2 eq al0 al1 <-> al0 = al1.
Proof.
  revert al1. induction al0; ss; i; split; i; eauto; inv H; try econs; eauto.
  - f_equal. eapply IHal0. eauto.
  - eapply IHal0. eauto.
Qed.

Lemma list_forall2_lift A B (R0 R1: A -> B -> Prop) al bl
      (SAME: forall a (IN: In a al) b, R0 a b -> R1 a b)
      (FORALL: list_forall2 R0 al bl):
    list_forall2 R1 al bl.
Proof.
  generalize dependent bl. revert SAME. induction al; ss; i; inv FORALL; econs; eauto.
Qed.

Lemma Forall_map A B la (R: B -> Prop) (f: A -> B)
      (RMAP: forall a, R (f a)):
    Forall R (map f la).
Proof. induction la; econs; ss. Qed.

Lemma f_hequal A (B : A -> Type) (f : forall a, B a)
      a1 a2 (EQ : a1 = a2):
    f a1 ~= f a2.
Proof. destruct EQ. econs. Qed.

Lemma list_forall2_rev A B R (la: list A) (lb: list B)
      (FORALL: list_forall2 R la lb):
    list_forall2 (flip R) lb la.
Proof.
  generalize dependent lb. induction la; i; eauto; inv FORALL; econs; eauto.
Qed.

Ltac uo := unfold o_bind, o_map, o_join in *.

Lemma some_injective
      X (x0 x1: X)
      (EQ: Some x0 = Some x1):
    x0 = x1.
Proof. injection EQ. auto. Qed.

Ltac align_opt :=
  repeat
    match goal with
    (* remove trivial things *)
    | H: Some ?x = Some ?y |- _ => rewrite some_injective in H
    | H: Some _ = None |- _ => by (inversion H)
    | H: None = Some _ |- _ => by (inversion H)
    | H: None = None |- _ => clear H
    (* align *)
    | H: Some _ = ?x |- _ => symmetry in H
    | H: None = ?x |- _ => symmetry in H
    end.
(* Ltac clarify0 := repeat (align_opt; progress clarify). *)

Fixpoint list_diff X (dec: (forall x0 x1, {x0 = x1} + {x0 <> x1})) (xs0 xs1: list X): list X :=
  match xs0 with
  | [] => []
  | hd :: tl =>
    if in_dec dec hd xs1
    then list_diff dec tl xs1
    else hd :: list_diff dec tl xs1
  end.

Lemma list_diff_spec
      X dec (xs0 xs1 xs2: list X)
      (DIFF: list_diff dec xs0 xs1 = xs2):
    <<SPEC: forall x0, In x0 xs2 <-> (In x0 xs0 /\ ~ In x0 xs1)>>.
Proof.
  subst. split; i.
  - ginduction xs0; ii; des; ss. des_ifs.
    { exploit IHxs0; et. i; des. esplits; et. }
    ss. des; clarify.
    { tauto. }
    exploit IHxs0; et. i; des. esplits; et.
  - ginduction xs0; ii; des; ss. des; clarify; des_ifs; ss; try tauto; exploit IHxs0; et.
Qed.

Fixpoint last_option X (xs: list X): option X :=
  match xs with
  | [] => None
  | hd :: nil => Some hd
  | hd :: tl => last_option tl
  end.
Lemma not_ex_all_not
      U (P: U -> Prop)
      (NEX: ~ (exists n : U, P n)):
    <<NALL: forall n : U, ~ P n>>.
Proof. eauto. Qed.

(* Remark: if econs/econsr gives different goal, at least 2 econs is possible *)
Ltac econsr :=
  first
    [ econstructor 16
     |econstructor 15
     |econstructor 14
     |econstructor 13
     |econstructor 12
     |econstructor 11
     |econstructor 10
     |econstructor  9
     |econstructor  8
     |econstructor  7
     |econstructor  6
     |econstructor  5
     |econstructor  4
     |econstructor  3
     |econstructor  2
     |econstructor  1].

Ltac it TERM := instantiate (1:=TERM).
Ltac itl TERM :=
  first[ instantiate (10:=TERM)|
         instantiate (9:=TERM)|
         instantiate (8:=TERM)|
         instantiate (7:=TERM)|
         instantiate (6:=TERM)|
         instantiate (5:=TERM)|
         instantiate (4:=TERM)|
         instantiate (3:=TERM)|
         instantiate (2:=TERM)|
         instantiate (1:=TERM)|
         fail].

Lemma NoDup_norepet
      X (xs: list X):
    NoDup xs <-> list_norepet xs.
Proof. split; induction 1; econs; ss. Qed.

Ltac swapname NAME1 NAME2 :=
  let tmp := fresh "TMP" in
  rename NAME1 into tmp; rename NAME2 into NAME1; idtac NAME1; rename tmp into NAME2
.

Global Program Instance top2_PreOrder X: PreOrder (top2: X -> X -> Prop).

Lemma app_eq_inv
      A (x0 x1 y0 y1: list A)
      (EQ: x0 ++ x1 = y0 ++ y1)
      (LEN: (length x0) = (length y0)):
    x0 = y0 /\ x1 = y1.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify. exploit IHx0; eauto. i; des. clarify.
Qed.

Lemma pos_elim_succ: forall p,
    <<ONE: p = 1%positive>> \/
    <<SUCC: exists q, (Pos.succ q) = p>>.
Proof. i. hexploit (Pos.succ_pred_or p); eauto. i; des; ss; eauto. Qed.

Lemma ple_elim_succ
      p q
      (PLE: Ple p q):
    <<EQ: p = q>> \/
    <<SUCC: Ple (Pos.succ p) q>>.
Proof.
  revert_until p. pattern p. apply Pos.peano_ind; clear p; i.
  { hexploit (pos_elim_succ q); eauto. i. des; clarify; eauto. right. r. extlia. }
  hexploit (pos_elim_succ q); eauto. i. des; clarify.
  { left. extlia. }
  exploit H; eauto.
  { it q0. extlia. }
  i; des; clarify.
  - left. r. extlia.
  - right. r. extlia.
Qed.

Section FLIPS.

Definition flip2 A B C D: (A -> B -> C -> D) -> A -> C -> B -> D. intros; eauto. Defined.
Definition flip3 A B C D E: (A -> B -> C -> D -> E) -> A -> B -> D -> C -> E. intros; eauto. Defined.
Definition flip4 A B C D E F: (A -> B -> C -> D -> E -> F) -> A -> B -> C -> E -> D -> F. intros; eauto. Defined.

Variable A B C D: Type.
Variable f: A -> B -> C -> D.

Let put_dummy_arg_without_filp A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (fun a _ => f a).
Let put_dummy_arg1 A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (flip (fun _ => f)).
Let put_dummy_arg21 A DUMMY B C: (A -> B -> C) -> (A -> DUMMY -> B -> C) := fun f => (flip (fun _ => f)).
Let put_dummy_arg22 A B DUMMY C: (A -> B -> C) -> (A -> B -> DUMMY -> C) :=
  fun f => (flip2 (flip (fun _ => f))).

End FLIPS.
Hint Unfold flip2 flip3 flip4.

Definition DUMMY_PROP := True.
Hint Unfold DUMMY_PROP.

Ltac clarify_meq :=
  repeat
    match goal with
    | [ H0: ?A m= ?B |- _ ] => inv H0
    | [ H0: ?A = ?A -> _ |- _ ] => exploit H0; eauto; check_safe; intro; des; clear H0
    end;
    clarify.

Local Transparent list_nth_z.
Lemma list_nth_z_eq
      A (l: list A) z
      (POS: 0 <= z):
    list_nth_z l z = List.nth_error l (Z.to_nat z).
Proof.
  ginduction l; ii; ss.
  - destruct ((Z.to_nat z)); ss.
  - des_ifs. destruct (Z.to_nat) eqn:T; ss.
    + destruct z; ss. destruct p; ss. extlia.
    + rewrite IHl; ss; eauto; try extlia. rewrite Z2Nat.inj_pred. rewrite T. ss.
Qed.
Local Opaque list_nth_z.

Lemma list_nth_z_firstn
      (A:Type) (l: list A) n x
      (T:list_nth_z l n = Some x):
      list_nth_z (firstn (Z.to_nat (n + 1)) l) n = Some x.
Proof.
  exploit list_nth_z_range; eauto. intro RANGE; des.
  rewrite list_nth_z_eq in *; try extlia. rewrite Z2Nat.inj_add; ss. rewrite Pos2Nat.inj_1. rewrite Nat.add_comm.
  exploit nth_error_Some; et. intro X. rewrite T in X. des.
  exploit X; eauto. { ss. } intro Y.
  erewrite <- (firstn_skipn (1 + (Z.to_nat n)) l) in T.
  rewrite nth_error_app1 in T; eauto. rewrite firstn_length. extlia.
Qed.

Lemma firstn_S
      (A: Type) (l: list A) n:
      (le (Datatypes.length l) n /\ firstn (n + 1) l = firstn n l)
    \/ (lt n (Datatypes.length l) /\ exists x, firstn (n + 1) l = (firstn n l) ++ [x]).
Proof.
  ginduction l; i; try by (left; do 2 rewrite firstn_nil; split; ss; lia). destruct n.
  { right. ss. split; try lia. eauto. }
  specialize (IHl n). ss. des.
  - left. split; try lia. rewrite IHl0. ss.
  - right. split; try lia. rewrite IHl0. eauto.
Qed.

Lemma map_firstn
      (A B: Type) (l: list A) (f: A -> B) n:
    map f (firstn n l) = firstn n (map f l).
Proof.
  ginduction l; ss; i.
  { ss. do 2 rewrite firstn_nil. ss. }
  destruct n; ss. rewrite IHl. ss.
Qed.

Lemma list_nth_z_map
      (A B: Type) (l: list A) n x (f: A -> B)
      (NTH: list_nth_z l n = Some x):
    list_nth_z (map f l) n = Some (f x).
Proof.
  exploit list_nth_z_range; eauto. intro RANGE; des.
  rewrite list_nth_z_eq in *; try extlia. rewrite list_map_nth in *. rewrite NTH. ss.
Qed.

Lemma tail_In A l0 l1 (a: A)
      (IN: In a l0)
      (TAIL: is_tail l0 l1):
    In a l1.
Proof. induction TAIL; auto. econs 2; eauto. Qed.

Lemma Forall2_apply_Forall2 A B C D (f: A -> C) (g : B -> D)
      (P: A -> B -> Prop) (Q: C -> D -> Prop)
      la lb
      (FORALL: Forall2 P la lb)
      (IMPLY: forall a b (INA: In a la) (INB: In b lb),
          P a b -> Q (f a) (g b)):
    Forall2 Q (map f la) (map g lb).
Proof.
  ginduction la; ss; i; inv FORALL; ss. econs; eauto.
Qed.

Lemma forall2_in_exists A B (P: A -> B -> Prop) la lb
      (ALL: list_forall2 P la lb)
      a
      (IN: In a la):
    exists b, (<<IN: In b lb>>) /\ (<<SAT: P a b>>).
Proof.
  revert la lb ALL a IN. induction la; ss.
  i. inv ALL. des.
  - clarify. esplits; eauto. econs. auto.
  - eapply IHla in H3; eauto. des. esplits; eauto. econs 2. auto.
Qed.
