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

Lemma func_ext1
      X0 Y0
      (P Q: X0 -> Y0)
      (EQ: all1 (P =1= Q))
  :
    <<EQ: P = Q>>
.
Proof. apply Axioms.functional_extensionality. ii; ss. Qed.

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

Lemma o_bind_ignore
      X Y
      (x: option X) (y: option Y)
  :
    (do _ <- x ; y) = assertion(x) ; y
.
Proof. des_ifs. Qed.

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
     end)
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
  clear name
.

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
    (negb (true && false) = true) -> True -> False
.
Proof.
  i. revert H9.
  all_once_fast ltac:(fun H => try apply negb_true_iff in H).
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
  end
.

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
  end
.

Goal let my_nat := nat in
     let my_f := my_nat -> Prop in
     forall (f: my_f) (g: nat -> Prop) (x: nat) (y: my_nat), False.
  i.
  spc f. spc g.
Abort.

Lemma map_ext_strong
      X Y
      (f g: X -> Y)
      xs
      (EXT: forall x (IN: In x xs), f x = g x)
  :
    map f xs = map g xs
.
Proof.
  ginduction xs; ii; ss.
  exploit EXT; eauto. i; des.
  f_equal; ss.
  eapply IHxs; eauto.
Qed.

(* copied from : https://robbertkrebbers.nl/research/ch2o/tactics.html *)
Hint Extern 998 (_ = _) => f_equal : f_equal.
Hint Extern 999 => congruence : congruence.
Hint Extern 1000 => lia : lia.



Section ALIGN.

  Lemma align_refl
        x
        (NONNEG: x >= 0)
  :
    <<ALIGN: align x x = x>>
  .
  Proof.
    destruct (Z.eqb x 0) eqn: T.
    { rewrite Z.eqb_eq in T. clarify. }
    rewrite Z.eqb_neq in T.
    red.
    unfold align.
    replace ((x + x - 1) / x) with 1.
    { xomega. }
    replace (x + x - 1) with (1 * x + (1 * x + (- 1))); cycle 1.
    { xomega. }
    rewrite Z.div_add_l; try eassumption.
    rewrite Z.div_add_l; try eassumption.
    replace (Z.div (Zneg xH) x) with (Zneg xH).
    { xomega. }
    destruct x; ss.
    clear - p.
    unfold Z.div. des_ifs.
    ginduction p; i; ss; des_ifs.
  Qed.

  Lemma align_zero
        x
    :
      <<ALIGN: align x 0 = 0>>
  .
  Proof.
    unfold align. red. ss.
    xomega.
  Qed.

  Lemma align_divisible
        z y
        (DIV: (y | z))
        (NONNEG: y > 0)
    :
      <<ALIGN: align z y = z>>
  .
  Proof.
    red.
    unfold align.
    replace ((z + y - 1) / y) with (z / y + (y - 1) / y); cycle 1.
    {
      unfold Z.divide in *. des. clarify.
      rewrite Z_div_mult; ss.
      replace (z0 * y + y - 1) with (z0 * y + (y - 1)); cycle 1.
      { xomega. }
      rewrite Z.div_add_l with (b := y); ss.
      xomega.
    }
    replace ((y - 1) / y) with 0; cycle 1.
    { erewrite Zdiv_small; ss. xomega. }
    unfold Z.divide in *. des. clarify.
    rewrite Z_div_mult; ss.
    rewrite Z.add_0_r.
    xomega.
  Qed.

  Lemma align_idempotence
        x y
        (NONNEG: y > 0)
    :
      <<ALIGN: align (align x y) y = align x y>>
  .
  Proof.
    apply align_divisible; ss.
    apply align_divides; ss.
  Qed.

End ALIGN.

Hint Rewrite align_refl: align.
Hint Rewrite align_zero: align.
Hint Rewrite align_idempotence: align.

Ltac inv_all_once := all_once_fast ltac:(fun H => try inv H).
Ltac apply_all_once LEMMA :=  all_once_fast ltac:(fun H => try apply LEMMA in H).

Lemma find_map
      X Y (f: Y -> bool) (x2y: X -> Y)
      xs
  :
    find f (map x2y xs) = o_map (find (f <*> x2y) xs) x2y
.
Proof.
  u. ginduction xs; ii; ss.
  des_ifs; ss.
Qed.

Ltac revert_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => revert id'; revert_until_bar
                               end)
.

(* Ltac folder := all_once_fast ltac:(fun H => try (is_local_definition H; fold_all H)). *)
Ltac folder :=
  repeat multimatch goal with
         | [ H: _ |- _ ] => is_local_definition H; fold_all H
         end
.

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
  ii. revert H0. induction H; auto. i.
  exploit IHclos_refl_trans_1n; eauto.
Qed.

Lemma rtc_tail A R
      (a1 a3:A)
      (REL: rtc R a1 a3):
  (exists a2, rtc R a1 a2 /\ R a2 a3) \/
  (a1 = a3).
Proof.
  induction REL; auto. des; subst.
  - left. eexists. splits; [|eauto].
    econs; eauto.
  - left. eexists. splits.
    econs. eauto.
Qed.

Lemma rtc_implies A (R1 R2: A -> A -> Prop)
      (IMPL: R1 <2= R2):
  rtc R1 <2= rtc R2.
Proof.
  ii. induction PR; eauto.
  etrans; [|eauto]. econs 2; [|econs 1].
  apply IMPL. auto.
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
Proof.
  etrans; eauto. econs 2; eauto.
Qed.

Lemma rtc_reverse
      A R (a b:A)
      (RTC: rtc R a b):
  rtc (fun x y => R y x) b a.
Proof.
  induction RTC; eauto.
  etrans; eauto. econs 2; eauto.
Qed.

Lemma rtc_once
      A (R: A -> A -> Prop)
      a b
      (ONCE: R a b)
  :
    rtc R a b
.
Proof.
  econs; eauto.
Qed.

Lemma Forall2_length
      X Y (P: X -> Y -> Prop) xs ys
      (FORALL2: Forall2 P xs ys)
  :
    length xs = length ys
.
Proof.
  ginduction FORALL2; ii; ss.
  xomega.
Qed.

Ltac hexpl_aux H NAME :=
  let n := fresh NAME in
  first[hexploit H; eauto; check_safe; repeat intro n; des]
.
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
  i. hexpl HH ABC.
  hexpl HH.
Abort.

Hint Extern 997 => xomega : xomega.

Hint Rewrite
     Z.add_0_l Z.add_0_r Z.add_assoc Z.add_simpl_l Z.add_simpl_r Z.add_opp_r Z.add_opp_l
     Z.mul_0_l Z.mul_0_r Z.mul_assoc
     Z.sub_0_r Z.sub_diag Z.sub_simpl_l Z.sub_simpl_r Z.sub_0_l
     Z.div_0_l Zdiv_0_r Z.div_1_r
     Z.mod_1_r Z.mod_0_l Z.mod_same Z.mod_mul Z.mod_mod
     Z.sub_add 
  : zsimpl
.

Ltac zsimpl := repeat autorewrite with zsimpl in *.

Ltac rp := first [erewrite f_equal8|
                  erewrite f_equal7|
                  erewrite f_equal6|
                  erewrite f_equal5|
                  erewrite f_equal4|
                  erewrite f_equal3|
                  erewrite f_equal2|
                  erewrite f_equal|
                  fail]
.

Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Definition range (lo hi: Z): Z -> Prop := fun x => lo <= x < hi. (* TODO: Use Notation instead *)
Hint Unfold range.

Ltac sym := symmetry.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.

Ltac eapply_all_once LEMMA :=
  all_once_fast ltac:(fun H => try eapply LEMMA in H; try eassumption; check_safe)
.

Ltac Nsimpl := all_once_fast ltac:(fun H => try apply NNPP in H; try apply not_and_or in H; try apply not_or_and in H).

Ltac hexploit1 H :=
  match goal with
  | [ H: ?A -> ?B |- _ ] =>
    apply (@mp B); [apply H|clear H; intro H]
  end
.
