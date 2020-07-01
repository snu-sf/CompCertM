Require Import sflib CoqlibC.
Require Import Program.
Require Import ClassicalDescription EquivDec.

Set Implicit Arguments.
Set Universe Polymorphism.



Inductive Any: Type :=
  Any_intro : forall {A:Type} {x:A}, Any.
(* Arguments Any [A P]. *)

Definition downcast {T: Type} (a: Any): option T.
destruct a.
destruct (excluded_middle_informative (A = T)).
- subst. apply Some. assumption.
- apply None.
Defined.

Definition upcast {T} (a: T): Any := @Any_intro _ a.

Arguments Any_intro {A} x.

Lemma upcast_downcast
      T (a: T)
  :
    downcast (upcast a) = Some a
.
Proof.
  cbn. des_ifs. dependent destruction e. cbn. eauto.
Qed.

Lemma unfold_up
      (a: Any)
  :
    <<CAST: exists T (t: T), a = upcast t>>
.
Proof.
  unfold upcast in *. dependent destruction a. ss. eauto.
Qed.

Lemma unfold_down
      (a: Any)
  :
    <<CAST: exists T (t: T), downcast a = Some t>>
.
Proof.
  unfold downcast in *. destruct a. esplits. des_ifs. dependent destruction e. ss.
Qed.

Lemma upcast_downcast_iff
      (a: Any) T (t: T)
  :
    <<UPCAST: a = upcast t>> <-> <<DOWNCAST: downcast a = Some t>>
.
Proof.
  split; ii; des.
  - clarify. rewrite upcast_downcast. ss.
  - destruct a; ss. des_ifs. cbn in *. clarify.
Qed.

Definition Any_dec (a0 a1: Any): {a0=a1} + {a0<>a1}.
  destruct a0, a1.
  destruct (excluded_middle_informative (A = A0)).
  - clarify.
    destruct (excluded_middle_informative (x = x0)).
    + clarify. left. ss.
    + right. ii. simpl_depind. clarify.
  - right. ii. simpl_depind.
Defined.

Goal (upcast tt = upcast 0 -> False).
  ii. Fail timeout 1 clarify.
Abort.

Lemma upcast_inj
      A B (a: A) (b: B)
      (EQ: upcast a = upcast b)
  :
    <<EQ: A = B>> /\ <<EQ: a ~= b>>
.
Proof. unfold upcast in *. simpl_depind. ss. Qed.

Lemma upcast_eta
      A B a b
      (EQTY: A = B)
      (EQVAL: a ~= b)
  :
    <<EQ: @upcast A a = @upcast B b>>
.
Proof.
  clarify. eapply JMeq_eq in EQVAL. clarify.
Qed.


(* Global Opaque upcast downcast. *)

(* Goal (upcast tt = upcast 0 -> False). *)
(*   ii. clarify. (* at least it terminates *) *)
(*   Undo 1. *)
(*   apply_all_once upcast_inj; des. *)
(* Abort. *)

Ltac clarify := repeat des_u;
                repeat match goal with
                       | [ H: upcast ?A = upcast ?B |- _ ] => apply upcast_inj in H; desH H
                       end; sflib.clarify.

Global Opaque upcast.
Global Opaque downcast.

