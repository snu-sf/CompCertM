Require Import Program.
Require Import CoqlibC.
Require Import Any.

Set Implicit Arguments.



Class LeibEq (A B: Type) := { leibeq: A = B }.
Arguments LeibEq: clear implicits.
Definition cast_sigT (a: Any) (B: Type) `{LeibEq (projT1 a) B}: B.
  rewrite <- leibeq. destruct a. simpl. auto.
Defined.
(* Global Program Instance LeibEq_rev (A B: Type) `{LeibEq A B}: LeibEq B A. *)
(* Next Obligation. rewrite leibeq. eauto. Defined. *)
Program Definition LeibEq_rev (A B: Type) (LEQ: LeibEq A B): LeibEq B A.
Proof. rewrite leibeq. econstructor. refl. Defined.
Definition cast (A B: Type) `{LeibEq A B} (a: A): B. rewrite <- leibeq. apply a. Defined.
Global Program Instance LeibEq_refl (A: Type): LeibEq A A.

Lemma cast_sigT_existT
      (x: Any) X
      (TY: LeibEq (projT1 x) X)
  :
    x = existT id _ (@cast_sigT x X TY)
.
Proof.
  destruct x. destruct TY. ss. clarify.
Qed.

Lemma cast_sigT_eq
      Y (x: Any) (y: Y)
      (JMEQ: projT2 x ~= y)
      (LEIBEQ: LeibEq (projT1 x) Y)
  :
    cast_sigT x = y
.
Proof.
  unfold cast_sigT. unfold eq_rect_r. ss. des_ifs. ss.
  unfold eq_rect. des_ifs.
Qed.

Lemma cast_sigT_proj
      Y (x: Any) (y: Y)
      (LEIBEQ: LeibEq (projT1 x) Y)
      (EQ: cast_sigT x = y)
  :
      <<JMEQ: projT2 x ~= y>>
.
Proof.
  unfold cast_sigT in *. ss. des_ifs. ss. unfold eq_rect. des_ifs.
Qed.

Lemma cast_elim
      A LEQ (a: A)
  :
    <<EQ: (@cast A A LEQ a) = a>>
.
Proof.
  r. destruct LEQ.
  unfold cast. ss.
  unfold eq_rect. dependent destruction leibeq0. ss.
Qed.

Lemma unit_JMeq
      X (x: X)
      (TY: X = unit)
  :
    <<EQ: x ~= tt>>
.
Proof.
  revert x. rewrite TY.
  ii. clarify.
Qed.
