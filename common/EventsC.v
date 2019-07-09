Require Import String.
Require Import CoqlibC.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
(** newly added **)
Require Export Events.

Set Implicit Arguments.



Lemma eventval_valid_le
      se_small ev se_big
      (VALID: eventval_valid se_small ev)
      (LE: se_small.(Senv.public_symbol) <1= se_big.(Senv.public_symbol)):
    <<VALID: eventval_valid se_big ev>>.
Proof. u in *. unfold eventval_valid in *. des_ifs. erewrite LE; eauto. Qed.

Lemma match_traces_le
      se_small tr0 tr1 se_big
      (MATCH: match_traces se_small tr0 tr1)
      (LE: se_small.(Senv.public_symbol) <1= se_big.(Senv.public_symbol)):
    <<MATCH: match_traces se_big tr0 tr1>>.
Proof. u in *. inv MATCH; econs; eauto; eapply eventval_valid_le; eauto. Qed.

Ltac inv_match_traces :=
  match goal with
  | [ H: match_traces _ _ _ |- _ ] => inv H
  end.
