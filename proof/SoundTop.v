
Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

(* Require Import IntegersC LinkingC. *)
(* Require Import SimSymb Skeleton Mod ModSem. *)
Require Import ModSem Skeleton.
(* Require SimSymbId. *)
(* Require Import SimMem. *)

Require Import Sound.
Require Import SemiLattice.
Require Import FinFun.

Set Implicit Arguments.


(* TODO: move to CoqlibC *)
Global Program Instance top2_PreOrder X: PreOrder (top2: X -> X -> Prop).

Global Program Instance Top: Sound.class := {
  t := unit;
  le := top2;
  get_greatest := top3;
  args := top2;
  retv := top2;
  mle := top3;
  skenv := top3;
}
.
Next Obligation.
  destruct su_gr0, su_gr1; ss.
Qed.
Next Obligation.
  esplits; eauto.
Qed.
(* Next Obligation. *)
  (* destruct su_gr0, su_gr1; ss. *)
(* Qed. *)
Next Obligation.
  esplits; eauto. econs; eauto.
Qed.
Next Obligation.
  esplits; eauto.
Qed.


Require Import Preservation.

Definition sound_state {STATE: Type}: Sound.t -> mem -> STATE -> Prop := top3.

Lemma sound_state_local_preservation
      ms
  :
    <<PRSV: local_preservation ms sound_state>>
.
Proof.
  econs; ii; ss; eauto.
Qed.
