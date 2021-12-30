Require Import CoqlibC.
From compcertr Require Import
     Memory
     Values
     Maps
     Events
     Globalenvs
     sflib.
Require Import RelationClasses.
Require Import FSets.
From compcertr Require Import
     Ordered
     AST
     Integers.

(* Require Import IntegersC LinkingC. *)
(* Require Import SimSymb Skeleton Mod ModSem. *)
Require Import ModSem Skeleton.
(* Require SimSymbId. *)
(* Require Import SimMem. *)

Require Import Sound.
Require Import SemiLattice.
Require Import FinFun.

Set Implicit Arguments.


Global Program Instance Top: Sound.class := {
  t := unit;
  lepriv := top2;
  wf := top1;
  val := top2;
  mem := top2;
  mle := top3;
  skenv := top3;
}.
(* Next Obligation. *)
  (* destruct su_gr0, su_gr1; ss. *)
(* Qed. *)
Next Obligation. esplits; eauto. econs; eauto. Qed.
Next Obligation. esplits; eauto. Qed.


Require Import Preservation.

Definition sound_state {STATE: Type}: Sound.t -> mem -> STATE -> Prop := top3.

Lemma sound_state_local_preservation: forall ms,
    <<PRSV: local_preservation ms sound_state>>.
Proof.
  econs; ii; ss; eauto.
  { esplits; eauto. rr. des_ifs. esplits; eauto. rr. rewrite Forall_forall. ii; ss. }
  { esplits; eauto. rr. des_ifs. }
Unshelve.
  all: ss.
Qed.
