Require Import Classical.
Require Import ClassicalEpsilon.
Require Import CoqlibC.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
(** newly added **)
Require Export Behaviors.
Require Import Simulation.

Set Implicit Arguments.


Definition improves (L1 L2: semantics): Prop := forall
    beh2
    (BEH: program_behaves L2 beh2)
  ,
    exists beh1, <<BEH: program_behaves L1 beh1>> /\ <<IMPRV: behavior_improves beh1 beh2>>
.

Global Program Instance improves_PreOrder: PreOrder improves.
Next Obligation.
  ii. esplits; eauto. eapply behavior_improves_refl.
Qed.
Next Obligation.
  ii. r in H. r in H0. repeat spc H0. des. specialize (H _ BEH0). des.
  esplits; eauto. eapply behavior_improves_trans; eauto.
Qed.

Lemma bsim_improves
      L1 L2
      (BSIM: backward_simulation L1 L2)
  :
    <<IMRPV: improves L1 L2>>
.
Proof.
  ii.
  eapply backward_simulation_behavior_improves; eauto.
  eapply backward_to_compcert_backward_simulation; eauto.
Qed.

