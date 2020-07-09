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


Definition improves (L1 L2: semantics): Prop := forall beh2
    (BEH: program_behaves L2 beh2),
    exists beh1, <<BEH: program_behaves L1 beh1>> /\ <<IMPRV: behavior_improves beh1 beh2>>.

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
      (BSIM: backward_simulation L1 L2):
    <<IMRPV: improves L1 L2>>.
Proof.
  ii. eapply backward_simulation_behavior_improves; eauto.
  eapply backward_to_compcert_backward_simulation; eauto.
Qed.

Lemma back_propagate_ub_behav
      beh0
      (INITUB: behavior_improves beh0 (Goes_wrong E0)):
    <<INITUB: beh0 = Goes_wrong E0>>.
Proof.
  rr in INITUB. des; clarify; et.
  rr in INITUB0. des. unfold behavior_app in *. des_ifs. destruct t; ss.
Qed.

Lemma back_propagate_ub_program
      sem0 sem1
      (IMPR: improves sem0 sem1)
      (INITUB: program_behaves sem1 (Goes_wrong E0)):
    <<INITUB: program_behaves sem0 (Goes_wrong E0)>>.
Proof.
  exploit IMPR; eauto. i; des.
  hexploit back_propagate_ub_behav; et. i ;des. clarify.
Qed.

Lemma improves_free_theorem
      L1 L2
      (IMPRV: forall
          (INITSAFE: exists st, <<INIT: Smallstep.initial_state L1 st>>)
          (INITSAFE: forall st (INIT: Smallstep.initial_state L1 st),
              <<SAFE: safe L1 st>>)
        ,
          improves L1 L2)
  :
    <<IMPRV: improves L1 L2>>
.
Proof.
  destruct (classic (exists st, <<INIT: Smallstep.initial_state L1 st>>)); cycle 1.
  { clear - H.
    ii.
    exists (Goes_wrong []). esplits; ss; eauto using behavior_improves_bot.
    econs 2; eauto.
  }
  destruct (classic (forall st (INIT: Smallstep.initial_state L1 st), <<SAFE: safe L1 st>>)); cycle 1.
  { clear - H0. rename H0 into H.
    ii.
    exists (Goes_wrong []). esplits; ss; eauto.
    - apply Classical_Pred_Type.not_all_ex_not in H. des.
      apply Classical_Prop.imply_to_and in H. des.
      econs 1; eauto.
      clear - H0.
      apply Classical_Pred_Type.not_all_ex_not in H0. des.
      repeat (apply_all_once Classical_Prop.imply_to_and; des).
      apply Classical_Prop.not_or_and in H1. des.
      econs 5; eauto; ss.
      ii. eapply H2; eauto.
    - eapply behavior_improves_bot; eauto.
  }
  eauto.
Qed.
