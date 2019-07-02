Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMem SimMemLift.
Require SimSymbId.
Require Import Conventions1.
Require Export SimMemInjC.

Set Implicit Arguments.

Global Program Instance lepriv_Transitive: RelationClasses.Transitive lepriv.
Next Obligation.
  ii. inv H; inv H0.
  des; clarify.
  econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + econs; eauto.
    ii; des.
    destruct (inj y b_src) eqn:T.
    * destruct p.
      exploit INCR0; eauto. i; clarify.
      inv FROZEN.
      hexploit NEW_IMPLIES_OUTSIDE; eauto.
    * inv FROZEN0.
      hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
      esplits; congruence.
Qed.


Global Program Instance SimMemInjLift : SimMemLift.class SimMemInjC.SimMemInj :=
{
  lift := lift';
  unlift := unlift';
}.
Next Obligation.
  rename H into VALID.
  inv VALID. econs; ss; eauto; ii; des; ss; eauto.
  - eapply Pos.compare_gt_iff in H. xomega.
  - eapply Pos.compare_gt_iff in H. xomega.
  - eapply Pos.compare_gt_iff in H. xomega.
  - eapply Pos.compare_gt_iff in H. xomega.
Qed.
Next Obligation.
  eapply unlift_spec; et.
Qed.
Next Obligation.
  eapply unlift_wf; eauto.
Qed.
Next Obligation.
  inv MWF.
  destruct sm0; ss.
  econs; ss; et.
  - etrans; et.
  - etrans; et.
  - eapply frozen_refl.
Qed.
Next Obligation.
  inv MWF. inv MLE. inv MLIFT.
  (* destruct sm1; ss. *)
  econs; ss; et; try congruence.
  - eapply frozen_refl.
Qed.
