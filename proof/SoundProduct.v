Require Import CoqlibC.
Require Import MemoryC.
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

Require Import ModSem.
Require Import Skeleton.
Require Import System.
Require Import Sound Preservation.

Set Implicit Arguments.
Section SOUNDPRODUCT.

  Variable SU0 SU1: Sound.class.

  (* Local Obligation Tactic := idtac. *)

  Global Program Instance sound_class_product: Sound.class :=
    {
      Sound.t := SU0.(@Sound.t) * SU1.(@Sound.t);
      Sound.mle su0 m0 m1 := SU0.(@Sound.mle) su0.(fst) m0 m1 /\ SU1.(@Sound.mle) su0.(snd) m0 m1;
      Sound.lepriv su0 su1 := SU0.(@Sound.lepriv) su0.(fst) su1.(fst) /\ SU1.(@Sound.lepriv) su0.(snd) su1.(snd);
      Sound.hle su0 su1 := SU0.(@Sound.hle) su0.(fst) su1.(fst) /\ SU1.(@Sound.hle) su0.(snd) su1.(snd);
      Sound.wf su0 := SU0.(@Sound.wf) su0.(fst) /\ SU1.(@Sound.wf) su0.(snd);
      Sound.val su0 v := SU0.(@Sound.val) su0.(fst) v /\ SU1.(@Sound.val) su0.(snd) v;
      Sound.mem su0 m := SU0.(@Sound.mem) su0.(fst) m /\ SU1.(@Sound.mem) su0.(snd) m;
      Sound.skenv su0 m ske := SU0.(@Sound.skenv) su0.(fst) m ske /\ SU1.(@Sound.skenv) su0.(snd) m ske
    }
  .
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  (* Next Obligation. *)
  (*   ii; ss. des. *)
  (*   (* destruct su0, su1; ss. *) *)
  (*   esplits; ss; eauto. *)
  (*   - eapply Sound.hle_le; et. *)
  (*   - eapply Sound.hle_le; et. *)
  (* Qed. *)
  Next Obligation.
    ii; ss.
    esplits; ss; eauto.
    - eapply Sound.hle_lepriv; et.
    - eapply Sound.hle_lepriv; et.
  Qed.
  Next Obligation.
    ii; ss.
    (* destruct su0, su1; ss. *)
    esplits; ss; eauto.
    - eapply Sound.hle_mle; et.
    - eapply Sound.hle_mle; et.
  Qed.
  Next Obligation.
    ii; ss. des.
    (* destruct su0, su1; ss. *)
    esplits; ss; eauto.
    - eapply Sound.hle_val; et.
    - eapply Sound.hle_val; et.
  Qed.
  Next Obligation.
    exploit (@Sound.init_spec SU0); eauto. i; des.
    exploit (@Sound.init_spec SU1); eauto. i; des.
    exists (su_init, su_init0); eauto.
    inv SUARGS. inv SUARGS0. ss. des.
    esplits; ss; eauto.
  Qed.
  Next Obligation.
    ss. esplits; eauto.
    - eapply Sound.skenv_lepriv; eauto.
    - eapply Sound.skenv_lepriv; eauto.
  Qed.
  Next Obligation.
    ss. esplits; eauto.
    - eapply Sound.skenv_mle; eauto.
    - eapply Sound.skenv_mle; eauto.
  Qed.
  Next Obligation.
    ss. esplits; eauto.
    - eapply Sound.skenv_project; eauto.
    - eapply Sound.skenv_project; eauto.
  Qed.
  Next Obligation.
    ss. rr.
    esplits; ii; des.
    - erewrite <- ! (Sound.system_skenv) in *; eauto.
    - erewrite <- (Sound.system_skenv) in H; eauto.
      erewrite <- (Sound.system_skenv) in H0; eauto.
  Qed.
  Next Obligation.
    ss. des.
    exploit (@Sound.system_axiom SU0); et.
    { rr. esplits; eauto. rr. rewrite Forall_forall in *. ii; ss; eauto. eapply H2; eauto. }
    intro T.
    exploit (@Sound.system_axiom SU1); et.
    { rr. esplits; eauto. rr. rewrite Forall_forall in *. ii; ss; eauto. eapply H2; eauto. }
    intro T0.
    des.
    unfold Sound.retv in *. ss. des.
    eexists (su0, su1). esplits; ss; eauto.
  Qed.

  Lemma sound_args_iff
        su0 su1 args
    :
      (@Sound.args SU0 su0 args) /\ (@Sound.args SU1 su1 args) <-> (@Sound.args sound_class_product (su0, su1) args)
  .
  Proof.
    unfold Sound.args. unfold Sound.vals. ss.
    split; ii; des; esplits; eauto; rewrite Forall_forall in *; ii; ss; eauto.
    - eapply VALS; eauto.
    - eapply VALS; eauto.
  Qed.

  Lemma sound_skenv_iff
        su0 su1 m ske
    :
      (@Sound.skenv SU0 su0 m ske) /\ (@Sound.skenv SU1 su1 m ske) <-> (@Sound.skenv sound_class_product (su0, su1) m ske)
  .
  Proof.
    split; ii; des; esplits; ss; des; eauto.
  Qed.

  Lemma sound_retv_iff
        su0 su1 args
    :
      (@Sound.retv SU0 su0 args) /\ (@Sound.retv SU1 su1 args) <-> (@Sound.retv sound_class_product (su0, su1) args)
  .
  Proof.
    unfold Sound.retv. ss.
    split; ii; des; esplits; eauto; rewrite Forall_forall in *; ii; ss; eauto.
  Qed.

  Theorem preservation_product
          ms
          sound_state0 sound_state1
          (PRSV0: @local_preservation SU0 ms sound_state0)
          (PRSV1: @local_preservation SU1 ms sound_state1)
    :
      <<PRSV: @local_preservation sound_class_product ms
                                  (fun su m st => sound_state0 su.(fst) m st /\ sound_state1 su.(snd) m st)>>
  .
  Proof.
    inv PRSV0. inv PRSV1.
    econs; eauto.
    - clear - INIT INIT0.
      ii. ss.
      specialize (INIT su_init.(fst)).
      specialize (INIT0 su_init.(snd)).
      split; ss.
      + eapply INIT; eauto.
        { destruct su_init; ss. eapply sound_args_iff in SUARG; eauto. ss; des; ss. }
        { destruct su_init; ss. eapply sound_skenv_iff in SKENV; eauto. ss; des; ss. }
      + eapply INIT0; eauto.
        { destruct su_init; ss. eapply sound_args_iff in SUARG; eauto. des. ss. }
        { destruct su_init; ss. eapply sound_skenv_iff in SKENV; eauto. ss; des; ss. }
    - clear - STEP STEP0.
      ii. ss. des.
      specialize (STEP m_arg su0.(fst)).
      specialize (STEP0 m_arg su0.(snd)).
      split; ss.
      + eapply STEP; eauto.
      + eapply STEP0; eauto.
    - clear - CALL CALL0.
      ii. ss. des.
      exploit CALL; eauto. i; des.
      exploit CALL0; eauto. i; des.
      esplits; eauto.
      { instantiate (1:= (su_gr, su_gr0)).
        eapply sound_args_iff; eauto.
      }
      { ss. }
      { ss. }
      i. ss. des.
      split; ss.
      + eapply K; eauto.
        destruct su_ret; ss. eapply sound_retv_iff in RETV. des; ss.
      + eapply K0; eauto.
        destruct su_ret; ss. eapply sound_retv_iff in RETV. des; ss.
    - clear - RET RET0.
      ii. ss. des.
      specialize (RET m_arg su0.(fst)).
      specialize (RET0 m_arg su0.(snd)).
      exploit RET; eauto. i; des.
      exploit RET0; eauto. i; des.
      exists (su_ret, su_ret0).
      esplits; eauto.
      eapply sound_retv_iff. ss.
  Qed.

End SOUNDPRODUCT.

