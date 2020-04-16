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

Require Import ModSem.
Require Export SimMem.
(* Include SimMem. *)

Set Implicit Arguments.


(* A special instance of private transition, for backward compatibility *)

Module SimMemLift.

  (* Context `{SM: SimMem.class}. *)

  Class class (SM: SimMem.class) :=
  {

    lift: SimMem.t -> SimMem.t;
    unlift: SimMem.t -> SimMem.t -> SimMem.t;

    lift_wf: forall mrel, SimMem.wf mrel -> SimMem.wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(SimMem.src) = mrel.(SimMem.src);
    lift_tgt: forall mrel, (lift mrel).(SimMem.tgt) = mrel.(SimMem.tgt);
    lift_ptt_src: forall mrel, (lift mrel).(SimMem.ptt_src) = mrel.(SimMem.ptt_src);
    lift_ptt_tgt: forall mrel, (lift mrel).(SimMem.ptt_tgt) = mrel.(SimMem.ptt_tgt);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.src) = mrel1.(SimMem.src);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.tgt) = mrel1.(SimMem.tgt);
    unlift_ptt_src: forall sm0 sm1, (unlift sm0 sm1).(SimMem.ptt_src) = sm1.(SimMem.ptt_src);
    unlift_ptt_tgt: forall sm0 sm1, (unlift sm0 sm1).(SimMem.ptt_tgt) = sm1.(SimMem.ptt_tgt);

    lift_spec: forall mrel0 mrel1, SimMem.le (lift mrel0) mrel1 -> SimMem.wf mrel0 -> SimMem.le mrel0 (unlift mrel0 mrel1);
    unlift_wf: forall mrel0 mrel1,
        SimMem.wf mrel0 -> SimMem.wf mrel1 -> SimMem.le (lift mrel0) mrel1 -> SimMem.wf (unlift mrel0 mrel1);

    lift_sim_val: forall mrel, SimMem.sim_val mrel <2= SimMem.sim_val (lift mrel);

    (* Required for "forward" compatibility *)

    lift_priv: forall sm0 (MWF: SimMem.wf sm0), SimMem.lepriv sm0 (lift sm0);
    (* unlift_priv: forall sm0 sm1 (MWF: SimMem.wf sm0), SimMem.lepriv sm1 (unlift sm0 sm1); *)
    unlift_priv: forall
        sm_at sm_arg sm_ret
        (MWF: SimMem.wf sm_at)
        (MLIFT: SimMem.lepriv sm_at sm_arg)
        (MLE: SimMem.le sm_arg sm_ret)
        (MWF: SimMem.wf sm_ret),
        SimMem.lepriv sm_ret (unlift sm_at sm_ret);
  }.

  Section PROPS.

  Context {SM: SimMem.class}.
  Context {SML: SimMemLift.class SM}.

  Lemma lift_sim_regset: forall sm0, SimMem.sim_regset sm0 <2= SimMem.sim_regset (SimMemLift.lift sm0).
  Proof. ii. eapply SimMemLift.lift_sim_val; et. Qed.

  Lemma le_lift_lepriv
        sm0 sm1 sm_lift
        (MWF0: SimMem.wf sm0)
        (MWF1: SimMem.wf sm1)
        (MLE: SimMem.le sm0 sm1)
        (MLIFT: SimMemLift.lift sm1 = sm_lift):
      <<MLE: SimMem.lepriv sm0 sm_lift>>.
  Proof.
    subst. hexploit (SimMemLift.lift_priv sm1); eauto. intro T. r. etrans; et.
  Qed.

  Lemma lift_args
        args_src args_tgt sm_arg0
        (ARGS: SimMem.sim_args args_src args_tgt sm_arg0):
      <<ARGS: SimMem.sim_args args_src args_tgt (SimMemLift.lift sm_arg0)>>.
  Proof.
    inv ARGS.
    - econs; eauto.
      + eapply SimMemLift.lift_sim_val; et.
      + erewrite <- SimMem.sim_val_list_spec in *.
        eapply Forall2_impl.
        { eapply SimMemLift.lift_sim_val; et. }
        ss.
      + rewrite SimMemLift.lift_src. ss.
      + rewrite SimMemLift.lift_tgt. ss.
    - econs 2; eauto.
      + eapply lift_sim_regset; et.
      + rewrite SimMemLift.lift_src. ss.
      + rewrite SimMemLift.lift_tgt. ss.
  Qed.

  Lemma lift_unch
        (sm: SimMem.t)
        mi
    :
      SimMem.unch mi sm (lift sm)
  .
  Proof.
    econs.
    - rewrite lift_src. refl.
    - rewrite lift_tgt. refl.
    - rewrite lift_ptt_src. refl.
    - rewrite lift_ptt_tgt. refl.
  Qed.

  Lemma unlift_unch
        (sm0 sm1: SimMem.t)
        mi
    :
      SimMem.unch mi sm1 (unlift sm0 sm1)
  .
  Proof.
    econs.
    - rewrite unlift_src. refl.
    - rewrite unlift_tgt. refl.
    - rewrite unlift_ptt_src. refl.
    - rewrite unlift_ptt_tgt. refl.
  Qed.
  (* Lemma unlift_le_lepriv *)
  (*       sm_arg sm_ret sm1 *)
  (*       (MWF0: SimMem.wf sm_arg) *)
  (*       (MWF1: SimMem.wf (SimMemLift.unlift sm_arg sm_ret)) *)
  (*       (MLE: SimMem.le (SimMemLift.unlift sm_arg sm_ret) sm1) *)
  (*   : *)
  (*     <<MLE: SimMem.lepriv sm_ret sm1>> *)
  (* . *)
  (* Proof. *)
  (*   hexploit (SimMemLift.unlift_priv sm_arg sm_ret); eauto. intro T. *)
  (*   r. etrans; et. *)
  (* Qed. *)

  End PROPS.

End SimMemLift.



Module SimMemOhLift.

  (* Context `{SM: SimMem.class}. *)

  (* Class class (owned_heap_src owned_heap_tgt: Type) *)
  (*       `(SMO: SimMemOh.class owned_heap_src owned_heap_tgt) := *)
  Class class `{SM: SimMem.class} (SMO: SimMemOh.class) :=
  {

    lift: SimMemOh.t -> SimMemOh.t;
    unlift: SimMemOh.t -> SimMemOh.t -> SimMemOh.t;

    lift_wf: forall mrel, SimMemOh.wf mrel -> SimMemOh.wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(SimMem.src) = mrel.(SimMem.src);
    lift_tgt: forall mrel, (lift mrel).(SimMem.tgt) = mrel.(SimMem.tgt);
    lift_ptt_src: forall mrel, (lift mrel).(SimMem.ptt_src) = mrel.(SimMem.ptt_src);
    lift_ptt_tgt: forall mrel, (lift mrel).(SimMem.ptt_tgt) = mrel.(SimMem.ptt_tgt);
    lift_oh_src: forall mrel, (lift mrel).(SimMemOh.oh_src) = mrel.(SimMemOh.oh_src);
    lift_oh_tgt: forall mrel, (lift mrel).(SimMemOh.oh_tgt) = mrel.(SimMemOh.oh_tgt);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.src) = mrel1.(SimMem.src);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.tgt) = mrel1.(SimMem.tgt);
    unlift_ptt_src: forall sm0 sm1, (unlift sm0 sm1).(SimMem.ptt_src) = sm1.(SimMem.ptt_src);
    unlift_ptt_tgt: forall sm0 sm1, (unlift sm0 sm1).(SimMem.ptt_tgt) = sm1.(SimMem.ptt_tgt);

    lift_spec: forall mrel0 mrel1, SimMemOh.le (lift mrel0) mrel1 -> SimMemOh.wf mrel0 -> SimMemOh.le mrel0 (unlift mrel0 mrel1);
    unlift_wf: forall mrel0 mrel1,
        SimMemOh.wf mrel0 -> SimMemOh.wf mrel1 -> SimMemOh.le (lift mrel0) mrel1 -> SimMemOh.wf (unlift mrel0 mrel1);

    lift_sim_val: forall (mrel: SimMemOh.t), SimMem.sim_val mrel <2= SimMem.sim_val (lift mrel);

    (* Required for "forward" compatibility *)

    lift_priv: forall sm0 (MWF: SimMemOh.wf sm0), SimMemOh.lepriv sm0 (lift sm0);
    (* unlift_priv: forall sm0 sm1 (MWF: SimMemOh.wf sm0), SimMemOh.lepriv sm1 (unlift sm0 sm1); *)
    unlift_priv: forall
        sm_at sm_arg sm_ret
        (MWF: SimMemOh.wf sm_at)
        (MLIFT: SimMemOh.lepriv sm_at sm_arg)
        (MLE: SimMemOh.le sm_arg sm_ret)
        (MWF: SimMemOh.wf sm_ret),
        SimMemOh.lepriv sm_ret (unlift sm_at sm_ret);
  }.

  Lemma lift_unch
        `{SMOL: class}
        (sm: SimMemOh.t)
    :
      SimMem.unch SimMemOh.midx sm (lift sm)
  .
  Proof.
    econs.
    - rewrite lift_src. refl.
    - rewrite lift_tgt. refl.
    - rewrite lift_ptt_src. refl.
    - rewrite lift_ptt_tgt. refl.
  Qed.

  Lemma unlift_unch
        `{SMOL: class}
        (sm0 sm1: SimMemOh.t)
    :
      SimMem.unch SimMemOh.midx sm1 (unlift sm0 sm1)
  .
  Proof.
    econs.
    - rewrite unlift_src. refl.
    - rewrite unlift_tgt. refl.
    - rewrite unlift_ptt_src. refl.
    - rewrite unlift_ptt_tgt. refl.
  Qed.
  (* Lemma lift_sm_commute *)
  (*       {SM: SimMem.class} *)
  (*       {SML: SimMemLift.class SM} *)
  (*       owned_heap_src owned_heap_tgt *)
  (*       {SMO: SimMemOh.class owned_heap_src owned_heap_tgt} *)
  (*       {SMOL: SimMemOhLift.class SMO} *)
  (*   : *)
  (*     forall smo, (SimMemOh.sm (SimMemOhLift.lift smo)) = SimMemLift.lift (SimMemOh.sm smo) *)
  (* . *)
  (* Proof. *)
  (*   i. *)
  (* Qed. *)

  Section TRANSFORMER.

    Context `{SML: SimMemLift.class}.
    Context {SMO: SimMemOh.class}.

    (* Hypothesis memory_owned_heap_independent_le: forall *)
    (*     sm0 sm1 smo0 smo1 *)
    (*     (MLE: SimMem.le sm0 sm1) *)
    (*     (MLE: SimMemOh.le smo0 smo1) *)
    (*   , *)
    (*     <<MLE: SimMemOh.le (SimMemOh.set_sm smo0 sm0) *)
    (*                        (SimMemOh.set_sm smo1 sm1)>> *)
    (* . *)
    (* Hypothesis memory_owned_heap_independent_lepriv: forall *)
    (*     sm0 sm1 smo0 smo1 *)
    (*     (MLE: SimMem.lepriv sm0 sm1) *)
    (*     (MLE: SimMemOh.lepriv smo0 smo1) *)
    (*   , *)
    (*     <<MLE: SimMemOh.lepriv (SimMemOh.set_sm smo0 sm0) *)
    (*                            (SimMemOh.set_sm smo1 sm1)>> *)
    (* . *)

    Global Program Instance SimMemOhLift_transform: SimMemOhLift.class SMO :=
    {
      lift   := fun smo0 => SimMemOh.set_sm smo0 (SimMemLift.lift smo0);
      unlift := fun smo0 smo1 => SimMemOh.set_sm smo1 (SimMemLift.unlift smo0 smo1);
    }
    .
    Next Obligation.
      eapply SimMemOh.set_sm_wf; eauto.
      - eapply SimMemLift.lift_wf; eauto.
        eapply SimMemOh.wf_proj; eauto.
      - rewrite SimMemLift.lift_src. refl.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.lift_src; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.lift_tgt; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. rewrite SimMemLift.lift_ptt_src; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. rewrite SimMemLift.lift_ptt_tgt; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.set_sm_oh_src; ss.
    Qed.
    Next Obligation.
      rewrite SimMemOh.set_sm_oh_tgt; ss.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.unlift_src; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.unlift_tgt; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.unlift_ptt_src; eauto.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.unlift_ptt_tgt; eauto.
    Qed.
    Next Obligation.
      exploit SimMemLift.lift_spec; eauto.
      {
        instantiate (1:= mrel1).
        instantiate (1:= mrel0).
        eapply SimMemOh.le_proj in H.
        rewrite SimMemOh.getset_sm in H. ss.
      }
      { eapply SimMemOh.wf_proj. ss. }
      intro T.

      eapply SimMemOh.set_sm_le in H.
      { rewrite SimMemOh.setset_sm in H. rewrite SimMemOh.setget_sm in H. eauto. }
      { eauto. }
    Qed.
    Next Obligation.
      eapply SimMemOh.set_sm_wf; eauto.
      - eapply SimMemLift.unlift_wf; try eapply SimMemOh.wf_proj; eauto.
        eapply SimMemOh.le_proj in H1. rewrite SimMemOh.getset_sm in H1. ss.
      - rewrite SimMemLift.unlift_src. refl.
    Qed.
    Next Obligation.
      rewrite SimMemOh.getset_sm. eapply SimMemLift.lift_sim_val; eauto.
    Qed.
    Next Obligation.
      rewrite <- SimMemOh.setget_sm with sm0.
      eapply SimMemOh.set_sm_lepriv; eauto.
      - rewrite SimMemOh.setget_sm.
        eapply SimMemLift.lift_priv; eauto. eapply SimMemOh.wf_proj; eauto.
      - rewrite SimMemOh.setget_sm. refl.
    Qed.
    Next Obligation.
      rewrite <- SimMemOh.setget_sm with sm_ret.
      eapply SimMemOh.set_sm_lepriv; eauto.
      - rewrite SimMemOh.setget_sm.
        eapply SimMemLift.unlift_priv; eauto.
        + eapply SimMemOh.wf_proj; eauto.
        + eapply SimMemOh.lepriv_proj; eauto.
        + eapply SimMemOh.le_proj; eauto.
        + eapply SimMemOh.wf_proj; eauto.
      - rewrite SimMemOh.setget_sm. refl.
    Qed.

  End TRANSFORMER.

  Global Program Instance SimMemOhLift_default_transform `{SML: SimMemLift.class}:
    SimMemOhLift.class (SimMemOh_default SM) := @SimMemOhLift_transform _ _ (SimMemOh_default SM).

  Section PROPS.

  Context `{SMO: SimMemOh.class}.
  Context {SML: SimMemOhLift.class SMO}.

  Lemma lift_sim_regset: forall (sm0: SimMemOh.t), SimMem.sim_regset sm0 <2= SimMem.sim_regset (SimMemOhLift.lift sm0).
  Proof. ii. eapply SimMemOhLift.lift_sim_val; et. Qed.

  Lemma le_lift_lepriv
        sm0 sm1 sm_lift
        (MWF0: SimMemOh.wf sm0)
        (MWF1: SimMemOh.wf sm1)
        (MLE: SimMemOh.le sm0 sm1)
        (MLIFT: SimMemOhLift.lift sm1 = sm_lift):
      <<MLE: SimMemOh.lepriv sm0 sm_lift>>.
  Proof.
    subst. hexploit (SimMemOhLift.lift_priv sm1); eauto. intro T. r. etrans; et.
  Qed.

  Lemma lift_args
        args_src args_tgt (sm_arg0: SimMemOh.t)
        (ARGS: SimMem.sim_args args_src args_tgt sm_arg0):
      <<ARGS: SimMem.sim_args args_src args_tgt (SimMemOhLift.lift sm_arg0)>>.
  Proof.
    inv ARGS.
    - econs; eauto.
      + eapply SimMemOhLift.lift_sim_val; et.
      + erewrite <- SimMem.sim_val_list_spec in *.
        eapply Forall2_impl.
        { eapply SimMemOhLift.lift_sim_val; et. }
        ss.
      + rewrite SimMemOhLift.lift_src. ss.
      + rewrite SimMemOhLift.lift_tgt. ss.
    - econs 2; eauto.
      + eapply lift_sim_regset; et.
      + rewrite SimMemOhLift.lift_src. ss.
      + rewrite SimMemOhLift.lift_tgt. ss.
  Qed.

  (* Lemma unlift_le_lepriv *)
  (*       sm_arg sm_ret sm1 *)
  (*       (MWF0: SimMem.wf sm_arg) *)
  (*       (MWF1: SimMem.wf (SimMemOhLift.unlift sm_arg sm_ret)) *)
  (*       (MLE: SimMem.le (SimMemOhLift.unlift sm_arg sm_ret) sm1) *)
  (*   : *)
  (*     <<MLE: SimMem.lepriv sm_ret sm1>> *)
  (* . *)
  (* Proof. *)
  (*   hexploit (SimMemOhLift.unlift_priv sm_arg sm_ret); eauto. intro T. *)
  (*   r. etrans; et. *)
  (* Qed. *)

  End PROPS.

End SimMemOhLift.
