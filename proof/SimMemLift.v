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

Module SimMemOhLift.

  (* Context `{SM: SimMem.class}. *)

  Class class (owned_heap_src owned_heap_tgt: Type)
        `(SMO: SimMemOh.class owned_heap_src owned_heap_tgt) :=
  { lepriv_Trans :> Transitive SimMemOh.lepriv;

    lift: SimMemOh.t -> SimMemOh.t;
    unlift: SimMemOh.t -> SimMemOh.t -> SimMemOh.t;

    lift_wf: forall mrel, SimMemOh.wf mrel -> SimMemOh.wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(SimMem.src) = mrel.(SimMem.src);
    lift_tgt: forall mrel, (lift mrel).(SimMem.tgt) = mrel.(SimMem.tgt);
    lift_oh_src: forall mrel, (lift mrel).(SimMemOh.oh_src) = mrel.(SimMemOh.oh_src);
    lift_oh_tgt: forall mrel, (lift mrel).(SimMemOh.oh_tgt) = mrel.(SimMemOh.oh_tgt);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.src) = mrel1.(SimMem.src);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.tgt) = mrel1.(SimMem.tgt);
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

  Section PROPS.

  Context (owned_heap_src owned_heap_tgt: Type).
  Context `{SMO: SimMemOh.class owned_heap_src owned_heap_tgt}.
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
