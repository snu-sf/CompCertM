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
    (* lepriv_PreOrder :> PreOrder SimMem.lepriv; *)
    (* lepriv_Trans :> Transitive SimMem.lepriv; *)
    trans_pub_priv: forall sm0 sm1 sm2, SimMem.lepriv sm0 sm1 -> SimMem.le sm1 sm2 -> SimMem.lepriv sm0 sm2;
    trans_priv_pub: forall sm0 sm1 sm2 (MWF: SimMem.wf sm0), SimMem.le sm0 sm1 -> SimMem.lepriv sm1 sm2 -> SimMem.lepriv sm0 sm2;


    lift: SimMem.t -> SimMem.t;
    unlift: SimMem.t -> SimMem.t -> SimMem.t;

    lift_wf: forall mrel, SimMem.wf mrel -> SimMem.wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(SimMem.src) = mrel.(SimMem.src);
    lift_tgt: forall mrel, (lift mrel).(SimMem.tgt) = mrel.(SimMem.tgt);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.src) = mrel1.(SimMem.src);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(SimMem.tgt) = mrel1.(SimMem.tgt);
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
        (MWF: SimMem.wf sm_ret)
      ,
        SimMem.lepriv sm_ret (unlift sm_at sm_ret)
    ;
  }
  .

End SimMemLift.



Section PROPS.

  Context {SM: SimMem.class} {SML: SimMemLift.class SM}.

  Lemma le_lift_lepriv
        sm0 sm1 sm_lift
        (MWF0: SimMem.wf sm0)
        (MWF1: SimMem.wf sm1)
        (MLE: SimMem.le sm0 sm1)
        (MLIFT: SimMemLift.lift sm1 = sm_lift)
    :
      <<MLE: SimMem.lepriv sm0 sm_lift>>
  .
  Proof.
    subst.
    hexploit (SimMemLift.lift_priv sm1); eauto. intro T.
    r. eapply SimMemLift.trans_priv_pub; et.
  Qed.

  Lemma lift_args
        args_src args_tgt sm_arg0
        (ARGS: SimMem.sim_args args_src args_tgt sm_arg0)
    :
      <<ARGS: SimMem.sim_args args_src args_tgt (SimMemLift.lift sm_arg0)>>
  .
  Proof.
    inv ARGS. econs; eauto.
    - eapply SimMemLift.lift_sim_val; et.
    - erewrite <- SimMem.sim_val_list_spec in *.
      eapply Forall2_impl.
      { eapply SimMemLift.lift_sim_val; et. }
      ss.
    - rewrite SimMemLift.lift_src. ss.
    - rewrite SimMemLift.lift_tgt. ss.
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

