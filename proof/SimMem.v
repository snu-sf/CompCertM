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

Set Implicit Arguments.






Module SimMem.

  Class class :=
  {
    t: Type;
    src: t -> mem;
    tgt: t -> mem;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;
    (* Time order: unlift second arg into first arg. *)
    (* TODO: reorder arg? from->to? *)

    le_PreOrder :> PreOrder le;

    pub_priv: forall sm0 sm1, wf sm0 -> le sm0 sm1 -> lepriv sm0 sm1;
    (* lift_le: forall mrel, le mrel (lift mrel); *)
    (* lift_spec: forall mrel0 mrel1, le (lift mrel0) mrel1 -> wf mrel0 -> le mrel0 (unlift mrel0 mrel1); *)

    sim_val: t -> val -> val -> Prop;
    sim_val_list: t -> list val -> list val -> Prop;
    lepriv_sim_val: forall mrel0 mrel1 (MLE: lepriv mrel0 mrel1), sim_val mrel0 <2= sim_val mrel1;
    sim_val_list_spec: forall sm0, (List.Forall2 sm0.(sim_val) = sm0.(sim_val_list));
    sim_val_int: forall sm0 v_src v_tgt, sim_val sm0 v_src v_tgt -> forall i, v_src = Vint i -> v_tgt = Vint i;
  }
  .

  Lemma le_sim_val
        `{SM: class}
        mrel0 mrel1
        (MWF: SimMem.wf mrel0)
        (MLE: le mrel0 mrel1)
    :
      sim_val mrel0 <2= sim_val mrel1
  .
  Proof.
    eapply lepriv_sim_val; et.
    eapply pub_priv; et.
  Qed.

  Lemma sim_val_list_length
        `{SM: class} (sm0: t)
        vs_src vs_tgt
        (SIMVS: sm0.(sim_val_list) vs_src vs_tgt)
    :
      length vs_src = length vs_tgt
  .
  Proof.
    rewrite <- sim_val_list_spec in SIMVS.
    ginduction SIMVS; ii; ss.
    congruence.
  Qed.

  Definition sim_block `{SM: class} (sm0: t) (blk_src blk_tgt: block): Prop :=
    sm0.(sim_val) (Vptr blk_src Ptrofs.zero) (Vptr blk_tgt Ptrofs.zero)
  .

  (* Definition lifted `{SM: class} (sm0 sm1: t): Prop := SimMem.lift sm0 = sm1 /\ SimMem.wf sm0. *)

  Definition future `{SM: class}: t -> t -> Prop := rtc (lepriv \2/ le).

  (* Definition sim_regset `{SM: class} (sm0: t) (rs_src rs_tgt: regset): Prop := *)
  (*   forall pr, sm0.(sim_val) (rs_src pr) (rs_tgt pr) *)
  (* . *)

  Inductive sim_args `{SM: class} (args_src args_tgt: Args.t) (sm0: SimMem.t): Prop :=
  | sim_args_intro
      (FPTR: sm0.(SimMem.sim_val) args_src.(Args.fptr) args_tgt.(Args.fptr))
      (VALS: sm0.(SimMem.sim_val_list) args_src.(Args.vs) args_tgt.(Args.vs))
      (MEMSRC: args_src.(Args.m) = sm0.(SimMem.src))
      (MEMTGT: args_tgt.(Args.m) = sm0.(SimMem.tgt))
  .

  Inductive sim_retv `{SM: class} (retv_src retv_tgt: Retv.t) (sm0: SimMem.t): Prop :=
  | sim_retv_intro
      (RETV: sm0.(SimMem.sim_val) retv_src.(Retv.v) retv_tgt.(Retv.v))
      (MEMSRC: retv_src.(Retv.m) = sm0.(SimMem.src))
      (MEMTGT: retv_tgt.(Retv.m) = sm0.(SimMem.tgt))
  .

  Lemma sim_val_list_lepriv
        `{SM: class}
        sm0 sm1 vs_src vs_tgt
        (LEPRIV: SimMem.lepriv sm0 sm1)
        (SIMVS: SimMem.sim_val_list sm0 vs_src vs_tgt)
    :
      <<SIMVS: SimMem.sim_val_list sm1 vs_src vs_tgt>>
  .
  Proof.
    rewrite <- sim_val_list_spec in *.
    induction SIMVS; ii; ss.
    econs; eauto.
    eapply lepriv_sim_val; et.
  Qed.

End SimMem.

Hint Unfold SimMem.future.

Hint Resolve SimMem.pub_priv.


