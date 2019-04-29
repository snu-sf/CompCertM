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
    lift: t -> t;
    (* Time order: unlift second arg into first arg. *)
    (* TODO: reorder arg? from->to? *)
    unlift: t -> t -> t;

    le_PreOrder :> PreOrder le;

    (* lift_le: forall mrel, le mrel (lift mrel); *)
    lift_wf: forall mrel, wf mrel -> wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(src) = mrel.(src);
    lift_tgt: forall mrel, (lift mrel).(tgt) = mrel.(tgt);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(src) = mrel1.(src);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(tgt) = mrel1.(tgt);
    unlift_spec: forall mrel0 mrel1, le (lift mrel0) mrel1 -> wf mrel0 -> le mrel0 (unlift mrel0 mrel1);
    unlift_wf: forall mrel0 mrel1,
        wf mrel0 -> wf mrel1 -> le (lift mrel0) mrel1 -> wf (unlift mrel0 mrel1);

    sim_val: t -> val -> val -> Prop;
    sim_val_list: t -> list val -> list val -> Prop;
    le_sim_val: forall mrel0 mrel1 (MLE: le mrel0 mrel1), sim_val mrel0 <2= sim_val mrel1;
    lift_sim_val: forall mrel, sim_val mrel <2= sim_val (lift mrel);
    sim_val_list_spec: forall sm0, (List.Forall2 sm0.(sim_val) = sm0.(sim_val_list));
  }
  .

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

  Definition lifted `{SM: class} (sm0 sm1: t): Prop := SimMem.lift sm0 = sm1 /\ SimMem.wf sm0.

  Definition future `{SM: class}: t -> t -> Prop := rtc (le \2/ lifted).

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

End SimMem.

Hint Unfold SimMem.future SimMem.lifted.


