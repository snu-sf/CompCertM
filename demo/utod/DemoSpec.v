Require Import CoqlibC.
From compcertr Require Import
     Maps
     Integers
     Memory
     Globalenvs
     Op
     Registers
     sflib.
Require Import ASTC ValuesC EventsC.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import AsmC.
Require Import DemoHeader.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Section MODSEM.

  Definition prog : AST.program (AST.fundef (signature)) unit :=
    {| prog_defs :=
         [(func_id, Gfun (Internal ((mksignature [Tlong] (Tret Tfloat) cc_default))))];
       prog_public := [func_id; main_id];
       prog_main := main_id |}.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program id prog).

  Record state := mkstate { get_arg: int64; get_mem: mem; }.

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      st
      (VS: (Args.vs args) = [Vlong st.(get_arg)])
      (M: (Args.m args) = st.(get_mem))
    :
      initial_frame args st
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_return
      st v_ret
      (SPEC: Val.floatoflongu (Vlong st.(get_arg)) = Some v_ret)
    :
      final_frame st (Retv.mk v_ret st.(get_mem))
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.state := state;
      ModSem.genvtype := unit;
      ModSem.step := bot5;
      ModSem.at_external := bot2;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := bot3;
      ModSem.globalenv := tt;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => prog; Mod.get_modsem := modsem; |}.
