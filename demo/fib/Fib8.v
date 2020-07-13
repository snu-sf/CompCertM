Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import FibHeader.
Require Import Fib0.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.



Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) Fib0.module.

  Inductive state: Type :=
  | State
      (n: nat)
      (m: mem)
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      i m blk n
      (SYMB: Genv.find_symbol skenv _fib = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vint i])
      (NAT: to_nat_opt i = Some n)
      (M: (Args.m args) = m)
    :
      initial_frame args (State n m)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_return
      n m
    :
      final_frame (State n m) (Retv.mk (Vint (of_nat (fib_nat n))) m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := bot5;
      ModSem.at_external := bot3;
      ModSem.initial_frame := coerce initial_frame;
      ModSem.final_frame := coerce final_frame;
      ModSem.after_external := bot4;
      ModSem.globalenv := skenv;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
      ModSem.midx := Some "fib";
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => Fib0.module; Mod.get_modsem := modsem; Mod.midx := Some "fib" |}.
