Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import CtypesC CtypingC.
Require Import ClightC.
Require Import MutrecHeader.
Require Import StaticMutrecA.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) prog.(CSk.of_program signature_of_function).
  (* Let ge: genv := Build_genv (skenv.(SkEnv.revive) prog) prog.(prog_comp_env). *)

  Inductive state: Type :=
  | Callstate
      (i: int)
      (m: mem)
  | Interstate
      (i: int)
      (m: mem)
  | Returnstate
      (i: int)
      (m: mem)
  .

  Definition get_mem (st: state): mem :=
    match st with
    | Callstate _ m => m
    | Interstate _ m => m
    | Returnstate _ m => m
    end
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      i m blk
      (SYMB: Genv.find_symbol skenv f_id = Some blk)
      (FPTR: args.(Args.fptr) = Vptr blk Ptrofs.zero)
      (RANGE: 0 <= i.(Int.intval) < MAX)
      (* (DEF: Genv.find_funct skenv args.(Args.fptr) = *)
      (*         Some (AST.Internal (mksignature [AST.Tint] (Some AST.Tint) cc_default))) *)
      (VS: args.(Args.vs) = [Vint i])
      (M: args.(Args.m) = m)
    :
      initial_frame args (Callstate i m)
  .

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      g_fptr i m
      (FINDG: Genv.find_symbol skenv g_id = Some g_fptr)
    :
      at_external (Interstate i m) (Args.mk (Vptr g_fptr Ptrofs.zero) [Vint (Int.sub i (Int.repr 1))] m)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      i m retv
      i_after
      (INT: retv.(Retv.v) = Vint i_after)
      (SUM: i_after = sum (Int.sub i Int.one))
    :
      after_external (Interstate i m) retv (Returnstate (sum i) retv.(Retv.m))
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_sum
      i m
    :
      step se ge (Callstate i m) E0 (Returnstate (sum i) m)
  | step_call
      i m
      (NZERO: i.(Int.intval) <> 0%Z)
    :
      step se ge (Callstate i m) E0 (Interstate i m)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_return
      i m
    :
      final_frame (Returnstate i m) (Retv.mk (Vint i) m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := skenv;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => CSk.of_program signature_of_function prog; Mod.get_modsem := modsem; |}.
