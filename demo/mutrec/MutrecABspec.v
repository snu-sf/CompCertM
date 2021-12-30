Require Import CoqlibC.
From compcertr Require Import
     Maps Integers Memory Globalenvs
     Op Registers
     sflib.
Require Import ASTC ValuesC EventsC.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import CtypesC CtypingC.
Require Import ClightC AsmC.
Require Import LinkingC.
Require Import MutrecHeader.
Require Import MutrecA MutrecB.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Definition sk_link: Sk.t :=
  match link (CSk.of_program signature_of_function MutrecA.prog) (Sk.of_program fn_sig MutrecB.prog) with
  | Some sk => sk
  | None => Sk.empty
  end
.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) sk_link.
  Let ge: SkEnv.t := skenv.

  Inductive state: Type :=
  | Callstate
      (i: int)
      (m: mem)
  | Returnstate
      (s: int)
      (m: mem)
  .

  Definition get_mem (st: state): mem :=
    match st with
    | Callstate _ m => m
    | Returnstate _ m => m
    end
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      i m func_fg
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (AST.Internal func_fg))
      (VS: (Args.vs args) = [Vint i])
      (M: (Args.m args) = m)
      (RANGE: 0 <= i.(Int.intval) < MAX)
    :
      initial_frame args (Callstate i m)
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_zero
      i m
    :
      step se ge (Callstate i m) E0 (Returnstate (sum i) m)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_return
      s m
    :
      final_frame (Returnstate s m) (Retv.mk (Vint s) m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := bot2;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := bot3;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => sk_link; Mod.get_modsem := modsem; |}.
