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
Require Import MutrecA.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(CSk.of_program signature_of_function).
  Let ge: genv := Build_genv (skenv.(SkEnv.revive) p) p.(prog_comp_env).

  Inductive state: Type :=
  | Callstate
      (i: int)
      (m: mem)
  | Returnstate
      (i: int)
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
      i m
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal func_f))
      (* (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *) *)
      (* (TYP: CopC.typecheck args.(Args.vs) (type_of_params (fn_params fd))) *)
      (VS: args.(Args.vs) = [Vint i])
      (M: args.(Args.m) = m)
    :
      initial_frame args (Callstate i m)
  .

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      g_fptr i m
      (FINDG: Genv.find_symbol ge g_id = Some g_fptr)
      (* (EXTERNAL: ge.(Genv.find_funct) (Vptr g_fptr Ptrofs.zero) = None) *)
      (* vs_arg k0 m0 *)
      (* targs tres cconv *)
      (* (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr g_fptr Ptrofs.zero) = Some skd *)
      (*                   /\ signature_of_type targs tres cconv = SkEnv.get_sig skd) *)
      (NZERO: i.(Int.intval) <> 0%Z)
    :
      at_external (Callstate i m) (Args.mk (Vptr g_fptr Ptrofs.zero) [Vint (Int.sub i (Int.repr 1))] m)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      i m retv
      i_after
      (INT: retv.(Retv.v) = Vint i_after)
      (SUM: i_after = sum (Int.sub i Int.one))
    :
      after_external (Callstate i m) retv (Returnstate (sum i) retv.(Retv.m))
  .

  Inductive step (se: Senv.t) (ge: genv): state -> trace -> state -> Prop :=
  | step_zero
      i m
      (ZERO: i.(Int.intval) = 0%Z)
    :
      step se ge (Callstate i m) E0 (Returnstate i m)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  (* | final_frame_call *)
  (*     i m *)
  (*     (ZERO: i.(Int.intval) = 0%Z) *)
  (*   : *)
  (*     final_frame (Callstate i m) (Retv.mk (Vint i) m) *)
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
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link; 
    |}
  .
  (* Next Obligation. rewrite INT in *. clarify. Qed. *)

End MODSEM.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := CSk.of_program signature_of_function; Mod.get_modsem := modsem; |}.
