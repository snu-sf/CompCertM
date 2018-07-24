Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Asmregs Conventions1.

Require Import Mod ModSem Skeleton.

Set Implicit Arguments.



Section SYSMODSEM.

  Variable skenv_link: SkEnv.t.

  Definition genvtype: Type := Genv.t external_function unit.

  Definition globalenv: genvtype :=
    skenv_link.(Genv_map_defs) (fun _ gd =>
                                  match gd with
                                  | Gfun (External ef) => Some (Gfun ef)
                                  | Gfun _ => None
                                  | Gvar gv => Some (Gvar gv)
                                  end)
  .

  Definition skd: Type := globdef (fundef signature) unit.

  Definition gd_to_skd V (gd: globdef external_function V): skd :=
    match gd with
    | Gfun ef => (Gfun (Internal ef.(ef_sig)))
    | Gvar (mkglobvar info init ro volatile) => (Gvar (mkglobvar tt init ro volatile))
    end
  .

  Definition skenv: SkEnv.t :=
    globalenv.(Genv_map_defs) (fun _ gd => Some gd.(gd_to_skd))
  .

  Inductive state: Type :=
  | Callstate
      (args: Args.t)
  | Returnstate
      (retv: Retv.t)
  .

  Inductive step (ge: genvtype): state -> trace -> state -> Prop :=
  | step_intro
      args ef
      (FPTR: ge.(Genv.find_funct) args.(Args.fptr) = Some ef)
      tr retv
      (EXTCALL: external_call ef ge args.(Args.vs) args.(Args.m) tr retv.(Retv.v) retv.(Retv.m))
    :
      step ge (Callstate args) tr (Returnstate retv)
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
    :
      initial_frame args (Callstate args)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      retv
    :
      final_frame (Returnstate retv) retv
  .

  Program Definition modsem: ModSem.t := {|
    ModSem.state := state;
    ModSem.genvtype := genvtype;
    ModSem.step := step;
    ModSem.at_external := bot3;
    ModSem.initial_frame := initial_frame;
    ModSem.final_frame := final_frame;
    ModSem.after_external := bot3;
    ModSem.globalenv:= globalenv;
    ModSem.skenv := skenv;
  |}
  .
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. ii; des; ss; all_prop_inv; ss. Qed.
  Next Obligation. ii; des; ss; all_prop_inv; ss. Qed.
  Next Obligation. ii; des; ss; all_prop_inv; ss. Qed.

End SYSMODSEM.








(* Section SYSMOD. *)

(*   Variable prog_main: ident. *)

(*   Program Definition mod: Mod.t := {| *)
(*     Mod.datatype := unit; *)
(*     Mod.get_sk := fun _ => (mkprogram [] [] prog_main); *)
(*     Mod.get_modsem := fun skenv _ => modsem skenv; *)
(*     Mod.data := tt; *)
(*   |} *)
(*   . *)

(* End SYSMOD. *)

