Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.

Require Import Mod ModSem Skeleton.

Set Implicit Arguments.



Section SYSMODSEM.

  Variable skenv_link: SkEnv.t.

  Definition genvtype: Type := SkEnv.t.

  Definition globalenv: genvtype := skenv_link.

  Definition skenv: SkEnv.t :=
    skenv_link.(Genv_map_defs)(fun _ gd =>
                                 match gd with
                                 | Gfun (External ef) => Some (Gfun (Internal ef.(ef_sig)))
                                 | Gfun _ => None
                                 | Gvar gv => Some gd
                                 end)
  .

  Lemma skenv_globlaenv_equiv
    :
      Senv.equiv skenv globalenv
  .
  Proof.
    rr. splits; ii; ss; eauto.
    unfold skenv, globalenv.
    (* unfold skenv, globalenv. *)
    unfold Genv.block_is_volatile, Genv.find_var_info.
    des_ifs; repeat (apply_all_once Genv_map_defs_def; des); ss; des_ifs.
    eapply_all_once Genv_map_defs_def_inv.
    all_once_fast ltac:(fun H => try erewrite H in *; ss).
  Qed.

  Inductive state: Type :=
  | Callstate
      (args: Args.t)
  | Returnstate
      (retv: Retv.t)
  .

  Inductive step (ge: genvtype): state -> trace -> state -> Prop :=
  | step_intro
      args ef
      (FPTR: ge.(Genv.find_funct) args.(Args.fptr) = Some (External ef))
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
    ModSem.at_external := bot2;
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

