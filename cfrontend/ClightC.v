Require Import CoqlibC.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import ValuesC.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CtypesC.
Require Import Cop.
(** newly added **)
Require Import sflib.
Require Export Clight.
Require Import Skeleton Mod ModSem.
Require Import CtypesC.
Require Import CtypingC.
Require Import Simulation.

Set Implicit Arguments.

(* copied from Cshmgen *)
Definition signature_of_function (fd: function) :=
  {| sig_args := map typ_of_type (map snd (fn_params fd));
     sig_res  := opttyp_of_type (fn_return fd);
     sig_cc   := fn_callconv fd |}.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end
.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(defs).
  Let ge: genv := Build_genv (skenv.(SkEnv.revive) p) p.(prog_comp_env).

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg vs_arg k0 m0
      targs tres cconv
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd
                        /\ signature_of_type targs tres cconv = SkEnv.get_sig skd)
    :
      at_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k0 m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      tvs fd tyf
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: typecheck args.(Args.vs) (signature_of_function fd) tvs)
    :
      initial_frame args
                    (Callstate args.(Args.fptr) tyf tvs Kstop args.(Args.m))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret
    :
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret)
  .

  Inductive after_external1: state -> Retv.t -> state -> Prop :=
  | after_external1_intro
      fptr_arg vs_arg m_arg
      k retv tv
      (* tyf *)
      targs tres cconv
      (TYP: typify_c retv.(Retv.v) tres tv)
    :
      after_external1 (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k retv.(Retv.m))
  .

  Program Definition modsem1: ModSem.t :=
    {|
      ModSem.step := step1;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external1;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. f_equal. determ_tac typify_c_dtm. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Inductive after_external2: state -> Retv.t -> state -> Prop :=
  | after_external2_intro
      fptr_arg vs_arg m_arg
      k retv tv
      (* tyf *)
      targs tres cconv
      (TYP: tv = typify retv.(Retv.v) (typ_of_type tres))
    :
      after_external2 (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k retv.(Retv.m))
  .

  Program Definition modsem2: ModSem.t :=
    {|
      ModSem.step := step2;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external2;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Let lift_receptive: forall
      st
      (RECEP: receptive_at (semantics1_with_ge p ge) st)
    ,
      receptive_at modsem1 st
  .
  Proof. i.
    inv RECEP. econs; eauto; ii; ss. exploit sr_receptive_at; eauto.
    eapply match_traces_preserved; try eassumption. ii; ss.
  Qed.

  Lemma modsem1_receptive
        st
    :
      receptive_at modsem1 st
  .
  Proof. admit "this should hold". Qed.

  Lemma modsem1_determinate
        st
    :
      determinate_at modsem1 st
  .
  Proof. admit "this should hold". Qed.

  Lemma modsem2_receptive
        st
    :
      receptive_at modsem2 st
  .
  Proof. admit "this should hold". Qed.

  Lemma modsem2_determinate
        st
    :
      determinate_at modsem2 st
  .
  Proof. admit "this should hold". Qed.

End MODSEM.





Section MODULE.

  Variable p: program.

  Program Definition module1: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := CSk.of_program signature_of_function;
      Mod.get_modsem := modsem1;
    |}
  .
  Next Obligation.
    rewrite CSk.of_program_defs. ss.
  Qed.

  Program Definition module2: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := CSk.of_program signature_of_function;
      Mod.get_modsem := modsem2;
    |}
  .
  Next Obligation.
    rewrite CSk.of_program_defs. ss.
  Qed.

End MODULE.

