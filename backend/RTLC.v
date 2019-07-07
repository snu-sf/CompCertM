Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
(** newly added **)
Require Export Simulation RTL.
Require Import Skeleton Mod ModSem.
Require Import JunkBlock.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Definition fn_ssig := fun fd => Some (fd.(fn_sig)).

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_ssig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg vs_arg m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd /\ Sk.get_sig skd = Some sg_arg):
      at_external (Callstate stack fptr_arg sg_arg vs_arg m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd tvs
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LEN: args.(Args.vs).(length) = fd.(fn_sig).(sig_args).(length)):
      initial_frame args (Callstate [] args.(Args.fptr) fd.(fn_sig) tvs args.(Args.m)).

  Inductive initial_frame2 (args: Args.t): state -> Prop :=
  | initial_frame2_intro
      fd tvs n m0
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LEN: args.(Args.vs).(length) = fd.(fn_sig).(sig_args).(length))
      (JUNK: assign_junk_blocks args.(Args.m) n = m0):
      initial_frame2 args (Callstate [] args.(Args.fptr) fd.(fn_sig) tvs m0).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate [] v_ret m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg vs_arg m_arg retv tv
      (CSTYLE: Retv.is_cstyle retv)
      (TYP: typify retv.(Retv.v) sg_arg.(proj_sig_res) = tv):
      after_external (Callstate stack fptr_arg sg_arg vs_arg m_arg)
                     retv
                     (Returnstate stack tv retv.(Retv.m)).

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv; 
       ModSem.skenv_link := skenv_link; 
    |}.

  Program Definition modsem2: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame2;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv; 
       ModSem.skenv_link := skenv_link; 
    |}.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem2_receptive: forall st, receptive_at modsem2 st.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_builtin_args_determ; check_safe);
                try (determ_tac external_call_determ; check_safe);
                esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem2_determinate: forall st, determinate_at modsem2 st.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_builtin_args_determ; check_safe);
                try (determ_tac external_call_determ; check_safe);
                esplits; eauto;try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_ssig; Mod.get_modsem := modsem; |}.

Program Definition module2 (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_ssig; Mod.get_modsem := modsem2; |}.
