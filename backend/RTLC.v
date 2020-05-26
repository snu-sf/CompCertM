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

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  Let ge: genv := (SkEnv.revive skenv) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg vs_arg m0
      (EXTERNAL: (Genv.find_funct ge) fptr_arg = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr_arg = Some skd /\ Sk.get_csig skd = Some sg_arg /\ sg_arg.(sig_cstyle)):
      at_external (Callstate stack fptr_arg sg_arg vs_arg m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd tvs
      (CSTYLE: Args.is_cstyle args /\ fd.(fn_sig).(sig_cstyle) = true)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd.(fn_sig) tvs)
      (LEN: (Args.vs args).(length) = fd.(fn_sig).(sig_args).(length)):
      initial_frame args (Callstate [] (Args.fptr args) fd.(fn_sig) tvs (Args.m args)).

  Inductive initial_frame2 (args: Args.t): state -> Prop :=
  | initial_frame2_intro
      fd tvs n m0
      (CSTYLE: Args.is_cstyle args /\ fd.(fn_sig).(sig_cstyle) = true)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd.(fn_sig) tvs)
      (LEN: (Args.vs args).(length) = fd.(fn_sig).(sig_args).(length))
      (JUNK: assign_junk_blocks (Args.m args) n = m0):
      initial_frame2 args (Callstate [] (Args.fptr args) fd.(fn_sig) tvs m0).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate [] v_ret m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg vs_arg m_arg retv tv
      (CSTYLE: Retv.is_cstyle retv)
      (TYP: typify (Retv.v retv) (proj_sig_res sg_arg) = tv):
      after_external (Callstate stack fptr_arg sg_arg vs_arg m_arg)
                     retv
                     (Returnstate stack tv (Retv.m retv)).

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := coerce at_external;
       ModSem.initial_frame := coerce initial_frame;
       ModSem.final_frame := coerce final_frame;
       ModSem.after_external := coerce after_external;
       ModSem.globalenv := ge;
       ModSem.codeseg := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := None;
    |}.

  Program Definition modsem2: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := coerce at_external;
       ModSem.initial_frame := coerce initial_frame2;
       ModSem.final_frame := coerce final_frame;
       ModSem.after_external := coerce after_external;
       ModSem.globalenv := ge;
       ModSem.codeseg := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := None;
    |}.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem2_receptive: forall st, receptive_at modsem2 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_builtin_args_determ; check_safe);
                try (determ_tac external_call_determ; check_safe);
                esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem2_determinate: forall st, determinate_at modsem2 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_builtin_args_determ; check_safe);
                try (determ_tac external_call_determ; check_safe);
                esplits; eauto;try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem; Mod.midx := None; |}.

Program Definition module2 (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem2; Mod.midx := None; |}.
