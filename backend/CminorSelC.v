Require Import CoqlibC.
From compcertr Require Import
     Maps
     Floats
     Memory
     Globalenvs
     Switch.
Require Import ASTC.
Require Import IntegersC.
Require Import EventsC.
Require Import ValuesC.
Require Import SmallstepC.
(** newly added **)
Require Import Simulation Skeleton Mod ModSem.
From compcertr Require Export CminorSel.
(* Require Import AsmregsC. *)
(* Require Import Conventions. *)
(* Require Import Locations. *)

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  Let ge: genv := (SkEnv.revive skenv) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg sg_arg vs_arg k0 m0
      (EXTERNAL: (Genv.find_funct ge) fptr_arg = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr_arg = Some skd /\ Sk.get_csig skd = Some sg_arg):
      at_external (Callstate fptr_arg sg_arg vs_arg k0 m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd tvs
      (CSTYLE: Args.is_cstyle args /\ fd.(fn_sig).(sig_cstyle) = true)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd.(fn_sig) tvs)
      (LEN: (length (Args.vs args)) = (length fd.(fn_sig).(sig_args))):
      initial_frame args (Callstate (Args.fptr args) fd.(fn_sig) tvs Kstop (Args.m args)).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg sg_arg vs_arg k m_arg retv tv
      (CSTYLE: Retv.is_cstyle retv)
      (TYP: rettypify (Retv.v retv) (sig_res sg_arg) = tv):
      after_external (Callstate fptr_arg sg_arg vs_arg k m_arg)
                     retv
                     (Returnstate tv k (Retv.m retv)).

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

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.

  Lemma eval_expr_determ:
    forall sp e m le a v, eval_expr skenv_link ge sp e m le a v -> forall v', eval_expr skenv_link ge sp e m le a v' -> v' = v
  with eval_exprlist_determ:
    forall sp e m le al vl, eval_exprlist skenv_link ge sp e m le al vl -> forall vl', eval_exprlist skenv_link ge sp e m le al vl' -> vl' = vl
  with eval_condexpr_determ:
    forall sp e m le a v, eval_condexpr skenv_link ge sp e m le a v  -> forall v', eval_condexpr skenv_link ge sp e m le a v' -> v' = v.
  Proof.
    - induction 1; intros v' EV; inv EV; try (by determ_tac eval_expr_determ); try (by determ_tac eval_exprlist_determ); try (by determ_tac eval_condexpr_determ); try congruence.
      + determ_tac eval_condexpr_determ. determ_tac eval_expr_determ.
      + determ_tac eval_expr_determ. clear H. determ_tac eval_expr_determ.
      + determ_tac eval_exprlist_determ. eapply external_call_deterministic; et.
      + determ_tac eval_exprlist_determ. eapply external_call_deterministic; et.
    - induction 1; intros v' EV; inv EV; try (by determ_tac eval_expr_determ); try (by determ_tac eval_exprlist_determ); try (by determ_tac eval_condexpr_determ); try congruence.
      + determ_tac eval_expr_determ. determ_tac eval_exprlist_determ.
    - induction 1; intros v' EV; inv EV; try (by determ_tac eval_expr_determ); try (by determ_tac eval_exprlist_determ); try (by determ_tac eval_condexpr_determ); try congruence.
      + determ_tac eval_condexpr_determ. clear H. determ_tac eval_condexpr_determ.
      + determ_tac eval_expr_determ. determ_tac eval_condexpr_determ.
  Qed.

  Let eval_expr_or_symbol_determ:
    forall sp e m le a vf, eval_expr_or_symbol skenv_link ge sp e m le a vf -> forall vf', eval_expr_or_symbol skenv_link ge sp e m le a vf' -> vf = vf'.
  Proof.
    induction 1; intros vf' EV; inv EV; try congruence. determ_tac eval_expr_determ.
  Qed.

  Let eval_exitexpr_determ:
    forall sp e m le a n, eval_exitexpr skenv_link ge sp e m le a n -> forall n', eval_exitexpr skenv_link ge sp e m le a n' -> n = n'.
  Proof.
    induction 1; intros vf' EV; inv EV; try (by determ_tac eval_expr_determ); try (by determ_tac eval_condexpr_determ); try congruence.
    + determ_tac eval_condexpr_determ. eapply IHeval_exitexpr; et.
    + determ_tac eval_expr_determ. eapply IHeval_exitexpr; et.
  Qed.

  Let eval_builtin_arg_determ:
    forall sp e m a v, eval_builtin_arg skenv_link ge sp e m a v -> forall v', eval_builtin_arg skenv_link ge sp e m a v' -> v = v'.
  Proof.
    induction 1; intros vf' EV; inv EV; try (by determ_tac eval_expr_determ); try congruence.
    + determ_tac eval_expr_determ. clear H. determ_tac eval_expr_determ.
    + erewrite IHeval_builtin_arg1; et. erewrite IHeval_builtin_arg2; et.
  Qed.

  Let eval_builtin_args_determ:
    forall sp e m al vl, list_forall2 (eval_builtin_arg skenv_link ge sp e m) al vl -> forall vl', list_forall2 (eval_builtin_arg skenv_link ge sp e m) al vl' -> vl = vl'.
  Proof.
    i. generalize dependent al. generalize dependent vl'. induction vl; i.
    { inv H. inv H0. ss. }
    inv H. inv H0. determ_tac eval_builtin_arg_determ. f_equal. eapply IHvl; et.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq;
                try (determ_tac eval_expr_determ; check_safe); try (determ_tac eval_exprlist_determ; check_safe);
                  try (determ_tac eval_condexpr_determ; check_safe); try (determ_tac eval_expr_or_symbol_determ; check_safe);
                    try (determ_tac eval_exitexpr_determ; check_safe); try (determ_tac eval_builtin_args_determ; check_safe);
                      try (determ_tac external_call_determ; check_safe);
                      esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.

End MODSEM.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem; |}.
