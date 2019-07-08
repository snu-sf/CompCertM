Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import ValuesC.
Require Import Memory.
Require Import EventsC.
Require Import Globalenvs.
Require Import Switch.
Require Cminor.
Require Import Smallstep.
(** newly added **)
Require Export Csharpminor.
Require Import sflib.
Require Export Simulation Csharpminor.
Require Import Skeleton Mod ModSem.

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
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg sg_arg vs_arg k0 m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd /\ Sk.get_csig skd = Some sg_arg)
    :
      at_external (Callstate fptr_arg sg_arg vs_arg k0 m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd tvs
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LEN: args.(Args.vs).(length) = fd.(fn_sig).(sig_args).(length))
    :
      initial_frame args (Callstate args.(Args.fptr) fd.(fn_sig) tvs Kstop args.(Args.m)).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret
    :
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg sg_arg vs_arg k0 m_arg
      retv tv
      (CSTYLE: Retv.is_cstyle retv)
      (TYP: typify retv.(Retv.v) sg_arg.(proj_sig_res) = tv)
    :
      after_external (Callstate fptr_arg sg_arg vs_arg k0 m_arg)
                     retv
                     (Returnstate tv k0 retv.(Retv.m)).

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
    |}.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Let eval_expr_determ:
    forall e le m a v, eval_expr ge e le m a v -> forall v', eval_expr ge e le m a v' -> v = v'.
  Proof.
    induction 1; intros v' EV; inv EV; try congruence.
    - inv H; inv H1; congruence.
    - exploit IHeval_expr; et. i; clarify.
    - exploit IHeval_expr1; et. exploit IHeval_expr2; et. i; clarify.
    - exploit IHeval_expr; et. i; clarify.
  Qed.

  Let eval_exprlist_determ:
    forall e le m al vl, eval_exprlist ge e le m al vl -> forall vl', eval_exprlist ge e le m al vl' -> vl = vl'.
  Proof.
    induction 1; intros vl' EV; inv EV; try congruence; try determ_tac eval_expr_determ.
    - exploit IHeval_exprlist; et. determ_tac eval_expr_determ.
  Qed.

  Let alloc_variables_determ:
    forall env m vars e m1, alloc_variables env m vars e m1 -> forall e' m1', alloc_variables env m vars e' m1' -> e = e' /\ m1 = m1'.
  Proof.
    induction 1; intros e' m1' EV; inv EV; f_equal; eauto. rewrite H in H8. des_ifs. eapply IHalloc_variables; et.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_expr_determ; check_safe); try (determ_tac eval_exprlist_determ; check_safe); try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe); esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
      + determ_tac eval_expr_determ. clear H1. determ_tac eval_expr_determ.
      + determ_tac eval_expr_determ. inv H2. inv H13. ss.
      + inv H2; inv H13; ss.
      + hexploit (alloc_variables_determ H4 H15); et. i; des. clarify.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem; |}.
