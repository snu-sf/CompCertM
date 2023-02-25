From compcertr Require Import
     Errors
     Maps
     Integers
     Floats
     AST
     Memory
     Globalenvs
     Smallstep
     sflib.
Require Import CoqlibC.
Require Import ValuesC.
Require Import EventsC.
Require Import CtypesC.
Require Import CopC.
(** newly added **)
Require Import Skeleton Mod ModSem.
Require Import CtypesC.
Require Import CtypingC.
Require Import Simulation.
From compcertr Require Export Clight.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify; try by f_equal.

(* copied from Cshmgen *)
Definition signature_of_function (fd: function) :=
  {| sig_args := map typ_of_type (map snd (fn_params fd));
     sig_res  := rettype_of_type (fn_return fd);
     sig_cc   := fn_callconv fd ; sig_cstyle := true |}.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function p).
  Let ge: genv := Build_genv (SkEnv.revive (skenv) p) p.(prog_comp_env).

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg vs_arg k0 m0
      targs tres cconv
      (EXTERNAL: (Genv.find_funct ge) fptr_arg = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr_arg = Some skd
                        /\ Some (signature_of_type targs tres cconv) = Sk.get_csig skd):
      at_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k0 m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame1 (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      fd tyf
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: CopC.typecheck (Args.vs args) (type_of_params (fn_params fd))):
      initial_frame1 args (Callstate (Args.fptr args) tyf (Args.vs args) Kstop (Args.m args)).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external1: state -> Retv.t -> state -> Prop :=
  | after_external1_intro
      fptr_arg vs_arg m_arg k retv tv targs tres cconv
      (CSTYLE: Retv.is_cstyle retv)
      (* tyf *)
      (TYP: tv = rettypify (Retv.v retv) (rettype_of_type tres)):
      after_external1 (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k (Retv.m retv)).

  Program Definition modsem1: ModSem.t :=
    {| ModSem.step := step1;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame1;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external1;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
    |}.

  Inductive initial_frame2 (args: Args.t): state -> Prop :=
  | initial_frame2_intro
      tvs fd tyf
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: ValuesC.typecheck (Args.vs args) (signature_of_function fd) tvs):
      initial_frame2 args (Callstate (Args.fptr args) tyf tvs Kstop (Args.m args)).

  Inductive after_external2: state -> Retv.t -> state -> Prop :=
  | after_external2_intro
      fptr_arg vs_arg m_arg k retv tv targs tres cconv
      (CSTYLE: Retv.is_cstyle retv)
      (* tyf *)
      (TYP: tv = rettypify (Retv.v retv) (rettype_of_type tres)):
      (* (TYP: tv = typify (Retv.v retv) (typ_of_type tres)): *)
      after_external2 (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k (Retv.m retv)).

  Program Definition modsem2: ModSem.t :=
    {| ModSem.step := step2;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame2;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external2;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
    |}.

  Lemma eval_expr_determ:
    forall e le m a v, eval_expr ge e le m a v -> forall v', eval_expr ge e le m a v' -> v = v'
  with eval_lvalue_determ:
    forall e le m a loc ofs bf, eval_lvalue ge e le m a loc ofs bf -> forall loc' ofs' bf', eval_lvalue ge e le m a loc' ofs' bf' -> loc = loc' /\ ofs = ofs' /\ bf = bf'.
  Proof.
    - induction 1; intros v' EV; inv EV;
        try (by determ_tac eval_expr_determ); try (by determ_tac eval_lvalue_determ);
          try congruence; try by inv H; try by inv H0; try by inv H1; try by inv H2.
      + determ_tac eval_expr_determ. clear H. determ_tac eval_expr_determ.
      + determ_tac eval_lvalue_determ. inv H0; inv H2; try congruence.
        inv H3; inv H8. congruence.
    - induction 1; intros loc' ofs' bf' EV; inv EV; des_ifs; try (by determ_tac eval_expr_determ); try congruence.
      + determ_tac eval_expr_determ. rewrite H0 in H7. des_ifs. rewrite H2 in H12. des_ifs.
      + determ_tac eval_expr_determ. rewrite H0 in H7. des_ifs. rewrite H2 in H12. des_ifs.
  Qed.

  Let eval_exprlist_determ:
    forall e le m bl tyl vl, eval_exprlist ge e le m bl tyl vl  -> forall vl', eval_exprlist ge e le m bl tyl vl' -> vl' = vl.
  Proof.
    induction 1; intros v' EV; inv EV; f_equal; eauto.
    exploit eval_expr_determ. apply H. apply H6. i. subst.
    rewrite H0 in H8. inv H8; auto.
  Qed.

  Let alloc_variables_determ:
    forall env m vars e m1, alloc_variables ge env m vars e m1 -> forall e' m1', alloc_variables ge env m vars e' m1' -> e = e' /\ m1 = m1'.
  Proof.
    induction 1; intros e' m1' EV; inv EV; f_equal; eauto. rewrite H in H8. des_ifs. eapply IHalloc_variables; et.
  Qed.

  Let bind_parameters_determ:
    forall e m params vargs m1, bind_parameters ge e m params vargs m1 -> forall m1', bind_parameters ge e m params vargs m1' -> m1 = m1'.
  Proof.
    induction 1; intros m1' EV; inv EV; f_equal; eauto. replace m1 with m3 in *. des_ifs. eapply IHbind_parameters; et.
    inv H0; inv H10; congruence.
  Qed.

  Lemma modsem1_receptive: forall st, receptive_at modsem1 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.

  Lemma modsem1_determinate: forall st, determinate_at modsem1 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_expr_determ; check_safe);
                try (determ_tac eval_lvalue_determ; check_safe); try (determ_tac eval_exprlist_determ; check_safe);
                  try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe);
                    esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
      + inv H4; inv H16; try congruence. inv H; inv H8. congruence.
      + determ_tac eval_exprlist_determ.
      + inv H1. inv H8. hexploit (alloc_variables_determ H0 H3). i; des; clarify. determ_tac bind_parameters_determ.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Unshelve.
    all: des; ss; try (by exfalso; des; ss).
  Qed.

  Lemma modsem2_receptive: forall st, receptive_at modsem2 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.

  Lemma modsem2_determinate: forall st, determinate_at modsem2 st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0; clarify_meq; try (determ_tac eval_expr_determ; check_safe);
                try (determ_tac eval_lvalue_determ; check_safe); try (determ_tac eval_exprlist_determ; check_safe);
                  try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe);
                    esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
      + inv H4; inv H16; try congruence. inv H; inv H8. congruence.
      + determ_tac eval_exprlist_determ.
      + inv H1. inv H8. hexploit (alloc_variables_determ H3 H7). i; des; clarify.
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Unshelve.
    all: des; ss; try (by exfalso; des; ss).
  Qed.

End MODSEM.


Program Definition module1 (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := CSk.of_program signature_of_function; Mod.get_modsem := modsem1; |}.

Program Definition module2 (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := CSk.of_program signature_of_function; Mod.get_modsem := modsem2; |}.
