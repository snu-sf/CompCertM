Require Import Classical.
Require Import CoqlibC.
Require Import MapsC.
Require Import IntegersC.
Require Import ValuesC.
Require Import ASTC.
Require Import MemoryC.
Require Import EventsC.
From compcertr Require Import
     Axioms
     Errors
     Floats
     Globalenvs
     Smallstep
     Ctypes
     Cop
     Csyntax.
Require Import CsemC.
From compcertr Require Import sflib.
(** newly added **)
Require Import Simulation Skeleton Mod ModSem.
Require Import CtypesC.
From compcertr Require Import Conventions.
Require Import CtypingC.
Require Export CopC.
From compcertr Require Export Ctypes Ctyping Csyntax Cexec Csem Cstrategy.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; do 2 inv_all_once; ss; clarify.

Definition get_mem (st: state): option mem :=
  match st with
  | State _ _ _ _ m0 => Some m0
  | ExprState _ _ _ _ m0 => Some m0
  | Callstate _ _ _ _ m0 => Some m0
  | Returnstate _ _ m0 => Some m0
  | Stuckstate => None
  end.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function p).
  Let ce_ge: composite_env := prog_comp_env p.
  Let ge_ge: Genv.t fundef type := SkEnv.revive skenv p.
  Let ge: genv := Build_genv ge_ge ce_ge.

  Inductive at_external : state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg vs_arg targs tres cconv k0 m0
      (EXTERNAL: (Genv.find_funct ge) fptr_arg = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr_arg = Some skd
                        /\ Some (signature_of_type targs tres cconv) = Sk.get_csig skd)
      (CALL: is_call_cont_strong k0):
      at_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k0 m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd tyf
      (CSTYLE: Args.is_cstyle args)
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: typecheck (Args.vs args) (type_of_params (fn_params fd))):
      initial_frame args (Callstate (Args.fptr args) tyf (Args.vs args) Kstop (Args.m args)).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg vs_arg m_arg k retv tv targs tres cconv
      (CSTYLE: Retv.is_cstyle retv)
      (* tyf *)
      (TYP: tv = rettypify (Retv.v retv) (rettype_of_type tres)):
      after_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
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

  Lemma modsem_strongly_receptive: forall st, strongly_receptive_at modsem st.
  Proof.
    i. econs; ss; i.
    - inversion H; subst. inv H1.
      + (* valof volatile *)
        exploit deref_loc_receptive; eauto. intros [A [v' B]].
        econstructor; econstructor. left; eapply step_rvalof_volatile; eauto.
      + (* assign *)
        exploit assign_loc_receptive; eauto. intro EQ; rewrite EQ in H.
        econstructor; econstructor; eauto.
      + (* assignop *)
        destruct t0 as [ | ev0 t0]; simpl in H10.
        subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
        econstructor; econstructor; eauto.
        inv H10. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
        destruct (sem_binary_operation ge op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
        destruct (sem_cast v3' tyres (typeof l) m) as [v4'|] eqn:?.
        destruct (classic (exists t2', exists m'', exists v'', assign_loc skenv_link ge (typeof l) m b ofs bf v4' t2' m'' v'')).
        destruct H1 as [t2' [m'' [v'' P]]].
        econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; exists v'0; auto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* assignop stuck *)
        exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
        destruct (sem_binary_operation ge op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
        destruct (sem_cast v3' tyres (typeof l) m) as [v4'|] eqn:?.
        destruct (classic (exists t2', exists m'', exists v'', assign_loc skenv_link ge (typeof l) m b ofs bf v4' t2' m'' v'')).
        destruct H1 as [t2' [m'' [ v'' P]]].
        econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; eexists; eauto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* postincr *)
        destruct t0 as [ | ev0 t0]; simpl in H9.
        subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
        econstructor; econstructor; eauto.
        inv H9. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
        destruct (sem_incrdecr ge id v1' (typeof l) m) as [v2'|] eqn:?.
        destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l) m) as [v3'|] eqn:?.
        destruct (classic (exists t2', exists m'', exists v'', assign_loc skenv_link ge (typeof l) m b ofs bf v3' t2' m'' v'')).
        destruct H1 as [t2' [m'' [v'' P]]].
        econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; eauto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* postincr stuck *)
        exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
        destruct (sem_incrdecr ge id v1' (typeof l) m) as [v2'|] eqn:?.
        destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l) m) as [v3'|] eqn:?.
        destruct (classic (exists t2', exists m'', exists v'', assign_loc skenv_link ge (typeof l) m b ofs bf v3' t2' m'' v'')).
        destruct H1 as [t2' [m'' [v'' P]]].
        econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; eauto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* builtin *)
        exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
        exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
        econstructor; econstructor. left; eapply step_builtin; eauto.
        lia.
      + (* external calls *)
        inv H1.
        exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
        exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
        exists (Returnstate vres2 k m2); exists E0; right; econstructor; eauto.
        lia.
    - red; intros. inv H; inv H0; ss.
      + (* valof volatile *)
        exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
      + (* assign *)
        exploit assign_loc_trace; eauto. destruct t; auto. destruct t; simpl; tauto.
      + (* assignop *)
        exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
        destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
        destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
        tauto.
      + (* assignop stuck *)
        exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
      + (* postincr *)
        exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
        destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
        destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
        tauto.
      + (* postincr stuck *)
        exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
      + (* builtins *)
        exploit external_call_trace_length; eauto.
        destruct t; simpl; auto. destruct t; simpl; auto. intros; lia.
      + (* external calls *)
        exploit external_call_trace_length; eauto.
        destruct t; simpl; auto. destruct t; simpl; auto. intros; lia.
  Qed.

End MODSEM.



Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := CSk.of_program signature_of_function; Mod.get_modsem := modsem; |}.
