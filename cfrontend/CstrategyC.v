Require Import Axioms.
Require Import Classical.
Require Import CoqlibC.
Require Import Errors.
Require Import MapsC.
Require Import IntegersC.
Require Import Floats.
Require Import ValuesC.
Require Import ASTC.
Require Import MemoryC.
Require Import EventsC.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import CsemC.
Require Import sflib.
(** newly added **)
Require Export Simulation Cstrategy CopC Ctypes Ctyping Csyntax Cexec.
Require Import Skeleton Mod ModSem.
Require Import CtypesC.
Require Import Conventions.
Require Import CtypingC.

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
  (* Set Printing All. *)
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(CSk.of_program signature_of_function).
  Let ce_ge: composite_env := prog_comp_env p.
  Let ge_ge: Genv.t fundef type := SkEnv.revive skenv p.
  Let ge: genv := Build_genv ge_ge ce_ge.

  Inductive at_external : state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg vs_arg targs tres cconv k0 m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd
                        /\ signature_of_type targs tres cconv = SkEnv.get_sig skd)
      (CALL: is_call_cont_strong k0):
      at_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k0 m0) (Args.mk fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd tyf
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: typecheck args.(Args.vs) (type_of_params (fn_params fd))):
      initial_frame args (Callstate args.(Args.fptr) tyf args.(Args.vs) Kstop args.(Args.m)).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret:
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg vs_arg m_arg k retv tv targs tres cconv
      (* tyf *)
      (TYP: typify_c retv.(Retv.v) tres tv):
      after_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k retv.(Retv.m)).

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
        destruct (classic (exists t2', exists m'', assign_loc skenv_link ge (typeof l) m b ofs v4' t2' m'')).
        destruct H1 as [t2' [m'' P]].
        econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* assignop stuck *)
        exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
        destruct (sem_binary_operation ge op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
        destruct (sem_cast v3' tyres (typeof l) m) as [v4'|] eqn:?.
        destruct (classic (exists t2', exists m'', assign_loc skenv_link ge (typeof l) m b ofs v4' t2' m'')).
        destruct H1 as [t2' [m'' P]].
        econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
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
        destruct (classic (exists t2', exists m'', assign_loc skenv_link ge (typeof l) m b ofs v3' t2' m'')).
        destruct H1 as [t2' [m'' P]].
        econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* postincr stuck *)
        exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
        destruct (sem_incrdecr ge id v1' (typeof l) m) as [v2'|] eqn:?.
        destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l) m) as [v3'|] eqn:?.
        destruct (classic (exists t2', exists m'', assign_loc skenv_link ge (typeof l) m b ofs v3' t2' m'')).
        destruct H1 as [t2' [m'' P]].
        econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; rewrite Heqo0; auto.
        econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
        rewrite Heqo; auto.
      + (* builtin *)
        exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
        exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
        econstructor; econstructor. left; eapply step_builtin; eauto.
        omegaContradiction.
      + (* external calls *)
        inv H1.
        exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
        exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
        exists (Returnstate vres2 k m2); exists E0; right; econstructor; eauto.
        omegaContradiction.
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
        destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
      + (* external calls *)
        exploit external_call_trace_length; eauto.
        destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
  Qed.

End MODSEM.



Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := CSk.of_program signature_of_function; Mod.get_modsem := modsem; |}.


(* Definition geof (skenv_link: SkEnv.t) (cp: program): genv := *)
(*   (Build_genv (revive (SkEnv.project skenv_link (defs cp)) cp) cp.(prog_comp_env)) *)
(* . *)
(* Hint Unfold geof. *)











(** newly added **)
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.


Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog: program.
Let md_src: Mod.t := (CsemC.module prog).
Let md_tgt: Mod.t := (module prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge: genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog) prog.(prog_comp_env).
Let tge: genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Csem.state) (st_tgt0: Csem.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: st_src0 = st_tgt0)
    (MWF: SimMem.wf sm0).

Require Import Classes.Equivalence. Ltac inv H := inversion H; clear H; subst *.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS. ss. subst *. destruct args_src, args_tgt; ss. subst *. inv INITTGT.
    eexists. eexists (SimMemId.mk _ _). esplits; eauto; cycle 1.
    + econs; ss; eauto.
    + econs; eauto; ss.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    destruct args_src, args_tgt; ss. subst *. inv TYP.
    esplits; eauto. econs; eauto. ss.
  - (* call wf *)
    inv MATCH; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. ss. des; ss. clarify.
    folder. eexists _, (SimMemId.mk _ _). esplits; ss; eauto.
    + econs; eauto.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. des; ss. clarify. destruct retv_src, retv_tgt; ss. clarify. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
  - (* final fsim *)
    inv MATCH. inv FINALSRC. ss. des; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto.
  - (* step *)
    right; i. inv MATCH; ss. splits.
    { ii. exploit progress; eauto.
      { instantiate (1:= ModSem.is_call (CsemC.modsem skenv_link prog) \1/
                                        ModSem.is_return (CsemC.modsem skenv_link prog)).
        ss. intro T. des; inv T; inv H0; ss.
      }
      { ii. exploit H; eauto. i; des; eauto. }
      i; des; eauto.
      - inv H0. contradict NOTRET. rr. esplits. econs; eauto.
      - inv H0. contradict NOTCALL. rr. esplits. eauto.
      - inv H0. contradict NOTRET. rr. esplits. eauto.
    }
    i. folder.
    exploit step_simulation; eauto. i. esplits; eauto.
    { econs; eauto. instantiate (1:= sm0). ss. }
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog: program.
Definition mp: ModPair.t := ModPair.mk (CsemC.module prog) (module prog).(Mod.Atomic.trans) tt.

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK.
    eapply factor_simmodsem_target; eauto.
    { ii. eapply CsemC.single_events_at; eauto. ss. eauto. }
    { ii. ss. hexploit (@modsem_strongly_receptive skenv_link_tgt prog s); eauto. intro SR.
      inv SR. exploit ssr_traces_at; eauto.
    }
    eapply sim_modsem; eauto.
Qed.

End SIMMOD.

