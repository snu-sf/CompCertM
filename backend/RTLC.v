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





Section RTLEXTRA.

  Definition is_external (ge: genv) (st: state): Prop :=
    match st with
    | Callstate stack fptr sg args m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => is_external_ef ef = true
      | _ => False
      end
    | _ => False
    end
  .

  Variable se: Senv.t.
  Variable ge: genv.
  Definition semantics_with_ge := Semantics_gen step bot1 final_state ge se.
  (* *************** ge is parameterized *******************)

  Lemma semantics_receptive
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      receptive_at semantics_with_ge st
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma semantics_determinate
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      determinate_at semantics_with_ge st
  .
  Proof.
    admit "this should hold".
  Qed.

End RTLEXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)




















Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg vs_arg m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd /\ SkEnv.get_sig skd = sg_arg)
    :
      at_external (Callstate stack fptr_arg sg_arg vs_arg m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd tvs
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LEN: args.(Args.vs).(length) = fd.(fn_sig).(sig_args).(length))
    :
      initial_frame args
                    (Callstate [] args.(Args.fptr) fd.(fn_sig) tvs args.(Args.m))
  .

  Inductive initial_frame2 (args: Args.t)
    : state -> Prop :=
  | initial_frame2_intro
      fd tvs
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LEN: args.(Args.vs).(length) = fd.(fn_sig).(sig_args).(length))
      n m0
      (JUNK: assign_junk_blocks args.(Args.m) n = m0)
    :
      initial_frame2 args
                    (Callstate [] args.(Args.fptr) fd.(fn_sig) tvs m0)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret
    :
      final_frame (Returnstate [] v_ret m_ret) (Retv.mk v_ret m_ret)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg vs_arg m_arg
      retv tv
      (TYP: typify retv.(Retv.v) sg_arg.(proj_sig_res) = tv)
    :
      after_external (Callstate stack fptr_arg sg_arg vs_arg m_arg)
                     retv
                     (Returnstate stack tv retv.(Retv.m))
  .

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
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Program Definition modsem2: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame2;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv; 
      ModSem.skenv_link := skenv_link; 
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Hypothesis (INCL: SkEnv.includes skenv_link (Sk.of_program fn_sig p)).
  Hypothesis (WF: SkEnv.wf skenv_link).

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply SkEnv.project_revive_no_external; eauto.
  Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge skenv_link ge) st)
    :
      receptive_at modsem st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.

  Lemma modsem2_receptive
        st
    :
      receptive_at modsem2 st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge skenv_link ge) st0)
    :
      determinate_at modsem st0
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed.

  Lemma modsem2_determinate
        st
    :
      determinate_at modsem2 st
  .
  Proof. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed.

End MODSEM.





Section MODULE.

  Variable p: program.

  Program Definition module: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := Sk.of_program fn_sig;
      Mod.get_modsem := modsem;
    |}
  .

  Program Definition module2: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := Sk.of_program fn_sig;
      Mod.get_modsem := modsem2;
    |}
  .

End MODULE.

