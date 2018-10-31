Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC Events Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
(** newly added **)
Require Export Simulation RTL.
Require Import Skeleton Mod ModSem.
Require Import AsmregsC.
Require Import Conventions.
(* Require Import Locations. *)

Set Implicit Arguments.





Section RTLEXTRA.

  Definition is_external (ge: genv) (st: state): Prop :=
    match st with
    | Callstate stack fptr sg args m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => is_external_ef ef
      | _ => False
      end
    | _ => False
    end
  .

  Variable ge: genv.
  Definition semantics_with_ge := Semantics step bot1 final_state ge.
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
                     (Returnstate stack retv.(Retv.v) retv.(Retv.m))
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
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply SkEnv.revive_no_external; eauto.
  Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge ge) st)
    :
      receptive_at modsem st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss. exploit sr_receptive_at; eauto.
    eapply match_traces_preserved; try eassumption. ii; ss.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge ge) st0)
    :
      determinate_at modsem st0
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    determ_tac sd_determ_at. esplits; eauto.
    eapply match_traces_preserved; try eassumption. ii; ss.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
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
  Next Obligation.
    rewrite Sk.of_program_defs. ss.
  Qed.

End MODULE.

