Require Import CoqlibC Maps.
Require Import ASTC Integers Values Events Memory Globalenvs.
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

  Definition is_external (ge: genv) (st: RTL.state): Prop :=
    match st with
    | Callstate stack fptr sg args m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => is_external_ef ef
      | _ => False
      end
    | _ => False
    end
  .

  Variable prog: RTL.program.
  Variable ge: genv.
  Definition semantics_with_ge := Semantics step (initial_state prog) final_state ge.
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

  Inductive at_external: state -> regset -> mem -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg vs_arg m0
      m_arg_pre rs_arg m_arg
      (EXTERNAL: Genv.find_funct ge fptr_arg = None)
      (STORE: store_arguments fptr_arg vs_arg m_arg_pre sg_arg rs_arg m_arg)
    :
      at_external (Callstate stack fptr_arg sg_arg vs_arg m0)
                  rs_arg m_arg
  .

  Inductive initial_frame (rs_arg: regset) (m_arg: mem)
    : state -> Prop :=
  | initial_frame_intro
      fptr_arg fd
      (FINDF: Genv.find_funct ge fptr_arg = Some (Internal fd))
      vs_arg m_init
      (LOAD: load_arguments rs_arg m_arg fd.(fn_sig) fptr_arg vs_arg m_init)
    :
      initial_frame rs_arg m_arg
                    (Callstate [] fptr_arg fd.(fn_sig) vs_arg m_init)
  .

  Inductive final_frame (rs_init: regset): state -> regset -> Prop :=
  | final_frame_intro
      fd
      (FINDF: Genv.find_funct ge (rs_init PC) = Some (Internal fd))
      v_ret m_ret rs_ret
      (STORE: store_result rs_init v_ret fd.(fn_sig) rs_ret)
    :
      final_frame rs_init (Returnstate [] v_ret m_ret) rs_ret
  .

  Inductive after_external: state -> regset -> regset -> mem -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg vs_arg m_arg
      rs_ret m_ret
      v_ret rs_arg
      (LOAD: load_result rs_arg rs_ret sg_arg v_ret)
    :
      after_external (Callstate stack fptr_arg sg_arg vs_arg m_arg)
                     rs_arg
                     rs_ret m_ret
                     (Returnstate stack v_ret m_ret)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.get_mem := get_mem;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv; 
    |}
  .
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    all_once_fast ltac:(fun H => try inv H).
    determ_tac load_arguments_dtm0.
    determ_tac load_arguments_dtm1.
  Qed.
  Next Obligation.
    all_once_fast ltac:(fun H => try inv H); rewrite FINDF in *; clarify. determ_tac store_result_dtm.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H); rewrite EXTERNAL in *; clarify.
  Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H); rewrite EXTERNAL in *; clarify.
  Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H).
  Qed.

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    Local Opaque Genv.invert_symbol.
    u in *. des_ifs.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    repeat all_once_fast ltac:(fun H => try apply Genv_map_defs_spec in H; des).
    u in *. des_ifs_safe. des_ifs.
  Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge p ge) st)
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
        (DTM: determinate_at (semantics_with_ge p ge) st0)
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
      Mod.get_sk := Sk.of_program;
      Mod.get_modsem := modsem;
    |}
  .
  Next Obligation.
    rewrite Sk.of_program_defs.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

End MODULE.

