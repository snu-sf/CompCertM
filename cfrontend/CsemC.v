Require Import CoqlibC Maps.
Require Import ASTC Integers Values Events Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
(** newly added **)
Require Export Simulation Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Skeleton Mod ModSem.
Require Import AsmregsC CtypesC.
Require Import Conventions.
(* Require Import Locations. *)

Set Implicit Arguments.





Section CEXTRA.

  Definition is_external (ge: genv) (s:state) : Prop :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | External ef targs tres cconv => is_external_ef ef
        | _ => False
        end
      | None => False
      end
    | _ => False
    end
  .

  Definition internal_function_state (ge: genv) (s:state) : Prop :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | Internal func => type_of_fundef f = Tfunction Tnil type_int32s cc_default
        | _ => False
        end
      | None => False
      end
    | _ => False
    end
  .

  Definition external_state (ge: genv) (s:state) : bool :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | External ef targs tres cconv => is_external_ef ef
        | _ => false
        end
      | None => false
      end
    | _ => false
    end
  .

End CEXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)


Definition get_mem (st: state): option mem :=
  match st with
  | State _ _ _ _ m0 => Some m0
  | ExprState _ _ _ _ m0 => Some m0
  | Callstate _ _ _ _ m0 => Some m0
  | Returnstate _ _ m0 => Some m0
  | Stuckstate => None
  end
.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  (* Set Printing All. *)
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) (defs p).
  Let ce_ge: composite_env := prog_comp_env p.
  Let ge_ge: Genv.t fundef type := revive skenv p.
  Let ge: genv := Build_genv ge_ge ce_ge.

  Inductive at_external : state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg tyf vs_arg sg_arg targs tres cconv k m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd
                   /\ (SkEnv.get_sig skd = sg_arg
                      -> tyf = Tfunction targs tres cconv
                      -> signature_of_type targs tres cconv = sg_arg))
                   (* /\ type_of_fundef skd = tyf) *)
    (* how can i check sg_args and tyf are same type? *)
    (* typ_of_type function is a projection type to typ. it delete some info *)
    :
      at_external (Callstate fptr_arg tyf vs_arg k m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd tyf
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf)
    :
      initial_frame args
                    (Callstate args.(Args.fptr) tyf args.(Args.vs) Kstop args.(Args.m))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret
      (* (CONT: forall f e C ty k', k <> Kcall f e C ty k') *)
    :
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg tyf vs_arg m_arg
      k retv
    :
      after_external (Callstate fptr_arg tyf vs_arg k m_arg)
                     retv
                     (Returnstate retv.(Retv.v) k retv.(Retv.m))
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
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. inv H.
                   inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once. inv H. inv H. Qed.
                   (* specialize (CONT f e C ty k0). clarify. Qed. *)
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply revive_no_external; eauto.
  Qed.

  (* Lemma lift_receptive_at *)
  (*       st *)
  (*       (RECEP: receptive_at (semantics_with_ge ge) st) *)
  (*   : *)
  (*     receptive_at modsem st *)
  (* . *)
  (* Proof. *)
  (*   inv RECEP. econs; eauto; ii; ss. exploit sr_receptive_at; eauto. *)
  (*   eapply match_traces_preserved; try eassumption. ii; ss. *)
  (* Qed. *)

  (* Lemma modsem_receptive *)
  (*       st *)
  (*   : *)
  (*     receptive_at modsem st *)
  (* . *)
  (* Proof. *)
  (*   econs. i. *)
  (*   eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed. *)

  (* not determ *)
  (* Lemma lift_determinate_at *)
  (*       st0 *)
  (*       (DTM: determinate_at (semantics_with_ge ge) st0) *)
  (*   : *)
  (*     determinate_at modsem st0 *)
  (* . *)
  (* Proof. *)
  (*   inv DTM. econs; eauto; ii; ss. *)
  (*   determ_tac sd_determ_at. esplits; eauto. *)
  (*   eapply match_traces_preserved; try eassumption. ii; ss. *)
  (* Qed. *)

  (* Lemma modsem_determinate *)
  (*       st *)
  (*   : *)
  (*     determinate_at modsem st *)
  (* . *)
  (* Proof. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed. *)


End MODSEM.

Section MODULE.

  Variable p: program.

  Program Definition module: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := of_program signature_of_function ;
      Mod.get_modsem := modsem;
    |}
  .
  Next Obligation.
    rewrite CtypesC.of_program_defs.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

End MODULE.

