Require Import CoqlibC MapsC.
Require Import ASTC Integers ValuesC Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions.
(** newly added **)
Require Export LTL.
Require Import Simulation Skeleton Mod ModSem.

Set Implicit Arguments.





Section LTLEXTRA.

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

End LTLEXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)












Section NEWSTEP.

Variable se: Senv.t.
Variable ge: genv.
Let find_function_ptr := find_function_ptr ge.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Block stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Definition step: state -> trace -> state -> Prop := fun st0 tr st1 =>
  <<STEP: LTL.step se ge st0 tr st1>> /\ <<NOTDUMMY: st1.(get_stack) <> []>>
.

End NEWSTEP.

Hint Unfold step.




Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Block _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.




Definition undef_outgoing_slots (ls: locset): locset :=
  fun l =>
    match l with
    | S Outgoing  _ _ => Vundef
    | _ => ls l
    end
.
  
Definition stackframes_after_external (stack: list stackframe): list stackframe :=
  match stack with
  | nil => nil
  | Stackframe f sp ls bb :: tl => Stackframe f sp ls.(undef_outgoing_slots) bb :: tl
  end
.




Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg ls vs_arg m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd /\ SkEnv.get_sig skd = sg_arg)
      (VALS: vs_arg = map (fun p => Locmap.getpair p ls) (loc_arguments sg_arg))
    :
      at_external (Callstate stack fptr_arg sg_arg ls m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd tvs ls_init sg
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYP: typecheck args.(Args.vs) fd.(fn_sig) tvs)
      (LOCSET: tvs = map (fun p => Locmap.getpair p ls_init) (loc_arguments sg))
      (PTRFREE: forall
          loc
          (* (NOTIN: Loc.notin loc (regs_of_rpairs (loc_arguments sg))) *)
          (NOTIN: ~In loc (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr (ls_init loc)>>)
      (SLOT: forall
          sl ty ofs
          (NOTIN: ~In (S sl ty ofs) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<UNDEF: ls_init (S sl ty ofs) = Vundef>>)

    :
      initial_frame args
                    (Callstate [dummy_stack sg ls_init] args.(Args.fptr) sg ls_init args.(Args.m))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      ls0 m_ret sg_init ls_init v_ret
      (VAL: Locmap.getpair (map_rpair R (loc_result sg_init)) ls0 = v_ret)
    :
      final_frame (Returnstate [dummy_stack sg_init ls_init] ls0 m_ret) (Retv.mk v_ret m_ret)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg ls_arg m_arg retv
      ls_after
      (LSAFTER: ls_after = Locmap.setpair (loc_result sg_arg)
                                          (typify retv.(Retv.v) sg_arg.(proj_sig_res))
                                          (undef_caller_save_regs ls_arg))
    :
      after_external (Callstate stack fptr_arg sg_arg ls_arg m_arg)
                     retv
                     (Returnstate stack.(stackframes_after_external) ls_after retv.(Retv.m))
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
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.

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

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge skenv_link ge) st0)
    :
      determinate_at modsem st0
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    - inv H. inv H0. determ_tac sd_determ_at.
    - inv H. exploit sd_traces_at; eauto.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge skenv_link ge) st)
    :
      receptive_at modsem st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss.
    - inv H. exploit sr_receptive_at; eauto. i; des.
      esplits; eauto. econs; eauto. admit "ez - See Mach.v for same admit".
    - inv H. exploit sr_traces_at; eauto.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.



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

End MODULE.
