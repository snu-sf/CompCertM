Require Import CoqlibC.
Require Import ASTC Integers ValuesC MemoryC EventsC GlobalenvsC Smallstep.
Require Import Op LocationsC LTL Conventions.
(** newly added **)
Require Export Linear.
Require Import Skeleton Mod ModSem.
Require Import Simulation AsmregsC.
Require Import JunkBlock.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; do 2 inv_all_once; repeat des_u; ss; clarify.

Section NEWSTEP.

Variable se: Senv.t.
Variable ge: genv.
Let find_function_ptr := find_function_ptr ge.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Definition step: state -> trace -> state -> Prop := fun st0 tr st1 =>
  <<STEP: Linear.step se ge st0 tr st1>> /\ <<NOTDUMMY: (get_stack st1) <> []>>.

End NEWSTEP.

Hint Unfold step.


Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

(* Definition get_stackframe (st: state): list stackframe := *)
(*   match st with *)
(*   | State stks _ _ _ _ _ => stks *)
(*   | Callstate stks _ _ _ _ => stks *)
(*   | Returnstate stks _ _ => stks *)
(*   end *)
(* . *)

Definition get_locset (st: state): locset :=
  match st with
  | State _ _ _ _ ls _ => ls
  | Callstate _ _ _ ls _ => ls
  | Returnstate _ ls _ => ls
  end.

Definition current_locset (stk: stackframe): locset :=
  match stk with
  | Stackframe _ _ ls _ => ls
  end.

Definition current_function (stk: Linear.stackframe): Linear.function :=
  match stk with
  | Linear.Stackframe f _ _ _ => f
  end.

Definition undef_outgoing_slots (ls: locset): locset :=
  fun l =>
    match l with
    | S Outgoing  _ _ => Vundef
    | _ => ls l
    end.

Definition stackframes_after_external (stack: list stackframe): list stackframe :=
  match stack with
  | nil => nil
  | Stackframe f sp ls bb :: tl => Stackframe f sp (undef_outgoing_slots ls) bb :: tl
  end.

Lemma parent_locset_after_external: forall stack,
    <<SPURRIOUS: parent_locset (stackframes_after_external stack) = parent_locset stack /\ stack = []>>
    \/ <<AFTER: parent_locset (stackframes_after_external stack) = (undef_outgoing_slots (parent_locset stack))>>.
Proof.
  destruct stack; ss.
  { left; ss. }
  des_ifs; ss. right. ss.
Qed.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  Let ge: genv := (SkEnv.revive skenv) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg ls vs_arg m0
      (EXTERNAL: (Genv.find_funct ge) fptr_arg = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr_arg = Some skd /\ Sk.get_csig skd = Some sg)
      (VALS: vs_arg = map (fun p => Locmap.getpair p ls) (loc_arguments sg)):
      at_external (Callstate stack fptr_arg sg ls m0) (Args.Cstyle fptr_arg vs_arg m0).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fd ls_init sg tvs n m0
      (CSTYLE: Args.is_cstyle args /\ fd.(fn_sig).(sig_cstyle) = true)
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) sg tvs)
      (LOCSET: tvs = map (fun p => Locmap.getpair p ls_init) (loc_arguments sg))
      (JUNK: assign_junk_blocks (Args.m args) n = m0)
      (PTRFREE: forall
          loc
          (* (NOTIN: Loc.notin loc (regs_of_rpairs (loc_arguments sg))) *)
          (NOTIN: ~In loc (regs_of_rpairs (loc_arguments sg))),
          <<PTRFREE: is_junk_value (Args.m args) m0 (ls_init loc)>>)
      (SLOT: forall
          sl ty ofs
          (NOTIN: ~In (S sl ty ofs) (regs_of_rpairs (loc_arguments sg))),
          <<UNDEF: ls_init (S sl ty ofs) = Vundef>>):
      initial_frame args (Callstate [dummy_stack sg ls_init] (Args.fptr args) sg ls_init m0).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      ls0 m0 sg_init ls_init v0
      (VAL: Locmap.getpair (map_rpair R (loc_result sg_init)) ls0 = v0):
      final_frame (Returnstate [dummy_stack sg_init ls_init] ls0 m0) (Retv.mk v0 m0).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg ls_arg m_arg retv ls_after
      (CSTYLE: Retv.is_cstyle retv)
      (LSAFTER: ls_after = Locmap.setpair (loc_result sg_arg)
                                          (typify (Retv.v retv) (proj_sig_res sg_arg))
                                          (undef_caller_save_regs ls_arg)):
      after_external (Callstate stack fptr_arg sg_arg ls_arg m_arg)
                     retv
                     (Returnstate (stackframes_after_external stack) ls_after (Retv.m retv)).

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := coerce at_external;
       ModSem.initial_frame := coerce initial_frame;
       ModSem.final_frame := coerce final_frame;
       ModSem.after_external := coerce after_external;
       ModSem.globalenv := ge;
       ModSem.codeseg := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := None;
    |}.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0. inv H1; inv H; clarify_meq; try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe); esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H. inv H0; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H. inv H1; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; [econs; eauto|]; eauto).
    - ii. inv H. inv H0; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.

Section PROPS.

  Lemma step_preserves_last_option
        se ge st0 tr st1 dummy_stack
        (STEP: step se ge st0 tr st1)
        (LAST: last_option (get_stack st0) = Some dummy_stack):
    <<LAST: last_option (get_stack st1) = Some dummy_stack>>.
  Proof. r in STEP. des. inv STEP0; ss; des_ifs. Qed.

End PROPS.

Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem; Mod.midx := None |}.
