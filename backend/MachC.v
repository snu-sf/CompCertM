Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Globalenvs.
Require Import EventsC.
Require Import Smallstep.
Require Import Op.
Require Import LocationsC.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Export Mach.
Require Import StoreArguments.
Require Import Skeleton Mod ModSem.
Require Import Simulation Integers.
Require Import JunkBlock.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; des; ss; clarify; eauto with congruence.

Section NEWSTEP.

Variable return_address_offset: function -> code -> ptrofs -> Prop.
Variable se: Senv.t.
Variable ge: genv.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Definition step: state -> trace -> state -> Prop := fun st0 tr st1 =>
  <<STEP: Mach.step return_address_offset se ge st0 tr st1>> /\ <<NOTDUMMY: (get_stack st1) <> []>>.

End NEWSTEP.

Hint Unfold step.

Definition locset_copy (diff: Z) (rs: Mach.regset): locset :=
  fun loc =>
    match loc with
    | S _ _ _ => Vundef
    | R r =>
      match rs r with
      | Vptr blk ofs => Vptr (Z.to_pos (blk.(Zpos) + diff)) ofs
      | _ => rs r
      end
    end.
Hint Unfold locset_copy.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Section MODSEM.

  Variable rao: function -> code -> ptrofs -> Prop.
  Hypothesis rao_dtm: forall f c ofs ofs',
      rao f c ofs -> rao f c ofs' -> ofs = ofs'.


  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  Let ge: genv := (SkEnv.revive skenv) p.

  Record state := mkstate {
    init_rs: Mach.regset;
    init_sg: signature;
    st: Mach.state;
  }.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack rs m0 m1 fptr sg vs blk ofs init_rs init_sg
      (EXTERNAL: Genv.find_funct ge fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd /\ Sk.get_csig skd = Some sg)
      (VALS: Mach.extcall_arguments rs m0 (parent_sp stack) sg vs)
      (ARGSRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (RSP: (parent_sp stack) = Vptr blk ofs)
      (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | (Ptrofs.unsigned ofs)))
      (FREE: Mem.free m0 blk (Ptrofs.unsigned ofs) ((Ptrofs.unsigned ofs) + 4 * (size_arguments sg)) = Some m1):
      at_external (mkstate init_rs init_sg (Callstate stack fptr rs m0)) (Args.mk fptr vs m1).

  Inductive initial_frame (args: Args.t) : state -> Prop :=
  | initial_frame_intro
      fd m0 rs sg ra targs n m1
      (CSTYLE: Args.is_cstyle args /\ fd.(fn_sig).(sig_cstyle) = true)
      (RAPTR: Val.has_type ra Tptr)
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge (Args.fptr args) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) sg targs)
      (STORE: store_arguments (Args.m args) rs targs sg m0)
      (JUNK: assign_junk_blocks m0 n = m1)
      (PTRFREE: forall mr
                  (* (NOTIN: Loc.notin (R mr) (regs_of_rpairs (loc_arguments sg))) *)
                  (NOTIN: ~In (R mr) (regs_of_rpairs (loc_arguments sg))),
          <<PTRFREE: is_junk_value m0 m1 (rs mr)>>):
      initial_frame args (mkstate rs sg
                                  (Callstate [dummy_stack
                                                (Vptr (Args.m args).(Mem.nextblock) Ptrofs.zero) ra]
                                             (Args.fptr args) rs m1)).
  (* TODO: change (Vptr args.(Args.m).(Mem.nextblock) Ptrofs.zero) into sp *)

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      (init_rs rs: regset) init_sp m0 m1 blk init_sg mr ra
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr -> Val.lessdef (init_rs mr) (rs mr))
      (INITRSP: init_sp = Vptr blk Ptrofs.zero)
      (FREE: Mem.free m0 blk 0 (4 * size_arguments init_sg) = Some m1)
      (RETV: loc_result init_sg = One mr):
      final_frame (mkstate init_rs init_sg (Returnstate [dummy_stack init_sp ra] rs m0)) (Retv.mk (rs mr) m1).

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      init_rs init_sg stack fptr ls0 m0 ls1 m1 retv sg blk ofs
      (CSTYLE: Retv.is_cstyle retv)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd /\ Sk.get_csig skd = Some sg)
      (REGSET: ls1 = (set_pair (loc_result sg) (Retv.v retv) (regset_after_external ls0)))
      (RSP: (parent_sp stack) = Vptr blk ofs)
      (MEMWF: Ple (Senv.nextblock skenv_link) (Retv.m retv).(Mem.nextblock))
      (UNFREE: Mem_unfree (Retv.m retv) blk (Ptrofs.unsigned ofs) (Ptrofs.unsigned (ofs) + 4 * (size_arguments sg)) = Some m1):
      after_external (mkstate init_rs init_sg (Callstate stack fptr ls0 m0))
                     retv
                     (mkstate init_rs init_sg (Returnstate stack ls1 m1)).

  Inductive step' (se: Senv.t) (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step'_intro
      (STEP: Mach.step rao se ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs))
      (INITFPTR: st0.(init_sg) = st1.(init_sg))
      (NOTDUMMY: (get_stack st1.(st)) <> []).

  Lemma extcall_arguments_dtm
        rs m rsp sg vs0 vs1
        (ARGS0: Mach.extcall_arguments rs m rsp sg vs0)
        (ARGS1: Mach.extcall_arguments rs m rsp sg vs1):
      vs0 = vs1.
  Proof.
    generalize dependent vs1. generalize dependent vs0. generalize dependent sg.
    assert (A: forall l v1 v2,
               Mach.extcall_arg rs m rsp l v1 -> Mach.extcall_arg rs m rsp l v2 -> v1 = v2).
    { intros. inv H; inv H0; congruence. }
    assert (B: forall p v1 v2,
               Mach.extcall_arg_pair rs m rsp p v1 -> Mach.extcall_arg_pair rs m rsp p v2 -> v1 = v2).
    { intros. inv H; inv H0.
      eapply A; eauto.
      f_equal; eapply A; eauto. }
    assert (C: forall ll vl1, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl1 ->
                         forall vl2, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl2 -> vl1 = vl2).
    {
      induction 1; intros vl2 EA; inv EA.
      auto.
      f_equal; eauto. }
    intros. eapply C; eauto.
  Qed.

  Lemma extcall_arguments_length
        rs m rsp sg vs
        (ARGS: extcall_arguments rs m rsp sg vs):
      length (loc_arguments sg) = length vs.
  Proof.
    unfold extcall_arguments in *. abstr (loc_arguments sg) locs.
    ginduction vs; ii; inv ARGS; ss. f_equal. erewrite IHvs; eauto.
  Qed.

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step';
       ModSem.at_external := coerce at_external;
       ModSem.initial_frame := coerce initial_frame;
       ModSem.final_frame := coerce final_frame;
       ModSem.after_external := coerce after_external;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := None;
    |}.
  Next Obligation.
    rewrite RSP in *. clarify. determ_tac extcall_arguments_dtm.
  Qed.
  Next Obligation.
    inv STEP; clarify. unfold Genv.find_funct in *. des_ifs_safe ss. clarify.
  Qed.
  Next Obligation.
    inv STEP; clarify. destruct st1; ss. destruct st0; ss. clarify.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H. destruct st0; ss. destruct s1; ss. clarify.
      inv STEP; try (exploit external_call_receptive; eauto; check_safe; intro T; des); try by (inv_match_traces; (eexists (mkstate _ _ _); econs; [econs| | |]; eauto)).
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0. destruct st0; ss. destruct s1; ss. destruct s2; ss. clarify.
      inv STEP; inv STEP0; clarify_meq; try (determ_tac rao_dtm; check_safe); try (determ_tac extcall_arguments_dtm; check_safe);
        try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe);
          esplits; eauto; try (econs; eauto); try (by rewrite Genv.find_funct_find_funct_ptr in *; congruence); ii; eq_closure_tac; clarify_meq.
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.


Section PROPS.

Variable rao: function -> code -> ptrofs -> Prop.

Lemma lift_star
      se ge st0 tr st1 init_sg init_rs
      (STAR: star (step rao) se ge st0 tr st1):
    star (step' rao) se ge (mkstate init_rs init_sg st0) tr
         (mkstate init_rs init_sg st1).
Proof.
  ginduction STAR; ii; ss.
  { econs; et. }
  inv H. econs; et. econs; et.
Qed.

Lemma lift_plus
      se ge st0 tr st1 init_sg init_rs
      (PLUS: plus (step rao) se ge st0 tr st1):
    plus (step' rao) se ge (mkstate init_rs init_sg st0) tr
         (mkstate init_rs init_sg st1).
Proof.
  inv PLUS. inv H. econs; et.
  { instantiate (1:= mkstate init_rs init_sg s2). econs; ss; et. }
  eapply lift_star; et.
Qed.

End PROPS.

Program Definition module (p: program) (rao: function -> code -> ptrofs -> Prop): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem rao; Mod.midx := None |}.
