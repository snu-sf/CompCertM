Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Skeleton.
Require Import CoqlibC.
Require Asm.

Set Implicit Arguments.



Module Args.

  Inductive t: Type :=
  | Cstyle
      (fptr: val)
      (vs: list val)
      (m: mem)
  | Asmstyle
      (rs: Asm.regset)
      (m: mem).

  (* intentional: it should work for both cases *)
  Definition get_fptr (args: Args.t): val :=
    match args with
    | Args.Cstyle fptr _ _ => fptr
    | Args.Asmstyle rs _ => rs Asm.PC
    end
  .

  (* intentional: it should work for both cases *)
  Definition get_m (args: Args.t): mem :=
    match args with
    | Args.Cstyle _ _ m => m
    | Args.Asmstyle _ m => m
    end
  .

  (* for backward compatibility: it should be used only when "args" is known to be C-style. *)
  (* it will return dummy value if it is assembly style. *)
  Definition fptr (args: Args.t): val :=
    match args with
    | Args.Cstyle fptr _ _ => fptr
    | Args.Asmstyle rs _ => Vundef (* should not happen *)
    end
  .

  (* for backward compatibility: it should be used only when "args" is known to be C-style. *)
  (* it will return dummy value if it is assembly style. *)
  Definition vs (args: Args.t): list val :=
    match args with
    | Args.Cstyle _ vs _ => vs
    | Args.Asmstyle _ _ => [] (* should not happen *)
    end
  .

  (* for backward compatibility: it should be used only when "args" is known to be C-style. *)
  (* it will return dummy value if it is assembly style. *)
  Definition m (args: Args.t): mem :=
    match args with
    | Args.Cstyle _ _ m => m
    | Args.Asmstyle _ m => Mem.empty (* should not happen *)
    end
  .

  (* for backward compatibility *)
  Definition mk (fptr: val) (vs: list val) (m: mem): t := Args.Cstyle fptr vs m.

  Definition is_cstyle (args: t): bool :=
    match args with
    | Cstyle _ _ _ => true
    | _ => false
    end
  .

  Lemma get_m_m: forall args (CSTYLE: is_cstyle args), (get_m args) = (m args). Proof. destruct args; ss. Qed.

End Args.

Module Retv.

  Inductive t: Type :=
  | Cstyle
      (v: val)
      (m: mem)
  | Asmstyle
      (rs: Asm.regset)
      (m: mem).

  (* intentional: it should work for both cases *)
  Definition get_m (retv: Retv.t): mem :=
    match retv with
    | Retv.Cstyle _ m => m
    | Retv.Asmstyle _ m => m
    end
  .

  (* for backward compatibility: it should be used only when "args" is known to be C-style. *)
  (* it will return dummy value if it is assembly style. *)
  Definition v (retv: Retv.t): val :=
    match retv with
    | Retv.Cstyle v _ => v
    | Retv.Asmstyle _ _ => Vundef (* should not happen *)
    end
  .

  (* for backward compatibility: it should be used only when "args" is known to be C-style. *)
  (* it will return dummy value if it is assembly style. *)
  Definition m (retv: Retv.t): mem :=
    match retv with
    | Retv.Cstyle _ m => m
    | Retv.Asmstyle _ m => Mem.empty (* should not happen *)
    end
  .

  (* for backward compatibility *)
  Definition mk (v: val) (m: mem): t := Retv.Cstyle v m.

  Definition is_cstyle (retv: t): bool :=
    match retv with
    | Cstyle _ _ => true
    | _ => false
    end
  .

  Lemma get_m_m: forall retv (CSTYLE: is_cstyle retv), (get_m retv) = (m retv). Proof. destruct retv; ss. Qed.

End Retv.

Hint Unfold Args.is_cstyle Args.mk Args.fptr Args.vs Args.m Retv.is_cstyle Retv.mk Retv.v Retv.m.
Hint Constructors Args.t Retv.t.

Module ModSem.

  Record t: Type := mk {
    local_state: Type;
    shared_state: Type;
    genvtype: Type;
    state := (local_state * shared_state)%type;
    step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop;
    at_external (st0: state) (args: Args.t): Prop;
    initial_frame (args: Args.t) (st0: state): Prop;
    final_frame (st0: state) (retv: Retv.t): Prop;
    after_external (st0: state) (retv: Retv.t) (st1: state): Prop;
    globalenv: genvtype;
    skenv: SkEnv.t;
    skenv_link: SkEnv.t;

    at_external_dtm: forall st args0 args1
        (AT0: at_external st args0)
        (AT1: at_external st args1),
        args0 = args1;

    final_frame_dtm: forall st retv0 retv1
        (FINAL0: final_frame st retv0)
        (FINAL1: final_frame st retv1),
        retv0 = retv1;
    after_external_dtm: forall st_call retv st0 st1
        (AFTER0: after_external st_call retv st0)
        (AFTER0: after_external st_call retv st1),
        st0 = st1;


    is_call (st0: state): Prop := exists args, at_external st0 args;
    is_step (st0: state): Prop := exists tr st1, step skenv_link globalenv st0 tr st1;
    is_return (st0: state): Prop := exists retv, final_frame st0 retv;

    call_step_disjoint: is_call /1\ is_step <1= bot1;
    step_return_disjoint: is_step /1\ is_return <1= bot1;
    call_return_disjoint: is_call /1\ is_return <1= bot1;
  }.

  Ltac tac :=
    try( let TAC := u; esplits; eauto in
         u in *; des_safe;
         first[ exfalso; eapply ModSem.call_step_disjoint; TAC; fail
              | exfalso; eapply ModSem.step_return_disjoint; TAC; fail
              | exfalso; eapply ModSem.call_return_disjoint; TAC; fail]
       ).

  Definition to_semantics (ms: t) :=
    (Semantics_gen (@step ms) bot1 bot2 ms.(globalenv) ms.(skenv_link)).

  Module Atomic.
  Section Atomic.

    Local Coercion ModSem.to_semantics: ModSem.t >-> Smallstep.semantics.

    Variable ms: t.

    Let state := (trace * ms.(state))%type.

    Inductive step (se: Senv.t) (ge: ms.(genvtype)): state -> trace -> state -> Prop :=
    | step_silent
        st0 st1
        (STEPSIL: Step ms st0 E0 st1):
        step se ge (E0, st0) E0 (E0, st1)
    | step_start
        st0 st1 ev tr
        (STEPEV: Step ms st0 (ev :: tr) st1):
        step se ge (E0, st0) [ev] (tr, st1)
    | step_continue
        ev tr st0
        (WBT: output_trace (ev :: tr)):
        step se ge (ev :: tr, st0) [ev] (tr, st0).

    Definition at_external (st0: state) (args: Args.t): Prop :=
      (fst st0) = [] /\ (@at_external ms) (snd st0) args.

    Definition initial_frame (args: Args.t) (st0: state): Prop :=
      (fst st0) = [] /\ (@initial_frame ms) args (snd st0).

    Definition final_frame (st0: state) (retv: Retv.t): Prop :=
      (fst st0) = [] /\ (@final_frame ms) (snd st0) retv.

    Definition after_external (st0: state) (retv: Retv.t) (st1: state): Prop :=
      (fst st0) = [] /\ (@after_external ms) (snd st0) retv (snd st1) /\ (fst st1) = [].

    Program Definition trans: t :=
      mk step at_external initial_frame final_frame after_external
         ms.(globalenv) ms.(skenv) ms.(skenv_link) _ _ _ _ _ _.
    Next Obligation. rr in AT0. rr in AT1. des. eapply at_external_dtm; eauto. Qed.
    Next Obligation. rr in FINAL0. rr in FINAL1. des. eapply final_frame_dtm; eauto. Qed.
    Next Obligation.
      rr in AFTER0. rr in AFTER1. des. destruct s, s0; ss. clarify. f_equal.
      eapply after_external_dtm; eauto.
    Qed.
    Next Obligation.
      ii. des. destruct x0, st1; ss. rr in PR. ss. des. clarify.
      eapply call_step_disjoint; eauto. esplits; eauto.
      { rr. esplits; eauto. }
      { rr. inv PR0; esplits; eauto. }
    Qed.
    Next Obligation.
      ii. des. destruct x0, st1; ss. rr in PR0. ss. des. clarify.
      eapply step_return_disjoint; eauto. esplits; eauto; cycle 1.
      { rr. esplits; eauto. }
      { rr. inv PR; esplits; eauto. }
    Qed.
    Next Obligation.
      ii. des. destruct x0; ss. rr in PR. rr in PR0. ss. des. clarify.
      eapply call_return_disjoint; eauto. esplits; eauto; rr; esplits; eauto.
    Qed.

    Lemma atomic_continue tr0 tr1 st_src0
          (WBT: output_trace (tr1 ** tr0)):
      star step (skenv_link ms) (globalenv ms) (tr1 ** tr0, st_src0) tr1 (tr0, st_src0).
    Proof.
      ginduction tr1; ii; ss.
      { econs; eauto. }
      des. econs; eauto; cycle 1.
      { instantiate (1:= [_]). ss. }
      econs; eauto. ss.
    Qed.

    Lemma atomic_lift_step st_src0 tr st_src1
          (WBT: well_behaved_traces ms)
          (STEP: Step ms st_src0 tr st_src1):
      Star trans ([], st_src0) tr ([], st_src1).
    Proof.
      destruct tr; ss.
      { apply star_one. econs; eauto. }
      eapply star_trans; swap 2 3.
      { eapply star_one with (t := [e]). econs; eauto. }
      { ss. }
      rpapply atomic_continue; ss; unfold Eapp in *; try rewrite app_nil_r in *; eauto. exploit WBT; eauto.
    Qed.

    Lemma atomic_lift_star st_src0 tr st_src1
          (WBT: well_behaved_traces ms)
          (STAR: Star ms st_src0 tr st_src1):
      Star trans ([], st_src0) tr ([], st_src1).
    Proof.
      ginduction STAR; ii; ss.
      { econs; eauto. }
      eapply star_trans; eauto. clear - H WBT. exploit atomic_lift_step; eauto.
    Qed.

  End Atomic.
  End Atomic.

End ModSem.

Hint Unfold ModSem.is_call ModSem.is_step ModSem.is_return.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
