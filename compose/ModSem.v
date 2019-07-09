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

  Lemma get_m_m: forall args (CSTYLE: is_cstyle args), args.(get_m) = args.(m). Proof. destruct args; ss. Qed.

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

  Lemma get_m_m: forall retv (CSTYLE: is_cstyle retv), retv.(get_m) = retv.(m). Proof. destruct retv; ss. Qed.

End Retv.

Hint Unfold Args.is_cstyle Args.mk Args.fptr Args.vs Args.m Retv.is_cstyle Retv.mk Retv.v Retv.m.
Hint Constructors Args.t Retv.t.

Module ModSem.

  Record t: Type := mk {
    state: Type;
    genvtype: Type;
    step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop;
    (* TOOD: is ge needed? I follow compcert for now. *)

    (* set_mem (m0: mem) (st0: state): state; *) (* This is not used, after_external is enough *)
    at_external (st0: state) (args: Args.t): Prop;
    initial_frame (args: Args.t) (st0: state): Prop;
    (* time: rs_arg >> st0 *)
    final_frame (* (st_init: state) *) (st0: state) (retv: Retv.t): Prop;
    (* time: st0 >> rs_arg *)
    after_external (st0: state) (retv: Retv.t) (st1: state): Prop;
    globalenv: genvtype;
    (* internals: list block; *)
    (* internals: block -> Prop; *)
    (* main_fptr: block; *)
    (* Note: "internals" is not enough! A ModSemPair should be able to specify which SimMem it relys. *)
    skenv: SkEnv.t;
    skenv_link: SkEnv.t;
    (* skenv: SkEnv.t; *)
    (* ########################################## I added SkEnv.t only for defining "compat" in sim_mem. *)
    (* If it is not used, remove it *)


    (* good properties *)
    (* We need to drop permission ! *)
    (* initial_machine_get_mem: forall *)
    (*     rs_arg m_arg st0 *)
    (*     (INIT: initial_frame rs_arg m_arg st0) *)
    (*   , *)
    (*     <<MEM: st0.(get_mem) = m_arg>> *)
    (* ; *)

    at_external_dtm: forall st args0 args1
        (AT0: at_external st args0)
        (AT1: at_external st args1),
        args0 = args1;

    final_frame_dtm: forall st retv0 retv1
        (FINAL0: final_frame st retv0)
        (FINAL1: final_frame st retv1),
        retv0 = retv1;
    (* final_frame_dtm: forall *)
    (*     rs_init st rs_ret0 m_ret0 rs_ret1 m_ret1 *)
    (*     (FINAL0: final_frame rs_init st rs_ret0 m_ret0) *)
    (*     (FINAL1: final_frame rs_init st rs_ret1 m_ret1) *)
    (*   , *)
    (*     rs_ret0 = rs_ret1 /\ m_ret0 = m_ret1 *)
    (* ; *)
    after_external_dtm: forall st_call retv st0 st1
        (AFTER0: after_external st_call retv st0)
        (AFTER0: after_external st_call retv st1),
        st0 = st1;


    is_call (st0: state): Prop := exists args, at_external st0 args;
    is_step (st0: state): Prop := exists tr st1, step skenv_link globalenv st0 tr st1;
    is_return (st0: state): Prop := exists retv, final_frame st0 retv;
      (* exists rs_init rs_ret m_ret, final_frame rs_init st0 rs_ret m_ret; *)
    (* Note: "forall" or "exists" for rs_init? *)
    (* "forall" -> easy for opt/hard for meta *)
    (* "exists" -> hard for opt/easy for meta *)
    (* I think "exists" is OK here. *)
    (* We can think of something like "forall rs_init (FUTURE: st0 is future of rs_init)", but is overkill. *)

    call_step_disjoint: is_call /1\ is_step <1= bot1;
    step_return_disjoint: is_step /1\ is_return <1= bot1;
    call_return_disjoint: is_call /1\ is_return <1= bot1;
  }.

  (* Note: I didn't want to define this tactic. I wanted to use eauto + Hint Resolve, but it didn't work. *)
  Ltac tac :=
    try( let TAC := u; esplits; eauto in
         u in *; des_safe;
         first[ exfalso; eapply ModSem.call_step_disjoint; TAC; fail
              | exfalso; eapply ModSem.step_return_disjoint; TAC; fail
              | exfalso; eapply ModSem.call_return_disjoint; TAC; fail]
       ).

  Definition to_semantics (ms: t) :=
    (Semantics_gen ms.(step) bot1 bot2 ms.(globalenv) ms.(skenv_link)).

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
      st0.(fst) = [] /\ ms.(at_external) st0.(snd) args.

    Definition initial_frame (args: Args.t) (st0: state): Prop :=
      st0.(fst) = [] /\ ms.(initial_frame) args st0.(snd).

    Definition final_frame (st0: state) (retv: Retv.t): Prop :=
      st0.(fst) = [] /\ ms.(final_frame) st0.(snd) retv.

    Definition after_external (st0: state) (retv: Retv.t) (st1: state): Prop :=
      st0.(fst) = [] /\ ms.(after_external) st0.(snd) retv st1.(snd) /\ st1.(fst) = [].

    Program Definition trans: t :=
      mk step at_external initial_frame final_frame after_external
         ms.(globalenv) ms.(skenv) ms.(skenv_link) _ _ _ _ _ _.
    Next Obligation. rr in AT0. rr in AT1. des. eapply at_external_dtm; eauto. Qed.
    Next Obligation. rr in FINAL0. rr in FINAL1. des. eapply final_frame_dtm; eauto. Qed.
    Next Obligation.
      rr in AFTER0. rr in AFTER1. des. destruct st0, st1; ss. clarify. f_equal.
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

  End Atomic.
  End Atomic.

End ModSem.

Hint Unfold ModSem.is_call ModSem.is_step ModSem.is_return.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
(* I want to use definitions like "Star" or "determinate_at" *)
