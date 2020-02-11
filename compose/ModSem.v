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

(* I want to make "Midx.t" somewhat opaque.
   "Global Opaque" keyword or "let tmp := 42 in nat" approach --> not really opaque.
   Module Type approach --> it works, but too much unwanted complexity.
   Record wrapper --> too inconvenient. we can add coercions but then there is no meaning..
 *)
(* Note: I tried to make Midx.t more opaque (not exploiting "Midx.t == nat"),
   but the object we will be handling (SimMemOhs.t) is inductively defined like a list,
   and I need to exploit (Midx.t == nat) somewhere.
 *)
(* TODO: move to CoqlibC *)
Module Midx.
Section Midx.
  Definition t: Type := nat.
  (* Definition nat2t: nat -> t := fun n => wrap n. *)
  (* Definition t2nat: t -> nat := fun t => unwrap t. *)
  (* Coercion nat2t: nat >-> t. *)
  (* Coercion t2nat: t >-> nat. *)

  (* Let mapi_aux A B (f: t -> A -> B) := *)
  Definition mapi_aux A B (f: t -> A -> B) :=
    let fix rec (cur : t) (la : list A) {struct la}: list B :=
        match la with
        | [] => []
        | hd :: tl => f cur hd :: rec (S cur) tl
        end
    in rec.

  Definition mapi A B (f: t -> A -> B) (la: list A): list B :=
    mapi_aux f (1%nat) la.

  Lemma in_mapi_aux_iff
        A B (f: t -> A -> B) la b
    :
      forall m,
      In b (mapi_aux f m la) <->
      (exists idx a, f (m + idx)%nat a = b /\ nth_error la idx = Some a)
  .
  Proof.
    ginduction la; split; ii; ss; des; firstorder (subst; auto).
    - destruct idx; ss.
    - exists 0%nat. rewrite Nat.add_0_r. esplits; eauto.
    - exploit IHla; eauto. intros [T _]. exploit T; eauto. i; des. esplits; eauto.
      { rp; eauto. f_equal. instantiate (1:= (S idx%nat)). omega. }
      ss.
    - destruct idx; ss; clarify.
      { left. f_equal. omega. }
      right. eapply IHla; eauto. esplits; eauto.
      { rp; eauto. f_equal. omega. }
  Qed.

  (* NOTE: If you give name << >>, rewrite tactic does not work... *)
  (* TODO: FIX IT *)
  Lemma in_mapi_iff
        A B (f: t -> A -> B) la b
    :
      (* (<<IN: In b (mapi f la)>>) <-> *)
      (* (<<NTH: (exists idx a, f idx a = b /\ nth_error la idx = Some a)>>) *)
      In b (mapi f la) <->
      (exists idx a, f (S idx) a = b /\ nth_error la idx = Some a)
  .
  Proof.
    eapply in_mapi_aux_iff.
  Qed.

  (* Let tmp: <<L: False>> <-> <<R: (0=1)%nat>>. Proof. ss. Qed. *)
  (* Let tmp2: False <-> (0=1)%nat. Proof. ss. Qed. *)
  (* Goal forall (H: (0=1)%nat /\ True), False. *)
  (*   intro. *)
  (*   rewrite <- tmp in H. Undo 1. *)
  (*   rewrite <- tmp2 in H. firstorder. *)
  (* Qed. *)

  Definition update X (map: t -> X) (t0: t) (x: X): t -> X :=
    fun t1 => if Nat.eqb t0 t1 then x else map t1.

  (* Fixpoint update A (la: list A) (midx: t) (a: A): list A := *)
  (*   match midx with *)
  (*   | O =>  *)
  (*     match la with *)
  (*     | hd :: tl => a :: tl *)
  (*     | _ => la *)
  (*     end *)
  (*   | S midx => *)
  (*     match la with *)
  (*     | hd :: tl => hd :: (update tl midx a) *)
  (*     | _ => la *)
  (*     end *)
  (*   end *)
  (* . *)

  (* Lemma update_spec *)
  (*       A (la: list A) midx a *)
  (*   : *)
  (*     forall n (LT: (n < length la)%nat), *)
  (*       <<NTH: nth_error (update la midx a) n = if Nat.eqb n midx *)
  (*                                               then Some a *)
  (*                                               else nth_error la n>>. *)
  (* Proof. *)
  (*   ginduction la; ii; ss. *)
  (*   { omega. } *)
  (*   destruct n; ss. *)
  (*   { des_ifs; ss. } *)
  (*   destruct midx; ss. *)
  (*   exploit (IHla midx a0 n); eauto. { omega. } *)
  (* Qed. *)

End Midx.
End Midx.

(* TODO: move to CoqlibC? *)
(* Definition is_eq: comparison -> bool := fun cmp => match cmp with | Eq => true | _ => false end. *)
(* Coercion is_eq: comparison >-> bool. *)

Module ModSem.

  Record t: Type := mk {
    state: Type;
    owned_heap: Type;
    genvtype: Type;
    step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop;
    at_external (st0: state) (oh: owned_heap) (args: Args.t): Prop;
    initial_frame (oh: owned_heap) (args: Args.t) (st0: state): Prop;
    final_frame (st0: state) (oh: owned_heap) (retv: Retv.t): Prop;
    after_external (st0: state) (oh: owned_heap) (retv: Retv.t) (st1: state): Prop;
    initial_owned_heap: owned_heap;
    globalenv: genvtype;
    skenv: SkEnv.t;
    skenv_link: SkEnv.t;
    midx: Midx.t;

    at_external_dtm: forall st oh0 oh1 args0 args1
        (AT0: at_external st oh0 args0)
        (AT1: at_external st oh1 args1),
        oh0 = oh1 /\ args0 = args1;

    final_frame_dtm: forall st oh0 oh1 retv0 retv1
        (FINAL0: final_frame st oh0 retv0)
        (FINAL1: final_frame st oh1 retv1),
        oh0 = oh1 /\ retv0 = retv1;
    after_external_dtm: forall st_call oh retv st0 st1
        (AFTER0: after_external st_call oh retv st0)
        (AFTER0: after_external st_call oh retv st1),
        st0 = st1;


    is_call (st0: state): Prop := exists oh args, at_external st0 oh args;
    is_step (st0: state): Prop := exists tr st1, step skenv_link globalenv st0 tr st1;
    is_return (st0: state): Prop := exists oh retv, final_frame st0 oh retv;

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
    (Semantics_gen ms.(step) bot1 bot2 ms.(globalenv) ms.(skenv_link)).

  Module Atomic.
  Section Atomic.

    Local Coercion ModSem.to_semantics: ModSem.t >-> Smallstep.semantics.

    Variable ms: t.

    Let state := (trace * ms.(state))%type.
    Let owned_heap := ms.(owned_heap).

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

    Definition at_external (st0: state) (oh: owned_heap) (args: Args.t): Prop :=
      (fst st0) = [] /\ ms.(at_external) (snd st0) oh args.

    Definition initial_frame (oh: owned_heap) (args: Args.t) (st0: state): Prop :=
      (fst st0) = [] /\ ms.(initial_frame) oh args (snd st0).

    Definition final_frame (st0: state) (oh: owned_heap) (retv: Retv.t): Prop :=
      (fst st0) = [] /\ ms.(final_frame) (snd st0) oh retv.

    Definition after_external (st0: state) (oh: owned_heap) (retv: Retv.t) (st1: state): Prop :=
      (fst st0) = [] /\ ms.(after_external) (snd st0) oh retv (snd st1) /\ (fst st1) = [].

    Program Definition trans: t :=
      mk step at_external initial_frame final_frame after_external
         ms.(initial_owned_heap) ms.(globalenv) ms.(skenv) ms.(skenv_link) ms.(midx) _ _ _ _ _ _.
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
      eapply star_trans; eauto. clear - owned_heap H WBT. exploit atomic_lift_step; eauto.
    Qed.

  End Atomic.
  End Atomic.

End ModSem.

Hint Unfold ModSem.is_call ModSem.is_step ModSem.is_return.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
