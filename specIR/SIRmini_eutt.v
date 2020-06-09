From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Export SIRCommon.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.




Open Scope itree_scope.

Lemma eq_eutt
      E R
      (a b: itree E R)
      (EQ: a = b)
  :
    eutt eq a b
.
Proof. i. clarify. refl. Qed.

Lemma vis_not_ret
      E R (r: R) X (e: E X) k
      (EUTT: Vis e k ≈ Ret r)
  :
    False
.
Proof. ii. punfold EUTT. inv EUTT. Qed.

(* Lemma eqit_inv_vis {E R1 R2 RR} b1 b2 {u1 u2} (e1: E u1) (e2: E u2) *)
(*       (k1: u1 -> itree E R1) (k2: u2 -> itree E R2) : *)
(*   eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2) -> *)
(*   u1 = u2 /\ e1 ~= e2 /\ (forall u1 u2 (EQ: u1 ~= u2), eqit RR b1 b2 (k1 u1) (k2 u2)). *)
(* Proof. *)
(*   intros. punfold H. repeat red in H. simpl in H. *)
(*   dependent destruction H. pclearbot. esplits; eauto. *)
(*   ii. apply JMeq_eq in EQ. clarify. *)
(* Qed. *)

Fail Lemma empty_nonempty
      (T: Type)
      (EQ: void = T)
      (INHAB: inhabited T)
  :
    False
.
(* Proof. *)
(*   inversion INHAB. rewrite <- EQ in H. inv H. *)
(* Qed. *)








Section OWNEDHEAP.

Variable owned_heap: Type.





Section EFF.

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (oh: owned_heap) (m: mem) (vs: list val):
      InternalCallE (owned_heap * (mem * val))
  .

  Variant EventE: Type -> Type :=
  | ENB: EventE void
  | EUB: EventE void
  | ESyscall (ef: external_function) (m: mem) (args: list val): EventE (val * mem)
  | ECall (fptr: val) (oh: owned_heap) (m: mem) (vs: list val): EventE (owned_heap * (mem * val))
  .

  Variant DoneE: Type -> Type :=
  | EDone (oh: owned_heap) (m: mem) (v: val): DoneE void
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' DoneE +' EventE.
  Definition eff1: Type -> Type := Eval compute in InternalCallE +' eff0.
  Definition E := Eval compute in eff1.

End EFF.

(* Q: Why manually match "void" type, not using "embed" or "trigger"?
   A: It returns arbitrary type "A", not "void" *)
Definition triggerUB {E A} `{EventE -< E}: itree E A :=
  vis (EUB) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E}: itree E A :=
  vis (ENB) (fun v => match v: void with end)
.
Definition triggerDone {E A} `{DoneE -< E} (oh: owned_heap) (m: mem) (v: val): itree E A :=
  vis (EDone oh m v) (fun v => match v: void with end)
.

Definition unwrapN {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB
  end.

Definition unwrapU {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB
  end.

Record function : Type := mkfunction
  { fn_sig: signature;
    fn_code: (forall (oh: owned_heap) (m: mem) (vs: list val),
                 itree E (owned_heap * (mem * val))); }
.

Definition program: Type := AST.program (fundef function) unit.





Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition interp_function: (InternalCallE ~> itree E) :=
    fun T ei =>
      let '(ICall func_name oh m vs) := ei in
      match (find (fun nf => ident_eq func_name (fst nf)) p.(prog_defs)) with
      | Some (_, Gfun (Internal f)) =>
        (f.(fn_code) oh m vs)
      | _ => triggerNB
      end
  .

  Definition interp_program0:
    (forall T, InternalCallE T -> itree eff0 T) :=
    fun _ ic =>
      let sem0: itree eff0 _ := (mrec interp_function) _ ic in
      sem0
  .

End DENOTE.






Section TEST.

Definition _sum := 55%positive.
  
Definition c_sum (oh: owned_heap) (m: mem) (vs: list val): itree E (owned_heap * (mem * val)) :=
  match vs with
  | [Vint n] =>
    if Int.eq n Int.zero
    then Ret (oh, (m, (Vint Int.zero)))
    else '(oh, (m, s)) <- trigger (ICall _sum oh m [Vint (Int.sub n Int.one)]) ;;
         Ret (oh, (m, (Val.add s (Vint n))))
  | _ => triggerUB
  end
.

Definition f_sum: function :=
  mkfunction signature_main c_sum
.

Definition global_definitions: list (ident * globdef (fundef (function)) unit) :=
  ((_sum, Gfun(Internal f_sum)) :: nil)
.

Definition p: program := mkprogram global_definitions nil 1%positive.

Variable initial_oh: owned_heap.
Let one := (interp_program0 p (ICall _sum initial_oh Mem.empty [Vint (Int.repr 1%Z)])).
(* Compute (burn 1 one). *)

Lemma one_spec
  :
    one ≈ Ret (initial_oh, (Mem.empty, Vint (Int.repr 1%Z)))
.
Proof.
  subst one. unfold interp_program0. ss.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  replace (Int.add Int.zero (Int.repr 1)) with (Int.repr 1); cycle 1.
  { refl. }
  refl.
Qed.

End TEST.





Section MODSEM.

  Variable mi: string.
  Variable skenv_link: SkEnv.t.
  Variable initial_owned_heap: owned_heap.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Definition genvtype: Type := unit.
  Let ge: genvtype := tt.

  Inductive state: Type :=
  | State
      (itr: itree eff0 (owned_heap * (mem * val)))
  | Callstate
      (fptr: val)
      (oh0: owned_heap)
      (m0: mem)
      (vs: list val)
      (k: (owned_heap * (mem * val)) -> itree eff0 (owned_heap * (mem * val)))
  .

  (* Record state := mk { *)
  (*   itr:> itree eff0 (owned_heap * (mem * val)); *)
  (* }. *)

  Let interp_program0 := interp_program0 p.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      itr fid blk m0 vs fd tvs
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)

      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FINDF: Genv.find_funct skenv (Vptr blk Ptrofs.zero) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd tvs)

      st0
      (ITR: itr ≈ (interp_program0 (ICall fid oh0 m0 vs)))
      (ST: st0 = (State itr))
    :
      initial_frame oh0 args st0
  .

  Inductive at_external: state -> owned_heap -> Args.t -> Prop :=
  | at_external_intro
      fptr vs k oh0 m0
    :
      at_external (Callstate fptr oh0 m0 vs k) oh0 (Args.mk fptr vs m0)
  .

  Inductive after_external: state -> owned_heap -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr oh0 m0 vs oh1 m1 rv
      k itr0
      (KONT: itr0 = (k (oh1, (m1, rv))))
    :
      after_external (Callstate fptr oh0 m0 vs k) oh1 (Retv.mk rv m1) (State itr0)
  .

  Inductive final_frame: state -> owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      itr0 oh0 m0 (rv: val)
      (RET: itr0 ≈ Ret (oh0, (m0, rv)))
    :
      final_frame (State itr0) oh0 (Retv.mk rv m0)
  .

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  (* | step_tau *)
  (*     itr0 *)
  (*     itr1 *)
  (*     (TAU: st0.(itr) = Tau itr1) *)

  (*     (ST0: st0 = mk itr0) *)
  (*     (TR: tr = E0) *)
  (*     (ST1: st1 = mk itr1) *)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      itr0 k
      (VIS: itr0 ≈ Vis (subevent _ (ENB)) k)
    :
      step se ge (State itr0) E0 (State itr0)
  | step_extcall
      itr0 k fptr oh0 m0 vs
      (VIS: itr0 ≈ Vis (subevent _ (ECall fptr oh0 m0 vs)) k)
    :
      step se ge (State itr0) E0 (Callstate fptr oh0 m0 vs k)
  | step_syscall
      itr0 tr m0 m1
      ef vs rv k
      (VIS: itr0 ≈ Vis (subevent _ (ESyscall ef m0 vs)) k)
      (SYSCALL: external_call ef se vs m0 tr rv m1)
    :
      step se ge (State itr0) tr (State (k (rv, m1)))
  | step_done
      itr0
      oh rv m k
      (VIS: itr0 ≈ Vis (subevent _ (EDone oh m rv)) k)
    :
      step se ge (State itr0) E0 (State (Ret (oh, (m, rv))))
  .

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.owned_heap := owned_heap;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.initial_owned_heap := initial_owned_heap;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := Some mi;
    |}.
  Next Obligation.
    inv AT0. inv AT1. esplits; et.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. rewrite RET in *. apply eqit_inv_ret in RET0. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1. f_equal.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss; try rewrite VIS in RET; exploit vis_not_ret; et.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Unshelve.
    all: ss.
  Qed.

  Inductive equiv: state -> state -> Prop :=
  | equiv_state
      itr0 itr1
      (EUTT: eutt eq itr0 itr1)
    :
      equiv (State itr0) (State itr1)
  | equiv_callstate
      k0 k1
      fptr oh m vs
      (EUTT: forall x, eutt eq (k0 x) (k1 x))
    :
      equiv (Callstate fptr oh m vs k0) (Callstate fptr oh m vs k1)
  .

  Theorem equiv_determ
          st0 tr st1
          st'0 tr' st'1
          (EQ: equiv st0 st'0)
          (STEP: Step modsem st0 tr st1)
          (STEP': Step modsem st'0 tr' st'1)
    :
      tr = tr' /\ equiv st1 st'1
  .
  Proof.
    ss.
    inv EQ.
    - inv STEP; inv STEP'; ss; esplits; et; try (econs; et);
        try (rewrite EUTT in *;
             rewrite VIS in *; punfold VIS0; inv VIS0; simpl_depind; subst; simpl_depind).
      + econs; et. ii. hexploit (REL x); et. intro T. unfold id in T. pclearbot. et.
      + try (determ_tac external_call_determ; check_safe).
        eapply REL.
      + rewrite EUTT in *.
        rewrite VIS in *; punfold VIS0; inv VIS0; simpl_depind; subst; simpl_depind.
      + rewrite EUTT in *.
        rewrite VIS in *; punfold VIS0; inv VIS0; simpl_depind; subst; simpl_depind.
        clarify.
    esplits; et.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss.
      inv H; inv H0; esplits; et; try econs; et;
        try by (rewrite VIS in *; punfold VIS0; inv VIS0; simpl_depind; subst; simpl_depind).
      + rewrite VIS in *. apply eqit_inv_vis in VIS0. des. clarify.
        esplits; et.
        admit "relax eq to equiv".
      + rewrite VIS in *. punfold VIS0. inv VIS0. simpl_depind. subst. simpl_depind.
        try (determ_tac external_call_determ; check_safe).
      + rewrite VIS in *. punfold VIS0. inv VIS0. simpl_depind. subst. simpl_depind.
        ii; clarify. try (determ_tac external_call_determ; check_safe).
        exploit H0; et. i; des. clarify.
        f_equal.
        admit "relax eq to equiv".
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Unshelve.
    all: des; ss; try (by exfalso; des; ss).
  Qed.

End MODSEM.

Program Definition module (p: program) (mi: string) (initial_owned_heap: SkEnv.t -> owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := (Sk.of_program fn_sig);
     Mod.get_modsem := fun skenv_link p => modsem mi skenv_link
                                                  (initial_owned_heap skenv_link) p;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.

