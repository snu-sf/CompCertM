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
(* Require Export SIRCommon. *)

Require Import Program.
Require Import Simulation.
Require Import AxiomsC.

Set Implicit Arguments.



(*** TODO: move to CoqlibC ***)
Global Unset Transparent Obligations.
Add Search Blacklist "_obligation_".










From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     OptionMonad
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Open Scope monad_scope.
Open Scope itree_scope.
Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 61, t at next level, t1 at next level, x ident, right associativity) : itree_scope.





Module Eqv.
Section Eqv.

  Variable X: Type.
  Context {eqv: X -> X -> Prop} `{Equivalence _ eqv}.

  Record t := mk {
    xs:> X -> Prop;
    sound: forall (x0 x1: X) (IN: xs x0) (IN: xs x1), <<EQV: eqv x0 x1>>;
    cmplt: forall x0 x1 (IN: xs x0) (EQV: eqv x0 x1), <<IN: xs x1>>;
  }
  .

  Lemma eta
        (t0 t1: t)
        (XS: t0.(xs) = t1.(xs))
    :
      <<EQ: t0 = t1>>
  .
  Proof.
    destruct t0, t1; ss. r.
    subst. f_equal.
    - eapply proof_irr.
    - eapply proof_irr.
  Qed.

  Lemma eqv_eq
        (t0 t1: t) x0 x1
        (EQV: eqv x0 x1)
        (IN0: t0 x0)
        (IN1: t1 x1)
    :
      <<EQ: t0 = t1>>
  .
  Proof.
    destruct t0, t1; ss.
    eapply eta; ss.
    apply func_ext1. ii. apply prop_ext. split; i.
    - assert(eqv x0 x2).
      { eapply sound0; et. }
      eapply cmplt1; et. etrans; et. sym. ss.
    - assert(eqv x1 x2).
      { eapply sound1; et. }
      eapply cmplt0; et. etrans; et.
  Qed.

  Program Definition lift (x0: X): t := {|
    xs := fun x1 => eqv x0 x1;
  |}
  .
  Next Obligation.
    r. etrans; et. sym. ss.
  Qed.
  Next Obligation.
    r. etrans; et.
  Qed.

  Lemma in_eqv
        (t0: t) x0 x1
        (IN0: t0 x0)
        (IN1: t0 x1)
    :
      <<EQV: eqv x0 x1>>
  .
  Proof.
    destruct t0; ss. et.
  Qed.

  Lemma lift_in
        x0
    :
      <<IN: lift x0 x0>>
  .
  Proof.
    unfold lift. ss. r. refl.
  Qed.

  Lemma eqv_lift
        x0 x1
        (EQV: eqv x0 x1)
    :
      <<EQ: lift x0 = lift x1>>
  .
  Proof.
    eapply eqv_eq in EQV; et.
    - eapply lift_in.
    - eapply lift_in.
  Qed.

  Lemma in_lift
        x0 x1
        (IN: (lift x0) x1)
    :
      <<EQV: eqv x0 x1>>
  .
  Proof.
    cbn in *. ss.
  Qed.

End Eqv.
End Eqv.

Coercion Eqv.xs: Eqv.t >-> Funclass.


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
  | ECall (sg: signature) (fptr: val)
          (oh: owned_heap) (m: mem) (vs: list val): EventE (owned_heap * (mem * val))
  | EDone (oh: owned_heap) (m: mem) (v: val): EventE void
  | EBP: EventE unit (* breakpoint for better "match_states" *)
  | EChoose (X: Type): EventE X
  .

  Definition eff0: Type -> Type := Eval compute in EventE.
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
Definition triggerDone {E A} `{EventE -< E} (oh: owned_heap) (m: mem) (v: val): itree E A :=
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

  (* Inductive state: Type := *)
  (* | State *)
  (*     (itr: itree eff0 (owned_heap * (mem * val))) *)
  (* | Callstate *)
  (*     (fptr: val) *)
  (*     (oh0: owned_heap) *)
  (*     (m0: mem) *)
  (*     (vs: list val) *)
  (*     (k: (owned_heap * (mem * val)) -> itree eff0 (owned_heap * (mem * val))) *)
  (* . *)

  Definition state: Type := (@Eqv.t (itree eff0 (owned_heap * (mem * val))) (eutt eq)).
  (* Record state := State { *)
  (*   itrs: itree eff0 (owned_heap * (mem * val)) -> Prop; *)
  (*   equiv: forall itr0 itr1 (IN: itrs itr0) (IN: itrs itr1), itr0 ≈ itr1; *)
  (* } *)
  (* . *)

  Let interp_program0 := interp_program0 p.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      itr fid blk m0 vs fd
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)

      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FINDF: Genv.find_funct skenv (Vptr blk Ptrofs.zero) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd (Args.vs args))
      (* (TYP: Val.has_type_list (Args.vs args) fd.(sig_args)) *)
      (DEF: Forall (fun v => v <> Vundef) (Args.vs args))

      st0
      (ITR: itr ≈ (interp_program0 (ICall fid oh0 m0 (Args.vs args))))
      (* (ST: st0 = (State itr)) *)
      (ST: st0 = Eqv.lift itr)
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      itr0 args sg fptr vs k oh0 m0
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ECall sg fptr oh0 m0 vs)) k)
      (EXT: Genv.find_funct skenv fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd
                        /\ sg = Sk.get_sig skd)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive get_k (st0: state):
    (owned_heap * (mem * val) -> itree eff0 (owned_heap * (mem * val))) -> Prop :=
  | get_k_intro
      itr0 _vs _sg _fptr _oh0 _m0 k
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ECall _sg _fptr _oh0 _m0 _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (KONT: st1 = Eqv.lift (k (oh0, (m0, rv))))
      (RETV: retv = Retv.mk rv m0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      itr0 oh0 m0 (rv: val)
      (IN: st0 itr0)
      (RET: itr0 ≈ Ret (oh0, (m0, rv)))
    :
      final_frame st0 oh0 (Retv.mk rv m0)
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state): trace -> state -> Prop :=
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
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ENB)) k)
    :
      step se ge st0 E0 st0
  | step_done
      itr0
      oh rv m k
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EDone oh m rv)) k)
    :
      step se ge st0 E0 (Eqv.lift (Ret (oh, (m, rv))))
  | step_breakpoint
      itr0 k
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EBP)) k)
    :
      step se ge st0 E0 (Eqv.lift (k tt))
  | step_choose
      itr0 X k (x: X)
      (IN: st0 itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EChoose X)) k)
    :
      step se ge st0 E0 (Eqv.lift (k x))
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
    inv AT0. inv AT1. determ_tac Eqv.in_eqv.
    rewrite VIS in *. rewrite VIS0 in *. eapply eqit_inv_vis in H. des; clarify.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. determ_tac Eqv.in_eqv.
    rewrite RET in *. rewrite RET0 in *. apply eqit_inv_ret in H. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1.
    inv GETK. inv GETK0. determ_tac Eqv.in_eqv.
    rewrite VIS in *. rewrite VIS0 in *. eapply eqit_inv_vis in H. des; clarify.
    eapply Eqv.eqv_lift; et.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss; determ_tac Eqv.in_eqv.
    - rewrite VIS in *. rewrite VIS0 in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
    - rewrite VIS in *. rewrite VIS0 in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
    - rewrite VIS in *. rewrite VIS0 in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
    - rewrite VIS in *. rewrite VIS0 in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss; determ_tac Eqv.in_eqv.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss. determ_tac Eqv.in_eqv.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Unshelve.
    all: ss.
  Qed.

  (* Inductive equiv: state -> state -> Prop := *)
  (* | equiv_state *)
  (*     itr0 itr1 *)
  (*     (EUTT: eutt eq itr0 itr1) *)
  (*   : *)
  (*     equiv (State itr0) (State itr1) *)
  (* . *)

  (* Theorem equiv_determ *)
  (*         st0 tr st1 *)
  (*         st'0 tr' st'1 *)
  (*         (EQ: equiv st0 st'0) *)
  (*         (STEP: Step modsem st0 tr st1) *)
  (*         (STEP': Step modsem st'0 tr' st'1) *)
  (*   : *)
  (*     tr = tr' /\ equiv st1 st'1 *)
  (* . *)
  (* Proof. *)
  (*   ss. *)
  (*   inv EQ. *)
  (*   - inv STEP; inv STEP'; ss; esplits; et; try (econs; et); *)
  (*       try (rewrite EUTT in *; *)
  (*            rewrite VIS in *; punfold VIS0; inv VIS0; simpl_depind; subst; simpl_depind). *)
  (*     + refl. *)
  (* Qed. *)

  Lemma modsem_determinate
        (st0: state)
        (NCHOOSE: forall X itr0 k (IN: st0 itr0), itr0 ≈ Vis (subevent _ (EChoose X)) k -> False)
    :
      determinate_at modsem st0.
  Proof.
    econs; eauto.
    - ii; ss.
      inv H; inv H0; esplits; et; try econs; et; ii; determ_tac Eqv.in_eqv;
        try (by rewrite VIS in *; rewrite VIS0 in *;
             punfold H0; inv H0; simpl_depind; subst; simpl_depind).
      + rewrite VIS in *. rewrite VIS0 in *. apply eqit_inv_vis in H0. des; clarify.
        eapply Eqv.eqv_lift; et.
      + exploit NCHOOSE; eauto. i; ss.
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

