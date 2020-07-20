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
Require Import AxiomsC.

Set Implicit Arguments.



Section OWNEDHEAP.

Variable owned_heap: Type.

Section MODSEM.

  Variable mi: string.
  Variable sk: Sk.t.
  Variable skenv_link: SkEnv.t.
  Variable initial_owned_heap: owned_heap.
  Variable p: program owned_heap.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) sk.
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Definition genvtype: Type := unit.
  Let ge: genvtype := tt.

  Notation ktr :=
    (ktree (eff1 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
  .
  Notation itr := (itree (eff1 owned_heap) (owned_heap * (mem * val))).

  Record state: Type := mk {
    cur: itr;
    cont: list ktr;
  }
  .

  Notation update_cur := (fun (st0: state) (cur0: itr) => mk cur0 st0.(cont)).

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      itr fid blk m0 vs fd
      (CSTYLE: Args.is_cstyle args)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)

      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FINDF: Genv.find_funct skenv (Vptr blk Ptrofs.zero) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd (Args.vs args))
      (DEF: Forall (fun v => v <> Vundef) (Args.vs args))
      (* (TYP: Val.has_type_list (Args.vs args) fd.(sig_args)) *)

      st0
      (ITR: itr = (interp_function p (ICall fid oh0 m0 (Args.vs args))))
      (* (ST: st0 = (State itr)) *)
      (ST: st0 = mk itr nil)
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      args sg fptr vs k oh0 m0
      (VIS: st0.(cur) = Vis (subevent _ (ECall sg fptr oh0 m0 vs)) k)
      (EXT: Genv.find_funct skenv fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd
                        /\ sg = Sk.get_sig skd)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive get_k (st0: state):
    (owned_heap * (mem * val) -> itree (eff1 owned_heap) (owned_heap * (mem * val))) -> Prop :=
  | get_k_intro
      _vs _sg _fptr _oh0 _m0 k
      (VIS: st0.(cur) = Vis (subevent _ (ECall _sg _fptr _oh0 _m0 _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      (CSTYLE: Retv.is_cstyle retv)
      k m0 rv st1
      (GETK: get_k st0 k)
      (KONT: st1 = update_cur st0 (k (oh0, (m0, rv))))
      (RETV: retv = Retv.mk rv m0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val)
      (NCONT: st0.(cont) = nil)
      (RET: st0.(cur) = Ret (oh0, (m0, rv)))
    :
      final_frame st0 oh0 (Retv.mk rv m0)
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state): trace -> state -> Prop :=
  | step_tau
      itr0
      (TAU: st0.(cur) = Tau itr0)

    :
      step se ge st0 E0 (update_cur st0 itr0)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      k
      (VIS: st0.(cur) = Vis (subevent _ (ENB)) k)
    :
      step se ge st0 [Event_pterm] st0
  (* | step_done *)
  (*     oh rv m k *)
  (*     (VIS: st0.(cur) = Vis (subevent _ (EDone oh m rv)) k) *)
  (*   : *)
  (*     step se ge st0 E0 (update_cur st0 (Ret (oh, (m, rv)))) *)
  | step_choose
      X k (x: X)
      (VIS: st0.(cur) = Vis (subevent _ (EChoose X)) k)
    :
      step se ge st0 E0 (update_cur st0 (k x))
  | step_call
      (cur: itr) (cont: list ktr) X k (x: X) next
      (ST0: st0 = (mk cur cont))
      fid oh0 m0 vs0
      (VIS: cur = Vis (subevent _ (ICall fid oh0 m0 vs0)) k)
      (NEXT: next = interp_function p (ICall fid oh0 m0 vs0))
    :
      step se ge st0 E0 (mk next (k :: cont))
  | step_return
      (cur: itr) (hd: ktr) (tl: list ktr) oh0 m0 (rv: val)
      (ST0: st0 = mk cur (hd :: tl))
      (RET: cur = Ret (oh0, (m0, rv)))
      next
      (NEXT: next = (hd (oh0, (m0, rv))))
    :
      step se ge st0 E0 (mk next tl)
  .

  (*** TODO: remove needless "IN" and "itr0"s ***)
  (*** TODO: remove needless "IN" and "itr0"s ***)
  (*** TODO: remove needless "IN" and "itr0"s ***)
  (*** TODO: remove needless "IN" and "itr0"s ***)
  (*** TODO: remove needless "IN" and "itr0"s ***)

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
    inv AT0. inv AT1. rewrite VIS in *. rewrite VIS0 in *. clarify.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. rewrite RET in *. rewrite RET0 in *. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1.
    inv GETK. inv GETK0. clarify.
    rewrite VIS in *. rewrite VIS0 in *. clarify. simpl_depind. clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss.
    - rewrite TAU in *. clarify.
    - rewrite VIS in *. rewrite VIS0 in *. simpl_depind.
    - rewrite VIS in *. rewrite VIS0 in *. simpl_depind.
    (* - rewrite VIS in *. rewrite VIS0 in *. simpl_depind. *)
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss.
    - rewrite TAU in *. clarify.
    - rewrite RET in *. rewrite VIS in *. clarify.
    - rewrite RET in *. rewrite VIS in *. clarify.
    (* - rewrite RET in *. rewrite VIS in *. clarify. *)
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss.
    - rewrite RET in *. rewrite VIS in *. clarify.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; try (exploit external_call_receptive; eauto; check_safe; intro T; des); inv_match_traces; try (by esplits; eauto; econs; eauto).
    - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Unshelve.
    all: ss.
  Qed.

  Lemma modsem_determinate
        (st0: state)
        (NCHOOSE: forall X k, ~(st0.(cur) = Vis (subevent _ (EChoose X)) k))
        (NNB: forall k, ~(st0.(cur) = Vis (subevent _ ENB) k))
    :
      determinate_at modsem st0.
  Proof.
    econs; eauto.
    - ii; ss. destruct st0; ss.
      inv H; inv H0; cbn in *; subst; esplits; et; try econs; et; ii;
        simpl_depind;
        try (by injection ST0; ii; simpl_depind);
        try congruence.
      + simpl_depind. exploit NNB; et. i; ss.
      + simpl_depind. clarify. f_equal. exploit NCHOOSE; et. i; ss.
    - ii. inv H; ss; try xomega.
  Unshelve.
    all: des; ss; try (by exfalso; des; ss).
  Qed.

End MODSEM.

End OWNEDHEAP.



Module SMod.
Section SMOD.

  Variable owned_heap: Type.
  Coercion is_some_coercion {X}: (option X) -> bool := is_some.
  Record t: Type := mk {
    sk: Sk.t;
    prog: program owned_heap;
    midx: string;
    initial_owned_heap: SkEnv.t -> owned_heap;
    sk_incl: (internals sk) <1= prog;
  }
  .
  
  Program Definition to_module (smd: t): Mod.t :=
  {|
    Mod.data := smd.(prog); Mod.get_sk := fun _ => smd.(sk);
    Mod.get_modsem :=
      fun skenv_link p => modsem (smd.(midx)) (smd.(sk)) skenv_link
                                 (smd.(initial_owned_heap) skenv_link) (smd.(prog));
    Mod.midx := Some smd.(midx);
  |}.

End SMOD.
End SMod. 
Coercion SMod.to_module: SMod.t >-> Mod.t.

(*** From "SIRStack", build "SIR"***)
Require SIR.
Ltac mimic :=
  match goal with
  | [ |- context[SIRStack.SMod.to_module ?A] ] =>
    unfold A;
    match goal with
    | [ |- context[SIRStack.SMod.mk ?sk ?prog ?mi ?ioh ?sk_icl] ] =>
      instantiate (1:= [_]);
      instantiate (1:= SIR.SMod.mk sk _ mi ioh _); cycle 2;
      unfold prog;
      match goal with
      | [ |- context[add ?_j _ (add ?_i _ (add ?_h _ (add ?_g _ (add ?_f _ empty))))] ] =>
        instantiate (2:= add _j (fun _ _ _ => _) (add _i (fun _ _ _ => _) (add _h (fun _ _ _ => _)
                             (add _g (fun _ _ _ => _) (add _f (fun _ _ _ => _) empty)))))
      | [ |- context[add ?_i _ (add ?_h _ (add ?_g _ (add ?_f _ empty)))] ] =>
        instantiate (2:= add _i (fun _ _ _ => _) (add _h (fun _ _ _ => _)
                             (add _g (fun _ _ _ => _) (add _f (fun _ _ _ => _) empty))))
      | [ |- context[add ?_h _ (add ?_g _ (add ?_f _ empty))] ] =>
        instantiate (2:= add _h (fun _ _ _ => _)
                             (add _g (fun _ _ _ => _) (add _f (fun _ _ _ => _) empty)))
      | [ |- context[add ?_g _ (add ?_f _ empty)] ] =>
        instantiate (2:= add _g (fun _ _ _ => _) (add _f (fun _ _ _ => _) empty))
      | [ |- context[add ?_f _ empty] ] =>
        instantiate (2:= add _f (fun _ _ _ => _) empty)
      end
    end
  end
.

Ltac _step :=
  by (repeat match goal with
             | [ |- Clight.eval_lvalue _ _ _ _ (Clight.Evar _ _) _ _ ] => idtac "EVAR" ; econsby (ss; et)
             | [ |- Clight.deref_loc _ _ _ _ _ ] => idtac "DEREF" ; econsby (ss; et)
             | [ |- list_disjoint _ _ ] => ii; ss; by (repeat des; ss; clarify)
             | _ => econs; ss; et
             end)
.

Ltac is_state st := match st with
                    | Clight.State _ _ _ _ _ _ => idtac
                    | _ => fail
                    end
.

Ltac step :=
  repeat match goal with
(*** TODO: More precisely, what I want is as follows.
(1) Basically, we don't progress on Callstate.
(2) However, if it is the beginning, we allow it. (the only exception)

Coincidently, "Star" and "Plus" only appears in the beginning, so I defined as below.
***)
         | [ |- Plus _ _ E0 _ ] =>
           eapply plus_left with (t1 := E0) (t2 := E0); ss; [_step|]
         | [ |- Star _ _ E0 _ ] =>
           eapply star_left with (t1 := E0) (t2 := E0); ss; [_step|]
         | [ |- star Clight.step2 _ _ ?st E0 _ ] =>
           is_state st; eapply star_left with (t1 := E0) (t2 := E0); ss; [_step|]
         | [ |- list_disjoint _ _ ] => ii; ss; try (by repeat des; ss; clarify)
         end
.
