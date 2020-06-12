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
Require Export SIRCommon2.

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
    (@Eqv.t (ktree (eff1 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
            eq2)
  .
  Notation itr := (@Eqv.t (itree (eff1 owned_heap) (owned_heap * (mem * val))) (eutt eq)).

  Record state: Type := mk {
    cur: itr;
    cont: list ktr;
  }
  .

  Notation update_cur := (fun (st0: state) (cur0: itr) => mk cur0 st0.(cont)).

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
      (ITR: itr ≈ (interp_function p (ICall fid oh0 m0 (Args.vs args))))
      (* (ST: st0 = (State itr)) *)
      (ST: st0 = mk (Eqv.lift itr) nil)
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      itr0 args sg fptr vs k oh0 m0
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ECall sg fptr oh0 m0 vs)) k)
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
      itr0 _vs _sg _fptr _oh0 _m0 k
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ECall _sg _fptr _oh0 _m0 _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (KONT: st1 = update_cur st0 (Eqv.lift (k (oh0, (m0, rv)))))
      (RETV: retv = Retv.mk rv m0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      itr0 oh0 m0 (rv: val)
      (IN: st0.(cur) itr0)
      (NCONT: st0.(cont) = nil)
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
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ENB)) k)
    :
      step se ge st0 E0 st0
  | step_done
      itr0
      oh rv m k
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EDone oh m rv)) k)
    :
      step se ge st0 E0 (update_cur st0 (Eqv.lift (Ret (oh, (m, rv)))))
  | step_breakpoint
      itr0 k
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EBP)) k)
    :
      step se ge st0 E0 (update_cur st0 (Eqv.lift (k tt)))
  | step_choose
      itr0 X k (x: X)
      (IN: st0.(cur) itr0)
      (VIS: itr0 ≈ Vis (subevent _ (EChoose X)) k)
    :
      step se ge st0 E0 (update_cur st0 (Eqv.lift (k x)))
  | step_call
      (cur: itr) (cont: list ktr) itr0 X k (x: X) next
      (ST0: st0 = (mk cur cont))
      fid oh0 m0 vs0
      (IN: cur itr0)
      (VIS: itr0 ≈ Vis (subevent _ (ICall fid oh0 m0 vs0)) k)
      (NEXT: next ≈ interp_function p (ICall fid oh0 m0 vs0))
    :
      step se ge st0 E0 (mk (Eqv.lift next) ((Eqv.lift k) :: cont))
  | step_return
      (cur: itr) (hd: ktr) (tl: list ktr) itr0 oh0 m0 (rv: val)
      (ST0: st0 = mk cur (hd :: tl))
      (IN: cur itr0)
      (RET: itr0 ≈ Ret (oh0, (m0, rv)))
      next
      ktr0
      (HD: hd ktr0)
      (NEXT: next ≈ (ktr0 (oh0, (m0, rv))))
    :
      step se ge st0 E0 (mk (Eqv.lift next) tl)
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
    f_equal.
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
    - rewrite VIS in *. rewrite VIS0 in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
    - rewrite VIS in *. rewrite RET in *.
      punfold H; inv H; simpl_depind; subst; simpl_depind.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss; inv PR0; ss; determ_tac Eqv.in_eqv.
    - rewrite RET in *. rewrite VIS in *. exploit vis_not_ret; et.
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

  (* Lemma modsem_determinate *)
  (*       (st0: state) *)
  (*       (NCHOOSE: forall X itr0 k (IN: st0.(cur) itr0), itr0 ≈ Vis (subevent _ (EChoose X)) k -> False) *)
  (*   : *)
  (*     determinate_at modsem st0. *)
  (* Proof. *)
  (*   econs; eauto. *)
  (*   - ii; ss. *)
  (*     inv H; inv H0; esplits; et; try econs; et; ii; determ_tac Eqv.in_eqv; *)
  (*       try (by rewrite VIS in *; rewrite VIS0 in *; *)
  (*            punfold H0; inv H0; simpl_depind; subst; simpl_depind). *)
  (*     + rewrite VIS in *. rewrite VIS0 in *. apply eqit_inv_vis in H0. des; clarify. *)
  (*       eapply Eqv.eqv_lift; et. *)
  (*     + exploit NCHOOSE; eauto. i; ss. *)
  (*   - ii. inv H; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega. *)
  (* Unshelve. *)
  (*   all: des; ss; try (by exfalso; des; ss). *)
  (* Qed. *)

End MODSEM.

Program Definition module (sk: Sk.t) (p: program _) (mi: string)
        (initial_owned_heap: SkEnv.t -> owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := fun _ => sk;
     Mod.get_modsem := fun skenv_link p => modsem mi sk skenv_link
                                                  (initial_owned_heap skenv_link) p;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.

