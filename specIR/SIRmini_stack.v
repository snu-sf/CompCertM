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
    (ktree (eff1 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
  .
  Notation itr := (itree (eff1 owned_heap) (owned_heap * (mem * val))).

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
      step se ge st0 E0 st0
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
    :
      determinate_at modsem st0.
  Proof.
    econs; eauto.
    - ii; ss. destruct st0; ss.
      inv H; inv H0; cbn in *; subst; esplits; et; try econs; et; ii;
        simpl_depind;
        try (by injection ST0; ii; simpl_depind);
        try congruence.
      + simpl_depind. clarify. f_equal. exploit NCHOOSE; et. i; ss.
    - ii. inv H; ss; try xomega.
  Unshelve.
    all: des; ss; try (by exfalso; des; ss).
  Qed.

End MODSEM.

Program Definition module (sk: Sk.t) (p: program _) (mi: string)
        (initial_owned_heap: SkEnv.t -> owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := fun _ => sk;
     Mod.get_modsem := fun skenv_link p => modsem mi sk skenv_link
                                                  (initial_owned_heap skenv_link) p;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.
