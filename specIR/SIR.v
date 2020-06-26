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
Require Export ITreelib SIRCommon.

Require Import Program.
Require Import Simulation.

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

  Definition state: Type := itree (eff0 owned_heap) (owned_heap * (mem * val)).
  (* Record state := mk { *)
  (*   itr:> itree eff0 (owned_heap * (mem * val)); *)
  (* }. *)

  Let interp_program0 := interp_program p.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      (CSTYLE: Args.is_cstyle args)
      fid blk m0 vs fd
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)

      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FINDF: Genv.find_funct skenv (Vptr blk Ptrofs.zero) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd (Args.vs args))
      (DEF: Forall (fun v => v <> Vundef) (Args.vs args))

      st0
      (ITR: st0 = (interp_program0 (ICall fid oh0 m0 vs)))
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      args sg fptr vs k oh0 m0
      (VIS: st0 = Vis (subevent _ (ECall sg fptr oh0 m0 vs)) k)
      (EXT: Genv.find_funct skenv fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd
                        /\ sg = Sk.get_sig skd)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive get_k (st0: state):
    (owned_heap * (mem * val) -> itree (eff0 owned_heap) (owned_heap * (mem * val))) -> Prop :=
  | get_k_intro
      _vs _sg _fptr _oh0 _m0 k
      (VIS: st0 = Vis (subevent _ (ECall _sg _fptr _oh0 _m0 _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      (CSTYLE: Retv.is_cstyle retv)
      k m0 rv st1
      (GETK: get_k st0 k)
      (V: (Retv.v retv) = rv)
      (M: (Retv.m retv) = m0)
      (KONT: st1 = (k (oh0, (m0, rv))))
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val) retv
      (RET: st0 = Ret (oh0, (m0, rv)))
      (RETV: retv = Retv.mk rv m0)
    :
      final_frame st0 oh0 retv
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_tau
      (TAU: st0 = Tau st1)
      (TR: tr = E0)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      k
      (VIS: st0 = Vis (subevent _ (ENB)) k)

      (TR: tr = [Event_pterm])
      (ST: st1 = st0)
  (* | step_done *)
  (*     oh rv m k *)
  (*     (VIS: st0 = Vis (subevent _ (EDone oh m rv)) k) *)

  (*     (TR: tr = E0) *)
  (*     (ST1: st1 = (Ret (oh, (m, rv)))) *)
  | step_choose
      X k (x: X)
      (VIS: st0 = Vis (subevent _ (EChoose X)) k)
      (TR: tr = E0)
      (ST: st1 = k x)
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
    inv AT0. inv AT1. clarify.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1. inv GETK. inv GETK0. clarify.
    simpl_depind. clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss.
  Qed.
  Next Obligation.
    ii. des. inv PR0; ss. inv PR; ss; clarify; try rewrite RET in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss; clarify; try rewrite VIS in *; ss; clarify.
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
        (NCHOOSE: forall X k, ~(st0 = Vis (subevent _ (EChoose X)) k))
        (NNB: forall k, ~(st0 = Vis (subevent _ ENB) k))
    :
      determinate_at modsem st0.
  Proof.
    econs; eauto.
    - ii; ss.
      inv H; inv H0; esplits; et; try econs; et; ii; clarify.
      + simpl_depind. exploit NNB; et. i; ss.
      + simpl_depind. clarify. exploit NCHOOSE; et. i; ss.
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
