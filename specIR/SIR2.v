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

Set Implicit Arguments.




Section OWNEDHEAP.

Variable owned_heap: Type.

Let eff1: Type -> Type := eff1 owned_heap.
Let eff2: Type -> Type := eff2 owned_heap.
Let eff3: Type -> Type := eff3 owned_heap.
Let eff4: Type -> Type := eff4 owned_heap.
Let eff5: Type -> Type := eff5 owned_heap.
Let E: Type -> Type := E owned_heap.
Let OwnedHeapE: Type -> Type := OwnedHeapE owned_heap.
Let program: Type := program owned_heap.
Let fn_sig := @fn_sig owned_heap.

Section MODSEM.

  Variable mi: string.
  Variable skenv_link: SkEnv.t.
  Variable initial_owned_heap: owned_heap.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Definition genvtype: Type := unit.
  Let ge: genvtype := tt.

  Record state := mk {
    itr:> itree eff2 val;
    oh: owned_heap;
    m: mem;
  }.

  Let interp_program2 := interp_program2 p skenv.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fid blk m0 vs itr fd tvs
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)

      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FINDF: Genv.find_funct skenv (Vptr blk Ptrofs.zero) = Some (Internal fd))
      (TYP: typecheck (Args.vs args) fd tvs)
      (PROG: interp_program2 (ICall fid vs) = itr)

      st0
      (ST: st0 = (mk itr oh0 m0))
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      args fptr vs k
      (VIS: (observe st0) = VisF (subevent _ (ECall fptr vs)) k)
      (ARGS: args = Args.mk fptr vs st0.(m))
    :
      at_external st0 st0.(oh) args
  .

  Inductive get_k (st0: state): (val -> itree eff2 val) -> Prop :=
  | get_k_intro
      _vs _fptr k
      (VIS: (observe st0) = VisF (subevent _ (ECall _fptr _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (V: (Retv.v retv) = rv)
      (M: (Retv.m retv) = m0)
      (KONT: st1 = mk (k rv) oh0 m0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val) retv
      (RET: (observe st0) = RetF rv)
      (RETV: retv = Retv.mk rv m0)
      (M: m0 = st0.(m))
      (OH: oh0 = st0.(oh))
    :
      final_frame st0 oh0 retv
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_tau
      itr0 oh0 m0
      itr1
      (TAU: (observe itr0) = TauF itr1)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk itr1 oh0 m0)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      msg k
      (VIS: (observe st0) = VisF (subevent _ (ENB msg)) k)

      (TR: tr = E0)
  | step_syscall
      itr0 oh0 m0
      ef vs rv m1 k
      (VIS: (observe st0) = VisF (subevent _ (ESyscall ef vs)) k)
      (SYSCALL: external_call ef se vs m0 tr rv m1)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k rv) oh0 m1)
  | step_done
      itr0 oh0 m0
      v k
      (VIS: (observe st0) = VisF (subevent _ (EDone v)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (Ret v) oh0 m0)
  | step_mget
      itr0 oh0 m0
      k
      (VIS: (observe st0) = VisF (subevent _ (Get _)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k m0) oh0 m0)
  | step_mput
      itr0 oh0 m0
      m1 k
      (VIS: (observe st0) = VisF (subevent _ (Put _ m1)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k tt) oh0 m1)
  | step_ohget
      itr0 oh0 m0
      k
      (VIS: (observe st0) = VisF (subevent _ (Get _)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k oh0) oh0 m0)
  | step_ohput
      itr0 oh0 m0
      oh1 k
      (VIS: (observe st0) = VisF (subevent _ (Put _ oh1)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k tt) oh1 m0)
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
    inv AT0. inv AT1. rewrite VIS in *. clarify.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. rewrite RET in *. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1. inv GETK. inv GETK0. rewrite VIS in *.
    ss. clarify. simpl_depind. clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss; clarify; try rewrite VIS in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR0; ss. inv PR; ss; clarify; try rewrite RET in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss; clarify; try rewrite VIS in *; ss; clarify.
  Qed.

End MODSEM.

Program Definition module (p: program) (mi: string) (initial_owned_heap: SkEnv.t -> owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := (Sk.of_program fn_sig);
     Mod.get_modsem := fun skenv_link p => modsem mi skenv_link
                                                  (initial_owned_heap skenv_link) p;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.

