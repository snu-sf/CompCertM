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





Section EFF.

  Variant LocalE: Type -> Type :=
  | LGet (x: ident): LocalE val
  | LPut (x: ident) (v: val): LocalE unit
  | LPush: LocalE unit
  | LPop: LocalE unit
  .

  Definition MemE: Type -> Type := stateE mem.

  Definition OwnedHeapE: Type -> Type := stateE owned_heap.

  (*** In shallow embedding, one may directly access globalenv.
       However, we may want to restrict its access (e.g., not allowing sth like "Genv.find_symbol x == 42")
       so that one may prove commutativity/unusedglob/etc.
   ***)
  Variant GlobalE: Type -> Type :=
  | GFindS (x: ident) : GlobalE val
  .

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (vs: list val): InternalCallE val
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (fptr: val) (oh: owned_heap) (m: mem) (vs: list val):
      ExternalCallE (owned_heap * (mem * val))
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (m: mem) (args: list val): EventE (val * mem)
  .

  Variant DoneE: Type -> Type :=
  | EDone (oh: owned_heap) (v: val) (m: mem): DoneE void
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' DoneE +' EventE.
  Definition eff1: Type -> Type := Eval compute in OwnedHeapE +' eff0.
  Definition eff2: Type -> Type := Eval compute in MemE +' eff1.
  Definition eff3: Type -> Type := Eval compute in LocalE +' eff2.
  Definition eff4: Type -> Type := Eval compute in GlobalE +' eff3.
  Definition eff5: Type -> Type := Eval compute in InternalCallE +' eff4.
  Definition E := Eval compute in eff5.

End EFF.

(* Q: Why manually match "void" type, not using "embed" or "trigger"?
   A: It returns arbitrary type "A", not "void" *)
Definition triggerUB {E A} `{EventE -< E} (msg: string): itree E A :=
  vis (EUB msg) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E} (msg: string) : itree E A :=
  vis (ENB msg) (fun v => match v: void with end)
.
Definition triggerDone {E A} `{DoneE -< E} (oh: owned_heap) (m: mem) (v: val): itree E A :=
  vis (EDone oh v m) (fun v => match v: void with end)
.

Definition unwrapN {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB "unwrap"
  end.

Definition unwrapU {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB "unwrap"
  end.

Record function : Type := mkfunction
  { fn_sig: signature;
    fn_code: (forall (vs: list val), itree E val); }
.

Definition program: Type := AST.program (fundef function) unit.





Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition interp_function: (InternalCallE ~> itree E) :=
    fun T ei =>
      let '(ICall func_name vs) := ei in
      match (find (fun nf => ident_eq func_name (fst nf)) p.(prog_defs)) with
      | Some (_, Gfun (Internal f)) =>
      (* match (prog_defmap p) ! func_name with *)
      (* | Some (Gfun (Internal f)) => *)
        trigger LPush ;;
        retv <- (f.(fn_code) vs) ;;
        trigger LPop ;;
        Ret retv
        (* trigger LPush ;; *)
        (*         retv <- f.(fn_code) ei ;; *)
        (*         trigger LPop ;; *)
        (*         Ret retv *)
      | _ => triggerNB "TODO: UB? NB? Which one is useful?"
      end
  .

  Global Instance lenv_Map: (Map ident val (ident -> option val)) := function_Map val Pos.eq_dec.
  Definition lenv := list (ident -> option val).
  Definition handle_LocalE {E: Type -> Type} `{EventE -< E}: LocalE ~> stateT lenv (itree E) :=
    fun _ e le =>
      let hd: ident -> option val := hd Maps.empty le in
      let tl: lenv := tl le in
      match e with
      | LGet x => v <- unwrapN (*** TODO: U? N? ***) (Maps.lookup x hd) ;; Ret (le, v)
      | LPut x v => Ret ((Maps.add x v hd) :: tl, tt)
      | LPush => Ret (Maps.empty :: hd :: tl, tt)
      | LPop => Ret (tl, tt)
      end.

  Definition interp_LocalE {E A} `{EventE -< E}
             (t: itree (LocalE +' E) A) (le: lenv): itree E (lenv * A) :=
    let t': stateT lenv (itree E) A := interp_state (case_ handle_LocalE pure_state) t in
    t' le
  .

  Definition handle_GlobalE {E: Type -> Type} `{EventE -< E}: GlobalE ~> itree E :=
    fun _ e =>
      match e with
      | GFindS x => blk <- unwrapN (Genv.find_symbol ge x) ;; Ret (Vptr blk Ptrofs.zero)
      end
  .

  Definition interp_GlobalE {E A} `{EventE -< E} (t: itree (GlobalE +' E) A): itree E A :=
    interp (case_ (handle_GlobalE) (id_ _)) t
  .

  Definition handle_MemE {E: Type -> Type}: MemE ~> stateT mem (itree E) := h_state mem.

  Definition interp_MemE {E A} (t: itree (MemE +' E) A) (m0: mem): itree E (mem * A) :=
    let t': stateT mem (itree E) A := interp_state (case_ handle_MemE pure_state) t in
    t' m0
  .

  Definition handle_OwnedHeapE {E: Type -> Type}: OwnedHeapE ~> stateT owned_heap (itree E) :=
    h_state owned_heap.

  Definition interp_OwnedHeapE {E A} (t: itree (OwnedHeapE +' E) A) (oh0: owned_heap):
    itree E (owned_heap * A) :=
    let t': stateT owned_heap (itree E) A := interp_state (case_ handle_OwnedHeapE pure_state) t in
    t' oh0
  .

  Definition interp_program0 (le0: lenv) (oh0: owned_heap) (m0: mem):
    (forall T, InternalCallE T -> itree eff0 (owned_heap * (mem * T))) :=
    (* let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in *)
    (* fun _ ic => *)
    (*   let sem1: itree eff1 _ := interp_GlobalE (sem0 _ ic) in *)
    (*   sem1 *)
    fun _ ic =>
      let sem4: itree eff4 _ := (mrec interp_function) _ ic in
      let sem3: itree eff3 _ := interp_GlobalE sem4 in
      let sem2: itree eff2 _ := snd <$> (interp_LocalE sem3 le0) in
      let sem1: itree eff1 (mem * _) := (interp_MemE sem2 m0) in
      let sem0: itree eff0 (owned_heap * (mem * _)) := (interp_OwnedHeapE sem1 oh0) in
      sem0
  .

End DENOTE.





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
    itr:> itree eff0 (owned_heap * (mem * val));
  }.

  Let interp_program0 := interp_program0 p skenv.

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
      (ITR: itr = (interp_program0 nil oh0 m0 (ICall fid vs)))
      (ST: st0 = (mk itr))
    :
      initial_frame oh0 args st0
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      args fptr vs k oh0 m0
      (VIS: (observe st0) = VisF (subevent _ (ECall fptr oh0 m0 vs)) k)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive get_k (st0: state):
    (owned_heap * (mem * val) -> itree eff0 (owned_heap * (mem * val))) -> Prop :=
  | get_k_intro
      _vs _fptr _oh0 _m0 k
      (VIS: (observe st0) = VisF (subevent _ (ECall _fptr _oh0 _m0 _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (V: (Retv.v retv) = rv)
      (M: (Retv.m retv) = m0)
      (KONT: st1 = mk (k (oh0, (m0, rv))))
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val) retv
      (RET: (observe st0) = RetF (oh0, (m0, rv)))
      (RETV: retv = Retv.mk rv m0)
    :
      final_frame st0 oh0 retv
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_tau
      itr0
      itr1
      (TAU: (observe st0) = TauF itr1)

      (ST0: st0 = mk itr0)
      (TR: tr = E0)
      (ST1: st1 = mk itr1)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      msg k
      (VIS: (observe st0) = VisF (subevent _ (ENB msg)) k)

      (TR: tr = E0)
  | step_syscall
      itr0 m0 m1
      ef vs rv k
      (VIS: (observe st0) = VisF (subevent _ (ESyscall ef m0 vs)) k)
      (SYSCALL: external_call ef se vs m0 tr rv m1)

      (ST0: st0 = mk itr0)
      (TR: tr = E0)
      (ST1: st1 = mk (k (rv, m1)))
  | step_done
      itr0
      oh rv m k
      (VIS: (observe st0) = VisF (subevent _ (EDone oh rv m)) k)

      (ST0: st0 = mk itr0)
      (TR: tr = E0)
      (ST1: st1 = mk (Ret (oh, (m, rv))))
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

