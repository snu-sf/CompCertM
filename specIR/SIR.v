From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     (* Data.String *)
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Structures.Maps
     (* Data.List *)
.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
.

Import SumNotations.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Import ITreeNotations.
Import Monads.
Import MonadNotation.



Set Implicit Arguments.


(*** Put some other place ***)
Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end)
.



(* Section SCOPE. *)
(*   Context {eff : Type -> Type}. *)
(*   Context {HasInternalCall: InternalCallE -< eff}. *)
(*   Context {HasExternalCall: ExternalCallE -< eff}. *)
(*   Context {HasLocal: LocalE -< eff}. *)
(*   Context {HasMem: MemE -< eff}. *)
(*   Context {HasEvent: EventE -< eff}. *)
(* End SCOPE. *)
Section TMP.
  Local Open Scope sum_scope.
  Variable A: Type -> Type.
  Variable B: Type -> Type.
  Variable C: Type -> Type.
  Variable D: Type -> Type.
  Variable E: Type -> Type.
  Let eff: Type -> Type := A +' B +' C +' D +' E.
  Check ((A +' B) +' (C +' D)) +' E.
  Variable a: A unit.
  Variable c: C unit.
  Check (a).
  Check (|a).
  Check (||a).
  Check (|||a).
  Check (|||||||a).
  Check (a|).
  (* Check (a||). *)
  Check (|a|).
  Check (||a|).
  Check (||||||a|).
  (* Check (||||a||). *)
  Check (trigger c: itree eff unit).
End TMP.



Section OWNEDHEAP.
Variable owned_heap: Type.

Section EFF.

  Variant LocalE: Type -> Type :=
  | LGet (x: ident) : LocalE val
  | LPut (x: ident) (v: val) : LocalE unit
  | LPush: LocalE unit
  | LPop: LocalE unit
  .

  (*** In shallow embedding, one may directly access globalenv.
       However, we may want to restrict its access (e.g., not allowing sth like "Genv.find_symbol x == 42")
       so that one may prove commutativity/unusedglob/etc.
   ***)
  Variant GlobalE: Type -> Type :=
  | GFindS (x: ident) : GlobalE val
  .

  (* Variant OwnedHeapE: Type -> Type := *)
  (* | OGet: OwnedHeapE Any *)
  (* | OPut (a: Any): OwnedHeapE unit *)
  (* . *)
  Definition OwnedHeapE: Type -> Type := State.stateE owned_heap.

  Definition MemE: Type -> Type := State.stateE mem.
  (* Variant MemE: Type -> Type := *)
  (* | MGet: MemE mem *)
  (* | MPut (m: mem): MemE unit *)
  (* . *)
  Set Printing Universes.
  Print MemE.
  (* Variant MemE: Type -> Type := *)
  (* | MLoad (chunk: memory_chunk) (blk: block) (ofs: Z): MemE val *)
  (* | MStore (chunk: memory_chunk) (blk: block) (ofs: Z) (v: val): MemE unit *)
  (* | MAlloc (lo hi: Z): MemE block *)
  (* | MFree (blk: block) (lo hi: Z): MemE unit *)
  (* . *)

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (args: list val): InternalCallE val
  .

  Variant ExternalCallE: Type -> Type :=
  (* | ECall (fptr: val) (args: list val): ExternalCallE (owned_heap * val) *)
  (* | ECall (fptr: val) (vs: list val) (m: mem): ExternalCallE (owned_heap * mem * val) *)
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (args: list val): EventE val
  .

  Definition eff4: Type -> Type := Eval compute in ExternalCallE +' EventE.
  Definition eff3: Type -> Type := Eval compute in MemE +' eff4.
  Definition eff2: Type -> Type := Eval compute in OwnedHeapE +' eff3.
  Definition eff1: Type -> Type := Eval compute in GlobalE +' eff2.
  Definition eff0: Type -> Type := Eval compute in LocalE +' eff1.
  Definition eff: Type -> Type := Eval compute in InternalCallE +' eff0.

End EFF.

Definition triggerUB {E A} `{EventE -< E} (msg: string): itree E A :=
  vis (EUB msg) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E} (msg: string) : itree E A :=
  vis (ENB msg) (fun v => match v: void with end)
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






(* Definition itr: Type := itree eff val. *)
(* Definition ktr: Type := ktree eff block val. *)

Record function : Type := mkfunction
  { fn_sig: signature; fn_code: (InternalCallE ~> itree eff); }
.

Definition program: Type := AST.program (fundef function) unit.



Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.
  Set Printing Universes.
  (* Print Universes. *)
  Fail Check (prog_defmap p).

  Definition denote_function: (InternalCallE ~> itree eff) :=
    fun T ei =>
      let '(ICall func_name args) := ei in
      match (find (fun nf => ident_eq func_name (fst nf)) p.(prog_defs)) with
      | Some (_, Gfun (Internal f)) =>
        trigger LPush ;;
                retv <- f.(fn_code) (ICall 1%positive args) ;;
                trigger LPop ;;
                Ret retv
      | _ => triggerNB "TODO: UB? NB? Which one is useful?"
      end
  .

  Instance lenv_Map: (Map ident val (ident -> option val)) := function_Map val Pos.eq_dec.
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

  Definition interp_LocalE {E A} `{EventE -< E} (t : itree (LocalE +' E) A): stateT lenv (itree E) A :=
    let t' := State.interp_state (case_ handle_LocalE State.pure_state) t in
    t'
  .

  Definition handle_GlobalE {E: Type -> Type} `{EventE -< E}: GlobalE ~> itree E :=
    fun _ e =>
      match e with
      | GFindS x => blk <- unwrapN (Genv.find_symbol ge x) ;; Ret (Vptr blk Ptrofs.zero)
      end
  .

  Definition interp_GlobalE {E A} `{EventE -< E} (t : itree (GlobalE +' E) A): itree E A :=
    interp (case_ (handle_GlobalE) (id_ _)) t
  .

  Definition handle_OwnedHeapE {E: Type -> Type} `{EventE -< E}: OwnedHeapE ~> stateT owned_heap (itree E) :=
    fun _ e oh0 =>
      match e with
      | OGet => Ret (oh0, oh0)
      | OPut oh1 => Ret (oh1, tt)
      end
  .

  Definition interp_OwnedHeapE {E A} `{EventE -< E} (t: itree (OwnedHeapE +' E) A): stateT owned_heap (itree E) A :=
    let t' := State.interp_state (case_ handle_OwnedHeapE State.pure_state) t in
    t'
  .

  Definition handle_MemE {E: Type -> Type} `{EventE -< E}: MemE ~> stateT mem (itree E) :=
    fun _ e m0 =>
      match e with
      | MLoad chunk blk ofs => v <- unwrapU (Mem.load chunk m0 blk ofs) ;; Ret (m0, v)
      | MStore chunk blk ofs v => m1 <- unwrapU (Mem.store chunk m0 blk ofs v) ;; Ret (m1, tt)
      | MAlloc lo hi => let '(m1, blk) := Mem.alloc m0 lo hi in Ret (m1, blk)
      | MFree blk lo hi => m1 <- unwrapU (Mem.free m0 blk lo hi) ;; Ret (m1, tt)
      end
  .

  Definition interp_MemE {E A} `{EventE -< E} (t : itree (MemE +' E) A): stateT mem (itree E) A :=
    let t' := State.interp_state (case_ handle_MemE State.pure_state) t in
    t'
  .

  Definition denote_program (oh: owned_heap) (m0: mem):
    (forall T, InternalCallE T -> itree eff4 (owned_heap * mem * T)) :=
    let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in
    fun _ ic =>
      let sem1: itree eff1 _ := ret <- (interp_LocalE (sem0 _ ic) []) ;; Ret (snd ret) in
      let sem2: itree eff2 _ := interp_GlobalE sem1 in
      let sem3: itree eff3 _ := ret <- (interp_OwnedHeapE sem2 oh) ;; Ret ret in
      let sem4: itree eff4 _ := ret <- (interp_MemE sem3 m0) ;;
                                    Ret ((fst (snd ret)), (fst ret), (snd (snd ret))) in
      sem4
  .

End DENOTE.



Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Let ge: SkEnv.t := skenv.

  Definition state := itree eff4 (owned_heap * mem * val).
  (* Record state := mk { *)
  (*   it: itree eff4 val; *)
  (* } *)
  (* . *)
  Let denote_program := denote_program p skenv.

  Inductive initial_frame (oh: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fid blk m0 vs itr
      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)
      (DENOTE: denote_program oh m0 (ICall fid vs) = itr)
    :
      initial_frame oh args itr
  .

  Goal forall (st0 st1: state), st0 = st1 -> False.
    i.
    destruct (observe st0) eqn:T.
    admit "".
    admit "".
    admit "".
  Abort.

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      oh0 m0 args fptr vs k
      (*** TODO: oh0 is free ***)
      (VIS: (observe st0) = VisF (inl1 (ECall fptr vs m0)) k)
      (* (VIS: (observe st0) = VisF (subevent _ (ECall fptr vs)) k) *)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive after_external (st0: state): owned_heap -> Retv.t -> state -> Prop :=
  | after_external_intro
      m0 fptr vs k 
      (VIS: (observe st0) = VisF (inl1 (ECall fptr vs)) k)
      m0 v0
      (RETV: retv = Retv.mk m0 v0)
      (ST: st1 = k v0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 v0
      (RET: (observe st0) = RetF (oh0, m0, v0))
    :
      final_frame st0 oh0 (Retv.mk v0 m0)
  .

  Inductive step (se: Senv.t) (ge: unit): state -> trace -> state -> Prop :=
  | step_tau
      st0 E0 st1
      (TAU: (observe st0) = TauF st1)
    :
      step se ge st0 E0 st1
  .

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step1;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := None;
    |}.

End MODSEM.
Definition module (itr: itree eff val) (mi: Midx.t): Mod.t.



Section REMOVELATER.
Inductive expr : Type :=
| Var (_ : var)
| Val (_ : val)
(* | Load (_: var) (_: expr) *)
(* | CoqCode (_: list (var + expr)) (P: list val -> (val * list val)) *)
| Shallow (itr: itree eff val)
(* | Syscall (code: string) (msg: string) (e: expr) *)
(* | Call (func_name: string) (params: list (var + expr)) *)
(* | PutOwnedHeap (_: expr) *)
(* | GetOwnedHeap *)
.

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| AssumeFail
| GuaranteeFail
| Store (x: var) (ofs: expr) (e: expr) (* x->ofs := e *)
| Expr (e: expr)
| Return (e: expr)
| Break
| Continue
.

Section Denote.

  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (LGet v)
    | Val n     => ret n
    | Shallow itr => itr
    end.

End Denote.
End REMOVELATER.
