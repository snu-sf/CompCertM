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
Require Import Mod ModSem Any.

Import ITreeNotations.
Import Monads.
Import MonadNotation.




Section EFF.
  Definition var: Set := positive.

  Variant LocalE: Type -> Type :=
  | LGet (x: var) : LocalE val
  | LSet (x: var) (v: val) : LocalE unit
  | LPush: LocalE unit
  | LPop: LocalE unit
  .

  Variant GlobalE: Type -> Type :=
  | GGet (x: var) : GlobalE val
  | GSet (x: var) (v: val) : GlobalE unit
  .

  Variant OwnedHeapE: Type -> Type :=
  | OGet: OwnedHeapE Any
  | OSet (a: Any) : OwnedHeapE unit
  .

  Variant MemE: Type -> Type :=
  | MLoad (chunk: memory_chunk) (blk: block) (ofs: Z): MemE val
  | MStore (chunk: memory_chunk) (blk: block) (ofs: Z) (v: val): MemE unit
  | MAlloc (lo hi: Z): MemE block
  | MFree (blk: block) (lo hi: Z): MemE unit
  .

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (args: list val): InternalCallE val
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (fptr: val) (args: list val): ExternalCallE val
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (args: list val): EventE val
  .

  Definition eff0: Type -> Type := ExternalCallE +' LocalE +' GlobalE +' OwnedHeapE +' MemE +' EventE.
  Definition eff: Type -> Type := InternalCallE +' eff0.
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





Local Open Scope sum_scope.

(* Definition itr: Type := itree eff val. *)
(* Definition ktr: Type := ktree eff block val. *)

Definition program: Type := AST.program (InternalCallE ~> itree eff) unit.

Variable p: program.
Variable func_name: ident.
Check ((prog_defmap p) ! func_name).

(* Section SCOPE. *)
(*   Context {eff : Type -> Type}. *)
(*   Context {HasInternalCall: InternalCallE -< eff}. *)
(*   Context {HasExternalCall: ExternalCallE -< eff}. *)
(*   Context {HasLocal: LocalE -< eff}. *)
(*   Context {HasMem: MemE -< eff}. *)
(*   Context {HasEvent: EventE -< eff}. *)
(* End SCOPE. *)
Section TMP.
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

Definition denote_function (p: program): (InternalCallE ~> itree eff) :=
  fun T ei =>
    let '(ICall func_name args) := ei in
    match ((prog_defmap p) ! func_name) with
    | Some (Gfun f) =>
      trigger LPush ;;
      retv <- f _ (ICall 1%positive args) ;;
      trigger LPop ;;
      Ret retv
    | _ => triggerNB "TODO: UB? NB? Which one is useful?"
    end
.

Definition denote_program (p: program): (InternalCallE ~> itree eff0) := mrec (denote_function p).



Section MODSEM.

  Variable p: program.
  (* Context {eff : Type -> Type}. *)
  (* Context {HasLocalE: LocalE -< eff}. *)
  (* Context {HasMemE: MemE -< eff}. *)
  (* Context {HasCallE : CallE -< eff}. *)
  (* Context {HasEventE : EventE -< eff}. *)

  (* Variable itr: sir. *)
  (* Variable mi: Midx.t. *)

  Record state := mk {
    it: itree eff0 val;
    lenv: list (var -> option val);
    m: mem;
  }
  .

  (* Check (observe itr): (itreeF eff val (itree eff val)). *)

  Inductive step (se: Senv.t) (ge: unit): state -> trace -> state -> Prop :=
  | step_tau
      st0 E0 st1
      (TAU: (observe st0) = TauF st1)
    :
      step se ge st0 E0 st1
  | step_local_get
      (st0: state) (x: var) (k: val -> sir)
      (LOCAL: (observe st0) = VisF (LGet x|) k)
    :
      step se ge st0 E0 st0
  .

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step1;
       ModSem.at_external := coerce at_external;
       ModSem.initial_frame := coerce initial_frame1;
       ModSem.final_frame := coerce final_frame;
       ModSem.after_external := coerce after_external1;
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
