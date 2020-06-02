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

Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import Mod ModSem.




Section EFF.
  Definition var : Set := positive.

  Variant LocalE : Type -> Type :=
  | LGet (x: var) : LocalE val
  | LSet (x: var) (v: val) : LocalE unit
  | LPush: LocalE unit
  | LPop: LocalE unit
  .

  Variant MemE: Type -> Type :=
  | MLoad (chunk: memory_chunk) (blk: block) (ofs: Z): MemE val
  | MStore (chunk: memory_chunk) (blk: block) (ofs: Z) (v: val): MemE unit
  | MAlloc (lo hi: Z): MemE block
  | MFree (blk: block) (lo hi: Z): MemE unit
  .

  Variant CallE: Type -> Type :=
  | CCall (fptr: val) (args: list val): CallE val
  .

  Variant EventE: Type -> Type :=
  | ENB: EventE void
  | EUB: EventE void
  | ESyscall (ef: external_function) (args: list val): EventE val
  .

  Definition eff: Type -> Type := LocalE +' MemE +' CallE +' EventE.
End EFF.





Local Open Scope sum_scope.

Section MODSEM.
  (* Context {eff : Type -> Type}. *)
  (* Context {HasLocalE: LocalE -< eff}. *)
  (* Context {HasMemE: MemE -< eff}. *)
  (* Context {HasCallE : CallE -< eff}. *)
  (* Context {HasEventE : EventE -< eff}. *)


  (* Variable itr: sir. *)
  (* Variable mi: Midx.t. *)

  Definition itr := itree eff val.

  Record state := mk {
    it: list itr;
    lenv: list (var -> option val);
    m: mem;
  }
  .

  Check (observe itr): (itreeF eff val (itree eff val)).

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
