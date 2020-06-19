From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Require Import Program.

Set Implicit Arguments.



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

Program Instance function_MapOk (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}):
  MapOk eq (function_Map V dec) (K := K) := {| mapsto := fun k v m => m k = Some v |}.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.
Next Obligation. des_ifs. Qed.

Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 61, t at next level, t1 at next level, x ident, right associativity) : itree_scope.



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
  | ECall (fptr: val) (vs: list val): ExternalCallE (val)
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (args: list val): EventE (val)
  | EDone (v: val): EventE void
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' EventE.
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
Definition triggerDone {E A} `{EventE -< E} (v: val): itree E A :=
  vis (EDone v) (fun v => match v: void with end)
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

  Definition interp_program0 (oh0: owned_heap) (m0: mem) (le0: lenv):
    (forall T, InternalCallE T -> itree eff0 (owned_heap * (mem * (lenv * T)))) :=
    (* let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in *)
    (* fun _ ic => *)
    (*   let sem1: itree eff1 _ := interp_GlobalE (sem0 _ ic) in *)
    (*   sem1 *)
    fun _ ic =>
      let sem4: itree eff4 _ := (mrec interp_function) _ ic in
      let sem3: itree eff3 _ := interp_GlobalE sem4 in
      let sem2: itree eff2 (lenv * _) := (interp_LocalE sem3 le0) in
      let sem1: itree eff1 (mem * (lenv * _)) := (interp_MemE sem2 m0) in
      let sem0: itree eff0 (owned_heap * (mem * (lenv * _))) := (interp_OwnedHeapE sem1 oh0) in
      sem0
  .

  Definition interp_program2: (InternalCallE ~> itree eff2) :=
    (* let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in *)
    (* fun _ ic => *)
    (*   let sem1: itree eff1 _ := interp_GlobalE (sem0 _ ic) in *)
    (*   sem1 *)
    fun _ ic =>
      let sem4: itree eff4 _ := (mrec interp_function) _ ic in
      let sem3: itree eff3 _ := interp_GlobalE sem4 in
      let sem2: itree eff2 _ := snd <$> (interp_LocalE sem3 nil) in
      sem2
  .

  Definition interp_program3: (InternalCallE ~> itree eff3) :=
    fun _ ic =>
      let sem4: itree eff4 _ := (mrec interp_function) _ ic in
      let sem3: itree eff3 _ := interp_GlobalE sem4 in
      sem3
  .

End DENOTE.



End OWNEDHEAP.

Definition assume oh (P: Prop): itree (E oh) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerUB "assume"
.
  
Definition guarantee oh (P: Prop): itree (E oh) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerNB "guarantee"
.

