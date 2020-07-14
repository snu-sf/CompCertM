From Coq Require Import
     Arith.PeanoNat
     (* Strings.String *)
     Lists.List
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

Require Import Program.
Require Import Simulation.
Require Import AxiomsC.
Require Export ITreelib.
Require Export AuxBuffer.

Set Implicit Arguments.
Set Universe Polymorphism.



Section OWNEDHEAP.

Variable owned_heap: Type.

Section EFF.

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (oh: owned_heap) (m: mem) (vs: list val):
      InternalCallE (owned_heap * (mem * val))
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (sg: signature) (fptr: val)
          (oh: owned_heap) (m: mem) (vs: list val): ExternalCallE (owned_heap * (mem * val))
  .

  Variant EventE: Type -> Type :=
  | ENB: EventE void
  | EUB: EventE void
  | EChoose (X: Type): EventE X
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' EventE.
  Definition eff1: Type -> Type := Eval compute in InternalCallE +' eff0.
  Definition E := Eval compute in eff1.

End EFF.

(* Q: Why manually match "void" type, not using "embed" or "trigger"?
   A: It returns arbitrary type "A", not "void" *)
Definition triggerUB {E A} `{EventE -< E}: itree E A :=
  vis (EUB) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E}: itree E A :=
  vis (ENB) (fun v => match v: void with end)
.
(* Definition triggerDone {E A} `{EventE -< E} (oh: owned_heap) (m: mem) (v: val): itree E A := *)
(*   vis (EDone oh m v) (fun v => match v: void with end) *)
(* . *)

Definition unwrapN {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB
  end.

Definition unwrapU {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB
  end.

(* Record function : Type := mkfunction *)
(*   { fn_sig: signature; *)
(*     fn_code: (forall (oh: owned_heap) (m: mem) (vs: list val), *)
(*                  itree E (owned_heap * (mem * val))); } *)
(* . *)

(* Definition program: Type := AST.program (fundef function) unit. *)
Definition function: Type := (forall (oh: owned_heap) (m: mem) (vs: list val),
                                 itree E (owned_heap * (mem * val))).
Definition program: Type := ident -> option function.

Global Instance program_Map: (Map _ _ _) := (@function_Map ident function ident_eq).




Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition interp_function: (InternalCallE ~> itree E) :=
    fun T ei =>
      let '(ICall func_name oh m vs) := ei in
      match (lookup func_name p) with
      | Some (f) => (f oh m vs)
      | _ => triggerNB
      end
  .

  Definition interp_program:
    (forall T, InternalCallE T -> itree eff0 T) :=
    fun _ ic =>
      let sem0: itree eff0 _ := (mrec interp_function) _ ic in
      sem0
  .

End DENOTE.






Section TEST.

Definition _sum := 55%positive.

Definition c_sum (oh: owned_heap) (m: mem) (vs: list val): itree E (owned_heap * (mem * val)) :=
  match vs with
  | [Vint n] =>
    if Int.eq n Int.zero
    then Ret (oh, (m, (Vint Int.zero)))
    else '(oh, (m, s)) <- trigger (ICall _sum oh m [Vint (Int.sub n Int.one)]) ;;
         Ret (oh, (m, (Val.add s (Vint n))))
  | _ => triggerUB
  end
.

Definition f_sum: function := c_sum.

Definition global_definitions: list (ident * globdef (fundef (function)) unit) :=
  ((_sum, Gfun(Internal f_sum)) :: nil)
.

Definition p: program := Maps.add _sum c_sum (Maps.empty).

Variable initial_oh: owned_heap.
Let one := (interp_program p (ICall _sum initial_oh Mem.empty [Vint (Int.repr 1%Z)])).
(* Compute (burn 1 one). *)

Lemma one_spec
  :
    one ≈ Ret (initial_oh, (Mem.empty, Vint (Int.repr 1%Z)))
.
Proof.
  subst one. unfold interp_program. ss.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  rewrite mrec_as_interp. cbn. des_ifs. cbn. des_ifs.
  autorewrite with itree. cbn.
  replace (Int.add Int.zero (Int.repr 1)) with (Int.repr 1); cycle 1.
  { refl. }
  refl.
Qed.

End TEST.

End OWNEDHEAP.



Definition assumeK E X `{EventE -< E} (P: X -> Prop): ktree E X X :=
  fun x =>
    if ClassicalDescription.excluded_middle_informative (P x)
    then Ret x
    else triggerUB
.

Definition assume E `{EventE -< E} (P: Prop): itree E unit := Eval red in assumeK (fun _ => P) tt.

Definition guaranteeK E X `{EventE -< E} (P: X -> Prop): ktree E X X :=
  fun x =>
    if ClassicalDescription.excluded_middle_informative (P x)
    then Ret x
    else triggerNB
.

Definition guarantee E `{EventE -< E} (P: Prop): itree E unit := Eval red in guaranteeK (fun _ => P) tt.
(* Hint Unfold assume guarantee assumeK guaranteeK triggerUB triggerNB unwrapU unwrapN. *)



Require Export AdequacyLocal RUSC.
Require Import SimMemId SoundTop.
Definition defaultR: program_relation.t -> Prop := eq (mkPR SimMemId SimSymbId Top).
Hint Unfold defaultR.
