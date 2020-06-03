From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

(* From ExtLib Require Import *)
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     (* Structures.Maps *)
     (* Data.List *)
(* . *)

From ITree Require Export
     ITree
     ITreeFacts
     (* Events.MapDefault *)
     (* Events.StateFacts *)
.

Import SumNotations.
Import ITreeNotations.
Import Monads.
Import MonadNotation.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Require Import Sem.



Set Implicit Arguments.




(*** Put some other place ***)
(* Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) := *)
(*   Build_Map *)
(*     (fun _ => None) *)
(*     (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1) *)
(*     (fun k0 m => fun k1 => if dec k0 k1 then None else m k1) *)
(*     (fun k m => m k) *)
(*     (fun m0 m1 => fun k => match (m0 k) with *)
(*                            | Some v => Some v *)
(*                            | _ => m1 k *)
(*                            end) *)
(* . *)



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




Definition val': Type := val + Any.
Definition Vabs := (@inr val Any).
Definition val_to_val': val -> val' := inl.
Coercion val_to_val': val >-> val'.



Section OWNEDHEAP.
Variable owned_heap: Type.

Section EFF.

  (* Variant LocalE: Type -> Type := *)
  (* | LGet (x: ident): LocalE val *)
  (* | LPut (x: ident) (v: val): LocalE unit *)
  (* | LPush: LocalE unit *)
  (* | LPop: LocalE unit *)
  (* . *)

  (*** In shallow embedding, one may directly access globalenv.
       However, we may want to restrict its access (e.g., not allowing sth like "Genv.find_symbol x == 42")
       so that one may prove commutativity/unusedglob/etc.
   ***)
  Variant GlobalE: Type -> Type :=
  | GFindS (x: ident) : GlobalE val
  .

  Variant InternalCallE: Type -> Type :=
  | ICall (oh: owned_heap) (name: ident) (vs: list val') (m: mem):
      InternalCallE (owned_heap * mem * val' * list val')
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (oh: owned_heap) (fptr: val) (vs: list val) (m: mem): ExternalCallE (owned_heap * mem * val)
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (args: list val) (m0: mem): EventE (mem * val)
  .

  Definition eff1: Type -> Type := Eval compute in ExternalCallE +' EventE.
  Definition eff0: Type -> Type := Eval compute in GlobalE +' eff1.
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







Record function : Type := mkfunction
  { fn_sig: signature; fn_code: (InternalCallE ~> itree eff); }
.

Definition program: Type := AST.program (fundef function) unit.



Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition denote_function: (InternalCallE ~> itree eff) :=
    fun T ei =>
      let '(ICall oh func_name vs m) := ei in
      match (find (fun nf => ident_eq func_name (fst nf)) p.(prog_defs)) with
      | Some (_, Gfun (Internal f)) =>
      (* match (prog_defmap p) ! func_name with *)
      (* | Some (Gfun (Internal f)) => *)
        (f.(fn_code) ei)
        (* trigger LPush ;; *)
        (*         retv <- f.(fn_code) ei ;; *)
        (*         trigger LPop ;; *)
        (*         Ret retv *)
      | _ => triggerNB "TODO: UB? NB? Which one is useful?"
      end
  .

  (* Instance lenv_Map: (Map ident val (ident -> option val)) := function_Map val Pos.eq_dec. *)
  (* Definition lenv := list (ident -> option val). *)
  (* Definition handle_LocalE {E: Type -> Type} `{EventE -< E}: LocalE ~> stateT lenv (itree E) := *)
  (*   fun _ e le => *)
  (*     let hd: ident -> option val := hd Maps.empty le in *)
  (*     let tl: lenv := tl le in *)
  (*     match e with *)
  (*     | LGet x => v <- unwrapN (*** TODO: U? N? ***) (Maps.lookup x hd) ;; Ret (le, v) *)
  (*     | LPut x v => Ret ((Maps.add x v hd) :: tl, tt) *)
  (*     | LPush => Ret (Maps.empty :: hd :: tl, tt) *)
  (*     | LPop => Ret (tl, tt) *)
  (*     end. *)

  (* Definition interp_LocalE {E A} `{EventE -< E} (t : itree (LocalE +' E) A): stateT lenv (itree E) A := *)
  (*   let t' := State.interp_state (case_ handle_LocalE State.pure_state) t in *)
  (*   t' *)
  (* . *)

  Definition handle_GlobalE {E: Type -> Type} `{EventE -< E}: GlobalE ~> itree E :=
    fun _ e =>
      match e with
      | GFindS x => blk <- unwrapN (Genv.find_symbol ge x) ;; Ret (Vptr blk Ptrofs.zero)
      end
  .

  Definition interp_GlobalE {E A} `{EventE -< E} (t : itree (GlobalE +' E) A): itree E A :=
    interp (case_ (handle_GlobalE) (id_ _)) t
  .

  Definition denote_program: (InternalCallE ~> itree eff1) :=
    (* let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in *)
    (* fun _ ic => *)
    (*   let sem1: itree eff1 _ := interp_GlobalE (sem0 _ ic) in *)
    (*   sem1 *)
    fun _ ic =>
      let sem0: itree eff0 _ := (mrec denote_function) _ ic in
      let sem1: itree eff1 _ := interp_GlobalE sem0 in
      sem1
  .

End DENOTE.



Section MODSEM.

  Variable mi: string.
  Variable initial_owned_heap: owned_heap.
  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Definition genvtype: Type := unit.
  Let ge: genvtype := tt.

  Set Printing Universes.
  Definition state := itree eff1 (owned_heap * mem * val' * list val').

  Let denote_program := denote_program p skenv.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fid blk m0 vs itr
      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)
      (DENOTE: denote_program (ICall oh0 fid (List.map val_to_val' vs) m0) = itr)
    :
      initial_frame oh0 args itr
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      oh0 m0 args fptr vs k
      (VIS: (observe st0) = VisF (subevent _ (ECall oh0 fptr vs m0)) k)
      (ARGS: args = Args.mk fptr vs m0)
    :
      at_external st0 oh0 args
  .

  Inductive get_k (st0: state):
    (owned_heap * mem * val -> itree eff1 (owned_heap * mem * val' * list val')) -> Prop :=
  | get_k_intro
      _oh0 _m0 _fptr _vs k
      (VIS: (observe st0) = VisF (subevent _ (ECall _oh0 _fptr _vs _m0)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (V: (Retv.v retv) = rv)
      (M: (Retv.m retv) = m0)
      (KONT: st1 = k (oh0, m0, rv))
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val) _rvs retv
      (RET: (observe st0) = RetF (oh0, m0, rv: val', _rvs))
      (RETV: retv = Retv.mk rv m0)
    :
      final_frame st0 oh0 retv
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state): trace -> state -> Prop :=
  | step_tau
      E0 st1
      (TAU: (observe st0) = TauF st1)
    :
      step se ge st0 E0 st1
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      msg k
      (VIS: (observe st0) = VisF (subevent _ (ENB msg)) k)
    :
      step se ge st0 E0 st0
  | step_syscall
      ef vs m0 tr rv m1 k st1
      (VIS: (observe st0) = VisF (subevent _ (ESyscall ef vs m0)) k)
      (SYSCALL: external_call ef se vs m0 tr rv m1)
      (KONT: st1 = k (m1, rv))
    :
      step se ge st0 tr st1
  .

  Set Printing Universes.
  Print Universes.

  Record my_mod: Type := mk {
    datatype: Type;
    (* val: datatype; *)
  }.
  Definition my_mods_tl (mms: list my_mod): list my_mod := tl mms.
  Fail Definition boo := tl [(mk (itree void1 (list nat)))].
  (* Definition my_tree := (itree void1 (list nat)). *)
  (* Definition my_weird (mt: my_tree): my_tree := rvs <- mt ;; Ret (tl rvs). *)
  (* Definition boo: my_mod := mk my_tree. *)
  Definition boo: my_mod := mk (itree void1 unit).
  Print Universes.
  Check (itree void1 (list (itree void1 nat))).

"Type@{max(Set,ITree.Core.ITreeDefinition.2,ITree.Core.ITreeDefinition.3,itreeF.u1+1)}" is a subtype of
"Type@{ModSem.t.u0}").

Error: Universe inconsistency. Cannot enforce
ITree.Core.ITreeDefinition.3 <= Mod.Mod.t.u0 because
Mod.Mod.t.u0 < Coq.Lists.List.1 <= option.u0 = ITree.Core.ITreeDefinition.3.


                     
ModSem.t.u0 < Coq.Lists.List.1
            <= ex.u0
            < Ge.t.u0
            <= eq.u0
            <= eq_ind_r.u0
            < flip.u0
            < flip.u2
            <= f_equal6.u0
            <= f_equal6.u3
            <= prod.u1
            <= f_equal6.u5
            <= Coq.Init.Datatypes.33
            <= less1.u0
            < list.u0
            < Coq.Lists.List.169
            < Coq.Lists.List.170
            <= compcomp.ModSem.278
            < Smallstep.semantics.u0
            <= bot1.u0
            <= bot2.u0

Coq.Lists.List.1 = MonadFix.MonadFix.u0
Fun.u0 = MonadFix.MonadFix.u0
MonadFix.MonadFix.u0 < ITree.Basics.CategoryFunctor.1
                     < ITree.Basics.CategoryOps.1
                     < ITree.Basics.CategoryTheory.1
                     < Coq.Relations.Relation_Definitions.1
                     <= Paco.gpaco2.1
                     <= Paco.paco2.1
                     < ITree.Basics.CategoryFunctor.2
                     <= ITree.Basics.CategoryOps.2
                     <= ITree.Basics.Monad.2
                     <= MonadPlus.MonadPlus.u1
                     <= MonadZero.MonadZero.u1
                     <= Shallow.inj_pair2.u1
                     <= sig.u0
                     <= Paco.gpaco2.2
                     <= Paco.paco2.2
                     <= Fun.u2
                     <= MonadExc.MonadExc.u2
                     <= skdef_of_gdef.u0
                     <= compose.u0
                     <= compose.u1
                     <= Kleisli.u1
                     <= update_snd.u1
                     <= itreeF.u0
                     < ex.u0
                     <= compose.u2
                     <= Kleisli.u4
                     <= pacotac_internal.paco_eq_JMeq.u0
                     <= gpaco2_gen_guard.u0
                     <= pacotac_internal.paco_JMeq_eq.u0
                     <= gpaco2_gen_guard.u1
                     <= eq.u0
                     <= sigT.u0
                     <= sigT.u1
                     <= Equality.solution_left.u0
                     <= Kleisli_apply.u1
                     < ITree.Basics.CategoryOps.14
                     <= ITree.Basics.CategoryOps.15
                     <= eq_ind_r.u0
                     <= pacotac_internal._paco_pre2.u0
                     <= flip.u0
                     <= pacotac_internal._paco_pre2.u1
                     <= flip.u1
                     <= eq_rect_r.u0
                     <= ITree.Core.Subevent.17
                     <= eq_rect_r.u1
                     <= gpaco2_gpaco.u0
                     <= gpaco2_gpaco.u1
                     < ITree.Basics.CategoryTheory.22
                     <= app_nil_r.u0
                     <= globdef.u0
                     <= app_nil_r.u1
                     <= app_assoc.u0
                     <= Equality.simplification_heq.u0
                     <= app_assoc.u1
                     <= prod.u0
                     <= AST.program.u0
                     <= prod.u1
                     <= Coq.Classes.Morphisms.30
                     <= Coq.Init.Datatypes.33
                     <= Equality.simplification_existT2.u1
                     <= app_inv_tail.u0
                     <= Equality.simplification_existT1.u1
                     <= Equivalence.pointwise_equivalence.u0
                     <= Equivalence.pointwise_equivalence.u1
                     < ITree.Basics.CategoryTheory.50
                     <= Proper_interp_mrec.u4
                     <= list.u0
                     <= Coq.Init.Datatypes.62
                     <= length.u0
                     <= app.u0
                     < ITree.Basics.CategoryFacts.68
                     <= Applicative_itree.u0
                     <= nth_split.u0
                     <= Coq.Classes.Morphisms.74
                     <= flip_clo.u0
                     <= flip_clo.u1
                     < ITree.Basics.CategoryOps.80
                     <= flip_arrow.u0
                     <= ITree.Basics.CategoryOps.81
                     <= flip_arrow.u1
                     <= eq_Handler.u4
                     <= fundef.u0
                     <= nth_error_split.u0
                     <= eutt_Handler.u4
                     <= euttge_interp_mrec.u4
                     <= ID.u0
                     <= respectful_eq_itree.u6
                     <= respectful_eutt.u6
                     <= suttF_inv_tau_left.u3
                     <= suttF_inv_tau_left.u4
                     <= suttF_inv_tau_left.u5
                     <= removelast_app.u0
                     <= eq_itree_apply_IFun.u5
                     < eq_itree_apply_IFun.u6
                     <= euttge_interp.u5
                     <= eutt_apply_IFun.u5
                     < eutt_apply_IFun.u6
                     <= eqitC_wcompat.u2
                     <= eqitC_wcompat.u3
                     <= eqitC_wcompat.u4
                     <= eqitC_wcompat.u5
                     <= eqitC_wcompat.u6
                     <= eqitC_wcompat.u7
                     <= eqitC_wcompat.u8
                     <= eqitC_wcompat.u9
                     <= transL_closed.u3
                     <= transL_closed.u4
                     <= transL_closed.u5
                     <= transL_closed.u6
                     <= transL_closed.u7
                     <= transL_closed.u8
                     <= transL_closed.u9
                     <= transL_closed.u10
                     < ITree.Basics.CategoryTheory.257
                     <= rcompose.u0
                     <= rcompose.u2
                     <= sumor.u0
                     <= eqit_trans.u9
                     <= eqit_trans.u10
                     <= eqit_trans.u11
                     <= eqit_trans.u12
                     <= eqit_trans.u13
                     <= eqit_trans.u14
                     <= eqit_trans.u15
                     <= eqit_trans.u16
                     <= eqit_trans.u17
                     <= eqit_trans.u18
                     <= eqit_trans.u19
                     <= eqit_trans.u20
                     <= eqit_trans.u21
                     <= eqit_trans.u22
                     <= eqit_trans.u23
                     <= program.u0
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
    ii. des. inv PR; ss. inv PR0; try rewrite VIS in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR0; ss. inv PR; try rewrite RET in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; try rewrite VIS in *; ss; clarify.
  Qed.

End MODSEM.

Program Definition module (p: program) (mi: string) (initial_owned_heap: owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := (Sk.of_program fn_sig); Mod.get_modsem := modsem mi initial_owned_heap;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.

