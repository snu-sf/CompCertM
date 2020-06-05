Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import UnionFindTarget.
Require Import SIR.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.

Definition key: Type := block.

Definition eq_key: forall (x y: key), {x = y} + {x <> y}.
  decide equality.
Defined.

Definition update V (map: key -> option V) (k0: key) (v: option V): key -> option V :=
  fun k1 => if eq_key k0 k1 then v else map k1.

Definition owned_heap: Type := key -> option (key * int).
Definition initial_owned_heap: SkEnv.t -> owned_heap := fun _ => fun _ => None.

Variable global_definitions:
  list (ident * globdef (fundef (SIR.function owned_heap)) unit).

Definition c_makeSet (oh0: owned_heap) (vs: list val) (m0: mem):
  itree (eff owned_heap) (owned_heap * mem * val) :=
  let '(m1, blk) := (Mem.alloc m0 0%Z 0%Z) in
  let oh1 := update oh0 blk (Some (blk, Int.zero)) in
  Ret (oh1, m1, (Vptr blk Ptrofs.zero))
.

Definition f_makeSet: function owned_heap :=
  mkfunction (ClightC.signature_of_function f_makeSet) c_makeSet.

Definition g_makeSet:
  (ident * globdef (fundef (SIR.function owned_heap)) unit) :=
  (_makeSet, Gfun(Internal f_makeSet)).

Definition assume (P: Prop): itree (eff owned_heap) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerUB "assume"
.
  
Definition guarantee (P: Prop): itree (eff owned_heap) unit :=
  if ClassicalDescription.excluded_middle_informative P
  then Ret tt
  else triggerNB "guarantee"
.

Definition c_find (oh0: owned_heap) (vs: list val) (m0: mem):
  itree (eff owned_heap) (owned_heap * mem * val) :=
  match vs with
  | [Vptr x ofs] =>
    assume (Ptrofs.eq_dec ofs Ptrofs.zero) ;;
    '(p, rx) <- unwrapU (oh0 blk) ;;
    if negb (block_eq p x)
    then
      p0 <- trigger (ICall _find oh0 ([Vptr p Ptrofs.zero]) m0) ;;
      match p0 with
      | [Vptr p0 ofs] =>
        guarantee (Ptrofs.eq_dec ofs Ptrofs.zero) ;;
        let oh1 := update oh0 x (Some (p0, rx)) in
        Ret tt
    else Ret tt;;
    Ret (
  | _ => triggerUB ""
  end
.

struct Node* find(struct Node* x) {
  struct Node *p, *p0;
  p = x -> parent;
  if (p != x) {
    p0 = find(p);
    x -> parent = p0;
  }
  return p;
};

void unionS(struct Node* x, struct Node* y) {
  struct Node *xRoot, *yRoot;
  unsigned int xRank, yRank;
  xRoot = find(x);
  yRoot = find(y);
  if (xRoot == yRoot) {
    return;
  }
  xRank = xRoot -> rank;
  yRank = yRoot -> rank;
  if (xRank < yRank) {
    xRoot -> parent = yRoot;
  } else if (xRank > yRank) {
    yRoot -> parent = xRoot;
  } else {
    yRoot -> parent = xRoot;
    xRoot -> rank = xRank + 1;
  }
};

/////////////////////////////////////////////////

int same_set(struct Node* x, struct Node *y) {
  return (find(x) == find(y));
}


Definition prog: SIR.program owned_heap :=
  mkprogram global_definitions public_idents _main.

Variable p: program owned_heap.
Definition module: Mod.t := SIR.module p "UF" (initial_owned_heap).


(_makeSet, Gfun(Internal f_makeSet)) :: (_find, Gfun(Internal f_find)) ::
 (_unionS, Gfun(Internal f_unionS)) ::
 (_same_set, Gfun(Internal f_same_set))










Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function prog).

  Definition owned_heap: Type := key -> option (int * bool).
  Variable p: SIR.program owned_heap.
  Definition initial_owned_heap: owned_heap := fun _ => None.

  Inductive state: Type :=
  | CallstateNew
      (v: int)
      (oh: owned_heap) (m: mem)
  | CallstateGet
      (k: key)
      (oh: owned_heap) (m: mem)
  | CallstateSet
      (k: key)
      (v: int)
      (oh: owned_heap) (m: mem)
  | CallstateDelete
      (k: key)
      (oh: owned_heap) (m: mem)
  | CallstateFromRaw
      (k: key)
      (oh: owned_heap) (m: mem)
  | CallstateIntoRaw
      (k: key)
      (oh: owned_heap) (m: mem)
  | ReturnstateNew
      (k: key)
      (oh: owned_heap) (m: mem)
  | ReturnstateGet
      (v: int)
      (oh: owned_heap) (m: mem)
  | ReturnstateSet
      (oh: owned_heap) (m: mem)
  | ReturnstateDelete
      (oh: owned_heap) (m: mem)
  | ReturnstateFromRaw
      (k: key)
      (oh: owned_heap) (m: mem)
  | ReturnstateIntoRaw
      (k: key)
      (oh: owned_heap) (m: mem)
  .

  (*** TODO:
we can say that,
(1) if is_raw is false (new/delete) --> ptrofs is zero
(2) mem.valid_block thing
   ***)
  Definition oh_wf: owned_heap -> Prop := top1.

  Inductive initial_frame (oh: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_new
      (WF: oh_wf oh)
      m blk val
      (SYMB: Genv.find_symbol skenv _new = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vint val])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateNew val oh m)
  | initial_frame_get
      (WF: oh_wf oh)
      m blk key
      (SYMB: Genv.find_symbol skenv _get = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vptr key Ptrofs.zero])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateGet key oh m)
  | initial_frame_set
      (WF: oh_wf oh)
      m blk key val
      (SYMB: Genv.find_symbol skenv _get = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (OHSOME: oh key <> None)
      (VS: (Args.vs args) = [Vptr key Ptrofs.zero ; Vint val])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateSet key val oh m)
  | initial_frame_delete
      (WF: oh_wf oh)
      m blk key
      (SYMB: Genv.find_symbol skenv _delete = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vptr key Ptrofs.zero])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateDelete key oh m)
  | initial_frame_from_raw
      (WF: oh_wf oh)
      m blk key
      (SYMB: Genv.find_symbol skenv _from_raw = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vptr key Ptrofs.zero])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateFromRaw key oh m)
  | initial_frame_into_raw
      (WF: oh_wf oh)
      m blk key
      (SYMB: Genv.find_symbol skenv _into_raw = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [Vptr key Ptrofs.zero])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (CallstateIntoRaw key oh m)
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_new
      oh0 m0 oh1 m1 m2 key val
      (ALLOC: Mem.alloc m0 lo hi = (m1, key))
      (FREE: Mem.free m1 key lo hi = Some m2)
      (OH: update oh0 key (Some (val, false)) = oh1)
    :
      step se ge (CallstateNew val oh0 m0) E0 (ReturnstateNew key oh1 m2)
  | step_get
      oh m key val is_raw
      (GET: oh key = Some (val, is_raw))
    :
      step se ge (CallstateGet key oh m) E0 (ReturnstateGet val oh m)
  | step_set
      oh0 m key val oh1 UNUSED_oldval is_raw
      (SOME: oh0 key = Some (UNUSED_oldval, is_raw))
      (SET: update oh0 key (Some (val, is_raw)) = oh1)
    :
      step se ge (CallstateSet key val oh0 m) E0 (ReturnstateSet oh1 m)
  | step_delete
      oh0 m key UNUSED_oldval oh1
      (SOME: oh0 key = Some (UNUSED_oldval, false))
      (SET: update oh0 key None = oh1)
    :
      step se ge (CallstateDelete key oh0 m) E0 (ReturnstateDelete oh1 m)
  | step_from_raw
      oh0 m0 key val oh1 m1
      (LOAD: Mem.load Mint32 m0 key 0%Z = Some (Vint val))
      (FREE: Mem.free m0 key 0%Z hi = Some m1)
      (NONE: oh0 key = None) (*** <- TODO: is it needed? ***)
      (SET: update oh0 key (Some (val, true)) = oh1)
    :
      step se ge (CallstateFromRaw key oh0 m0) E0 (ReturnstateFromRaw key oh1 m1)
  | step_into_raw
      oh0 m0 key val m1 oh1 m2
      (*** TODO: we should "GUARANTEE" that store succeeds. ***)
      (SOME: oh0 key = Some (val, true))
      (UNFREE: Mem_unfree m0 key 0%Z hi  = Some m1)
      (STORE: Mem_stored Mint32 m1 key 0%Z (Vint val) m2)
      (SET: update oh0 key None = oh1)
    :
      step se ge (CallstateIntoRaw key oh0 m0) E0 (ReturnstateIntoRaw key oh1 m2)
  .

  Inductive final_frame: state -> owned_heap -> Retv.t -> Prop :=
  | final_new
      key oh m
    :
      final_frame (ReturnstateNew key oh m) oh (Retv.mk (Vptr key Ptrofs.zero) m)
  | final_get
      val oh m
    :
      final_frame (ReturnstateGet val oh m) oh (Retv.mk (Vint val) m)
  | final_set
      oh m
    :
      final_frame (ReturnstateSet oh m) oh (Retv.mk Vundef m)
  | final_delete
      oh m
    :
      final_frame (ReturnstateDelete oh m) oh (Retv.mk Vundef m)
  | final_from_raw
      key oh m
    :
      final_frame (ReturnstateFromRaw key oh m) oh (Retv.mk (Vptr key Ptrofs.zero) m)
  | final_into_raw
      key oh m
    :
      final_frame (ReturnstateIntoRaw key oh m) oh (Retv.mk (Vptr key Ptrofs.zero) m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := bot3;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := bot4;
      ModSem.globalenv := skenv;
      ModSem.skenv := skenv;
      ModSem.midx := Some "OHAlloc";
      ModSem.skenv_link := skenv_link;
      ModSem.owned_heap := owned_heap;
      ModSem.initial_owned_heap := initial_owned_heap;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => CSk.of_program signature_of_function prog; Mod.get_modsem := modsem; Mod.midx := Some "OHAlloc" |}.

(* Lemma find_symbol_find_funct_ptr *)
(*       skenv_link blk *)
(*       ske *)
(*       (WF: SkEnv.wf skenv_link) *)
(*       (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function MutrecA.prog)) *)
(*       (SKE: ske = (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog))) : *)
(*     (<<SYMB: Genv.find_symbol ske f_id = Some blk>>) <-> *)
(*     (<<FINDF: exists if_sig, Genv.find_funct_ptr ske blk = Some (AST.Internal if_sig)>>). *)
(* Proof. *)
(*   clarify. *)
(*   hexploit (SkEnv.project_impl_spec INCL); eauto. intro PROJ. *)
(*   exploit SkEnv.project_spec_preserves_wf; eauto. intro WFSMALL. *)
(*   inv INCL. specialize (DEFS f_id). ss. exploit DEFS; eauto. i; des. *)
(*   inv MATCH. inv H0. *)
(*   inv PROJ. exploit (SYMBKEEP f_id); eauto. intro T; des. rewrite T in *. *)
(*   exploit DEFKEEP; eauto. *)
(*   { eapply Genv.find_invert_symbol; et. } *)
(*   { ss. } *)
(*   i; des. *)
(*   inv LO. inv H1; ss. clarify. *)
(*   split; ii; ss; des; clarify. *)
(*   - unfold Genv.find_funct_ptr. rewrite DEFSMALL. ss. esplits; eauto. *)
(*   - unfold Genv.find_funct_ptr in *. des_ifs. *)
(*     clear_tac. *)
(*     assert(blk = blk0). *)
(*     { clear - DEFSMALL Heq. *)
(*       uge. ss. rewrite MapsC.PTree_filter_map_spec in *. uo. des_ifs. *)
(*       apply_all_once in_prog_defmap. ss. unfold update_snd in *. ss. des; clarify. *)
(*       apply_all_once Genv.invert_find_symbol. clarify. *)
(*     } clarify. *)
(* Qed. *)
