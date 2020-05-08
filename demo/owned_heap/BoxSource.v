Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import CtypesC CtypingC.
Require Import ClightC.
Require Import BoxTarget.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.

Definition update V (map: block -> option V) (k0: block) (v: option V): block -> option V :=
  fun k1 => if eq_block k0 k1 then v else map k1.

Definition lo:Z := -8.
Definition hi:Z := 4.
Hint Unfold lo hi.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function prog).

  Definition owned_heap: Type := block -> option int.
  Definition initial_owned_heap: owned_heap := fun _ => None.

  Inductive state: Type :=
  | CallstateNew
      (v: int)
      (oh: owned_heap) (m: mem)
  | CallstateGet
      (k: block)
      (oh: owned_heap) (m: mem)
  | CallstateSet
      (k: block)
      (v: int)
      (oh: owned_heap) (m: mem)
  | CallstateDelete
      (k: block)
      (oh: owned_heap) (m: mem)
  | ReturnstateNew
      (k: block)
      (oh: owned_heap) (m: mem)
  | ReturnstateGet
      (v: int)
      (oh: owned_heap) (m: mem)
  | ReturnstateSet
      (oh: owned_heap) (m: mem)
  | ReturnstateDelete
      (oh: owned_heap) (m: mem)
  .

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
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_new
      oh0 m0 oh1 m1 m2 key val
      (ALLOC: Mem.alloc m0 lo hi = (m1, key))
      (FREE: Mem.free m1 key lo hi = Some m2)
      (OH: update oh0 key (Some val) = oh1)
    :
      step se ge (CallstateNew val oh0 m0) E0 (ReturnstateNew key oh1 m2)
  | step_get
      oh m key val
      (GET: oh key = Some val)
    :
      step se ge (CallstateGet key oh m) E0 (ReturnstateGet val oh m)
  | step_set
      oh0 m key val oh1
      (SOME: oh0 key <> None)
      (SET: update oh0 key (Some val) = oh1)
    :
      step se ge (CallstateSet key val oh0 m) E0 (ReturnstateSet oh1 m)
  | step_delete
      oh0 m key oh1
      (SOME: oh0 key <> None)
      (SET: update oh0 key None = oh1)
    :
      step se ge (CallstateDelete key oh0 m) E0 (ReturnstateDelete oh1 m)
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
