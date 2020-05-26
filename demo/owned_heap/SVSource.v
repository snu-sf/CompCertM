Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import CtypesC CtypingC.
Require Import ClightC.
Require Import SVTarget.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; repeat des_u; ss; clarify.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function prog).

  Definition owned_heap: Type := int.
  Definition initial_owned_heap: owned_heap := Int.zero.

  Inductive state: Type :=
  | Callstate
      (F: int + int) (* get or incr *)
      (m: mem)
  | Returnstate
      (s: int + int) (* get or incr *)
      (m: mem)
  .

  Inductive initial_frame (oh: int) (args: Args.t): state -> Prop :=
  | initial_frame_get
      (WF: (Int.signed oh >= 0)%Z)
      m blk
      (SYMB: Genv.find_symbol skenv _get = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (Callstate (inl oh) m)
  | initial_frame_incr
      (WF: (Int.signed oh >= 0)%Z)
      m blk
      (SYMB: Genv.find_symbol skenv _incr = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = [])
      (M: (Args.m args) = m)
    :
      initial_frame oh args (Callstate (inr oh) m)
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_get
      i m
    :
      step se ge (Callstate (inl i) m) E0 (Returnstate (inl i) m)
  | step_incr
      i m
    :
      step se ge (Callstate (inr i) m) E0
           (Returnstate (inr (Int.mods (Int.add Int.one i) (Int.repr 10))) m)
  .

  Inductive final_frame: state -> owned_heap -> Retv.t -> Prop :=
  | final_get
      i m
    :
      final_frame (Returnstate (inl i) m) i (Retv.mk (Vint i) m)
  | final_incr
      i m
    :
      final_frame (Returnstate (inr i) m) i (Retv.mk Vundef m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := bot3;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := bot4;
      ModSem.globalenv := skenv;
      ModSem.codeseg := skenv;
      ModSem.skenv_link := skenv_link;
      ModSem.midx := Some "SV";
      ModSem.owned_heap := owned_heap;
      ModSem.initial_owned_heap := initial_owned_heap;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => CSk.of_program signature_of_function prog; Mod.get_modsem := modsem; Mod.midx := Some "SV" |}.

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
