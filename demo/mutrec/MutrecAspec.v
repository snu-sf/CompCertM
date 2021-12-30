Require Import CoqlibC.
From compcertr Require Import
     Maps
     Integers
     Memory
     Globalenvs.
Require Import ASTC ValuesC EventsC.
From compcertr Require Import Op Registers.
From compcertr Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require Import CtypesC CtypingC.
Require Import ClightC.
Require Import MutrecHeader.
Require Import MutrecA.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; ss; clarify.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: unit.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function prog).

  Inductive state: Type :=
  | Callstate
      (i: int)
      (m: mem)
  | Interstate
      (i: int)
      (m: mem)
  | Returnstate
      (s: int)
      (m: mem)
  .

  Definition get_mem (st: state): mem :=
    match st with
    | Callstate _ m => m
    | Interstate _ m => m
    | Returnstate _ m => m
    end
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame1_intro
      i m blk
      (SYMB: Genv.find_symbol skenv f_id = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (RANGE: 0 <= i.(Int.intval) < MAX)
      (VS: (Args.vs args) = [Vint i])
      (M: (Args.m args) = m)
    :
      initial_frame args (Callstate i m)
  .

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      g_fptr i m
      (FINDG: Genv.find_symbol skenv g_id = Some g_fptr)
    :
      at_external (Interstate i m) (Args.mk (Vptr g_fptr Ptrofs.zero) [Vint (Int.sub i (Int.repr 1))] m)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      i m retv
      i_after
      (INT: (Retv.v retv) = Vint i_after)
      (SUM: i_after = sum (Int.sub i Int.one))
    :
      after_external (Interstate i m) retv (Returnstate (sum i) (Retv.m retv))
  .

  Inductive step (se: Senv.t) (ge: SkEnv.t): state -> trace -> state -> Prop :=
  | step_sum
      i m
    :
      step se ge (Callstate i m) E0 (Returnstate (sum i) m)
  | step_call
      i m
      (NZERO: i.(Int.intval) <> 0%Z)
    :
      step se ge (Callstate i m) E0 (Interstate i m)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_return
      s m
    :
      final_frame (Returnstate s m) (Retv.mk (Vint s) m)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := skenv;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .

End MODSEM.

Program Definition module: Mod.t :=
  {| Mod.data := tt; Mod.get_sk := fun _ => CSk.of_program signature_of_function prog; Mod.get_modsem := modsem; |}.

Lemma find_symbol_find_funct_ptr
      skenv_link blk
      ske
      (WF: SkEnv.wf skenv_link)
      (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function MutrecA.prog))
      (SKE: ske = (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog))) :
    (<<SYMB: Genv.find_symbol ske f_id = Some blk>>) <->
    (<<FINDF: exists if_sig, Genv.find_funct_ptr ske blk = Some (AST.Internal if_sig)>>).
Proof.
  clarify.
  hexploit (SkEnv.project_impl_spec INCL); eauto. intro PROJ.
  exploit SkEnv.project_spec_preserves_wf; eauto. intro WFSMALL.
  inv INCL. specialize (DEFS f_id). ss. exploit DEFS; eauto. i; des.
  inv MATCH. inv H0.
  inv PROJ. exploit (SYMBKEEP f_id); eauto. intro T; des. rewrite T in *.
  exploit DEFKEEP; eauto.
  { eapply Genv.find_invert_symbol; et. }
  { ss. }
  i; des.
  inv LO. inv H1; ss. clarify.
  split; ii; ss; des; clarify.
  - unfold Genv.find_funct_ptr. rewrite DEFSMALL. ss. esplits; eauto.
  - unfold Genv.find_funct_ptr in *. des_ifs.
    clear_tac.
    assert(blk = blk0).
    { clear - DEFSMALL Heq.
      uge. ss. rewrite MapsC.PTree_filter_map_spec in *. uo. des_ifs.
      apply_all_once in_prog_defmap. ss. unfold update_snd in *. ss. des; clarify.
      apply_all_once Genv.invert_find_symbol. clarify.
    } clarify.
Qed.
