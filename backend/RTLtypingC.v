(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Typing rules and a type inference algorithm for RTL. *)

Require Import CoqlibC.
Require Import Errors.
Require Import Unityping.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import ValuesC.
Require Import IntegersC.
Require Import MemoryC.
Require Import Events.
Require Import RTLC.
Require Import Conventions.
Require Import sflib.
(** newly added **)
Require Export RTLtyping.

Inductive wt_stackframes: list stackframe -> signature -> Prop :=
  | wt_stackframes_nil: forall sg,
      wt_stackframes nil sg
  | wt_stackframes_cons:
      forall s res f sp pc rs env sg,
      wt_function f env ->
      wt_regset env rs ->
      env res = proj_sig_res sg ->
      wt_stackframes s (fn_sig f) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) sg.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs m env
        (WT_STK: wt_stackframes s (fn_sig f))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s f sp pc rs m)
  | wt_state_call:
      forall s fptr sg args m,
      wt_stackframes s sg ->
      DUMMY_PROP ->
      Val.has_type_list args (sig_args sg) ->
      wt_state (Callstate s fptr sg args m)
  | wt_state_return:
      forall s v m sg,
      wt_stackframes s sg ->
      Val.has_type v (proj_sig_res sg) ->
      wt_state (Returnstate s v m).

Remark wt_stackframes_change_sig:
  forall s sg1 sg2,
  sg1.(sig_res) = sg2.(sig_res) -> wt_stackframes s sg1 -> wt_stackframes s sg2.
Proof.
  intros. inv H0.
- constructor; congruence.
- econstructor; eauto. rewrite H3. unfold proj_sig_res. rewrite H. auto.
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Variable se: Senv.t.
Variable ge: genv.

Hypothesis CONTAINED: forall
    fptr f
    (FINDF: Genv.find_funct ge fptr = Some f)
  ,
    exists i, In (i, Gfun f) (prog_defs p)
.

Lemma subject_reduction:
  forall st1 t st2, step se ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; intros; inv WT;
  try (generalize (wt_instrs _ _ WT_FN pc _ H); intros WTI).
  (* Inop *)
  econstructor; eauto.
  (* Iop *)
  econstructor; eauto. eapply wt_exec_Iop; eauto.
  (* Iload *)
  econstructor; eauto. eapply wt_exec_Iload; eauto.
  (* Istore *)
  econstructor; eauto.
  (* Icall *)
  econstructor; eauto.
  econstructor; eauto. inv WTI; auto.
  inv WTI. rewrite <- H8. apply wt_regset_list. auto.
  (* Itailcall *)
  econstructor; eauto.
  inv WTI. apply wt_stackframes_change_sig with (fn_sig f); auto.
  inv WTI. rewrite <- H7. apply wt_regset_list. auto.
  (* Ibuiltin *)
  econstructor; eauto. eapply wt_exec_Ibuiltin; eauto.
  (* Icond *)
  econstructor; eauto.
  (* Ijumptable *)
  econstructor; eauto.
  (* Ireturn *)
  econstructor; eauto.
  inv WTI; simpl. auto. unfold proj_sig_res; rewrite H2. auto.
  (* internal function *)
  assert(H5: wt_fundef (Internal f)). exploit CONTAINED; eauto. i; des. eapply wt_p; eauto.
  simpl in *. inv H5.
  econstructor; eauto.
  inv H1. apply wt_init_regs; auto. rewrite wt_params. auto.
  (* external function *)
  econstructor; eauto. simpl.
  eapply external_call_well_typed; eauto.
  (* return *)
  inv H1. econstructor; eauto.
  apply wt_regset_assign; auto. rewrite H10; auto.
Qed.

End SUBJECT_REDUCTION.



Require Import Skeleton ModSem Preservation.
Require Import SoundTop.
Require Import RTLC.

Section LPRSV.

  Variable prog: program.

  Hypothesis wt_prog:
    forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd
  .

  Theorem wt_state_local_preservation
          skenv_link
    :
      local_preservation (modsem skenv_link prog) (fun _ _ st => wt_state st)
  .
  Proof.
    econs; ii; ss; eauto.
    - (* init *)
      inv INIT.
      econs; et.
      + econs; et.
      + inv TYP. eapply typify_has_type_list; et.
    - (* step *)
      eapply subject_reduction; et.
      ii. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
      unfold Skeleton.SkEnv.revive in *.
      eapply Genv_map_defs_def in Heq. des. u in MAP. des_ifs_safe.
      esplits. eapply in_prog_defmap; eauto.
    - esplits; eauto.
      ii.
      inv AFTER.
      inv SUST.

      econs; et.
      admit "proj_sig_res change".
    - esplits; eauto. ss.
  Unshelve.
    all: ss.
  Qed.

End LPRSV.
