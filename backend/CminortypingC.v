
(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import CoqlibC Maps Errors.
Require Import AST Integers Floats ValuesC Memory Globalenvs Events Smallstep.
Require Import Cminor.
Require Import Unityping.
Require Import sflib.
(** newly added **)
Require Export Cminortyping.
Require Import Skeleton ModSem Preservation.
Require Import SoundTop.
Require Import CminorC.


Section LPRSV.

  Variable prog: program.

  Hypothesis wt_prog:
    forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

  Theorem wt_state_local_preservation: forall skenv_link,
      local_preservation (modsem skenv_link prog) (fun _ _ st => wt_state st).
  Proof.
    econs; ii; ss; eauto.
    - (* init *)
      inv INIT. econs; et.
      + inv TYP. eapply typify_has_type_list; et.
      + econs; et.
    - (* step *)
      eapply subject_reduction; et.
      ii. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
      unfold Skeleton.SkEnv.revive in *.
      eapply Genv_map_defs_def in Heq. des. u in MAP. des_ifs_safe.
      esplits. eapply in_prog_defmap; eauto.
    - esplits; eauto.
      { rr. esplits; ss; eauto. des_ifs. esplits; ss. rr. rewrite Forall_forall. ii; ss. }
      ii. inv AFTER. inv SUST. econs; et. apply typify_has_type.
    - esplits; eauto. rr. des_ifs.
  Unshelve.
    all: ss.
  Qed.

End LPRSV.
