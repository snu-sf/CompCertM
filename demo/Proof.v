Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import CtypesC CsemC Csyntax AsmC.
Require Import sflib.

Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.
Require Import MatchSimModSem.

Require Source.
Require Target.
Require Import Header.


Definition mp: ModPair.t := ModPair.mk Source.md Target.md tt.

Theorem correct
  :
    ModPair.sim mp
.
Proof.
  econs; eauto.
  { ss. }
  i.
  (* eapply match_states_sim; eauto. *)
  admit "Prove this!".
Qed.
