Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSemExcl.
Require SoundTop.
Require SimMemId.
Require Import Any.
Require Import SIR.
Require Import SIRStack.
Require Import Fib2.
Require Import Fib1.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.



Theorem correct: rusc defaultR [Fib2.module: Mod.t] [Fib1.module: Mod.t].
Proof.
  etrans; cycle 1.
  { mimic. eapply SIRStackproof.correct; ss; et. }
  { eapply SIREuttLocal.correct; ss; et. prog_tac.
    unfold Fib2.f_fib, f_fib.
    repeat (f_equiv; ii; des_ifs; try rewrite ! tau_eutt).
  }
Unshelve.
  sk_incl_tac.
Qed.
