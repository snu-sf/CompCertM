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

Theorem correct: rusc defaultR [Fib2.module] [Fib1.module].
Proof.
  etrans; cycle 1.
  { eapply SIRStackproof.correct. }
  { eapply SIREutt.correct.
    unfold Fib2.prog, prog.
    ii. clarify. rr. ss. des_ifs; ss. ii. clarify. r.
    unfold Fib2.f_fib, f_fib. rewrite tau_eutt. refl.
  }
Qed.
