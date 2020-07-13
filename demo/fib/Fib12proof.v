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
  { eapply SIREutt.correct; ss; et.
    unfold Fib2.prog, prog.
    ii. clarify. rr. ss. des_ifs; ss. ii. clarify. r.
    unfold Fib2.f_fib, f_fib. rewrite tau_eutt. refl.
  }
Unshelve.
  try (by ii; ss; unfold internals in *; des_ifs; eapply_all_once prog_defmap_image; ss; des; clarify).
Qed.
