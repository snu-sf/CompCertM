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
Require Import FibHeader.
Require Import Fib7.
Require Import Fib6.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.



Theorem correct: rusc defaultR [Fib7.module: Mod.t] [Fib6.module: Mod.t].
Proof.
  etrans.
  { mimic. eapply SIREutt.correct; ss; et. prog_tac.
    unfold Fib7.f_fib. do 2 setoid_rewrite <- tau_eutt at 2. refl.
  }
  eapply SIRLocal.correct; ss; et.
  prog_tac.
  unfold Fib7.f_fib, f_fib.
  unfold unwrapU. des_ifs; irw; cycle 1.
  { unfold triggerUB. irw. pfold. econs; et. }
  unfold assume, precond. des_ifs; cycle 1.
  { contradict n0. eauto. }
  des; clarify.
  irw. pfold. econs; et; cycle 1.
  { eexists. eexists (_, (_, _)). ss. des_ifs. }
  ii. destruct x_tgt; ss. destruct x as [ohr [mr vr]]. ss. des_ifs. des; clarify. left. pfold. econs; et.
Unshelve.
  all: try (by sk_incl_tac).
Qed.
