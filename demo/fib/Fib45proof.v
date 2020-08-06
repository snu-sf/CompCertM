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
Require Import Fib5.
Require Import Fib4.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.



Theorem correct: rusc defaultR [Fib5.module: Mod.t] [Fib4.module: Mod.t].
Proof.
  etrans; cycle 1.
  { mimic. eapply SIREuttLocal.correct; ss. prog_tac.
    { refl. }
    unfold f_fib. rewrite guaranteeK2_spec. unfold guaranteeK2. do 2 setoid_rewrite <- tau_eutt at 4.
    refl.
  }
  {
    eapply SIRLocal.correct with (SO := eq); ss.
    prog_tac.
    { refl. }
    unfold Fib5.f_fib, f_fib.
    repeat step. des_ifs; irw; try (pfold; econs; et). des; clarify.
    eexists (exist _ _ _); cbn. left. pfold. econs; et.
  }
  Unshelve.
  - sk_incl_tac.
  - ss. des_ifs.
Qed.
