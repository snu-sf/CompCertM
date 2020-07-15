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
Require Import Fib4.
Require Import Fib3.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.
Require Import ITreelib.
Require Import SIRHoare2.
From Coq Require Import
     Morphisms RelationClasses.
(*** TODO: export in in SIRCommon or somewhere ***)

Set Implicit Arguments.



(*** TODO: change unwrapU/unwrapN/assume/guarantee into notation?
     ---> It does not work well. I didn't type "parse only" but it works only for parsing.
          In other words, it does not work in printing, which results in unreadable code during the proof
 ***)

Definition manifesto (fname: ident): option (funspec owned_heap) :=
  if (ident_eq fname Fib0._fib: bool)
  then Some (mk _fib_ru FibHeader.precond FibHeader.postcond)
  else None
.
Definition images: ident -> bool := ident_eq _fib_ru.

Theorem correct: rusc defaultR [Fib4.module: Mod.t] [Fib3.module: Mod.t].
Proof.
  eapply SIRHoare2.correct with (manifesto:=manifesto) (images:=images); et.
  { unfold images, manifesto. images_tac. }
  econs; ss; et.
  - ii; ss. dup HOARE. unfold manifesto in HOARE. des_ifs; des_sumbool; clarify; ss. esplits; ss; eauto.
    econs; ss; et; cycle 1.
    + ii. iby3 ltac:(irw; refl).
    + unfold f_fib_ru. repeat step.
  - prog_tac.
Qed.
