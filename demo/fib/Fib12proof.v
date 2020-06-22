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
Require Import SIRmini.
Require Import SIRmini_stack.
Require Import Fib2.
Require Import Fib1.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.

Definition mp: ModPair.t := SimSymbId.mk_mp (Fib2.module) (Fib1.module).
Theorem sim_mod: ModPair.sim mp.
Proof. eapply SIRstackproof.sim_mod. Qed.
