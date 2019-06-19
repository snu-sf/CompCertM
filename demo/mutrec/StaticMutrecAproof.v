Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import StaticMutrecHeader.
Require Import StaticMutrecA StaticMutrecAspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SimMemId.
Require SoundTop.
Require Import Clightdefs.
Require Import CtypesC.

Set Implicit Arguments.

Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (StaticMutrecAspec.module) (ClightC.module2 prog) tt)
.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK.
    admit "".
    (* eapply sim_modsem; eauto. *)
Qed.
