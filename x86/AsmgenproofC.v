Require Import CoqlibC Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations MachC Conventions AsmC.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
Require Import Asmregs.
Require Import sflib.
(* newly added *)
Require Export Asmgenproof.
Require Import ModSem SimModSem SimSymbId SimMemId SimSymbId.

Set Implicit Arguments.


Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (MachC.modsem return_address_offset prog) (AsmC.modsem tprog) tt.

Theorem sim
  :
    ModSemPair.sim msp
.
Proof.
  admit "try this!".
Qed.

End PRESERVATION.
