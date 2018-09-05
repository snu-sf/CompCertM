Require Import FunInd.
Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import Registers Op RTL.
Require Import ValueDomain ValueAOp Liveness.
Require Import sflib.
(** copied from above **)
Require Export ValueAnalysis.
Require Import Preservation.

Theorem sound_state_preservation
        local_preservation_strong