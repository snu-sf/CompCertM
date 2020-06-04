Require Import SimMem.
Require Import Simulation.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
Require Import Values Integers.
Require Import Globalenvs.
Require Import Program.
Require Import MemoryC.

Require Import Skeleton SimSymb Ord.
Require Import Mod ModSem.
Require Import Sound Preservation.
Require Import ModSemProps.
Require Import Events.
Require Import SmallstepC.
Require Import Any.
Require Import SimModSem.

Set Printing Universes.

From ITree Require Import
     ITree
     ITreeFacts
.

Require Import SIR.

Error: Universe inconsistency. Cannot enforce
  ITree.Core.ITreeDefinition.3 <= Mod.Mod.t.u0
  because
  Mod.Mod.t.u0 < Coq.Lists.List.1 <= option.u0 = ITree.Core.ITreeDefinition.3.
ITree.Core.ITreeDefinition
Set Implicit Arguments.