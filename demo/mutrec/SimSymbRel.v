Require Import Events.
Require Import Values.
Require Import AST.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import IntegersC.
Require Import ASTC.
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimSymb.
Require Import SimMem.
Require Import SimMemInjC.
Require Import ModSem.


Global Program Instance SimSymbRel: SimSymb.class SimMemInj := {
  t := t';
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}
.