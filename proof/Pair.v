Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem SimMem SimSymb.

Set Implicit Arguments.































Module ProgPair.
Section PROGPAIR.
Context `{SS: SimSymb.class}.

  Definition t := list ModPair.t.

  Definition wf (pp: t) := List.Forall ModPair.wf pp.

  Definition src (pp: t): program := List.map ModPair.src pp.
  Definition tgt (pp: t): program := List.map ModPair.tgt pp.

  Definition ss_link (pp: t): option SimSymb.t := link_list (List.map ModPair.ss pp).
  (* ############ TODO: *)
  (* ModPair.wf mp0 /\ ModPair.wf mp1 /\ link mp0.(src) mp1.(src) = Some /\ link mp1.(tgt) mp1.(tgt) = Some *)
  (* =================> link mp0.(ss) mp1.(ss) suceeds. *)
  (* Move ModPair.wf into SimSymb and obligate its proof? *)

End PROGPAIR.
End ProgPair.















































