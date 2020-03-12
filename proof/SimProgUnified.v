Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import SimSymb.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem.
Require Import SimMem SimModSemUnified SimModUnified.
Require Import Sound SemProps.

Set Implicit Arguments.





Module ProgPair.
Section PROGPAIR.
Context `{SMOS: SimMemOhs.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Definition t := list ModPair.t.

  Definition sim (pp: t) := List.Forall ModPair.sim pp.

  Definition src (pp: t): program := List.map ModPair.src pp.
  Definition tgt (pp: t): program := List.map ModPair.tgt pp.

  (* Definition ss_link (pp: t): option SimSymb.t := link_list (List.map ModPair.ss pp). *)
  (* ############ TODO: *)
  (* ModPair.wf mp0 /\ ModPair.wf mp1 /\ link mp0.(src) mp1.(src) = Some /\ link mp1.(tgt) mp1.(tgt) = Some *)
  (* =================> link mp0.(ss) mp1.(ss) suceeds. *)
  (* Move ModPair.wf into SimSymb and obligate its proof? *)

End PROGPAIR.
End ProgPair.

Hint Unfold ProgPair.sim ProgPair.src ProgPair.tgt.
(* Hint Unfold ProgPair.ss_link. *)


Require Import SimProg.
Require Import SimMod.

Axiom mp_to_mp: forall `{SimMem.class} `{SimSymb.class},
    SimMod.ModPair.t -> SimModUnified.ModPair.t.

Theorem unification
        `{SimMem.class}
        `{Sound.class}
        `{SimSymb.class}
        pp
        (SIM: ProgPair.sim pp)
  :
    exists SMOS ppu,
      (<<SIM: SimProgUnified.ProgPair.sim ppu (SMOS := SMOS)>>)
      /\ (<<PROGSRC: (SimProgUnified.ProgPair.src ppu) = (ProgPair.src pp)>>)
      /\ (<<PROGTGT: (SimProgUnified.ProgPair.tgt ppu) = (ProgPair.tgt pp)>>)
.
Proof.
  ginduction pp; ii; ss.
  { unshelve esplits; eauto. admit "Make default instance for SimMemOhs". }
  inv SIM.
  exploit IHpp; eauto. i; des.
  assert(exists SMOS',
            (<<SIM: SimProgUnified.ProgPair.sim (SMOS := SMOS') ppu>>) /\
            (<<SIM: SimModUnified.ModPair.sim (SMOS := SMOS') (mp_to_mp a)>>)
        ).
  { admit "merge theorem". }
  des.
  eexists SMOS', ((mp_to_mp a) :: ppu).
  esplits; ss; eauto.
Qed.

SimProg.ProgPair.t
SimProgUnified.ProgPair.t

SimMod.ModPair.t
SimModUnified.ModPair.t

SimModSem.ModSemPair.t
SimModSemUnified.ModSemPair.t
