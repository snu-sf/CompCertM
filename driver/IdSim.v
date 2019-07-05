Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import Csem AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require IdSimAsm.
Include IdSimAsm.
Require IdSimCCC.
Include IdSimCCC.
Require IdSimClight.
Include IdSimClight.
Require IdSimAsmDropInv.
Include IdSimAsmDropInv.
Require IdSimClightDropInv.
Include IdSimClightDropInv.

Set Implicit Arguments.



Lemma lift
      `{SM: SimMem.class} `{@SimSymb.class SM} `{Sound.class}
      X (to_mod: X -> Mod.t)
      (MOD: forall x (WF: Sk.wf x.(to_mod))
        , exists mp,
            ModPair.sim mp /\ mp.(ModPair.src) = x.(to_mod) /\ mp.(ModPair.tgt) = x.(to_mod))
  :
    <<PROG: forall xs (WF: forall x (IN: In x xs), Sk.wf x.(to_mod)),
      exists pp,
        __GUARD__ (ProgPair.sim pp /\ ProgPair.src pp = map to_mod xs /\ ProgPair.tgt pp = map to_mod xs)
                  >>
.
Proof.
  ii.
  unfold __GUARD__ in *.
  induction xs; ii; ss.
  { esplits; eauto. }
  exploit MOD; eauto. i. des.
  exploit IHxs; eauto. i. des.
  exists (mp :: pp). esplits; ss; eauto with congruence.
Qed.
