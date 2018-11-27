Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import CsemC.
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

Set Implicit Arguments.

Local Existing Instance Val.mi_normal.
Local Opaque Z.mul Z.add Z.sub Z.div.



Lemma ccc_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_ext_top
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_ext_unreach
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_inj_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_inj_drop
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  admit "this should hold".
Qed.

