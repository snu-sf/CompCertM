Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import Csem AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.

Set Implicit Arguments.

Local Existing Instance Val.mi_normal.

Parameter C_module: Csyntax.program -> Mod.t.

Lemma tgt_id
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma tgt_ext_top
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma tgt_ext_unreach
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma tgt_inj_id
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimMemInj.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma tgt_inj_drop
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.




Lemma src_id
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_ext_top
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_ext_unreach
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_inj_id
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimMemInj.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_inj_drop
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.



Lemma lift
      `{SM: SimMem.class} `{@SimSymb.class SM} `{Sound.class}
      X (to_mod: X -> Mod.t)
      (MOD: forall x, exists mp,
            ModPair.sim mp /\ mp.(ModPair.src) = x.(to_mod) /\ mp.(ModPair.tgt) = x.(to_mod))
  :
    <<PROG: forall xs, exists pp,
        ProgPair.sim pp /\ ProgPair.src pp = map to_mod xs /\ ProgPair.tgt pp = map to_mod xs
                                                                                    >>
.
Proof.
  ii.
  induction xs; ii; ss.
  { esplits; eauto. }
  des.
  specialize (MOD a). des.
  exists (mp :: pp). esplits; ss; eauto with congruence.
Qed.

