Require Import EventsC.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep Simulation.
Require Import CoqlibC.

Require Import Mod ModSem Skeleton System.
Require Import SimMem Sound SimSymb Syntax.

Set Implicit Arguments.


Section SIM.
  Context `{SM: SimMem.class}.
  Context `{SU: Sound.class}.
  Context {SS: SimSymb.class SM}.

  Variables p: program.
  System.module p
  Definition mp: ModPair.t := SimSymb.mk_mp (RTLC.module prog) (RTLC.module tprog).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    econs; ss.
    - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
      + clarify. right. esplits; eauto.
      + clarify. left. esplits; eauto.
    - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
  Qed.
End SIM.
