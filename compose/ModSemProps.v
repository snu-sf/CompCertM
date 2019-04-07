Require Import EventsC.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Skeleton.
Require Import CoqlibC.
Require Import Simulation.
Require Import ModSem.

Set Implicit Arguments.



Lemma spread_dstar
      ms
      st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (STAR: Star ms st0 tr st1)
  :
    <<DSTAR: DStar ms st0 tr st1>>
.
Proof.
  ginduction STAR; ii; ss.
  { econs; eauto. }
  econs; eauto. eapply IHSTAR; eauto.
Qed.

Lemma spread_dplus
      ms
      st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (PLUS: Plus ms st0 tr st1)
  :
    <<DPLUS: DPlus ms st0 tr st1>>
.
Proof.
  inv PLUS. econs; eauto. eapply spread_dstar; eauto.
Qed.

Lemma at_external_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src)
  :
    <<RCP: receptive_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma at_external_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src)
  :
    <<RCP: determinate_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma final_frame_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src)
  :
    <<RCP: receptive_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma final_frame_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src)
  :
    <<RCP: determinate_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma step_atomic_step
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (STEP: Step ms st0 tr st1)
  :
    <<STEP: Step (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  exploit SINGLE; eauto. i.
  destruct tr; ss.
  - econs; eauto.
  - destruct tr; ss; try xomega. econs; eauto.
Qed.

Lemma star_atomic_star
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (STAR: Star ms st0 tr st1)
  :
    <<STAR: Star (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  ginduction STAR; ii; ss.
  - econs; eauto.
  - exploit IHSTAR; eauto. i. econs; eauto. eapply step_atomic_step; eauto.
Qed.

Lemma plus_atomic_plus
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (PLUS: Plus ms st0 tr st1)
  :
    <<PLUS: Plus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  inv PLUS.
  econs; eauto.
  { exploit step_atomic_step; eauto. }
  { eapply star_atomic_star; eauto. }
Qed.

Lemma determ_atomic_determ
      (ms: ModSem.t) st0
      (* (WBT: well_behaved_traces ms) *)
      (DTM: determinate_at ms st0)
  :
    <<DTM: forall tr, determinate_at (ModSem.Atomic.trans ms) (tr, st0)>>
.
Proof.
  ii. inv DTM. econs; eauto.
  - ii. ss. inv H; inv H0.
    + determ_tac sd_determ_at. esplits; eauto. i. exploit H0; eauto. i; des. clarify.
    + determ_tac sd_determ_at. inv H.
    + determ_tac sd_determ_at. inv H.
    + determ_tac sd_determ_at. esplits; eauto.
      { inv H; econs; eauto. }
      i; des. clarify.
      (* exploit WBT; eauto. i; des. ss. *)
      assert(tr = tr0).
      { inv H; ss. }
      clarify.
      exploit H0; eauto. i; des. clarify.
    + esplits; eauto. destruct ev; econs; eauto.
      THIS DOES NOT HODLR!!!!!!!!!!!!!!!!
      econs; eauto. determ_tac sd_determ_at. inv H.
    + determ_tac sd_determ_at. inv H.
    + determ_tac sd_determ_at. inv H.
Qed.

Lemma dstep_atomic_dstep
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (STEP: DStep ms st0 tr st1)
  :
    <<STEP: DStep (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  rr in STEP. des.
  exploit step_atomic_step; eauto. i.
  rr. esplits; eauto.
  exploit SINGLE; eauto. i.
  destruct tr; ss.
  - econs; eauto.
  - destruct tr; ss; try xomega. econs; eauto.
Qed.

Lemma star_atomic_star
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (STAR: Star ms st0 tr st1)
  :
    <<STAR: Star (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  ginduction STAR; ii; ss.
  - econs; eauto.
  - exploit IHSTAR; eauto. i. econs; eauto. eapply step_atomic_step; eauto.
Qed.

Lemma plus_atomic_plus
      (ms: ModSem.t) st0 tr st1
      (SINGLE: single_events ms)
      (PLUS: Plus ms st0 tr st1)
  :
    <<PLUS: Plus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>
.
Proof.
  inv PLUS.
  econs; eauto.
  { exploit step_atomic_step; eauto. }
  { eapply star_atomic_star; eauto. }
Qed.