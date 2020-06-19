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
      ms st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (STAR: Star ms st0 tr st1):
    <<DSTAR: DStar ms st0 tr st1>>.
Proof. ginduction STAR; ii; ss; econs; eauto. eapply IHSTAR; eauto. Qed.

Lemma spread_dplus
      ms st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (PLUS: Plus ms st0 tr st1):
    <<DPLUS: DPlus ms st0 tr st1>>.
Proof. inv PLUS. econs; eauto. eapply spread_dstar; eauto. Qed.

Lemma at_external_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src):
    <<RCP: receptive_at ms_src lst_src>>.
Proof. econs; ii; ModSem.tac. Qed.

Lemma at_external_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src):
    <<RCP: determinate_at ms_src lst_src>>.
Proof. econs; ii; ModSem.tac. Qed.

Lemma final_frame_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src):
    <<RCP: receptive_at ms_src lst_src>>.
Proof. econs; ii; ModSem.tac. Qed.

Lemma final_frame_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src):
    <<RCP: determinate_at ms_src lst_src>>.
Proof. econs; ii; ModSem.tac. Qed.

Lemma atomic_step_continue_star
    (ms: ModSem.t) st0 tr
    (WBT: output_trace tr):
    <<STEP: Star (ModSem.Atomic.trans ms) (tr, st0) tr ([], st0)>>.
Proof.
  i. ginduction tr; ii; ss; econs; eauto.
  { econs; eauto. }
  { eapply IHtr; eauto. des; ss. }
  ss.
Qed.

Lemma step_atomic_step
      (ms: ModSem.t) st0 tr st1
      (WBT: well_behaved_traces ms)
      (STEP: Step ms st0 tr st1):
    <<STEP: Plus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  destruct tr.
  { apply plus_one. econs; eauto. }
  s. econs; eauto; swap 2 3.
  { econs 2; eauto. }
  { ss. }
  exploit WBT; eauto. i; ss. hexploit atomic_step_continue_star; eauto. ss. eauto.
Qed.

Lemma star_atomic_star
      (ms: ModSem.t) st0 tr st1
      (WBT: well_behaved_traces ms)
      (STAR: Star ms st0 tr st1):
    <<STAR: Star (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  ginduction STAR; ii.
  - econs; eauto.
  - clarify. eapply star_trans.
    { exploit step_atomic_step; eauto. i. eapply plus_star; eauto. }
    { exploit IHSTAR; eauto. }
    ss.
Qed.

Lemma plus_atomic_plus
      (ms: ModSem.t) st0 tr st1
      (WBT: well_behaved_traces ms)
      (PLUS: Plus ms st0 tr st1):
    <<PLUS: Plus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  inv PLUS. eapply plus_star_trans.
  { exploit step_atomic_step; eauto. }
  { eapply star_atomic_star; eauto. }
  ss.
Qed.

Lemma determ_atomic_determ
      (ms: ModSem.t) st0 tr
      (* (WBT: well_behaved_traces ms) *)
      (DTM: determinate_at ms st0)
      (TR_INTACT: trace_intact tr)
      (WBT: output_trace tr):
    <<DTM: determinate_at (ModSem.Atomic.trans ms) (tr, st0)>>.
Proof.
  ii. inv DTM. econs; eauto; ii; ss; inv H; ss; try xomega; inv H0.
  - determ_tac sd_determ_at. esplits; eauto. i. exploit H0; eauto. i; des. clarify.
  - determ_tac sd_determ_at. inv H.
  - determ_tac sd_determ_at. inv H.
  - determ_tac sd_determ_at. esplits; eauto.
    { inv H; econs; eauto. }
    i; des. clarify. exploit H0; inv H; i; des; clarify; eauto.
  - esplits; eauto. ss. des.
    destruct ev; ss.
    + rr in TR_INTACT. ss.
      exfalso. eauto.
    + econs; eauto.
    + econs; eauto.
Qed.





Lemma output_trace_determinate_at
      (ms: ModSem.t)
      ev tr st0
      (EV_NOT_PTERM: ev <> Event_pterm)
      (WBT: output_event ev):
    determinate_at (ModSem.Atomic.trans ms) (ev :: tr, st0).
Proof.
  econs; eauto; ii; ss; inv H; ss; try xomega. inv H0. split; ss. destruct ev; ss; econs; eauto.
Qed.

Lemma atomic_dstep_continue_dstar
    (ms: ModSem.t) st0 tr
    (TR_INTACT: trace_intact tr)
    (WBT: output_trace tr):
    <<STEP: DStar (ModSem.Atomic.trans ms) (tr, st0) tr ([], st0)>>.
Proof.
  i. ginduction tr; ii; ss.
  { econs; eauto. }
  (* exploit determ_atomic_determ; eauto. *)
  (* { instantiate (1:= []). ss. } *)
  (* intro DTM0; des. *)
  rr in TR_INTACT.
  econs; eauto.
  { rr. des. esplits; eauto.
    - eapply output_trace_determinate_at; eauto.
      ss. eauto.
    - econs; eauto. ss.
  }
  { eapply IHtr; eauto.
    - ii. ss. eauto.
    - des; ss. }
  ss.
Qed.

Lemma DStep_trace_intact
      (ms: ModSem.t) st0 tr st1
      (STEP: DStep ms st0 tr st1):
  <<TR_INTACT: trace_intact tr>>.
Proof.
  rr in STEP. destruct STEP as [DET STEP].
  inv DET. ii.
  rr in  sd_traces_at. hexploit sd_traces_at; eauto. i.

  cut (tr = [Event_pterm]).
  { i. subst.
    hexploit sd_determ_at; et.
    clear. intro MATCH. inv MATCH.
    rename H into MATCH_TRACES.
    inv MATCH_TRACES. }

  destruct tr; ss.
  destruct tr; ss.
  { des; subst; ss. }
  { nia. }
Qed.

Lemma dstep_atomic_dstep
      (ms: ModSem.t) st0 tr st1
      (* (SINGLE: single_events ms) *)
      (WBT: well_behaved_traces ms)
      (STEP: DStep ms st0 tr st1):
    <<STEP: DPlus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  rr in STEP. des.
  exploit determ_atomic_determ; eauto.
  { instantiate (1:= []). ss. }
  { ss. }

  hexploit DStep_trace_intact.
  { econs; eauto. }
  intro TR_INTACT.
  intro DTM; des. destruct tr.
  { apply plus_one. econs; eauto. econs; eauto. }
  s. econs; eauto; swap 2 3.
  { rr. split; ss. instantiate (1:= (_, _)). econs 2; eauto. }
  { ss. }
  eapply atomic_dstep_continue_dstar; eauto.
  - rr in TR_INTACT. ss. ii. eauto.
  - exploit WBT; eauto.
Qed.

Lemma dstar_atomic_dstar
      (ms: ModSem.t) st0 tr st1
      (* (SINGLE: single_events ms) *)
      (WBT: well_behaved_traces ms)
      (STAR: DStar ms st0 tr st1):
    <<STAR: DStar (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  ginduction STAR; ii; ss.
  - econs; eauto.
  - exploit IHSTAR; eauto. i. eapply star_trans; eauto. apply plus_star. exploit dstep_atomic_dstep; eauto.
Qed.

Lemma dplus_atomic_dplus
      (ms: ModSem.t) st0 tr st1
      (* (SINGLE: single_events ms) *)
      (WBT: well_behaved_traces ms)
      (PLUS: DPlus ms st0 tr st1):
    <<PLUS: DPlus (ModSem.Atomic.trans ms) ([], st0) tr ([], st1)>>.
Proof.
  inv PLUS. eapply plus_star_trans.
  { exploit dstep_atomic_dstep; eauto. }
  { eapply dstar_atomic_dstar; eauto. }
  ss.
Qed.

Lemma atomic_single_events_at: forall (ms: ModSem.t),
    <<SINGLE: forall st, single_events_at (ModSem.Atomic.trans ms) st>>.
Proof. ii. inv H; ss. xomega. Qed.

Lemma atomic_single_evnents: forall (ms: ModSem.t),
    <<SINGLE: single_events (ModSem.Atomic.trans ms)>>.
Proof. ii. inv H; ss. xomega. Qed.

Lemma atomic_receptive_at
      (ms: ModSem.t) st0
      (SSR: strongly_receptive_at ms st0):
    <<RCP: forall tr, receptive_at (ModSem.Atomic.trans ms) (tr, st0)>>.
Proof.
  generalize (@atomic_single_evnents ms); eauto. intro SINGLE.
  inv SSR. econs; ss.
  { ii. ss. destruct t1; ss.
    { inv H. inv H0. esplits; eauto. econs; eauto. }
    exploit SINGLE; eauto. intro LEN. ss. destruct t1; ss; try xomega. destruct t2; ss.
    { inv H0. }
    destruct t2; ss; cycle 1.
    { inv H0. }
    inv H; ss.
    - exploit ssr_receptive_at; eauto. i; des. esplits; eauto. econs; eauto.
    - esplits; eauto. instantiate (1:= (_, _)).
      assert(e0 = e) by (des; inv H0; ss). clarify. econs 3; eauto.
  }
  eapply atomic_single_events_at; eauto.
Qed.

Lemma atomic_receptive_at_nonnil: forall (ms: ModSem.t),
    <<RCP: forall st0 ev tr, receptive_at (ModSem.Atomic.trans ms) (ev :: tr, st0)>>.
Proof.
  i. generalize (@atomic_single_evnents ms); eauto. intro SINGLE. ii. econs; ss.
  { ii. ss. destruct t1; ss.
    { inv H. }
    exploit SINGLE; eauto. intro LEN. ss. destruct t1; ss; try xomega. destruct t2; ss.
    { inv H0. }
    destruct t2; ss; cycle 1.
    { inv H0. }
    inv H; ss. des. assert(e = e0). { inv H0; ss. } clarify.
    esplits; eauto. econs; eauto. ss.
  }
  eapply atomic_single_events_at; eauto.
Qed.

Lemma atomic_receptive
      (ms: ModSem.t)
      (SSR: strongly_receptive ms):
    <<RCP: receptive (ModSem.Atomic.trans ms)>>.
Proof.
  generalize (@atomic_single_evnents ms); eauto. intro SINGLE.
  inv SSR. econs; ss.
  { ii. ss. destruct t1; ss.
    { inv H. inv H0. esplits; eauto. econs; eauto. }
    exploit SINGLE; eauto. intro LEN. ss. destruct t1; ss; try xomega.
    destruct t2; ss.
    { inv H0. }
    destruct t2; ss; cycle 1.
    { inv H0. }
    inv H; ss.
    - exploit ssr_receptive; eauto. i; des. esplits; eauto. econs; eauto.
    - esplits; eauto. instantiate (1:= (_, _)).
      assert(e0 = e) by (des; inv H0; ss). clarify. econs 3; eauto.
  }
Qed.

Lemma DStep_Step
      L st0 tr st1
      (STEP: DStep L st0 tr st1):
    <<STEP: Step L st0 tr st1>>.
Proof. rr in STEP. des. ss. Qed.

Lemma DStar_Star
      L st0 tr st1
      (STAR: DStar L st0 tr st1):
    <<STAR: Star L st0 tr st1>>.
Proof.
  ginduction STAR; ii; ss.
  { eapply star_refl. }
  clarify. eapply star_trans; eauto. eapply star_one. eapply DStep_Step; eauto.
Qed.

Lemma DPlus_Plus
      L st0 tr st1
      (PLUS: DPlus L st0 tr st1):
    <<PLUS: Plus L st0 tr st1>>.
Proof.
  inv PLUS.
  econs; eauto.
  { eapply DStep_Step; eauto. }
  { eapply DStar_Star; eauto. }
Qed.

Definition safe_modsem (ms: ModSem.t) (st0: ms.(ModSem.state)): Prop :=
  forall st1 (STAR: Star ms st0 E0 st1),
    (<<EVCALL: ms.(ModSem.is_call) st1>>) \/
    (<<EVRET: ms.(ModSem.is_return) st1>>) \/
    (<<EVSTEP: exists tr st2, Step ms st1 tr st2>>).
Hint Unfold safe_modsem.
