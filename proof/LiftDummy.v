Require Import FSets.
Require Import CoqlibC Maps Ordered Errors Lattice Kildall Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import sflib.


Section LIFTDUMMY.

Variable L: semantics.
Variable wf_tgt: L.(state) -> Prop.
Variable strong_wf_tgt: L.(state) -> Prop.
Hypothesis strong_wf_tgt_strong: strong_wf_tgt <1= wf_tgt.
Hypothesis strong_wf_tgt_spec:
  forall se ge n st0 st1 tr0 tr1 st2
  (STEP: step L se ge st0 tr0 st1)
  (STAR: starN (step L) se ge n st1 tr1 st2)
  (DUMMYTGT: strong_wf_tgt st0)
  (STKAFTER: wf_tgt st2)
  ,
    <<WF: strong_wf_tgt st1>>
.

Let wf_step (se: Senv.t) (ge: L.(genvtype)) (st0: L.(state)) (tr: trace) (st1: L.(state)) :=
  L.(step) se ge st0 tr st1 /\ wf_tgt st1
.

Lemma lift_starN
      cnt tse tge st_tgt0 tr st_tgt1
      (STAR: starN L.(step) tse tge cnt st_tgt0 tr st_tgt1)
      (DUMMYTGT: strong_wf_tgt st_tgt0)
      (STKAFTER: wf_tgt st_tgt1)
  :
    <<STAR: starN wf_step tse tge cnt st_tgt0 tr st_tgt1>>
.
Proof.
  induction STAR; ii; ss.
  { econs; et. }
  pose s as S1. pose s' as S2. pose s'' as S3.
  (* pose s1 as S1. pose s2 as S2. pose s3 as S3. *)
  econs; et.
  - econs; et. exploit strong_wf_tgt_spec; eauto.
  - des. exploit IHSTAR; et. exploit strong_wf_tgt_spec; eauto.
Qed.

Lemma lift_starN_stronger
      cnt tse tge st_tgt0 tr st_tgt1
      (STAR: starN L.(step) tse tge cnt st_tgt0 tr st_tgt1)
      (DUMMYTGT: strong_wf_tgt st_tgt0)
      (STKAFTER: wf_tgt st_tgt1)
  :
    <<STAR: starN wf_step tse tge cnt st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: strong_wf_tgt st_tgt1>>
.
Proof.
  induction STAR; ii; ss.
  { esplits; eauto. econs; et. }
  pose s as S1. pose s' as S2. pose s'' as S3.
  exploit strong_wf_tgt_spec; eauto. i; des.
  exploit IHSTAR; eauto. i; des.
  esplits; eauto. econs; eauto. rr. esplits; eauto.
Qed.

Lemma starN_plus_iff
      G ST (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se ge st0 tr st1
  :
    (exists n, starN step se ge n st0 tr st1 /\ (n > 0)%nat) <-> plus step se ge st0 tr st1
.
Proof.
  split; i; des.
  - destruct n; ss.
    { xomega. }
    ginduction H; ii; ss.
    { xomega. }
    clarify. inv H0.
    + eapply plus_star_trans; et.
      { apply plus_one; et. }
      { apply star_refl; et. }
    + eapply plus_trans; et.
      { apply plus_one; et. }
      eapply IHstarN; et. xomega.
  - inv H. apply star_starN in H1. des. exists (Datatypes.S n). esplits; et.
    { econs; et. }
    { xomega. }
Qed.

Lemma lift_plus
      tse tge st_tgt0 tr st_tgt1
      (PLUS: plus Linear.step tse tge st_tgt0 tr st_tgt1)
      (DUMMYTGT: wf_tgt st_tgt0)
      (STKAFTER: get_stack st_tgt1 <> [])
  :
    <<PLUS: plus step tse tge st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: wf_tgt st_tgt1>>
.
Proof.
  apply starN_plus_iff in PLUS. des. apply lift_starN_stronger in PLUS; et. des. esplits; et.
  apply starN_plus_iff; et.
Qed.


