Require Import FSets.
Require Import CoqlibC.
From compcertr Require Import
     Maps
     Ordered
     Errors
     Lattice
     Kildall
     Integers
     AST
     Linking
     Values
     Memory
     Events
     Globalenvs
     sflib.
Require Import SmallstepC.



Section LIFTDUMMY.

Context {G ST: Type}.
Variable step: Senv.t -> G -> ST -> trace -> ST -> Prop.
Variable wf_tgt: ST -> Prop.
Variable strong_wf_tgt: ST -> Prop.
Hypothesis strong_wf_tgt_strong: strong_wf_tgt <1= wf_tgt.
(* Note: I added an arbitrary "H" alphabet to avoid name collision *)
Hypothesis strong_wf_tgt_spec: forall se ge st0 st1 tr0
    (HSWF: strong_wf_tgt st0)
    (HSTEP: step se ge st0 tr0 st1),
    <<HSWF: strong_wf_tgt st1>> \/ <<STUCK: forall tr1 st2 (HSTEP0: step se ge st1 tr1 st2), False>>.
Hypothesis wf_tgt_strengthen: forall se ge st0 tr st1
    (HWF0: strong_wf_tgt st0)
    (HSTEP: step se ge st0 tr st1)
    (HWF1: wf_tgt st1),
    <<WFTGT1: strong_wf_tgt st1>>.

Let strong_wf_tgt_spec_starN: forall se ge n st0 st1 tr0 tr1 st2
    (STEP: step se ge st0 tr0 st1)
    (STAR: starN (step) se ge n st1 tr1 st2)
    (DUMMYTGT: strong_wf_tgt st0)
    (STKAFTER: wf_tgt st2) ,
    <<WF: strong_wf_tgt st1>>.
Proof.
  ii. exploit strong_wf_tgt_spec; eauto. intro P. destruct n; ss.
  { inv STAR. des; ss. eapply wf_tgt_strengthen; eauto. }
  des; ss. exfalso. inv STAR. eapply STUCK; eauto.
Qed.

Let wf_step (se: Senv.t) (ge: G) (st0: ST) (tr: trace) (st1: ST) :=
  step se ge st0 tr st1 /\ wf_tgt st1.

Lemma lift_starN
      cnt tse tge st_tgt0 tr st_tgt1
      (STAR: starN step tse tge cnt st_tgt0 tr st_tgt1)
      (DUMMYTGT: strong_wf_tgt st_tgt0)
      (STKAFTER: wf_tgt st_tgt1):
    <<STAR: starN wf_step tse tge cnt st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: strong_wf_tgt st_tgt1>>.
Proof.
  induction STAR; ii; ss.
  { esplits; eauto. econs; et. }
  pose s as S1. pose s' as S2. pose s'' as S3.
  exploit strong_wf_tgt_spec_starN; eauto. i; des.
  exploit IHSTAR; eauto. i; des.
  esplits; eauto. econs; eauto. rr. esplits; eauto.
Qed.

Lemma lift_plus
      se ge st_tgt0 tr st_tgt1
      (PLUS: plus step se ge st_tgt0 tr st_tgt1)
      (DUMMYTGT: strong_wf_tgt st_tgt0)
      (STKAFTER: wf_tgt st_tgt1):
    <<PLUS: plus wf_step se ge st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: strong_wf_tgt st_tgt1>>.
Proof.
  apply starN_plus_iff in PLUS. des. apply lift_starN in PLUS; et. des. esplits; et. apply starN_plus_iff; et.
Qed.

End LIFTDUMMY.
