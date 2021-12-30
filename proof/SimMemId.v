Require Import CoqlibC.
From compcertr Require Import
     Memory
     Values
     Maps
     Events
     Globalenvs
     sflib.
Require Import RelationClasses.
Require Import FSets.
From compcertr Require Import
     Ordered
     AST
     Integers.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require SimSymbId.
Require Import SimMemLift.

Set Implicit Arguments.




Record t' := mk {
  src: mem;
  tgt: mem;
}.

Program Instance SimMemId : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  wf := fun (rel: t') => rel.(src) = rel.(tgt);
  le := fun (mrel0 mrel1: t') => True;
  lepriv := top2;
  sim_val := fun (_: t') => eq;
  sim_val_list := fun (_: t') => eq;
}.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i). apply prop_ext1. split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. erewrite IHx; eauto.
  - ginduction x1; ii; ss. econs; eauto.
Qed.





Program Instance SimMemIdLift: SimMemLift.class SimMemId :=
{ lift := id;
  unlift := fun _ => id;
}.











Global Program Instance SimSymbId: SimSymb.class SimMemId := {
  t := SimSymbId.t';
  src := SimSymbId.src;
  tgt := SimSymbId.tgt;
  le := SimSymbId.le;
  wf := SimSymbId.wf;
  sim_skenv (_: SimMem.t) (_: SimSymbId.t') := SimSymbId.sim_skenv;
}.
Next Obligation. rr in SIMSK. r. congruence. Qed.
Next Obligation. eapply SimSymbId.wf_link; eauto. Qed.
Next Obligation. rr in SIMSKE. clarify. Qed.
Next Obligation.
  exploit SimSymbId.wf_load_sim_skenv; eauto. i; des.
  eexists. eexists (mk _ _). esplits; ss; eauto.
Qed.
Next Obligation. eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. Qed.
Next Obligation. eapply SimSymbId.sim_skenv_func_bisim; eauto. Qed.
Next Obligation. esplits; eauto. eapply SimSymbId.system_sim_skenv; eauto. Qed.
Next Obligation.
  inv ARGS; ss. clarify. destruct sm0; ss. clarify.
  destruct retv_src; ss.
  esplits; eauto.
  - eapply external_call_symbols_preserved; eauto.
    { eapply SimSymbId.sim_skenv_equiv; eauto. }
    instantiate (1:= Retv.mk _ _). ss. eauto.
  - instantiate (1:= mk _ _). econs; ss; eauto.
  - ss.
Qed.
