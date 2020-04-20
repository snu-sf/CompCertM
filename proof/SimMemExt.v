Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require SimSymbId.
Require Import SimMemLift.

Set Implicit Arguments.




Record t' := mk {
  src: mem;
  tgt: mem;
}.

Program Instance SimMemExt : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  ptt_src := fun _ _ _ => etc;
  ptt_tgt := fun _ _ _ => etc;
  wf := fun (rel: t') => Mem.extends rel.(src) rel.(tgt);
  le := fun (mrel0 mrel1: t') => True;
  lepriv := top2;
  sim_val := fun (_: t') => Val.lessdef;
  sim_val_list := fun (_: t') => Val.lessdef_list;
  unchanged_on := top3;
}.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext1.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. econs; eauto.
  - induction H; econs; eauto.
Qed.
Next Obligation. inv H. ss. Qed.


Program Instance SimMemExtLift: SimMemLift.class SimMemExt :=
{ lift := id;
  unlift := fun _ => id;
}.

Global Program Instance SimSymbExtends: SimSymb.class SimMemExt := {
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
  - apply Mem.extends_refl.
  - rewrite MAINSIM. ss.
Qed.
Next Obligation. eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto. i; des.
  inv H. inv SIMSKENV. econs; eauto.
  ii; ss. eapply FUNCFSIM; eauto. rpapply FUNCSRC. f_equal. inv SIMFPTR; ss.
Qed.
Next Obligation. esplits; eauto. eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  inv ARGS; ss. destruct sm0; ss; clarify.
  exploit external_call_mem_extends; eauto. i. des.
  exists (mk (Retv.m retv_src) m2'). exists (Retv.mk vres' m2').
  esplits; ss; eauto.
  { eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. }
  { destruct retv_src; ss. econs; ss; eauto. }
  { econs; ii; ss. }
Qed.
