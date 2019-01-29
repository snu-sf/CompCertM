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
Require Import SimMem.

Set Implicit Arguments.




Record t' := mk {
  src: mem;
  tgt: mem;
}.

Program Instance SimMemExt : SimMem.class :=
{
  t := t';
  src := src;
  tgt := tgt;
  wf := fun (rel: t') => Mem.extends rel.(src) rel.(tgt);
  le := fun (mrel0 mrel1: t') => True;
  lift := id;
  unlift := fun _ => id;
  sim_val := fun (_: t') => Val.lessdef;
  sim_val_list := fun (_: t') => Val.lessdef_list;
}.
Next Obligation.
  ss.
Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext1.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss.
    econs; eauto.
  - induction H; econs; eauto.
Qed.

Global Program Instance SimSymbExtends: SimSymb.class SimMemExt := {
  t := unit;
  le := SimSymbId.le;
  sim_sk := SimSymbId.sim_sk;
  sim_skenv (_: SimMem.t) (_: unit) := SimSymbId.sim_skenv;
}
.
Next Obligation.
  ss.
Qed.
Next Obligation.
  rr in SIMSK. clarify.
Qed.
Next Obligation.
  eapply SimSymbId.sim_sk_link; eauto.
Qed.
Next Obligation.
  rr in SIMSKE. clarify.
Qed.
Next Obligation.
  exploit SimSymbId.sim_sk_load_sim_skenv; eauto. i; des.
  eexists. eexists (mk _ _).
  esplits; ss; eauto.
  apply Mem.extends_refl.
Qed.
Next Obligation.
  eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto.
Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto.
  i; des.
  inv H. inv SIMSKENV.
  econs; eauto.
  - ii; ss.
    eapply FUNCFSIM; eauto.
    rpapply FUNCSRC. f_equal.
    inv SIMFPTR; ss.
  - ii; ss.
    eapply FUNCBSIM; eauto.
    rpapply FUNCTGT. f_equal.
    inv SIMFPTR; ss.
Qed.
Next Obligation.
  esplits; eauto.
  eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  inv ARGS; ss. destruct args_src, args_tgt; destruct sm0; ss; clarify.
  exploit external_call_mem_extends; eauto. i. des. 
  exists (mk retv_src.(Retv.m) m2'). exists (Retv.mk vres' m2').
  esplits; ss; eauto.
  eapply external_call_symbols_preserved; eauto.
  eapply SimSymbId.sim_skenv_equiv; eauto.
Qed.

