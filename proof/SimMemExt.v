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
  rename SAFESRC into _tr. rename H into _retv. rename H0 into SAFESRC.
  inv ARGS; ss. destruct args_src, args_tgt; destruct sm0; ss; clarify.
  exploit external_call_mem_extends; try apply SAFESRC; eauto. intro SYSTGT2ND; des.
  eapply external_call_symbols_preserved with (ge2 := skenv_sys_tgt) in SYSTGT2ND; cycle 1.
  { eapply SimSymbId.sim_skenv_equiv; eauto. }
  exploit external_call_receptive; try eapply SAFESRC; et.
  { instantiate (1:= tr).
    eapply match_traces_preserved with (ge1 := skenv_sys_tgt).
    { i. symmetry. eapply SimSymbId.sim_skenv_equiv; eauto. }
    eapply external_call_determ; et.
  }
  intro SYSSRC2ND; des.
  exploit external_call_mem_extends; try apply SYSSRC2ND; eauto. intro SYSTGT3RD; des.
  eapply external_call_symbols_preserved with (ge2 := skenv_sys_tgt) in SYSTGT3RD; cycle 1.
  { eapply SimSymbId.sim_skenv_equiv; eauto. }
  exploit external_call_determ; [apply SYSTGT|apply SYSTGT3RD|..]. i; des.
  specialize (H0 eq_refl). des. clarify.
  eexists (mk _ _), (Retv.mk _ _). ss.
  esplits; try apply SYSSRC2ND; et.
  econs; ss; et.
Qed.
Next Obligation.
  rename SAFESRC into _tr. rename H into _retv. rename H0 into SAFESRC.
  inv ARGS; ss. destruct args_src, args_tgt; destruct sm0; ss; clarify.
  exploit external_call_mem_extends; et. i; des. eexists (Retv.mk _ _), _. s. esplits; et.
  eapply external_call_symbols_preserved with (ge2 := skenv_sys_tgt); et.
  { eapply SimSymbId.sim_skenv_equiv; eauto. }
Qed.

