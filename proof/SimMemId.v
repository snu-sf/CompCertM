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
Require Import Asmregs.
Require Import Integers.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require SimSymbId.
Require Import SimMem.

Set Implicit Arguments.




Record t' := mk {
  src_mem: mem;
  tgt_mem: mem;
}.

Program Instance SimMemId : SimMem.class :=
{
  t := t';
  src := src_mem;
  tgt := tgt_mem;
  wf := fun (rel: t') => rel.(src_mem) = rel.(tgt_mem);
  le := fun (mrel0 mrel1: t') => True;
  lift := id;
  unlift := fun _ => id;
  sim_val := fun (_: t') => eq;
  sim_val_list := fun (_: t') => eq;
}.
Next Obligation.
  ss.
Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss.
    erewrite IHx; eauto.
  - ginduction x0; ii; ss.
    econs; eauto.
Qed.
(* Next Obligation. *)
(*   eexists (mkrelation _ _). *)
(*   esplits; ss; eauto. *)
(*   inv WF. ss. *)
(*   clear_tac. *)
(*   assert(NOCOVER0: forall id, <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>). *)
(*   { i. eapply NOCOVER. eauto. } *)
(*   clear NOCOVER. *)
(*   clear_tac. *)
(*   econs; eauto. *)
(*   - admit "This should hold; Maybe ""Genv.init_mem_match"" and ""Genv.init_mem_genv_next"" might help". *)
(*   - admit "This should hold;". *)
(* Qed. *)

















Global Program Instance SimSymbId: SimSymb.class SimMemId := {
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
  eapply SimSymbId.sim_sk_link; eauto.
Qed.
Next Obligation.
  exploit SimSymbId.sim_sk_load_sim_skenv; eauto. i; des.
  eexists. eexists (mk _ _).
  esplits; ss; eauto.
Qed.
Next Obligation.
  eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto.
Qed.
Next Obligation.
  eapply SimSymbId.sim_skenv_func_bisim; eauto.
Qed.

