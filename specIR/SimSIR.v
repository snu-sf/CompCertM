From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require Export SIRCommon2.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.



Local Obligation Tactic := ii; ss; eauto.

Section OWNEDHEAP.

Context `{SimMem.class}.

Variable mi: string.
Variable owned_heap0 owned_heap1: Type.
Variable OR: owned_heap0 -> owned_heap1 -> Prop.

Let ktr0 := function owned_heap0.
Let ktr1 := function owned_heap1.
Let itr0 := itree (E owned_heap0) (owned_heap0 * (mem * val)).
Let itr1 := itree (E owned_heap1) (owned_heap1 * (mem * val)).

Inductive sim_itr (sim_itr: itr0 -> itr1 -> Prop): itr0 -> itr1 -> Prop :=
.

(* Definition sim_ktr (k0: ktr0) (k1: ktr1): Prop := forall *)
(*     oh0 oh1 m0 m1 vs0 vs1 *)
(*     (SIMMEM: ) *)
(*     . *)


Record t := mk {
  sm:> SimMem.t;
  oh_src: owned_heap0;
  oh_tgt: owned_heap1;
}
.

Let wf (sm0:t): Prop := (SimMem.wf sm0) /\ (OR sm0.(oh_src) sm0.(oh_tgt)).
Let set_sm (smo0:t) (sm0:SimMem.t): t := mk sm0 smo0.(oh_src) smo0.(oh_tgt).

Program Definition SMO: (SimMemOh.class) :=
  {|
    SimMemOh.t := t;
    SimMemOh.sm := sm;
    SimMemOh.oh_src := fun sm0 => upcast (sm0.(oh_src));
    SimMemOh.oh_tgt := fun sm0 => upcast (sm0.(oh_tgt));
    SimMemOh.wf := wf;
    SimMemOh.le := SimMem.le;
    SimMemOh.lepriv := SimMem.lepriv;
    SimMemOh.set_sm := set_sm;
    SimMemOh.midx := (Some mi);
  |}
.
Next Obligation.
  econs; ii.
  - refl.
  - etrans; et.
Qed.
Next Obligation.
  econs; ii.
  - refl.
  - etrans; et.
Qed.
Next Obligation.
  rr in PR. des; ss.
Qed.
Next Obligation.
  rr in WF. des. rr. ss.
Qed.
Next Obligation.
  destruct smo0; ss.
Qed.



End OWNEDHEAP.

