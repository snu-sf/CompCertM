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
Require SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon2 SIRmini.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.



Local Obligation Tactic := ii; ss; eauto.

Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap0 owned_heap1: Type.
Variable SO: owned_heap0 -> owned_heap1 -> Prop.
Variable SM: mem -> mem -> Prop.
Variable SV: val -> val -> Prop.
Hypothesis (SVINT: forall v_src v_tgt i, v_src = Vint i -> SV v_src v_tgt -> v_tgt = Vint i).


Let ktr0 := function owned_heap0.
Let ktr1 := function owned_heap1.
Let itr0 := itree (E owned_heap0) (owned_heap0 * (mem * val)).
Let itr1 := itree (E owned_heap1) (owned_heap1 * (mem * val)).

(**************** TODO: eqit is defined in terms of "itree'", not "itree" *****************)


(* Variable fname: ident. *)
(* Variable oh0: owned_heap0. *)
(* Variable m0: mem. *)
(* Variable vs0: list val. *)
(* Check (ICall fname oh0 m0 vs0). *)
(* Variable k0: ((owned_heap0 * (mem * val)) -> itr0). *)
(* Check (Vis (subevent _ (ICall fname oh0 m0 vs0)) k0). *)


Inductive _sim_itr (sim_itr: itr0 -> itr1 -> Prop): itr0 -> itr1 -> Prop :=
| sim_ret
    oh0 m0 v0
    oh1 m1 v1
  :
    _sim_itr sim_itr (Ret (oh0, (m0, v0))) (Ret (oh1, (m1, v1)))
| sim_tau
    i0
    i1
    (SIM: sim_itr i0 i1)
  :
    _sim_itr sim_itr (Tau i0) (Tau i1)
| sim_icall
    fname
    oh0 m0 vs0 k0
    oh1 m1 vs1 k1
    (SIM: forall
        ohr0 mr0 vr0
        ohr1 mr1 vr1
      ,
        sim_itr (k0 (ohr0, (mr0, vr0))) (k1 (ohr1, (mr1, vr1))))
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ICall fname oh0 m0 vs0)) k0)
             (Vis (subevent _ (ICall fname oh1 m1 vs1)) k1)
| sim_ecall
    sg
    fptr0 oh0 m0 vs0 k0
    fptr1 oh1 m1 vs1 k1
    (SIM: forall
        ohr0 mr0 vr0
        ohr1 mr1 vr1
      ,
        sim_itr (k0 (ohr0, (mr0, vr0))) (k1 (ohr1, (mr1, vr1))))
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ECall sg fptr0 oh0 m0 vs0)) k0)
             (Vis (subevent _ (ECall sg fptr1 oh1 m1 vs1)) k1)
| sim_nb
    i0 k1
  :
    _sim_itr sim_itr i0 (Vis (subevent _ (ENB)) k1)
| sim_ub
    k0 i1
  :
    _sim_itr sim_itr (Vis (subevent _ (ENB)) k0) i1
(* | sim_choose_both *)
(*     X0 X1 *)
(*     k0 k1 *)
(*     (SIM: forall x1, exists x0, sim_itr (k0 x0) (k1 x1)) *)
(*   : *)
(*     _sim_itr sim_itr *)
(*              (Vis (subevent _ (EChoose X0)) k0) *)
(*              (Vis (subevent _ (EChoose X1)) k1) *)
| sim_choose_src
    X0
    k0 i1
    (SIM: exists x0, sim_itr (k0 x0) i1)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (EChoose X0)) k0)
             (Tau i1)
| sim_choose_tgt
    X1
    k1 i0
    (SIM: forall x1, sim_itr i0 (k1 x1))
  :
    _sim_itr sim_itr
             (Tau i0)
             (Vis (subevent _ (EChoose X1)) k1)
.

Definition sim_itr: itr0 -> itr1 -> Prop := paco2 _sim_itr bot2.

Lemma sim_itr_mon: monotone2 _sim_itr.
Proof.
  ii. inv IN; try econs; et.
  des. esplits; et.
Unshelve.
Qed.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.

Definition sim_ktr (k0: ktr0) (k1: ktr1): Prop := forall
    oh0 oh1 m0 m1 vs0 vs1
    (O: SO oh0 oh1)
    (M: SM m0 m1)
    (V: Forall2 SV vs0 vs1)
  ,
    sim_itr (k0 oh0 m0 vs0) (k1 oh1 m1 vs1)
.




(*** Lifting to SimModSem ***)

Record t' := mk' {
  src: mem;
  tgt: mem;
}.

Program Instance SimMem: (SimMem.class) :=
{ t := t';
  src := src;
  tgt := tgt;
  ptt_src := fun _ _ _ => etc;
  ptt_tgt := fun _ _ _ => etc;
  wf := fun (sm0: t') => SM sm0.(src) sm0.(tgt);
  le := top2;
  lepriv := top2;
  sim_val := fun _ => SV;
  sim_val_list := fun _ => Forall2 SV;
  unchanged_on := top3;
}
.

Record t := mk {
  sm:> SimMem.t;
  oh_src: owned_heap0;
  oh_tgt: owned_heap1;
}
.

Let wf (sm0:t): Prop := (SimMem.wf sm0) /\ (SO sm0.(oh_src) sm0.(oh_tgt)).
Let set_sm (smo0:t) (sm0:SimMem.t): t := mk sm0 smo0.(oh_src) smo0.(oh_tgt).

Program Instance SimMemOh: (SimMemOh.class) :=
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
  rr in PR. des; ss.
Qed.
Next Obligation.
  rr in WF. des. rr. ss.
Qed.
Next Obligation.
  destruct smo0; ss.
Qed.

Program Instance SimSymbId: SimSymb.class SimMem := {
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
  eexists. eexists (mk' _ _). esplits; ss; eauto.
  - admit "".
  - rr in SIMSK. rewrite SIMSK in *. clarify. admit "".
Qed.
Next Obligation. eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. Qed.
Next Obligation. rr. eapply SimSymbId.sim_skenv_func_bisim; eauto. Qed.
Next Obligation. esplits; eauto. eapply SimSymbId.system_sim_skenv; eauto. Qed.
Next Obligation.
  inv ARGS; ss. clarify. destruct sm0; ss. clarify.
  destruct retv_src; ss.
  esplits; eauto.
  - eapply external_call_symbols_preserved; eauto.
    { eapply SimSymbId.sim_skenv_equiv; eauto. }
    instantiate (1:= Retv.mk _ _). ss. eauto.
  - instantiate (1:= mk _ _). econs; ss; eauto.
  - econs; ii; ss.
Qed.



Definition sim_prog (p0: program owned_heap0) (p1: program owned_heap1): Prop :=
  forall fname, <<SIM: option_rel sim_ktr (p0 fname) (p1 fname)>>
.

Theorem sim_mod
        p0 p1
        ioh0 ioh1
        (SIMP: sim_prog p0 p1)
        (SIMO: forall skenv, SO (ioh0 skenv) (ioh1 skenv))
  :
    forall sk mi,
      ModPair.sim
        (SimSymbId.mk_mp (SIRmini.module sk p0 mi ioh0) (SIRmini.module sk p0 mi ioh1))
.
End OWNEDHEAP.













(*** Relating with SimMem Id ***)

Program Definition boo := SimMem eq eq _.
Next Obligation.
  subst. ss.
Qed.

Require Import SimMemId.
Lemma SimMem_eta
      (smc0 smc1: SimMem.class)
      (EQ0: smc0.(@SimMem.t) = smc1.(@SimMem.t))
      (EQ1: smc0.(@SimMem.src) ~= smc1.(@SimMem.src))
      (EQ2: smc0.(@SimMem.ptt_src) ~= smc1.(@SimMem.ptt_src))
      (EQ3: smc0.(@SimMem.tgt) ~= smc1.(@SimMem.tgt))
      (EQ4: smc0.(@SimMem.ptt_tgt) ~= smc1.(@SimMem.ptt_tgt))
      (EQ5: smc0.(@SimMem.wf) ~= smc1.(@SimMem.wf))
      (EQ6: smc0.(@SimMem.le) ~= smc1.(@SimMem.le))
      (EQ7: smc0.(@SimMem.lepriv) ~= smc1.(@SimMem.lepriv))
      (EQ8: smc0.(@SimMem.sim_val) ~= smc1.(@SimMem.sim_val))
      (EQ9: smc0.(@SimMem.sim_val_list) ~= smc1.(@SimMem.sim_val_list))
      (EQ10: smc0.(@SimMem.unchanged_on) ~= smc1.(@SimMem.unchanged_on))
  :
    smc0 = smc1
.
Proof.
  destruct smc0, smc1; ss.
  clarify.
  apply_all_once JMeq_eq. clarify.
  f_equal; try eapply Axioms.proof_irr.
Qed.

Goal boo = SimMemId.
Proof.
  eapply SimMem_eta; ss.
Abort.
  
(*** Maybe we should define common ancestor, and let SimMemId // SimSIR use the same thing. ***)
