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
Require SimMemId SimSymbId SoundTop.
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
    oh0 oh1 m v
  :
    _sim_itr sim_itr (Ret (oh0, (m, v))) (Ret (oh1, (m, v)))
| sim_tau
    i0
    i1
    (SIM: sim_itr i0 i1)
  :
    _sim_itr sim_itr (Tau i0) (Tau i1)
| sim_icall
    fname m vs
    oh0 k0
    oh1 k1
    (SIM: forall
        mr vr
        ohr0
        ohr1
      ,
        sim_itr (k0 (ohr0, (mr, vr))) (k1 (ohr1, (mr, vr))))
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ICall fname oh0 m vs)) k0)
             (Vis (subevent _ (ICall fname oh1 m vs)) k1)
| sim_ecall
    sg m vs
    fptr0 oh0 k0
    fptr1 oh1 k1
    (SIM: forall
        mr vr
        ohr0 ohr1
      ,
        sim_itr (k0 (ohr0, (mr, vr))) (k1 (ohr1, (mr, vr))))
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ECall sg fptr0 oh0 m vs)) k0)
             (Vis (subevent _ (ECall sg fptr1 oh1 m vs)) k1)
| sim_nb
    i0 k1
  :
    _sim_itr sim_itr i0 (Vis (subevent _ (ENB)) k1)
| sim_ub
    k0 i1
  :
    _sim_itr sim_itr (Vis (subevent _ (ENB)) k0) i1
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
    m vs
    oh0 oh1
    (O: SO oh0 oh1)
  ,
    <<SIM: sim_itr (k0 oh0 m vs) (k1 oh1 m vs)>>
.




(*** Lifting to SimModSem ***)

Definition sim_prog (p0: program owned_heap0) (p1: program owned_heap1): Prop :=
  forall fname, <<SIM: option_rel sim_ktr (p0 fname) (p1 fname)>>
.



Section SMO.

  Record t: Type :=
    mk {
      sm :> SimMem.t;
      oh_src: Any;
      oh_tgt: Any;
    }
  .

  Inductive wf (smo: t): Prop :=
  | wf_intro
      (oh0: owned_heap0) (oh1: owned_heap1)
      (MWF: SimMem.wf smo)
      (OHSRC: smo.(oh_src) = upcast oh0)
      (OHTGT: smo.(oh_tgt) = upcast oh1)
  .

  Local Obligation Tactic := try (by ii; des; ss).

  Program Instance SimMemOh: (SimMemOh.class) :=
    {|
      SimMemOh.t := t;
      SimMemOh.sm := sm;
      SimMemOh.oh_src := oh_src;
      SimMemOh.oh_tgt := oh_tgt;
      SimMemOh.wf := wf;
      SimMemOh.le := SimMem.le;
      SimMemOh.lepriv := SimMem.lepriv;
      SimMemOh.midx := Some mi;
      SimMemOh.set_sm := fun smo sm => mk sm smo.(oh_src) smo.(oh_tgt);
    |}
  .
  Next Obligation.
    ii. eapply PR.
  Qed.
  Next Obligation.
    ii. inv WF.
    econs; ss; et.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.



Variable p0: program owned_heap0.
Variable p1: program owned_heap1.
Variable ioh0: SkEnv.t -> owned_heap0.
Variable ioh1: SkEnv.t -> owned_heap1.
Hypothesis (SIMP: sim_prog p0 p1).
Hypothesis (SIMO: forall skenv, SO (ioh0 skenv) (ioh1 skenv)).
Variable sk: Sk.t.
Let md_src: Mod.t := (SIRmini.module sk p0 mi ioh0).
Let md_tgt: Mod.t := (SIRmini.module sk p1 mi ioh1).



Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let ms_src: ModSem.t := (Mod.modsem md_src skenv_link).
Let ms_tgt: ModSem.t := (Mod.modsem md_tgt skenv_link).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).

Local Existing Instance SimMemOh.
Local Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].

Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link)
                                              (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states (idx: nat): SIRmini.state owned_heap0 ->
                                   SIRmini.state owned_heap1 -> SimMemOh.t -> Prop :=
| match_states_intro
    st0 st1 smo0
    fid m vs oh0 oh1
    (O: SO oh0 oh1)
    (ST0: st0 = (interp_program0 p0 (ICall fid oh0 m vs)))
    (ST1: st1 = (interp_program0 p1 (ICall fid oh1 m vs)))
    (MWF: SimMemOh.wf smo0)
  :
    match_states idx st0 st1 smo0
.

(*** TODO: move to SIRCommon2 ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; et.
Qed.

Lemma match_states_lxsim
      idx st_src0 st_tgt0 smo0
      (MATCH: match_states idx st_src0 st_tgt0 smo0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun _ => () -> exists (_ : ()) (_ : mem), True)
                  (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 smo0>>
.
Proof.
  revert_until idx. revert idx.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.

  inv MATCH. ss.
  hexploit (SIMP fid); et. intro R.
  unfold interp_program0, mrec in *.
  (* f in ST0. rewrite unfold_interp_mrec in ST0. ss. *)
  inv R; des_ifs; ss.
  { des_ifs. rewrite ! unfold_interp_mrec. ss. econs 2; eauto. ii. econs 3; et.
    { ss. ii. inv STEPTGT; ss. }
    { esplits; ss; et. by (econs; ss). }
  }
  des_ifs.
  rename H1 into SK.
  exploit (SK m vs); et. intro SI. des.
  rewrite ! unfold_interp_mrec. rename f0 into f1. rename f into f0.
  punfold SI. inv SI.
  - (* RET *)
    econstructor 4 with (smo_ret := mk (SimMemId.mk m0 m0) (upcast oh2) (upcast oh3)); ss; eauto.
    { econs; ss; et. }
    { econs; ss; et. }
    { econs; ss; et. }
    { rr. esplits; ss; et. econs; ss; et. }
  - (* TAU *)
    econs 1; ss; et. ii. clear SU.
    econs 1; ss; et; swap 2 3.
    { split; intro T; rr in T; des; ss; inv T; ss. }
    { eapply modsem_receptive; et. }
    ii. inv STEPSRC; ss; clarify. esplits; ss; et.
    { left. apply plus_one. econs; ss; et.
      { eapply modsem_determinate; ss; et. }
      econs; ss; et.
    }
    right. eapply CIH. econs; ss; et.
Qed.



End SIMMODSEM.

Theorem sim_mod
        p0 p1
        ioh0 ioh1
        (SIMP: sim_prog p0 p1)
        (SIMO: forall skenv, SO (ioh0 skenv) (ioh1 skenv))
  :
    forall sk,
      ModPair.sim (SimSymbId.mk_mp (SIRmini.module sk p0 mi ioh0) (SIRmini.module sk p1 mi ioh1))
.
Proof.
  ii. econs; ss; eauto.
  ii. esplits; ss; et. econs; ss; et.
Qed.

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
