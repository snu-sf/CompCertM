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

Definition hrespectful A0 A1 B0 B1 (RA: A0 -> A1 -> Prop) (RB: B0 -> B1 -> Prop):
  (A0 -> B0) -> (A1 -> B1) -> Prop :=
  fun f0 f1 => forall a0 a1, RA a0 a1 -> RB (f0 a0) (f1 a1)
.

Definition hrespectful_respectful A B (RA: relation A) (RB: relation B):
  @hrespectful A A B B RA RB = @respectful A B RA RB.
Proof. ss. Qed.

Notation " R **> R' " := (@hrespectful _ _ _ _ (R%signature) (R'%signature))
                           (right associativity, at level 55).
                         (* : signature_scope. *)

Class HProper A0 A1 (R : A0 -> A1 -> Prop) (a0: A0) (a1: A1) : Prop := hproper_prf : R a0 a1.

Program Instance HProper_Proper A RA (a: A) (P: HProper RA a a): Proper RA a.

Hint Unfold hrespectful.
Hint Unfold HProper.
(**
Ltac uh := unfold hrespectful in *; unfold HProper in *.
Tactic Notation "uh" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Tactic Notation "u" := repeat (autounfold with *; cbn).
Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in * ).
**)



(*** TODO: move to SIRCommon ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; et.
Qed.

Lemma bind_ret_l : forall (E : Type -> Type) (R S : Type) (r : R) (k : R -> itree E S),
    ` x : _ <- Ret r;; k x = k r.
Proof.
  i. f. eapply bind_ret_l.
Qed.

Lemma bind_ret_r : forall (E : Type -> Type) (R : Type) (s : itree E R), ` x : R <- s;; Ret x = s.
Proof.
  i. f. eapply bind_ret_r.
Qed.

Lemma bind_tau : forall (E : Type -> Type) (R U : Type) (t : itree E U) (k : U -> itree E R),
  ` x : _ <- Tau t;; k x = Tau (` x : _ <- t;; k x).
Proof.
  i. f. eapply bind_tau.
Qed.

Lemma bind_vis: forall (E : Type -> Type) (R U V : Type) (e : E V) (ek : V -> itree E U) (k : U -> itree E R),
  ` x : _ <- Vis e ek;; k x = Vis e (fun x : V => ` x : _ <- ek x;; k x).
Proof.
  i. f. eapply bind_vis.
Qed.





Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap_src owned_heap_tgt: Type.
Variable SO: owned_heap_src -> owned_heap_tgt -> Prop.
Definition SALL: (owned_heap_src * (mem * val)) -> (owned_heap_tgt * (mem * val)) -> Prop :=
  fun '(oh_src, (m_src, vs_src)) '(oh_tgt, (m_tgt, vs_tgt)) =>
    <<O: SO oh_src oh_tgt>> /\ <<M: m_src = m_tgt>> /\ <<VS: vs_src = vs_tgt>>
.





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let itr_src := itree (E owned_heap_src) (owned_heap_src * (mem * val)).
Let itr_tgt := itree (E owned_heap_tgt) (owned_heap_tgt * (mem * val)).

Inductive _sim_itr (sim_itr: itr_src -> itr_tgt -> Prop): itr_src -> itr_tgt -> Prop :=
| sim_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    _sim_itr sim_itr (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| sim_tau
    i_src
    i_tgt
    (SIM: sim_itr i_src i_tgt)
  :
    _sim_itr sim_itr (Tau i_src) (Tau i_tgt)
| sim_icall
    fname m vs
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL **> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src *)
    (*     ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ICall fname oh_src m vs)) k_src)
             (Vis (subevent _ (ICall fname oh_tgt m vs)) k_tgt)
| sim_ecall
    sg m vs
    fptr_src oh_src k_src
    fptr_tgt oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL **> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ECall sg fptr_src oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr_tgt oh_tgt m vs)) k_tgt)
| sim_nb
    i_src k_tgt
  :
    _sim_itr sim_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| sim_ub
    k_src i_tgt
  :
    _sim_itr sim_itr (Vis (subevent _ (ENB)) k_src) i_tgt
| sim_choose_src
    X_src
    k_src i_tgt
    (SIM: exists x_src, sim_itr (k_src x_src) i_tgt)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (EChoose X_src)) k_src)
             (Tau i_tgt)
| sim_choose_tgt
    X_tgt
    k_tgt i_src
    (SIM: forall x_tgt, sim_itr i_src (k_tgt x_tgt))
  :
    _sim_itr sim_itr
             (Tau i_src)
             (Vis (subevent _ (EChoose X_tgt)) k_tgt)
.

Definition sim_itr: itr_src -> itr_tgt -> Prop := paco2 _sim_itr bot2.

Lemma sim_itr_mon: monotone2 _sim_itr.
Proof.
  ii. inv IN; try econs; et; rr; et.
  des. esplits; et.
Unshelve.
Qed.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.



(*** sim fn ***)
Let fn_src := function owned_heap_src.
Let fn_tgt := function owned_heap_tgt.

(*** TODO: curry "function", and we can state "SALL **> sim_itr ***)
(*** TODO: give better name than SALL ***)
Definition sim_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall
    m vs
    oh_src oh_tgt
    (O: SO oh_src oh_tgt)
  ,
    <<SIM: sim_itr (k_src oh_src m vs) (k_tgt oh_tgt m vs)>>
.





(*** sim prog ***)
Definition sim_prog (p_src: program owned_heap_src) (p_tgt: program owned_heap_tgt): Prop :=
  forall fname, option_rel sim_fn (p_src fname) (p_tgt fname)
.




(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)
Inductive bindC (r: itr_src -> itr_tgt -> Prop) : itr_src -> itr_tgt -> Prop :=
| bindC_intro
    i_src i_tgt
    (SIM: sim_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: HProper (SALL **> r) k_src k_tgt)
    (* (SIMK: forall *)
    (*     oh_src oh_tgt m vs *)
    (*     (O: SO oh_src oh_tgt) *)
    (*   , *)
    (*     <<SIM: r (k_src (oh_src, (m, vs))) (k_tgt (oh_tgt, (m, vs)))>>) *)
  :
    bindC r (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindC: core.

Lemma bindC_spec
      simC
  :
    bindC <3= gupaco2 (_sim_itr) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold SIM. inv SIM.
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et. rr; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc SIM0. pclearbot.
    (* gfinal. left. eapply CIH. econs. { et. } uh. ii. eapply SIMK. et. *)
    eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc SIM0. pclearbot.
    eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. des. pclearbot. eauto with paco.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. ii. pclearbot. eauto with paco.
Qed.

Global Instance sim_itr_bind :
  HProper ((SALL **> sim_itr) **> sim_itr **> sim_itr) ITree.bind' ITree.bind'
.
Proof.
  red. ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  guclo bindC_spec. ii. econs; et.
  u. ii.
  exploit H0; et.
  intro T. eauto with paco.
Qed.

End SYNTAX.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.









(*** sim semantics ***)
Section SEMANTICS.

(*** sim states ***)
Let st_src := (SIRmini.state owned_heap_src).
Let st_tgt := (SIRmini.state owned_heap_tgt).

Inductive _sim_st (sim_st: st_src -> st_tgt -> Prop): st_src -> st_tgt -> Prop :=
| sim_st_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    _sim_st sim_st (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| sim_st_tau
    i_src
    i_tgt
    (SIM: sim_st i_src i_tgt)
  :
    _sim_st sim_st (Tau i_src) (Tau i_tgt)
| sim_st_ecall
    sg m vs
    fptr_src oh_src k_src
    fptr_tgt oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL **> sim_st) k_src k_tgt)
  :
    _sim_st sim_st
             (Vis (subevent _ (ECall sg fptr_src oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr_tgt oh_tgt m vs)) k_tgt)
| sim_st_nb
    i_src k_tgt
  :
    _sim_st sim_st i_src (Vis (subevent _ (ENB)) k_tgt)
| sim_st_ub
    k_src i_tgt
  :
    _sim_st sim_st (Vis (subevent _ (ENB)) k_src) i_tgt
| sim_st_choose_src
    X_src
    k_src i_tgt
    (SIM: exists x_src, sim_st (k_src x_src) i_tgt)
  :
    _sim_st sim_st
            (Vis (subevent _ (EChoose X_src)) k_src)
            i_tgt 
| sim_st_choose_tgt
    X_tgt
    k_tgt i_src
    (SIM: forall x_tgt, sim_st i_src (k_tgt x_tgt))
  :
    _sim_st sim_st
            i_src
            (Vis (subevent _ (EChoose X_tgt)) k_tgt)
.

Definition sim_st: st_src -> st_tgt -> Prop := paco2 _sim_st bot2.

Lemma sim_st_mon: monotone2 _sim_st.
Proof.
  ii. inv IN; try econs; et.
  des. esplits; et.
Unshelve.
Qed.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.

End SEMANTICS.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.









Lemma sim_prog_sim_st_aux
      p_src p_tgt
      (SIMP: sim_prog p_src p_tgt)
      i_src i_tgt
      (SIM: sim_itr i_src i_tgt)
  :
    sim_st (interp_mrec (interp_function p_src) i_src) (interp_mrec (interp_function p_tgt) i_tgt)
.
Proof.
  revert_until SIMP.
  ginit.
  { intros. eapply cpn2_wcompat; et. eauto with paco. }
  gcofix CIH.
  i. rewrite ! unfold_interp_mrec.
  punfold SIM. inv SIM; cbn.
  - gstep. econs; et.
  - pclearbot. gstep. econs; et. gbase. et.
  - pclearbot. gstep. econs; et. gbase.
    eapply CIH. eapply sim_itr_bind.
    { u. ii. repeat spc SIM0. pclearbot. eauto. }
    hexploit (SIMP fname); et. intro T.
    inv T.
    { pfold. econs; et. }
    exploit H1; et.
  - gstep. econs; et. u in *. gstep. econs; et. repeat spc SIM0. des; ss. gbase. eapply CIH.
    eauto with paco.
  - gstep. econs; et.
  - gstep. econs; et.
  - gstep. des. pclearbot. econs; et. esplits; et. gstep. econs; et. eauto with paco.
  - gstep. pclearbot. econs; et. ii. repeat spc SIM0.
    gstep. econs; et. eauto with paco.
Qed.

Theorem sim_prog_sim_st
        p_src p_tgt
        (SIMP: sim_prog p_src p_tgt)
  :
    forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      (<<SIM: sim_st (interp_program0 p_src (ICall fname oh_src m vs))
                     (interp_program0 p_tgt (ICall fname oh_tgt m vs))
                     >>)
.
Proof.
  {
    ii.
    eapply sim_prog_sim_st_aux; ss.
    hexploit (SIMP fname); et. intro T. inv T; ss.
    { pfold. econs; et. }
    repeat (spc H1). des. ss.
  }
Qed.


(*** sim fn / program ***)
(* Let fn_src := InternalCallE owned_heap_src ~> SIRmini.state. *)
(* Let fn_tgt := InternalCallE owned_heap_tgt ~> SIRmini.state. *)

(* Definition sim_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall *)
(*     fname m vs *)
(*     oh_src oh_tgt *)
(*     (O: SO oh_src oh_tgt) *)
(*   , *)
(*     <<SIM: sim_st (k_src _ (ICall fname oh_src m vs)) (k_tgt _ (ICall fname oh_tgt m vs))>> *)
(* . *)
Let fn_src := function owned_heap_src.
Let fn_tgt := function owned_heap_tgt.

Definition sim_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall
    m vs
    oh_src oh_tgt
    (O: SO oh_src oh_tgt)
  ,
    <<SIM: sim_st (k_src oh_src m vs) (k_tgt oh_tgt m vs)>>
.

Definition sim_prog (p_src: program owned_heap_src) (p_tgt: program owned_heap_tgt): Prop :=
  (eq ===> 
.
Definition sim_prog (p_src: program owned_heap_src) (p_tgt: program owned_heap_tgt): Prop :=
  forall fname, <<SIM: option_rel sim_fn (p_src fname) (p_tgt fname)>>
.

Theorem sim_prog_sim_st
        p_src p_tgt
        (SIM: sim_prog p_src p_tgt)
  :
    <<SIM: sim_ktr (interp_program0 p_src) (interp_program0 p_tgt)>>
.
Proof.
Qed.
Global Instance eq_itree_mrec:
  Proper (sim_prog ==> eq ==> sim_st) (interp_program0).
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. auto with paco.
Qed.

Theorem sim_sim
        














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
      (oh_src: owned_heap_src) (oh1: owned_heap1)
      (MWF: SimMem.wf smo)
      (OHSRC: smo.(oh_src) = upcast oh_src)
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
    ss. ii. destruct smo_src; ss.
  Qed.

End SMO.



Variable p_src: program owned_heap_src.
Variable p1: program owned_heap1.
Variable ioh_src: SkEnv.t -> owned_heap_src.
Variable ioh1: SkEnv.t -> owned_heap1.
Hypothesis (SIMP: sim_prog p_src p1).
Hypothesis (SIMO: forall skenv, SO (ioh_src skenv) (ioh1 skenv)).
Variable sk: Sk.t.
Let md_src: Mod.t := (SIRmini.module sk p_src mi ioh_src).
Let md_tgt: Mod.t := (SIRmini.module sk p1 mi ioh1).



(*** Lifting to SimModSem ***)
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

Inductive match_states (idx: nat): SIRmini.state owned_heap_src ->
                                   SIRmini.state owned_heap1 -> SimMemOh.t -> Prop :=
| match_states_intro
    st_src st1 smo_src
    fid m vs oh_src oh1
    (O: SO oh_src oh1)
    (ST_src: st_src = (interp_program_src p_src (ICall fid oh_src m vs)))
    (ST1: st1 = (interp_program_src p1 (ICall fid oh1 m vs)))
    (MWF: SimMemOh.wf smo_src)
  :
    match_states idx st_src st1 smo_src
.

(*** TODO: move to SIRCommon2 ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; et.
Qed.

Lemma match_states_lxsim
      idx st_src_src st_tgt_src smo_src
      (MATCH: match_states idx st_src_src st_tgt_src smo_src)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun _ => () -> exists (_ : ()) (_ : mem), True)
                  (Ord.lift_idx lt_wf idx) st_src_src st_tgt_src smo_src>>
.
Proof.
  revert_until idx. revert idx.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.

  inv MATCH. ss.
  hexploit (SIMP fid); et. intro R.
  unfold interp_program_src, mrec in *.
  (* f in ST_src. rewrite unfold_interp_mrec in ST_src. ss. *)
  inv R; des_ifs; ss.
  { des_ifs. rewrite ! unfold_interp_mrec. ss. econs 2; eauto. ii. econs 3; et.
    { ss. ii. inv STEPTGT; ss. }
    { esplits; ss; et. by (econs; ss). }
  }
  des_ifs.
  rename H1 into SK.
  exploit (SK m vs); et. intro SI. des.
  rewrite ! unfold_interp_mrec. rename f_src into f1. rename f into f_src.
  punfold SI. inv SI.
  - (* RET *)
    econstructor 4 with (smo_ret := mk (SimMemId.mk m_src m_src) (upcast oh2) (upcast oh3)); ss; eauto.
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
        p_src p1
        ioh_src ioh1
        (SIMP: sim_prog p_src p1)
        (SIMO: forall skenv, SO (ioh_src skenv) (ioh1 skenv))
  :
    forall sk,
      ModPair.sim (SimSymbId.mk_mp (SIRmini.module sk p_src mi ioh_src) (SIRmini.module sk p1 mi ioh1))
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
