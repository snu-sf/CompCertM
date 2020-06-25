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

Notation " R !-> R' " := (@hrespectful _ _ _ _ (R%signature) (R'%signature))
                           (right associativity, at level 55).
                         (* : signature_scope. *)

Class HProper A0 A1 (R : A0 -> A1 -> Prop) (a0: A0) (a1: A1) : Prop := hproper_prf : R a0 a1.

Program Instance HProper_Proper A RA (a: A) (P: HProper RA a a): Proper RA a.

Hint Unfold hrespectful.
Hint Unfold HProper.



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

Lemma bind_trigger: forall (E : Type -> Type) (R U : Type) (e : E U) (k : U -> itree E R),
    ` x : _ <- ITree.trigger e;; k x = Vis e (fun x : U => k x).
Proof. i. f. eapply bind_trigger. Qed.

Lemma bind_bind : forall (E : Type -> Type) (R S T : Type) (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ` x : _ <- (` x : _ <- s;; k x);; h x = ` r : R <- s;; ` x : _ <- k r;; h x.
Proof. i. f. eapply bind_bind. Qed.




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
    (SIM: HProper (SALL !-> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src *)
    (*     ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (trigger (ICall fname oh_src m vs) >>= k_src)
             (trigger (ICall fname oh_tgt m vs) >>= k_tgt)
             (* (Vis (subevent _ (ICall fname oh_src m vs)) k_src) *)
             (* (Vis (subevent _ (ICall fname oh_tgt m vs)) k_tgt) *)
| sim_ecall
    sg m vs fptr
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL !-> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| sim_nb
    i_src k_tgt
  :
    _sim_itr sim_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| sim_ub
    k_src i_tgt
  :
    _sim_itr sim_itr (Vis (subevent _ (EUB)) k_src) i_tgt
| sim_choose_src
    X_src
    k_src i_tgt
    (SIM: exists x_src, sim_itr (k_src x_src) i_tgt)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (EChoose X_src)) k_src)
             (Tau (Tau i_tgt))
| sim_choose_tgt
    X_tgt
    k_tgt i_src
    (SIM: forall x_tgt, sim_itr i_src (k_tgt x_tgt))
    (INHAB: inhabited X_tgt)
  :
    _sim_itr sim_itr
             (Tau (Tau i_src))
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



Let fn_src := function owned_heap_src.
Let fn_tgt := function owned_heap_tgt.

(*** TODO: curry "function", and we can state "SALL --> sim_itr" ***)
(*** TODO: give better name than SALL ***)
Definition sim_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall
    m vs
    oh_src oh_tgt
    (O: SO oh_src oh_tgt)
  ,
    <<SIM: sim_itr (k_src oh_src m vs) (k_tgt oh_tgt m vs)>>
.





(*** sim prog ***)
Definition sim_prog: program owned_heap_src -> program owned_heap_tgt -> Prop :=
  eq !-> option_rel sim_fn
.




(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)
Inductive bindC (r: itr_src -> itr_tgt -> Prop) : itr_src -> itr_tgt -> Prop :=
| bindC_intro
    i_src i_tgt
    (SIM: sim_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: HProper (SALL !-> r) k_src k_tgt)
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
  - rewrite ! bind_bind. gstep. econs; eauto. u. ii. repeat spc SIM0. pclearbot. eauto with paco.
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
  HProper ((SALL !-> sim_itr) !-> sim_itr !-> sim_itr) ITree.bind' ITree.bind'
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
    sg m vs fptr
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL !-> sim_st) k_src k_tgt)
  :
    _sim_st sim_st
             (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| sim_st_nb
    i_src k_tgt
  :
    _sim_st sim_st i_src (Vis (subevent _ (ENB)) k_tgt)
| sim_st_ub
    k_src i_tgt
  :
    _sim_st sim_st (Vis (subevent _ (EUB)) k_src) i_tgt
| sim_st_choose_src
    X_src
    k_src i_tgt
    (SIM: exists x_src, sim_st (k_src x_src) i_tgt)
  :
    _sim_st sim_st
            (Vis (subevent _ (EChoose X_src)) k_src)
            (Tau i_tgt)
| sim_st_choose_tgt
    X_tgt
    k_tgt i_src
    (INHAB: inhabited X_tgt)
    (SIM: forall x_tgt, sim_st i_src (k_tgt x_tgt))
  :
    _sim_st sim_st
            (Tau i_src)
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








Section SIM.

  Variable p_src: program owned_heap_src.
  Variable p_tgt: program owned_heap_tgt.
  Hypothesis (SIMP: sim_prog p_src p_tgt).

  Lemma sim_prog_sim_st
        i_src i_tgt
        (SIM: sim_itr i_src i_tgt)
    :
      sim_st (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
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
      { u. ii. repeat spc SIM0. pclearbot. rewrite ! bind_ret_l. eauto. }
      exploit (@SIMP fname); et. intro T.
      inv T.
      { pfold. econs; et. }
      exploit H1; et.
    - gstep. econs; et. u in *. gstep. econs; et. repeat spc SIM0. des; ss. gbase. eapply CIH.
      eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - gstep. des. pclearbot. econs; et. esplits; et. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_tgt0)). cbn. econs; et. eauto with paco.
    - gstep. pclearbot. econs; et. ii. repeat spc SIM0. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_src0)). cbn. econs; et. eauto with paco.
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
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
      eapply sim_prog_sim_st; ss.
      hexploit (@SIMP fname); et. intro T. inv T; ss.
      { pfold. econs; et. }
      repeat (spc H1). des. ss.
    }
  Qed.

  (*** lifting above proof into small-step semantics ***)
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
        (o_src: owned_heap_src) (o_tgt: owned_heap_tgt)
        (MWF: SimMem.wf smo)
        (OHSRC: smo.(oh_src) = upcast o_src)
        (OHTGT: smo.(oh_tgt) = upcast o_tgt)
        (O: SO o_src o_tgt)
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

  Variable ioh_src: SkEnv.t -> owned_heap_src.
  Variable ioh_tgt: SkEnv.t -> owned_heap_tgt.
  Hypothesis (SIMO: forall skenv, SO (ioh_src skenv) (ioh_tgt skenv)).
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIRmini.module sk p_src mi ioh_src).
  Let md_tgt: Mod.t := (SIRmini.module sk p_tgt mi ioh_tgt).



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
                                       SIRmini.state owned_heap_tgt -> SimMemOh.t -> Prop :=
    | match_states_intro
        st_src st_tgt smo0
        (SIM: sim_st st_src st_tgt)
        (MWF: SimMemOh.wf smo0)
      :
        match_states idx st_src st_tgt smo0
    .

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
      ginit.
      { intros. eapply cpn4_wcompat; eauto with paco. }
      gcofix CIH. i. gstep.
      ii. clear SUSTAR.

      inv MATCH. ss.
      punfold SIM. inv SIM.
      - assert(U:=MWF).
        inv MWF. inv MWF0. destruct smo_src; ss. destruct sm0; ss. clarify.
        econstructor 4 with (smo_ret := mk (SimMemId.mk m m)
                                           (upcast oh_src0) (upcast oh_tgt0)); ss; eauto.
        + econs; ss; et.
        + econs; ss; et.
        + econs; ss; et.
        + rr. ss. esplits; ss; et.
          { econs; ss; et. }
      - (* TAU *)
        econs 1; et.
        econs 1; et; swap 2 3.
        { split; intro T; rr in T; des; ss; inv T; ss. }
        { eapply modsem_receptive; et. }
        ii; ss. inv STEPSRC; ss. clarify. esplits; ss; et.
        { left. eapply plus_one. rr. esplits; et.
          { eapply modsem_determinate; ss; et. }
          econs; et.
        }
        pclearbot. gbase. eapply CIH. econs; et.
      - (* ECALL *)
        econs 3; et.
        { admit "TODO: fix -- ~step, ~ret should suffice". }
        ii; ss. inv ATSRC. csc.
        eexists _, _, (mk (SimMemId.mk m0 m0) (upcast oh_src1) (upcast oh_tgt0)); ss.
        esplits; ss; et.
        { rr. ss. esplits; ss; et. econs; ss; et. }
        { econs; ss; et. }
        { econs; ss; et. }
        ii. des. inv AFTERSRC; ss. inv GETK; ss. csc.
        rename oh_src0 into oh_src1.
        rename _oh0 into oh_src0.
        rr in SIMRETV. des; ss. inv SIMRETV0; ss. clarify.
        inv MWF0. ss. destruct smo_ret; ss. destruct sm0; ss. subst. clarify. clear_tac.
        esplits; et.
        { econs; ss; et. econs; ss; et. }
        u in SIM0.
        hexploit SIM0; et.
        { instantiate (2:= (o_src, (_, _))). instantiate (1:= (o_tgt, (_, _))). ss. }
        intro T. des; ss.
        gbase. eapply CIH. econs; et.
      - (* NB *)
        econs 2; ss; et. ii.
        econs 3; ss; et.
        { ii; ss. inv STEPTGT; ss. }
        { esplits; et. econsby ss. }
      - (* UB *)
        econs 2; ss; et. ii.
        exploit SAFESRC; et.
        { eapply star_refl. }
        intro T; des; ss.
        + rr in EVCALL. des; ss. inv EVCALL; ss.
        + rr in EVRET. des; ss. inv EVRET; ss.
        + inv EVSTEP; ss.
      - (* CHOOSE SRC *)
        des. pclearbot.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; ss; et. econs; ss; et. }
        { ii. inv STEPTGT; ss; clarify. esplits; et.
          + left. eapply plus_one. econs 3; ss; et.
          + gbase. eapply CIH. econs; et.
        }
      - (* CHOOSE TGT *)
        des. pclearbot. inv INHAB.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; ss; et. econs 3; ss; et. }
        { ii. inv STEPTGT; ss; csc. esplits; et.
          + left. eapply plus_one. econs; ss; et.
          + gbase. eapply CIH. econs; et.
        }
    Unshelve.
      all: ss.
      all: try (econsby ss).
    Qed.

    Theorem sim_modsem: ModSemPair.sim msp.
    Proof.
      econstructor 1 with (sidx := unit) (sound_states := top4); eauto;
        try apply SoundTop.sound_state_local_preservation; et; try (by ii; ss).
      { ii. eapply Preservation.local_preservation_noguarantee_weak.
        apply SoundTop.sound_state_local_preservation; et.
      }
      { ii. ss. eexists (mk _ _ _); ss. esplits; eauto. econs; ss; eauto. }
      ii. ss. esplits; eauto.
      - ii. des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
        esplits; eauto.
        { econs; ss; et. }
        eapply match_states_lxsim; eauto.
        econs; ss; et.
        eapply sim_prog_sim_st; et.
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. inv MWF. ss. destruct sm_arg; ss.
        destruct sm0; ss. subst. clarify. clear_tac.
        assert(fid0 = fid).
        { apply_all_once Genv.find_invert_symbol. clarify. }
        clarify.
        rr in SIMP. repeat spc SIMP. hexploit1 SIMP; et. inv SIMP; ss.
        { pfold. econs; et. }
        { eapply H1; et. }
      - i; des. inv SAFESRC. ss. des_ifs.
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. destruct sm0; ss. clarify.
        esplits; et. econs; ss; et.
    Unshelve.
      all: ss.
      all: try (econsby ss).
    Qed.

  End SIMMODSEM.

  Theorem sim_mod: ModPair.sim (SimSymbId.mk_mp (SIRmini.module sk p_src mi ioh_src)
                                                (SIRmini.module sk p_tgt mi ioh_tgt)).
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem; et.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.
Hint Constructors bindC: core.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.
