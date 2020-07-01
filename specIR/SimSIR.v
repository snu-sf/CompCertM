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
Require Import SIRCommon SIR.

Require Import Program.
Require Import Simulation.
Require Import Lexicographic_Product.
Require Import Relation_Operators.

Set Implicit Arguments.












(*** TODO: Move to Ord.v ***)
Section LEXICO.

  Variable (idxh idxl: Type) (ordh: idxh -> idxh -> Prop) (ordl: idxl -> idxl -> Prop).

  Definition idx_prod := (idxh * idxl)%type.

  Inductive ord_prod: idx_prod -> idx_prod -> Prop :=
  | ord_prod_high
      idxh0 idxh1 idxl0 idxl1
      (ORDH: ordh idxh0 idxh1):
      ord_prod (idxh0, idxl0) (idxh1, idxl1)
  | ord_prod_low
      idxh idxl0 idxl1
      (ORDL: ordl idxl0 idxl1):
      ord_prod (idxh, idxl0) (idxh, idxl1).

  Theorem ord_prod_wf
          (WF0: well_founded ordl)
          (WF1: well_founded ordh):
      <<WF: well_founded ord_prod>>.
  Proof.
    assert(ACC: forall h, Acc ordh h -> forall l, Acc ordl l -> Acc ord_prod (h, l)).
    {
      induction 1.
      induction 1.
      econs. i. inv H3.
      - eauto.
      - eauto.
    }
    rr. i. destruct a. eapply ACC; eauto.
  Qed.

End LEXICO.



(* Inductive silent_taus E R: itree E R -> nat -> Prop := *)
(* | taus_ret *)
(*     r *)
(*   : *)
(*     silent_taus (Ret r) 0%nat *)
(* | taus_tau *)
(*     itr0 n *)
(*     (REC: silent_taus itr0 n) *)
(*   : *)
(*     silent_taus (Tau itr0) (S n) *)
(* | taus_vis *)
(*     X (e: E X) ktr0 *)
(*   : *)
(*     silent_taus (Vis e ktr0) 0%nat *)
(* . *)





Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap_src owned_heap_tgt: Type.
Variable SO: owned_heap_src -> owned_heap_tgt -> Prop.
Definition SALL: (owned_heap_src * (mem * val)) -> (owned_heap_tgt * (mem * val)) -> Prop :=
  fun '(oh_src, (m_src, vs_src)) '(oh_tgt, (m_tgt, vs_tgt)) =>
    <<O: SO oh_src oh_tgt>> /\ <<M: m_src = m_tgt>> /\ <<VS: vs_src = vs_tgt>>
.





(*** sim semantics ***)
Section SEMANTICS.

(*** sim states ***)
Let st_src := (SIR.state owned_heap_src).
Let st_tgt := (SIR.state owned_heap_tgt).

(***
In the definition of choose_src/choose_tgt...

Approach A (more flexible):
  Don't enforce tau. use coinductive-inductive definition
  (recurse with "_sim_st sim_st")
Approach B (not flexible but not that problematic):
  Enforce tau and just use coinductive definition.
  This auxiliary tau can be removed later by another translation,
  and this should not be a pain point because we have transitivity for free.


I tried approach A, but it is harder than I thought.
When proving soundness of this definition (i.e, SimSIR => SimModSem)
I need to know how many inductive steps it will take (so that I can give a proper index).
However, in case of choose_tgt, the recursion occurs under the forall quantifier.
I cannot predict the number of steps!
(In other words, non-determinism is the problem)
So, let's just go for the approach B.


Philosophy: "Tau" is the only one that is coinductive-inductively defined.
            All other cases should make progress, and auxiliary tau can be removed later.

            Some pain point is it is hard to combine choose_src/choose_tgt to get choose_both.
            Let's just put explicit choose_both constructor for now, and see what happens.

TODO: why does itree needs transitivity? is this difference an interesting point?
TODO: why itree has both `EqTauL/EqTauR` and `EqTau`? merely for convenience?
***)
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
| sim_st_choose
    X_src X_tgt
    k_src k_tgt
    (INHAB: inhabited X_tgt)
    (SIM: forall x_tgt, exists x_src, sim_st (k_src x_src) (k_tgt x_tgt))
  :
    _sim_st sim_st
            (Vis (subevent _ (EChoose X_src)) k_src)
            (Vis (subevent _ (EChoose X_tgt)) k_tgt)
| sim_st_choose_src
    X_src
    k_src i_tgt
    (* (SIM: exists x_src, _sim_st sim_st (k_src x_src) i_tgt) *)
    (*** looks good, but induction hypothesis becomes stupid. Can we fix that? ***)
    x_src
    (* (SIM: _sim_st sim_st (k_src x_src) i_tgt) *)
    (SIM: sim_st (k_src x_src) i_tgt)
  :
    _sim_st sim_st
            (Vis (subevent _ (EChoose X_src)) k_src)
            (Tau i_tgt)
| sim_st_choose_tgt
    X_tgt
    k_tgt i_src
    (INHAB: inhabited X_tgt)
    (* (SIM: forall x_tgt, _sim_st sim_st i_src (k_tgt x_tgt)) *)
    (SIM: forall x_tgt, sim_st i_src (k_tgt x_tgt))
    (*** cannot count the depth because of forall quantifier (it may different case by case) ***)
    (*** let's just put Tau and enforce progress here ... ***)
  :
    _sim_st sim_st
            (Tau i_src)
            (Vis (subevent _ (EChoose X_tgt)) k_tgt)
| sim_st_tau_src
    i_src i_tgt
    (SIM: _sim_st sim_st i_src i_tgt)
  :
    _sim_st sim_st (Tau i_src) i_tgt
| sim_st_tau_tgt
    i_src i_tgt
    (SIM: _sim_st sim_st i_src i_tgt)
  :
    _sim_st sim_st i_src (Tau i_tgt)
.

(* Section DEPTH. *)
(*   Variable (sim_st: st_src -> st_tgt -> Prop). *)
(*   Inductive depth: forall i_src i_tgt, _sim_st sim_st i_src i_tgt -> nat -> Prop := *)
(*   (* | depth_tau_src *) *)
(*   (*     (i_src0: st_src) (i_tgt0: st_tgt) *) *)
(*   (*     (SIM: _sim_st sim_st i_src0 i_tgt0) m *) *)
(*   (*     (REC: @depth i_src0 i_tgt0 SIM m) *) *)
(*   (*   : *) *)
(*   (*     @depth (Tau i_src0) i_tgt0 (@sim_st_tau_src sim_st i_src0 i_tgt0 SIM) (S m) *) *)
(*   | depth_tau_src *)
(*       (i_src0: st_src) (i_tgt0: st_tgt) *)
(*       (SIM: _sim_st sim_st i_src0 i_tgt0) m *)
(*       (REC: depth SIM m) *)
(*     : *)
(*       depth (sim_st_tau_src SIM) (S m) *)
(*   | depth_tau_tgt *)
(*       (i_src0: st_src) (i_tgt0: st_tgt) *)
(*       (SIM: _sim_st sim_st i_src0 i_tgt0) m *)
(*       (REC: depth SIM m) *)
(*     : *)
(*       depth (sim_st_tau_tgt SIM) (S m) *)
(*   . *)
(* End DEPTH. *)


Definition sim_st: st_src -> st_tgt -> Prop := paco2 _sim_st bot2.

Lemma sim_st_mon: monotone2 _sim_st.
Proof.
  ii. induction IN; try (by econs; et).
  - econs; et. i. exploit SIM; et. i; des. esplits; et.
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
  Variable sim_prog: forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      (<<SIM: sim_st (interp_program p_src (ICall fname oh_src m vs))
                     (interp_program p_tgt (ICall fname oh_tgt m vs))
                     >>)
  .

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
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh_src).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh_tgt).



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

    Inductive match_states: SIR.state owned_heap_src ->
                            SIR.state owned_heap_tgt -> SimMemOh.t -> Prop :=
    | match_states_intro
        st_src st_tgt smo0
        (SIM: sim_st st_src st_tgt)
        (MWF: SimMemOh.wf smo0)
      :
        match_states st_src st_tgt smo0
    .

    (*** lexicographic ***)
    Let idx: Type := (nat * nat).
    Let ord: idx -> idx -> Prop := ord_prod lt lt.
    Let wf_ord: well_founded ord := ord_prod_wf lt_wf lt_wf.

    Lemma match_states_lxsim
          st_src_src st_tgt_src smo_src
          (MATCH: match_states st_src_src st_tgt_src smo_src)
      :
        <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                      (fun _ => () -> exists (_ : ()) (_ : mem), True)
                      (Ord.lift_idx wf_ord (1%nat, 0%nat)) st_src_src st_tgt_src smo_src>>
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
      - (* CHOOSE BOTH *)
        inv INHAB.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; ss; et. econsby (ss; et). }
        { ii. inv STEPTGT; ss; csc.
          hexpl SIM0; et. pclearbot.
          esplits; et.
          + left. eapply plus_one. econs 3; ss; et.
          + gbase. eapply CIH. econs; et.
        }
      - (* CHOOSE SRC *)
        des. pclearbot.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; ss; et. econsby (ss; et). }
        { ii. inv STEPTGT; ss; clarify. esplits; et.
          + left. eapply plus_one. econs 3; ss; et.
          + gbase. eapply CIH. econs; et.
        }
      - (* CHOOSE TGT *)
        des. pclearbot. inv INHAB.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; ss; et. econsby (ss; et). }
        { ii. inv STEPTGT; ss; csc. esplits; et.
          + left. eapply plus_one. econs; ss; et.
          + gbase. eapply CIH. econs; et.
        }
      - (* TAU L *)
        silent_taus
        econs. ii. clear_tac.
        

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
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. inv MWF. ss. destruct sm_arg; ss.
        destruct sm0; ss. subst. clarify. clear_tac.
        assert(fid0 = fid).
        { apply_all_once Genv.find_invert_symbol. clarify. }
        clarify.
        eapply sim_prog; et.
      - i; des. inv SAFESRC. ss. des_ifs.
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. destruct sm0; ss. clarify.
        esplits; et. econs; ss; et.
    Unshelve.
      all: ss.
      all: try (econsby ss).
    Qed.

  End SIMMODSEM.

  Theorem sim_mod: ModPair.sim (SimSymbId.mk_mp (SIR.module sk p_src mi ioh_src)
                                                (SIR.module sk p_tgt mi ioh_tgt)).
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem; et.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.
