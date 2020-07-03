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

Set Implicit Arguments.



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

Variable idx: Type.
Variable ord: idx -> idx -> Prop.
Hypothesis wf_ord: well_founded ord.

Inductive _sim_st (sim_st: idx -> st_src -> st_tgt -> Prop) (i0: idx): st_src -> st_tgt -> Prop :=
| sim_st_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    _sim_st sim_st i0 (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| sim_st_tau
    i1
    it_src it_tgt
    (SIM: sim_st i1 it_src it_tgt)
  :
    _sim_st sim_st i0 (Tau it_src) (Tau it_tgt)
| sim_st_ecall
    i1
    sg m vs fptr
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL !-> sim_st i1) k_src k_tgt)
  :
    _sim_st sim_st i0
             (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| sim_st_nb
    it_src k_tgt
  :
    _sim_st sim_st i0 it_src (Vis (subevent _ (ENB)) k_tgt)
| sim_st_ub
    k_src it_tgt
  :
    _sim_st sim_st i0 (Vis (subevent _ (EUB)) k_src) it_tgt
| sim_st_choose
    i1 X_src X_tgt
    k_src k_tgt
    (INHAB: inhabited X_tgt \/ X_src = X_tgt)
    (SIM: forall x_tgt, exists x_src, sim_st i1 (k_src x_src) (k_tgt x_tgt))
  :
    _sim_st sim_st i0
            (Vis (subevent _ (EChoose X_src)) k_src)
            (Vis (subevent _ (EChoose X_tgt)) k_tgt)
| sim_st_choose_src
    i1 X_src
    k_src it_tgt
    (SIM: exists x_src, sim_st i1 (k_src x_src) it_tgt)
  :
    _sim_st sim_st i0
            (Vis (subevent _ (EChoose X_src)) k_src)
            (Tau it_tgt)
| sim_st_choose_tgt
    i1 X_tgt
    k_tgt it_src
    (INHAB: inhabited X_tgt)
    (SIM: forall x_tgt, sim_st i1 it_src (k_tgt x_tgt))
  :
    _sim_st sim_st i0
            (Tau it_src)
            (Vis (subevent _ (EChoose X_tgt)) k_tgt)
| sim_st_tau_src
    i1
    it_src it_tgt
    (SIM: sim_st i1 it_src it_tgt)
    (ORD: ord i1 i0)
  :
    _sim_st sim_st i0 (Tau it_src) (it_tgt)
| sim_st_tau_tgt
    i1
    it_src it_tgt
    (SIM: sim_st i1 it_src it_tgt)
    (ORD: ord i1 i0)
  :
    _sim_st sim_st i0 (it_src) (Tau it_tgt)
| sim_st_stutter
    i1
    it_src it_tgt
    (SIM: sim_st i1 it_src it_tgt)
    (ORD: ord i1 i0)
  :
    _sim_st sim_st i0 (it_src) (it_tgt)
.

Definition sim_st: idx -> st_src -> st_tgt -> Prop := paco3 _sim_st bot3.

Lemma sim_st_mon: monotone3 _sim_st.
Proof.
  ii. inv IN; try econs; et.
  - i. exploit SIM; et. i; des_safe. esplits; et.
  - des. esplits; et.
Unshelve.
Qed.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.

End SEMANTICS.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.








Section SIM.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis wf_ord: well_founded ord.
  Let sim_st := sim_st ord.

  Variable p_src: program owned_heap_src.
  Variable p_tgt: program owned_heap_tgt.
  Variable sim_prog: forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      exists (i0: idx),
      (<<SIM: sim_st i0 (interp_program p_src (ICall fname oh_src m vs))
                     (interp_program p_tgt (ICall fname oh_tgt m vs))
                     >>)
  .

  (*** lifting above proof into small-step semantics ***)
  Let SimMemOh: SimMemOh.class := Simple.class SO mi.
  Local Existing Instance SimMemOh.

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

    Inductive match_states (i0: idx): SIR.state owned_heap_src ->
                                      SIR.state owned_heap_tgt -> SimMemOh.t -> Prop :=
    | match_states_intro
        st_src st_tgt smo0
        (SIM: sim_st i0 st_src st_tgt)
        (MWF: SimMemOh.wf smo0)
      :
        match_states i0 st_src st_tgt smo0
    .

    Lemma match_states_lxsim
          i0 st_src_src st_tgt_src smo_src
          (MATCH: match_states i0 st_src_src st_tgt_src smo_src)
      :
        <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                      (fun _ => () -> exists (_ : ()) (_ : mem), True)
                      (Ord.lift_idx wf_ord i0) st_src_src st_tgt_src smo_src>>
    .
    Proof.
      revert_until i0. revert i0.
      ginit.
      { intros. eapply cpn4_wcompat; eauto with paco. }
      gcofix CIH. i. gstep.
      ii. clear SUSTAR.

      inv MATCH. ss.
      punfold SIM. inv SIM.
      - assert(U:=MWF).
        inv MWF. inv MWF0. destruct smo_src; ss. destruct sm; ss. clarify.
        econstructor 4 with (smo_ret := Simple.mk (SM:=SimMemId.SimMemId) (SimMemId.mk m m)
                                                  oh_src oh_tgt); ss; eauto.
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
        eexists _, _, (Simple.mk (SM:=SimMemId.SimMemId)
                                 (SimMemId.mk m0 m0) oh_src0 oh_tgt); ss.
        esplits; ss; et.
        { rr. ss. esplits; ss; et. econs; ss; et. }
        { econs; ss; et. }
        ii. des. inv AFTERSRC; ss. inv GETK; ss. csc.
        rename _oh0 into oh_src0.
        rr in SIMRETV. des; ss. inv SIMRETV0; ss. clarify.
        inv MWF0. ss. destruct smo_ret; ss. destruct sm; ss. subst. clarify. clear_tac.
        esplits; et.
        { econs; ss; et. econs; ss; et. }
        u in SIM0.
        hexploit SIM0; et.
        { instantiate (2:= (oh_src, (_, _))). instantiate (1:= (oh_tgt0, (_, _))). ss. }
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
        des; clarify.
        + inv INHAB.
          econs 2; ss; et. ii.
          econs 1; ss; et; cycle 1.
          { esplits; ss; et. econs 3; ss; et. }
          { ii. inv STEPTGT; ss; csc.
            hexpl SIM0; et. pclearbot.
            esplits; et.
            + left. eapply plus_one. econs 3; ss; et.
            + gbase. eapply CIH. econs; et.
          }
        +
          econs 2; ss; et. ii.
          exploit SAFESRC; try apply star_refl. i; des.
          { rr in EVCALL. des. inv EVCALL; ss. }
          { rr in EVRET. des. inv EVRET; ss. }
          inv EVSTEP; ss. csc.
          econs 1; ss; et; cycle 1.
          { esplits; ss; et. econs 3; ss; et. }
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
          + gbase. eapply CIH. econs; et. r; et.
        }
      - (* TAU SRC *)
        pclearbot.
        econs 1; ss; et. ii.
        econs 1; ss; et; swap 2 3.
        { split; intro T; rr in T; des; ss; inv T; ss. }
        { eapply modsem_receptive; et. }
        ii. inv STEPSRC; csc. esplits; et.
        { right. esplits; try apply star_refl. eapply Ord.lift_idx_spec; et. }
        { gbase. eapply CIH. econs; et. }
      - (* TAU TGT *)
        pclearbot.
        econs 2; ss; et. ii.
        econs 1; ss; et; cycle 1.
        { esplits; et. econs; et. }
        ii. inv STEPTGT; csc. esplits; et.
        { right. esplits; try apply star_refl. eapply Ord.lift_idx_spec; et. }
        { gbase. eapply CIH. econs; et. }
      - (* STUTTER *)
        pclearbot.
        econs 2; eauto.
        econs 2; eauto.
        { esplits; try apply star_refl.
          eapply Ord.lift_idx_spec; et. }
        gbase. eapply CIH. econs; et.
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
      { ii. ss. eexists (Simple.mk _ _ _); ss. esplits; eauto. econs; ss; eauto. }
      ii. ss. esplits; eauto.
      - ii. des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. inv MWF. ss. destruct sm_arg; ss.
        destruct sm; ss. subst. clarify. clear_tac.
        rename tgt into m0. rename vs_tgt into vs0.
        exploit (sim_prog fid0 m0 vs0); et. i; des.
        eexists _, (Simple.mk (SM:=SimMemId.SimMemId) (SimMemId.mk _ _) _ _), _. esplits; eauto.
        { econs; ss; et. }
        eapply match_states_lxsim; eauto.
        econs; ss; et.
        + assert(fid0 = fid).
          { apply_all_once Genv.find_invert_symbol. clarify. }
          clarify. eauto.
        + econs; ss; et.
      - i; des. inv SAFESRC. ss. des_ifs.
        rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. destruct sm; ss. clarify.
        esplits; et. econs; ss; et.
    Unshelve.
      all: ss.
      all: try (econsby ss).
    Qed.

  End SIMMODSEM.

  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem; et.
  Qed.

  Theorem correct: rusc defaultR [md_src] [md_tgt].
  Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.
