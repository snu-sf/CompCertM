Require Import CoqlibC.
Require Import MemoryC.
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
Require Import SimMemLift.

Set Implicit Arguments.






Definition ons_mem (ptt: partition) (ons: ownership): block -> Z -> Prop :=
  fun b ofs => (ptt b ofs) = ons
.
Hint Unfold ons_mem.
Hint Unfold privmods.

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => (Mem.valid_block m) b.
Hint Unfold valid_blocks.
Hint Unfold loc_out_of_bounds.





Record t' := mk {
  src: mem;
  tgt: mem;
  ptt: partition;
}.

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (MEXT: Mem.extends sm0.(src) sm0.(tgt))
    (PMPERM: forall mi, privmods mi sm0.(ptt) <2=
                          (valid_blocks sm0.(src) /2\ loc_out_of_bounds sm0.(src)))
.

Inductive le' (sm0 sm1: t'): Prop :=
| le_intro
    (PMLE: forall mi, privmods mi sm0.(ptt) <2= privmods mi sm1.(ptt))
.

Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
Next Obligation.
  econs; et.
Qed.
Next Obligation.
  econs; et.
  inv H. inv H0.
  etrans; et.
Qed.



Program Instance SimMemExtSep : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  ptt_src := ptt;
  ptt_tgt := ptt;
  wf := wf';
  le := le';
  lepriv := top2;
  sim_val := fun (_: t') => Val.lessdef;
  sim_val_list := fun (_: t') => Val.lessdef_list;
  unchanged_on := top3;
}.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext1.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. econs; eauto.
  - induction H; econs; eauto.
Qed.
Next Obligation. inv H. ss. Qed.

Program Instance SimMemExtSepLift: SimMemLift.class SimMemExtSep :=
{ lift := id;
  unlift := fun _ => id;
}.

Global Program Instance SimSymbExtSep: SimSymb.class SimMemExtSep := {
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
  eexists. eexists (mk _ _ (fun _ _ => etc)). esplits; ss; eauto.
  - econs; et; ss.
    + apply Mem.extends_refl.
    + u. ii. des_ifs.
  - rewrite MAINSIM. ss.
Qed.
Next Obligation. eapply SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto. i; des.
  inv H. inv SIMSKENV. econs; eauto.
  ii; ss. eapply FUNCFSIM; eauto. rpapply FUNCSRC. f_equal. inv SIMFPTR; ss.
Qed.
Next Obligation. esplits; eauto. eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  inv ARGS; ss. destruct sm0; ss; clarify.
  exploit external_call_mem_extends; eauto. { eapply MWF. } i. des.
  exists (mk (Retv.m retv_src) m2' ptt0). exists (Retv.mk vres' m2').
  esplits; ss; eauto.
  { eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. }
  { destruct retv_src; ss. econs; ss; eauto. }
  { econs; et. }
  { econs; ss; et. }
  { inv MWF. econs; ss; et. etrans; et.
    bar.
    u. ii. des. esplits; et.
    - eapply external_call_valid_block; et.
    - ii. exploit external_call_max_perm; try apply SYSSRC; eauto.
  }
Qed.





Section ORIGINALS.

Lemma alloc_parallel
      sm0 lo_src hi_src lo_tgt hi_tgt blk m_src0
      (MWF: wf' sm0)
      (ALCSRC: Mem.alloc sm0.(src) lo_src hi_src = (m_src0, blk))
      (LO: lo_tgt <= lo_src)
      (HI: hi_src <= hi_tgt):
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<ALCTGT: Mem.alloc sm0.(tgt) lo_tgt hi_tgt = (sm1.(tgt), blk)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.alloc_extends; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ sm0.(ptt)).
  dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
  - econs; ss; eauto.
  - econs; ss; eauto.
    etrans; et.
    u. ii. des. esplits; eauto with mem.
Qed.

Lemma free_left
      ons sm0 lo hi blk m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk lo hi = Some m_src0)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
      /\ (<<PMSRC: (brange blk lo hi) <2= ons_mem sm1.(ptt) ons>>)
.
Proof.
  exploit Mem.free_left_extends; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _
              (fun b ofs => if (eq_block b blk) && (lo <=? ofs) && (ofs <? hi)
                            then ons
                            else sm0.(ptt) b ofs)
          ).
  dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    inv SPLITHINT1. ss.
    ii.
    exploit PMPERM; et. intro T; des.
    revert PR. u. ii. des_ifs_safe. bsimpl. des. des_sumbool.
    rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
    clarify.
    rr in T0. contradict T0. exploit Mem.free_range_perm; eauto. intro PERM. eauto with mem.
  - econs; ss; eauto.
    + u. ii. des_ifs_safe. bsimpl; des; des_sumbool.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *. clarify.
      exfalso.
      exploit (PMPERM (Some mi) blk x1); et.
      { ss. des_ifs. des_sumbool. ss. }
      intro T; des.
      rr in T0. contradict T0. exploit Mem.free_range_perm; eauto. intro PERM. eauto with mem.
    + u. ii. des_ifs_safe. bsimpl; des; des_sumbool.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *. clarify.
      exfalso.
      exploit (PMPERM (Some mi) blk x1); et.
      { ss. des_ifs. des_sumbool. ss. }
      intro T; des.
      rr in T0. contradict T0. exploit Mem.free_range_perm; eauto. intro PERM. eauto with mem.
  - u. ii. des. clarify. rewrite <- Z.leb_le in *. rewrite <- Z.ltb_lt in *. des_ifs.
    bsimpl. des_sumbool; congruence.
  - des. clear_tac.
    econs; ss; eauto.
    intros mi b ofs. specialize (PMPERM mi b ofs). ss.
    u. u in PMPERM. ii. des_ifs_safe.
    des_sumbool. clarify.
    (* Set Printing All. *)
    destruct (eq_block b blk && (lo <=? ofs) && (ofs <? hi)) eqn:T.
    + unfold not in *. rewrite T in *.
      bsimpl. des. des_sumbool.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *. clarify.
      exploit Mem.free_range_perm; et. intro PERM.
      esplits; et.
      { eauto with mem. }
      i.
      exploit Mem_free_noperm; et.
    + unfold not in *. rewrite T in *.
      des_ifs.
      exploit PMPERM; et.
      { des_sumbool. ss. }
      i; des.
      esplits; eauto with mem.
Unshelve.
  all: ss.
Qed.

Lemma free_right_pm
      mi sm0 lo hi blk m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk lo hi = Some m_tgt0)
      (PRVTGT: brange blk lo hi <2= (ons_mem sm0.(ptt) (privmod mi)))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch (Some mi) sm0 sm1>>)
.
Proof.
  exploit Mem.free_right_extends; try apply MWF; eauto.
  {
    ii.
    exploit PRVTGT; et. intro T. r in T.
    inv MWF.
    exploit (PMPERM (Some mi) blk ofs); et.
    { ss. des_ifs. des_sumbool. ss. }
    intro U. des. r in U0. contradict U0. eauto with mem.
  }
  intro U; des. inv MWF.
  eexists (mk _ _ sm0.(ptt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
  - econs; ss; eauto.
Unshelve.
  all: ss.
Qed.

Lemma free_parallel
      sm0 lo hi blk m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk lo hi = Some m_src0)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<FREETGT: Mem.free sm0.(tgt) blk lo hi = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.free_parallel_extends; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ sm0.(ptt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
  - econs; ss; eauto.
  - econs; ss; eauto.
    etrans; et.
    u. ii. des. esplits; eauto with mem.
Unshelve.
  all: ss.
Qed.


Lemma store_parallel
      sm0 chunk v_src v_tgt blk ofs m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.store chunk sm0.(src) blk ofs v_src = Some m_src0)
      (SIMV: Val.lessdef v_src v_tgt)
:
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<STRTGT: Mem.store chunk sm0.(tgt) blk (ofs) v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.store_within_extends; try apply MWF; eauto. i; des.
  eexists (mk _ _ sm0.(ptt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
  - des. econs; ss; eauto.
  - econs; ss; eauto.
    inv MWF.
    etrans; et.
    u. ii. des. esplits; eauto with mem.
Qed.

Lemma store_right_pm
      mi sm0 chunk v_tgt ofs blk m_tgt0
      (MWF: wf' sm0)
      (PMTGT: brange blk (ofs) (ofs + size_chunk chunk) <2= (privmods mi sm0.(ptt)))
      (STRTGT: Mem.store chunk sm0.(tgt) blk (ofs) v_tgt = Some m_tgt0)
:
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch mi sm0 sm1>>)
.
Proof.
  exploit Mem.store_outside_extends; try apply MWF; eauto.
  { ii. unfold brange in *. exploit PMTGT; et.
    intro T.
    inv MWF.
    exploit PMPERM; et. intro U; des. rr in U0. eauto with mem.
  }
  intro U; des.
  eexists (mk _ _ sm0.(ptt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
  - econs; ss; eauto.
  - econs; ss; eauto.
    inv MWF.
    etrans; et.
Qed.

Lemma storev_parallel
      sm0 chunk v_src v_tgt addr_src addr_tgt m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.storev chunk sm0.(src) addr_src v_src = Some m_src0)
      (SIMADDR: Val.lessdef addr_src addr_tgt)
      (SIMV: Val.lessdef v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<STRTGT: Mem.storev chunk sm0.(tgt) addr_tgt v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.storev_extends; try apply MWF; eauto. i; des.
  unfold Mem.storev in STRSRC. des_ifs. inv SIMADDR. exploit store_parallel; eauto.
Qed.

End ORIGINALS.

