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
Require Import AxiomsC.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require SimSymbId.
Require Import SimMemLift.
Require Import MemoryC2.

Set Implicit Arguments.




(** TODO: move to proper place: MemoryC **)
Lemma Mem_unfree_left_extends
      m_src0 m_src1 blk lo hi m_tgt0
      (EXT: Mem.extends m_src0 m_tgt0)
      (UNFREESRC: Mem_unfree m_src0 blk lo hi = Some m_src1)
      (PERMTGT: Mem.range_perm m_tgt0 blk lo hi Cur Freeable)
  :
    <<EXT: Mem.extends m_src1 m_tgt0>>
.
Proof.
  unfold Mem_unfree in *. ss. des_ifs.
  inv EXT; ss. econs; ss; et.
  - econs; ss; et.
    + inv mext_inj. ii. unfold Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * ss.
        bsimpl. des. des_sumbool.
        exploit PERMTGT; et. intro T. unfold Mem.perm in T.
        unfold inject_id in *. clarify. zsimpl.
        clear - H0 T.
        eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto.
      * exploit mi_perm; et.
      * exploit mi_perm; et.
    + inv mext_inj. ii. unfold Mem.range_perm, Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * unfold inject_id in *. clarify. exists 0. xomega.
      * exploit mi_align; et.
    + inv mext_inj. ii. unfold Mem.perm in H0. ss.
      rewrite PMap.gsspec in *. des_ifs.
      * ss.
        bsimpl. des. des_sumbool.
        exploit PERMTGT; et. intro T. unfold Mem.perm in T.
        unfold inject_id in *. clarify. zsimpl.
        rewrite Mem_setN_in_repeat; ss.
        { econs; et. }
        { rewrite Z2Nat_range. des_ifs; try xomega. }
      * rewrite Mem.setN_outside; eauto.
        bsimpl. unfold inject_id in *. clarify.
        rewrite length_list_repeat.
        rewrite Z2Nat_range. des_ifs; try xomega.
        des; des_sumbool; try xomega.
      * unfold inject_id in *. clarify. exploit mi_memval; et.
  - ii.
    exploit mext_perm_inv; et. intro T. des.
    + left.
      unfold Mem.perm. ss.
      rewrite PMap.gsspec in *. des_ifs. bsimpl. des. des_sumbool. ss. econs; et.
    + destruct (classic (b = blk /\ lo <= ofs < hi)).
      * left.
        unfold Mem.perm. ss.
        rewrite PMap.gsspec in *. des_ifs; bsimpl; des; des_sumbool; ss. econs; et.
      * right.
        unfold Mem.perm. ss.
        rewrite PMap.gsspec in *. des_ifs. bsimpl. des. des_sumbool. ss. ii.
        apply not_and_or in H0. des; ss. xomega.
Qed.

Local Transparent Mem.loadbytes.
Lemma Mem_unfree_loadbytes
      m0 blk lo hi m1
      (UNFREE: Mem_unfree m0 blk lo hi = Some m1)
  :
    <<UNDEF: Mem.loadbytes m1 blk lo (hi - lo) = Some (list_repeat (Z.to_nat (hi - lo)) Undef)>>
.
Proof.
  hexploit Mem_unfree_perm; eauto. intro PERM.
  unfold Mem_unfree in *. des_ifs.
  unfold Mem.loadbytes. ss. des_ifs; cycle 1.
  { contradict n. ii.
    exploit (PERM Cur Readable ofs); eauto; ss.
    xomega.
  }
  r. f_equal.
  rewrite PMap.gsspec. des_ifs.
  rp; try rewrite Mem.getN_setN_same; eauto.
  rewrite length_list_repeat. ss.
Qed.
Local Opaque Mem.loadbytes.








(** TODO: move to proper place **)
Definition ons_mem (ptt: partition) (ons: ownership): block -> Z -> Prop :=
  fun b ofs => (ptt b ofs) = ons
.
Hint Unfold ons_mem.
Hint Unfold privmods privmod_others.

Lemma ons_mem_privmods
      ptt mi
  :
    ons_mem ptt (privmod mi) = privmods (Some mi) ptt
.
Proof.
  u. apply func_ext2. ii. apply prop_ext. split; i; des_ifs; des_sumbool; clarify; ss.
Qed.

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



Definition le': t' -> t' -> Prop := top2.

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
  unchanged_on := Mem.unchanged_on;
}.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext1.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. econs; eauto.
  - induction H; econs; eauto.
Qed.
Next Obligation. inv H. ss. Qed.
Next Obligation. ii. eapply Mem.unchanged_on_implies; et. Qed.

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
  { econs; ss; et.
    - exploit external_call_readonly; try apply SYSSRC; eauto. intro T.
      eapply Mem.unchanged_on_implies; eauto.
      u. ii. des_ifs.
      inv MWF. ss.
      exploit (PMPERM (Some mi)); et.
      { u. rewrite Heq. des_sumbool; ss. }
      intro U; des. eauto with mem.
    - eapply Mem.unchanged_on_implies; eauto.
      u. ii. des_ifs.
      inv MWF. ss.
      exploit (PMPERM (Some mi)); et.
      { u. rewrite Heq. des_sumbool; ss. }
      intro U; des. eauto with mem.
  }
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
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
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
    + eapply Mem.free_unchanged_on; eauto. u. ii.
      des_ifs. exploit (PMPERM (Some mi)); eauto.
      { u. rewrite Heq. des_sumbool; ss. }
      intro T; des. rr in T0. eapply T0. eapply Mem.free_range_perm in FREESRC. eauto with mem xomega.
    + refl.
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
      (* (PRVTGT: brange blk lo hi <2= (ons_mem sm0.(ptt) (privmod mi))) *)
      (PMTGT: brange blk lo hi <2= (privmods mi sm0.(ptt)))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch mi sm0 sm1>>)
      /\ (<<PMLE: forall mi, privmods mi sm0.(ptt) <2= privmods mi sm1.(ptt)>>)
.
Proof.
  exploit Mem.free_right_extends; try apply MWF; eauto.
  {
    ii.
    exploit PMTGT; et. intro T. r in T.
    inv MWF.
    exploit (PMPERM mi blk ofs); et.
    intro U. des. r in U0. contradict U0. eauto with mem.
  }
  intro U; des. inv MWF.
  eexists (mk _ _ sm0.(ptt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + eapply Mem.free_unchanged_on; et.
      u. ii. des_ifs_safe.
      exploit PMTGT; et. intro Y. u in *; des_ifs.
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
    + eapply Mem.free_unchanged_on; eauto. u. ii.
      des_ifs. exploit (PMPERM (Some mi)); eauto.
      { u. rewrite Heq. des_sumbool; ss. }
      intro T; des. rr in T0. eapply T0. eapply Mem.free_range_perm in FREESRC. eauto with mem xomega.
    + eapply Mem.free_unchanged_on; eauto. u. ii.
      des_ifs. exploit (PMPERM (Some mi)); eauto.
      { u. rewrite Heq. des_sumbool; ss. }
      intro T; des. rr in T0. eapply T0. eapply Mem.free_range_perm in FREESRC. eauto with mem xomega.
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
  - des. inv MWF.
    econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto. u. ii.
      des_ifs. exploit (PMPERM (Some mi)); eauto.
      { u. rewrite Heq. des_sumbool; ss. }
      intro T; des. rr in T0. eapply T0.
      apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
    + eapply Mem.store_unchanged_on; eauto. u. ii.
      des_ifs. exploit (PMPERM (Some mi)); eauto.
      { u. rewrite Heq. des_sumbool; ss. }
      intro T; des. rr in T0. eapply T0.
      apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
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
      /\ (<<PMLE: forall mi, privmods mi sm0.(ptt) <2= privmods mi sm1.(ptt)>>)
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
  - inv MWF.
    econs; ss; eauto.
    + refl.
    + eapply Mem.store_unchanged_on; eauto. ii.
      exploit PMTGT; et. intro T. unfold privmods in *. des_ifs. des_sumbool. clarify.
      u in H0. des_ifs. bsimpl. des_sumbool. ss.
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

Lemma unfree_left
      mi sm0 lo hi blk m_src0
      (MWF: wf' sm0)
      (UNFREESRC: Mem_unfree sm0.(src) blk lo hi = Some m_src0)
      (PMSRC: brange blk lo hi <2= (privmods mi sm0.(ptt)))
      (PERMTGT: Mem.range_perm sm0.(tgt) blk lo hi Cur Freeable)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch mi sm0 sm1>>)
      /\ (<<PMSRC: (brange blk lo hi) <2= ons_mem sm1.(ptt) etc>>)
.
Proof.
  exploit Mem_unfree_left_extends; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _
              (fun b ofs => if (eq_block b blk) && (lo <=? ofs) && (ofs <? hi)
                            then etc
                            else sm0.(ptt) b ofs)
          ).
  dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem_unfree_unchanged_on0; eauto. ii.
      exploit PMSRC; et. intro T. u in T. u in H0. des_ifs.
    + refl.
    + u. ii. des_ifs_safe. bsimpl; des; des_sumbool.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *. clarify.
      exfalso.
      exploit (PMSRC blk x1); ss. intro T. u in T. des_ifs. des_sumbool. clarify.
    + u. ii. des_ifs_safe. bsimpl; des; des_sumbool.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *. clarify.
      exfalso.
      exploit (PMSRC blk x1); ss. intro T. u in T. des_ifs. des_sumbool. clarify.
  - u. ii. des. clarify. rewrite <- Z.leb_le in *. rewrite <- Z.ltb_lt in *. des_ifs.
    bsimpl. des_sumbool; congruence.
  - des. clear_tac.
    econs; ss; eauto.
    intros mj b ofs. specialize (PMPERM mj b ofs). ss.
    u. u in PMPERM. ii. des_ifs_safe.
    des_sumbool. clarify.
    (* Set Printing All. *)
    destruct (eq_block b blk && (lo <=? ofs) && (ofs <? hi)) eqn:T.
    + unfold not in *. rewrite T in *. ss.
    + unfold not in *. rewrite T in *. clear_tac.
      exploit PMPERM; et. i; des.
      esplits; eauto with mem.
      * erewrite <- Mem_valid_block_unfree; eauto.
      * exploit Mem_unfree_unchanged_on; eauto. intro U. inv U.
        ii. exploit (unchanged_on_perm b ofs); eauto.
        { u. ii. des; clarify. bsimpl.
          rewrite Z.leb_nle in *. rewrite Z.ltb_nlt in *. des; des_sumbool; clarify; try xomega.
        }
        intro U. rewrite U in *. ss.
Unshelve.
  all: ss.
Qed.

End ORIGINALS.

