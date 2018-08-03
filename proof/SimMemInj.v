Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMem.
Require SimSymbId.
Require Import Conventions1 MachC.

Set Implicit Arguments.

(* Copied from CRELLVM *)
Inductive frozen (f_old f_new: meminj) (bound_src bound_tgt: block): Prop :=
| frozen_intro
    (NEW_IMPLIES_OUTSIDE:
       forall b_src b_tgt delta
              (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
         <<OUTSIDE_SRC: (bound_src <= b_src)%positive>> /\ <<OUTSIDE_TGT: (bound_tgt <= b_tgt)%positive>>)
.

Remark inject_separated_frozen
       f_old f_new m_src m_tgt
  :
    Events.inject_separated f_old f_new m_src m_tgt <->
    frozen f_old f_new m_src.(Mem.nextblock) m_tgt.(Mem.nextblock)
.
Proof.
  unfold Events.inject_separated in *.
  unfold Mem.valid_block in *.
  split; i.
  - econs; eauto.
    i. des.
    hexploit H; eauto. i; des.
    splits; xomega.
  - inv H.
    exploit NEW_IMPLIES_OUTSIDE; eauto.
    i; des.
    split; xomega.
Qed.

Lemma frozen_preserves_src
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_src
      (INSIDE: (b_src < bound_src)%positive)
  :
    <<PRESERVED: f_old b_src = f_new b_src>>
.
Proof.
  inv FROZEN.
  destruct (f_old b_src) eqn:T0; ss;
    destruct (f_new b_src) eqn:T1; ss.
  - destruct p, p0; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    exfalso.
    xomega.
Qed.

Lemma frozen_preserves_tgt
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_tgt
      (INSIDE: (b_tgt < bound_tgt)%positive)
  :
    <<PRESERVED: forall b_src delta (NOW: f_new b_src = Some (b_tgt, delta)),
      <<OLD: f_old b_src = Some (b_tgt, delta)>> >>
.
Proof.
  inv FROZEN.
  ii.
  destruct (f_old b_src) eqn:T; ss.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - exfalso.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    xomega.
Qed.

Lemma frozen_shortened
      f_old f_new
      bd_src0 bd_tgt0
      (FROZEN: frozen f_old f_new bd_src0 bd_tgt0)
      bd_src1 bd_tgt1
      (SHORT_SRC: (bd_src1 <= bd_src0)%positive)
      (SHORT_TGT: (bd_tgt1 <= bd_tgt0)%positive)
  :
    <<FROZEN: frozen f_old f_new bd_src1 bd_tgt1>>
.
Proof.
  inv FROZEN.
  econs; eauto.
  ii. des.
  hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
  split; ss.
  - red. etransitivity; eauto.
  - red. etransitivity; eauto.
Qed.

Lemma frozen_refl
      f
      bound_src bound_tgt
  :
    <<FROZEN: frozen f f bound_src bound_tgt>>
.
Proof.
  econs; eauto. i; des. clarify.
Qed.

Lemma loc_unmapped_frozen
      F F'
      fbound_src fbound_tgt
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_src)
      (UNMAPPED: loc_unmapped F b ofs)
  :
    loc_unmapped F' b ofs
.
Proof.
  unfold loc_unmapped in *.
  destruct (F' b) eqn:T; ss.
  destruct p; ss.
  inv FROZEN.
  exploit NEW_IMPLIES_OUTSIDE; eauto.
  i; des. xomega.
Qed.

Lemma loc_out_of_reach_frozen
      F F'
      fbound_src fbound_tgt
      (INCR: inject_incr F F')
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_tgt)
      m0 m1
      (UNMAPPED: loc_out_of_reach F m0 b ofs)
      (UNCHANGED: forall k p b0 delta (MAPPED: F b0 = Some (b, delta)),
          Mem.perm m0 b0 (ofs - delta) k p <-> Mem.perm m1 b0 (ofs - delta) k p)
  :
    loc_out_of_reach F' m1 b ofs
.
Proof.
  unfold loc_out_of_reach in *.
  i.
  exploit frozen_preserves_tgt; eauto.
  i. des.
  hexploit UNMAPPED; eauto. i.
  ii.
  contradict H1.
  eapply UNCHANGED; eauto.
Qed.


Section MEMINJ.

Context `{CTX: Val.meminj_ctx}.

Record t' := mk {
  src: mem;
  tgt: mem;
  inj: meminj;
  src_external: block -> Z -> Prop;
  tgt_external: block -> Z -> Prop;
  src_parent_nb: block;
  tgt_parent_nb: block;
}.

Definition update (sm0: t') (src tgt: mem) (inj: meminj): t' :=
  mk src tgt inj sm0.(src_external) sm0.(tgt_external) sm0.(src_parent_nb) sm0.(tgt_parent_nb)
.
Hint Unfold update.
(* Notation "sm0 '.(update_tgt)' tgt" := (sm0.(update) sm0.(src) tgt sm0.(inj)) (at level 50). *)
(* Definition update_tgt (sm0: t') (tgt: mem) := (sm0.(update) sm0.(src) tgt sm0.(inj)). *)
(* Definition update_src (sm0: t') (src: mem) := (sm0.(update) src sm0.(tgt) sm0.(inj)). *)
(* Hint Unfold update_src update_tgt. *)

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => m.(Mem.valid_block) b.
Hint Unfold valid_blocks.

Definition src_private (sm: t'): block -> Z -> Prop :=
  loc_unmapped sm.(inj) /2\ sm.(src).(valid_blocks)
.

Definition tgt_private (sm: t'): block -> Z -> Prop :=
  loc_out_of_reach sm.(inj) sm.(src) /2\ sm.(tgt).(valid_blocks)
.

Hint Unfold src_private tgt_private.

Lemma update_src_private
      sm0 sm1
      (INJ: sm0.(inj) = sm1.(inj))
      (SRC: sm0.(src).(Mem.nextblock) = sm1.(src).(Mem.nextblock))
  :
    sm0.(src_private) = (sm1).(src_private)
.
Proof.
  repeat (apply Axioms.functional_extensionality; i). apply prop_ext.
  u. split; ii; des; esplits; eauto with congruence.
Qed.

Lemma update_tgt_private
      sm0 sm1
      (SRC: sm0.(src) = sm1.(src))
      (TGT: sm0.(tgt).(Mem.nextblock) = sm1.(tgt).(Mem.nextblock))
      (INJ: sm0.(inj) = sm1.(inj))
  :
    sm0.(tgt_private) = sm1.(tgt_private)
.
Proof.
  repeat (apply Axioms.functional_extensionality; i). apply prop_ext.
  u. split; ii; des; esplits; eauto with congruence.
  - rewrite <- INJ. rewrite <- SRC. ss.
  - rewrite INJ. rewrite SRC. ss.
Qed.

(* Lemma update_src_private *)
(*       sm0 m_src *)
(*       (NB: sm0.(src).(Mem.nextblock) = m_src.(Mem.nextblock)) *)
(*   : *)
(*     sm0.(src_private) = (sm0.(update_src) m_src).(src_private) *)
(* . *)
(* Proof. *)
(*   repeat (apply Axioms.functional_extensionality; i). apply prop_ext. *)
(*   u. split; ii; des; esplits; eauto with congruence. *)
(* Qed. *)

(* Lemma update_tgt_private *)
(*       sm0 m_tgt *)
(*       (NB: sm0.(tgt).(Mem.nextblock) = m_tgt.(Mem.nextblock)) *)
(*   : *)
(*     sm0.(tgt_private) = (sm0.(update_tgt) m_tgt).(tgt_private) *)
(* . *)
(* Proof. *)
(*   repeat (apply Axioms.functional_extensionality; i). apply prop_ext. *)
(*   u. split; ii; des; esplits; eauto with congruence. *)
(* Qed. *)

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (PUBLIC: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
    (SRCEXT: sm0.(src_external) <2= sm0.(src_private))
    (TGTEXT: sm0.(tgt_external) <2= sm0.(tgt_private))
    (SRCLE: (sm0.(src_parent_nb) <= sm0.(src).(Mem.nextblock))%positive)
    (TGTLE: (sm0.(tgt_parent_nb) <= sm0.(tgt).(Mem.nextblock))%positive)
.

Inductive le' (mrel0 mrel1: t'): Prop :=
| le_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (SRCUNCHANGED: Mem.unchanged_on mrel0.(src_external) mrel0.(src) mrel1.(src))
    (TGTUNCHANGED: Mem.unchanged_on mrel0.(tgt_external) mrel0.(tgt) mrel1.(tgt))
    (SRCPARENTEQ: mrel0.(src_external) = mrel1.(src_external))
    (SRCPARENTEQNB: mrel0.(src_parent_nb) = mrel1.(src_parent_nb))
    (TGTPARENTEQ: mrel0.(tgt_external) = mrel1.(tgt_external))
    (TGTPARENTEQNB: mrel0.(tgt_parent_nb) = mrel1.(tgt_parent_nb))
    (FROZEN: frozen mrel0.(inj) mrel1.(inj) (mrel0.(src_parent_nb))
                                            (mrel0.(tgt_parent_nb)))
    (SRCBOUND: (mrel0.(src).(Mem.nextblock) <= mrel1.(src).(Mem.nextblock))%positive)
    (TGTBOUND: (mrel0.(tgt).(Mem.nextblock) <= mrel1.(tgt).(Mem.nextblock))%positive)
.

Definition lift' (mrel0: t'): t' :=
  (mk mrel0.(src) mrel0.(tgt) mrel0.(inj)
      mrel0.(src_private) mrel0.(tgt_private)
      mrel0.(src).(Mem.nextblock) mrel0.(tgt).(Mem.nextblock))
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mk mrel1.(src) mrel1.(tgt) mrel1.(inj)
      mrel0.(src_external) mrel0.(tgt_external)
      mrel0.(src_parent_nb) mrel0.(tgt_parent_nb))
.

Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
Next Obligation.
  econs; eauto; try reflexivity; try apply Mem.unchanged_on_refl; eauto.
  eapply frozen_refl; eauto.
Qed.
Next Obligation.
  ii. inv H; inv H0.
  des; clarify.
  econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + eapply Mem.unchanged_on_trans; eauto with congruence.
  + eapply Mem.unchanged_on_trans; eauto with congruence.
  + econs; eauto.
    ii; des.
    destruct (inj y b_src) eqn:T.
    * destruct p.
      exploit INCR0; eauto. i; clarify.
      inv FROZEN.
      hexploit NEW_IMPLIES_OUTSIDE; eauto.
    * inv FROZEN0.
      hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
      split; ss; red; etransitivity; eauto.
      { rewrite <- SRCPARENTEQNB. reflexivity. }
      { rewrite <- TGTPARENTEQNB. reflexivity. }
  + etransitivity; eauto.
  + etransitivity; eauto.
Qed.

(* TODO: Let's have this as policy. (giving explicit name) *)
(* TODO: apply this policy for identity/extension *)

(* "Global" is needed as it is inside section *)
Global Program Instance SimMemInj : SimMem.class :=
{
  t := t';
  src := src;
  tgt := tgt;
  wf := wf';
  le := le';
  lift := lift';
  unlift := unlift';
  sim_val := fun (mrel: t') => Val.inject mrel.(inj);
  sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
}.
Next Obligation.
  rename H into VALID.
  inv VALID. econs; ss; eauto; ii; des; ss; eauto.
  - eapply Pos.compare_gt_iff in H. xomega.
  - eapply Pos.compare_gt_iff in H. xomega.
  (* - econs; eauto. *)
  (*   ii; des. clarify. *)
  (* - eapply Mem.unchanged_on_refl. *)
  (* - eapply Mem.unchanged_on_refl. *)
Qed.
Next Obligation.
  inv H; ss.
  econs; ss; eauto; ii; des; ss.
  - eapply Mem.unchanged_on_implies; eauto.
    ii. eapply H0; eauto.
  - eapply Mem.unchanged_on_implies; eauto.
    ii. eapply H0; eauto.
  - inv H0. ss.
    eapply frozen_shortened; eauto.
Qed.
Next Obligation.
  inv H. inv H0. inv H1.
  des; clarify.
  econs; ss; try etransitivity; eauto. (* eauto did well here *)
  - (* etransitivity; eauto. *)
    rewrite SRCPARENTEQ.
    etransitivity; eauto.

    (* u. bar. i; des. esplits; eauto. *)
    (* + eapply loc_unmapped_frozen; eauto. *)
    (* + unfold Mem.valid_block in *. xomega. *)
  - (* etransitivity; eauto. *)
    rewrite TGTPARENTEQ.
    etransitivity; eauto.
Qed.
Next Obligation.
  ii. inv MLE. eapply val_inject_incr; eauto.
Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss.
    econs; eauto.
  - ginduction x0; ii; inv H; ss.
    econs; eauto.
Qed.

Section ORIGINALS.

Lemma store_mapped
      sm0 chunk v_src v_tgt blk_src ofs blk_tgt delta m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.store chunk sm0.(src) blk_src ofs v_src = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.store chunk sm0.(tgt) blk_tgt (ofs + delta) v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.store_mapped_inject; try apply MWF; eauto. i; des.
  inv MWF.
  eexists (mk _ _ _ _ _ _ _).
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto.
      ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
    + eapply Mem.store_unchanged_on; eauto.
      ii. apply TGTEXT in H2. red in H2. des. red in H2.
      eapply H2; eauto. clear - STRSRC H1 H4.
      apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC.
      eauto with mem xomega.
    + eapply frozen_refl.
    + erewrite <- Mem.nextblock_store; eauto. xomega.
    + erewrite <- Mem.nextblock_store; eauto. xomega.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR; eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_store; eauto. xomega.
    + etransitivity; eauto. erewrite <- Mem.nextblock_store; eauto. xomega.
Qed.
Lemma storev_mapped
      sm0 chunk v_src v_tgt addr_src addr_tgt m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.storev chunk sm0.(src) addr_src v_src = Some m_src0)
      (SIMADDR: Val.inject sm0.(inj) addr_src addr_tgt)
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.storev chunk sm0.(tgt) addr_tgt v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  admit "This should hold. - Mem.storev_mapped_inject".
Qed.
Lemma free_parallel
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<FREETGT: Mem.free sm0.(tgt) blk_tgt (lo + delta) (hi + delta) = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  admit "This should hold. - Mem.free_parallel_inject".
Qed.
Lemma free_left
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  admit "This should hold. - Mem.free_left_inject".
Qed.
Lemma free_right
      sm0 lo hi blk_tgt m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk_tgt lo hi = Some m_tgt0)
      (PRIVTGT: range lo hi <1= sm0.(tgt_private) blk_tgt)
  :
    exists sm1,
      (* (<<EXACT: sm1 = sm0.(update_tgt) m_tgt0>>) *)
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  admit "This should hold. - Mem.free_right_inject".
Qed.
Lemma alloc_parallel
      sm0 lo_src hi_src lo_tgt hi_tgt blk_src blk_tgt m_src0
      (MWF: wf' sm0)
      (ALCSRC: Mem.alloc sm0.(src) lo_src hi_src = (m_src0, blk_src))
      (LO: lo_tgt <= lo_src)
      (HI: hi_src <= hi_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<ALCTGT: Mem.alloc sm0.(tgt) lo_tgt hi_tgt = (sm1.(tgt), blk_tgt)>>)
      /\ (<<INJ: sm1.(inj) blk_src = Some (blk_tgt, 0) /\ forall b, b <> blk_src -> sm1.(inj) b = sm0.(inj) b>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  admit "This should hold. - Mem.alloc_parallel_inject".
Qed.
Lemma unfree_right
      sm0 lo hi blk m_tgt0
      (MWF: wf' sm0)
      (UNFR: Mem_unfree sm0.(tgt) blk lo hi = Some m_tgt0)
      (RANGE: brange blk lo hi <2= ~2 sm0.(tgt_external))
  :
    exists sm1,
      (* (<<EXACT: sm1 = sm0.(update_tgt) m_tgt0>>) *)
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exists (sm0.(update) sm0.(src) m_tgt0 sm0.(inj)).
  esplits; u; ss; eauto.
  - econs; ss; eauto.
    + inv MWF. eapply Mem_unfree_right_inject; eauto.
    + etransitivity; try eapply MWF; eauto.
    + etransitivity; try apply MWF; eauto.
      u. ii; des; esplits; eauto. erewrite <- Mem_valid_block_unfree; eauto.
    + etransitivity; try apply MWF; eauto. reflexivity.
    + etransitivity; try apply MWF; eauto. erewrite Mem_nextblock_unfree; eauto. refl.
  - econs; ss; eauto.
    + refl.
    + eapply Mem_unfree_unchanged_on; eauto.
    + eapply frozen_refl.
    + refl.
    + erewrite Mem_nextblock_unfree; eauto. refl.
Qed.
End ORIGINALS.

Lemma alloc_left_zero_simmem
      sm0
      (MWF: SimMem.wf sm0)
      blk_src sz m_src1 blk_tgt
      (ALLOC: Mem.alloc sm0.(SimMem.src) 0 sz = (m_src1, blk_src))
      (TGTPRIV: (range 0 sz) <1= sm0.(tgt_private) blk_tgt)
      (TGTNOTEXT: ((range 0 sz) /1\ sm0.(tgt_external) blk_tgt) <1= bot1)
      (TGTPERM: forall ofs k p (BOUND: 0 <= ofs < sz), Mem.perm sm0.(SimMem.tgt) blk_tgt ofs k p)
      (* (SZPOS: 0 < sz) *)
      (VALID: Mem.valid_block sm0.(tgt) blk_tgt)
      (PARENT: (sm0.(tgt_parent_nb) <= blk_tgt)%positive)
  :
    let sm1 := (mk m_src1
                   sm0.(tgt)
                   (fun blk => if eq_block blk blk_src
                               then Some (blk_tgt, 0)
                               else sm0.(inj) blk)
                         sm0.(src_external) sm0.(tgt_external)
                         sm0.(src_parent_nb) sm0.(tgt_parent_nb)) in
    <<MWF: SimMem.wf sm1>>
    /\
    <<MLE: SimMem.le sm0 sm1>>
.
Proof.
  i. subst_locals.
  inv MWF; ss.
  (* assert(VALID: Mem.valid_block (m_tgt sm0) blk_tgt). *)
  (* { specialize (TGTPRIV 0). eapply TGTPRIV. u. lia. } *)
  exploit Mem.alloc_result; eauto. i; clarify.
  esplits; eauto.
  * econs; ss; eauto.
    - eapply Mem_alloc_left_inject; eauto.
      ii. eapply TGTPRIV; eauto.
    - etransitivity; eauto.
      u. ii; ss. des.
      esplits; eauto.
      + hnf. des_ifs. exfalso. unfold Mem.valid_block in *. xomega.
      + eauto with mem.
    - u. ii; ss. dup PR. eapply TGTEXT in PR0. u in PR0. des.
      esplits; eauto.
      hnf. hnf in PR0. ii. des_ifs; eauto.
      + eapply TGTNOTEXT; eauto. esplits; eauto. u. rewrite Z.sub_0_r in *.
        apply NNPP. ii. eapply Mem_alloc_fresh_perm; eauto.
      + eapply PR0; eauto. eauto with mem.
    - etransitivity; eauto.
      exploit Mem.nextblock_alloc; eauto. i. rewrite H. xomega.
  * econs; cbn; eauto with mem; try xomega.
    - ii; ss. des_ifs; ss. exfalso.
      exploit Mem.mi_freeblocks; try apply MWF; eauto.
      { eauto with mem. }
      i; ss. clarify.
    - eapply Mem_unchanged_on_trans_strong; eauto.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eauto with mem.
    - econs; eauto.
      ii; ss. des; ss. des_ifs.
    - exploit Mem.nextblock_alloc; eauto. i. rewrite H. xomega.
Qed.

Lemma store_undef_simmem
      sm0
      (MWF: SimMem.wf sm0)
      chunk blk ofs m_src1
      (STORE: Mem.store chunk sm0.(SimMem.src) blk ofs Vundef = Some m_src1)
      (PUBLIC: ~ sm0.(src_private) blk ofs)
  :
    let sm1 := (mk m_src1 sm0.(tgt) sm0.(inj)
                         sm0.(src_external) sm0.(tgt_external)
                         sm0.(src_parent_nb) sm0.(tgt_parent_nb)) in
    <<MWF: SimMem.wf sm1>> /\
    <<MLE: SimMem.le sm0 sm1>>
.
Proof.
  inv STORE.
  exploit Mem_store_mapped_inject_undef; try apply MWF; eauto.
  i; des. inv MWF.
  subst_locals.
  esplits; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. u. ii; des; esplits; eauto with mem.
    + etransitivity; eauto. u. unfold loc_out_of_reach. ii; des; esplits; eauto with mem.
      ii. eapply PR; eauto. eauto with mem.
    + etransitivity; eauto. eauto with mem.
      exploit Mem.nextblock_store; eauto. i. rewrite H1. xomega.
  - econs; ss; eauto with mem; try xomega.
    + eapply Mem.unchanged_on_implies with (P:= sm0.(src_private)).
      { eapply Mem.store_unchanged_on; eauto. }
      i. eauto.
    + eapply frozen_refl; eauto.
    + exploit Mem.nextblock_store; eauto. i. rewrite H1. xomega.
Qed.

(* Lemma store_stored_simmem *)
(*       sm0 *)
(*       (MWF: SimMem.wf sm0) *)
(*       m_src1 *)
(*       v_src v_tgt *)
(*       (INJV: Val.inject sm0.(inj) v_src v_tgt)  *)
(*       ty rsp_src rsp_tgt rspdelta ofs *)
(*       (SRC: Mem.storev (chunk_of_type ty) sm0.(src) (Vptr rsp_src ofs true) v_src = Some m_src1) *)
(*       (TGT: Mem_stored (chunk_of_type ty) sm0.(tgt) rsp_tgt (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) v_tgt) *)
(*       (INJRSP: sm0.(inj) rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned))) *)
(*       (BOUND: Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta <= Ptrofs.max_unsigned) *)
(*   : *)
(*     let sm1 := (mk sm0.(inj) m_src1 sm0.(tgt) *)
(*                          sm0.(src_external) sm0.(tgt_external) *)
(*                          sm0.(src_parent_nb) sm0.(tgt_parent_nb)) in *)
(*     <<MWF: SimMem.wf sm1>> /\ *)
(*     <<MLE: SimMem.le sm0 sm1>> *)
(* . *)
(* Proof. *)
(*   exploit store_stored_inject; eauto. { apply MWF. } i; des. *)
(*   subst_locals. inv MWF. *)
(*   esplits; eauto. *)
(*   - econs; ss; eauto. *)
(*     + etransitivity; eauto. u; ss. ii; des. esplits; eauto with mem. *)
(*     + etransitivity; eauto. u. unfold loc_out_of_reach. ii; des; esplits; eauto with mem. *)
(*       ii. eapply PR; eauto. eauto with mem. *)
(*     + etransitivity; eauto. eauto with mem. *)
(*       exploit Mem.nextblock_store; eauto. i. rewrite H0. xomega. *)
(*   - econs; ss; eauto with mem; try xomega. *)
(*     + eapply Mem.unchanged_on_implies with (P:= sm0.(src_private)). *)
(*       { eapply Mem.store_unchanged_on; eauto. u. unfold loc_unmapped. ii; des; ss. clarify. } *)
(*       i. eauto. *)
(*     + eapply frozen_refl; eauto. *)
(*     + exploit Mem.nextblock_store; eauto. i. rewrite H0. xomega. *)
(* Qed. *)

Local Opaque Z.mul.

Lemma mach_store_arguments_simmem
      sm0 rs vs sg m_tgt0
      (MWF: SimMem.wf sm0)
      (STORE: store_arguments sm0.(SimMem.tgt) rs vs sg m_tgt0)
      (*** TODO: don't use unchanged_on, it is needlessly complex for our use. just define my own. *)
  :
    exists sm1,
    <<SM: sm1 = (mk sm0.(src) m_tgt0 sm0.(inj)
                         sm0.(src_external) sm0.(tgt_external)
                         sm0.(src_parent_nb) sm0.(tgt_parent_nb))>> /\
    <<MWF: SimMem.wf sm1>> /\
    <<MLE: SimMem.le sm0 sm1>> /\
    <<PRIV: forall ofs (IN: 0 <= ofs < 4 * size_arguments sg),
             sm1.(tgt_private) sm0.(SimMem.tgt).(Mem.nextblock) ofs>>
.
Proof.
  i. subst_locals.
  inv STORE.
  exploit Mem.alloc_right_inject; try apply MWF; eauto. i; des.
  hexpl Mem.alloc_result. clarify.
  hexpl Mem.nextblock_alloc.
  esplits; eauto.
  - econs; ss; try apply MWF; eauto.
    + eapply Mem.inject_extends_compose; eauto.
      admit "ez".
    + etransitivity; try apply MWF; eauto.
      unfold tgt_private. ss. u. ii; des. esplits; eauto with congruence.
      unfold Mem.valid_block in *. rewrite <- NB in *. eauto with xomega.
    + etransitivity; try apply MWF; eauto with mem congruence.
      rewrite <- NB. lia.
  - econs; ss; eauto with mem xomega.
    + inv MWF.
      etrans.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eapply Mem.unchanged_on_implies; eauto.
      i. ss. des_ifs. apply TGTEXT in H0. u in H0. des.
      exfalso. eapply Mem.fresh_block_alloc; eauto.
    + eapply frozen_refl.
    + rewrite <- NB. eauto with xomega.
  - ii. u. esplits; eauto.
    + ii.
      exploit Mem.mi_perm; try apply MWF; eauto. i.
      zsimpl.
      hexpl Mem_alloc_fresh_perm. eapply NOPERM; eauto.
    + unfold Mem.valid_block. rewrite <- NB. ss. eauto with xomega.
Qed.


End MEMINJ.

Hint Unfold valid_blocks src_private tgt_private range.









Section SIMSYMB.

Context `{CTX: Val.meminj_ctx}.

Inductive skenv_inject (skenv: SkEnv.t) (j: meminj): Prop :=
| sken_inject_intro
    (DOMAIN: forall b, Plt b skenv.(Genv.genv_next) -> j b = Some(b, 0))
    (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 skenv.(Genv.genv_next) -> b1 = b2)
.

Inductive sim_skenv_inj (sm: SimMem.t) (__noname__: unit) (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INJECT: skenv_inject skenv_src sm.(inj))
    (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_parent_nb))
    (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_parent_nb))
    (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
.

Global Program Instance SimSymbId: SimSymb.class SimMemInj := {
  t := unit;
  le := SimSymbId.le;
  sim_sk := SimSymbId.sim_sk;
  sim_skenv := sim_skenv_inj;
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
  eexists. eexists (mk m_src m_src (Mem.flat_inj m_src.(Mem.nextblock))
                       bot2 bot2 m_src.(Mem.nextblock) m_src.(Mem.nextblock)). ss.
  esplits; ss; eauto.
  - econs; ss; eauto.
    + econs; eauto; ii; ss.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto. reflexivity.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto. reflexivity.
  - econs; ss; try xomega; ii; des; ss; eauto.
    eapply Genv.initmem_inject; eauto.
    u in *. eauto.
Qed.
Next Obligation.
  inv SIMSKENV. inv INJECT.
  econs; eauto.
  econs; eauto.
  - ii. exploit DOMAIN; eauto. i. eapply MLE; eauto.
  - ii. inv MLE.
    eapply IMAGE; eauto.
    erewrite frozen_preserves_tgt; eauto.
    eapply Plt_Ple_trans; eauto.
  - inv MLE. eauto with congruence.
  - inv MLE. eauto with congruence.
Qed.
Next Obligation.
  inv MWF. inv SIMSKENV.
  econs; eauto.
  - etransitivity; try apply SRCLE; eauto.
  - etransitivity; try apply TGTLE; eauto.
Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto.
  i; des.
  inv SIMSKENV. inv LESRC. inv LETGT.
  econs; eauto.
  { inv INJECT.
    econs; ii; eauto.
    - eapply DOMAIN; eauto. rewrite NEXT. ss.
    - eapply IMAGE; eauto. rewrite NEXT. ss.
  }
  { rewrite <- NEXT. ss. }
  { rewrite <- NEXT. ss. }
Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto. { eapply SIMSKENV. } i; des.
  inv H. inv SIMSKENV. inv INJECT. inv SIMSKENV0.
  econs; eauto.
  - ii; ss.
    eapply FUNCFSIM; eauto.
    rpapply FUNCSRC. f_equal.
    { inv SIMFPTR; ss. des_ifs. rewrite Ptrofs.add_zero_l.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      exploit DOMAIN; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify. }
  - ii; ss.
    eapply FUNCBSIM; eauto.
    rpapply FUNCTGT. f_equal.
    { inv SIMFPTR; ss. des_ifs.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      exploit IMAGE; eauto. { rewrite NEXT. eapply Genv.genv_defs_range; eauto. } i; clarify.
      exploit DOMAIN; eauto. { rewrite <- DEFS in *. eapply Genv.genv_defs_range; eauto. } i; clarify.
      rewrite e. rewrite Ptrofs.add_zero in *. clarify.
    }
Qed.

End SIMSYMB.
