Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMemLift.
Require Import AxiomsC.
Require Import Conventions1.
(* Require Import SimMemInj. *)

Set Implicit Arguments.




Inductive ownership: Type :=
| privmod (mi: string)
| external
| priv
| pub
.

Definition ownership_dec (ons0 ons1: ownership): {ons0 = ons1} + {ons0 <> ons1}.
  decide equality.
  - apply string_dec.
Defined.

Definition is_privmod (ons: ownership) (mi: Midx.t): bool :=
  match mi with
  | Some mi =>
    match ons with
    | privmod mj => string_dec mi mj
    | _ => false
    end
  | _ => false
  end
.

Definition ownership_to_ownership (ons: ownership): SimMem.ownership :=
  match ons with
  | privmod mi => SimMem.privmod mi
  | _ => SimMem.etc
  end
.

Coercion ownership_to_ownership: ownership >-> SimMem.ownership.

Notation partition := (block -> Z -> ownership).

Definition ownership_mem_bool (ptt: partition) (ons: ownership): block -> Z -> bool :=
  fun b ofs => ownership_dec (ptt b ofs) ons
.

Definition ownership_mem (ptt: partition) (ons: ownership): block -> Z -> Prop :=
  fun b ofs => (ptt b ofs) = ons
.

Hint Unfold ownership_mem.


Section MEMINJ.

(* Local Existing Instance Val.mi_normal. *)
(* Variable gbound_src gbound_tgt: block. *)

Record t' := mk {
  src: mem;
  tgt: mem;
  inj: meminj;
  ptt_src: partition;
  ptt_tgt: partition;
}.

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => (Mem.valid_block m) b.
Hint Unfold valid_blocks.

Definition external_src (sm: t'): block -> Z -> Prop :=
  fun b ofs => sm.(ptt_src) b ofs = external
.

Definition external_tgt (sm: t'): block -> Z -> Prop :=
  fun b ofs => sm.(ptt_tgt) b ofs = external
.

Definition private_src (sm: t'): block -> Z -> Prop :=
  loc_unmapped sm.(inj) /2\ (valid_blocks sm.(src)).

Definition private_tgt (sm: t'): block -> Z -> Prop :=
  loc_out_of_reach sm.(inj) sm.(src) /2\ (valid_blocks sm.(tgt)).

Definition public_src (sm: t'): block -> Z -> Prop := ~2 (private_src sm).

Definition public_tgt (sm: t'): block -> Z -> Prop := ~2 (private_tgt sm).

Goal forall X Y (P Q: X -> Y -> Prop), (P = Q) <-> all2 (P <2> Q).
Proof.
  ii. split; i; clarify. eapply func_ext2. ii. eapply prop_ext. et.
Qed.

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (PUBLIC: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
    (* (PTTSRC: (public_src sm0) = (ownership_mem sm0.(ptt_src) pub)) *)
    (* (PTTTGT: (public_tgt sm0) = (ownership_mem sm0.(ptt_tgt) pub)) *)
    (PTTSRC: all2 ((public_src sm0) <2> (ownership_mem sm0.(ptt_src) pub)))
    (PTTTGT: all2 ((public_tgt sm0) <2> (ownership_mem sm0.(ptt_tgt) pub)))
.

Inductive le' (mrel0 mrel1: t'): Prop :=
| le_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (UNCHSRC: Mem.unchanged_on (external_src mrel0) mrel0.(src) mrel1.(src))
    (UNCHTGT: Mem.unchanged_on (external_tgt mrel0) mrel0.(tgt) mrel1.(tgt))
    (PUBSRC: (public_src mrel0) <2= (public_src mrel1))
    (PUBTGT: (public_tgt mrel0) <2= (public_tgt mrel1))
    (EXTSRC: (external_src mrel0) <2= (external_src mrel1))
    (EXTTGT: (external_tgt mrel0) <2= (external_tgt mrel1))
    (PMSRC: forall mi, (ownership_mem mrel0.(ptt_src) (privmod mi)) <2=
                       (ownership_mem mrel1.(ptt_src) (privmod mi)))
    (PMTGT: forall mi, (ownership_mem mrel0.(ptt_tgt) (privmod mi)) <2=
                       (ownership_mem mrel1.(ptt_tgt) (privmod mi)))
    (MAXSRC: forall b ofs
        (VALID: Mem.valid_block mrel0.(src) b),
        <<MAX: Mem.perm mrel1.(src) b ofs Max <1= Mem.perm mrel0.(src) b ofs Max>>)
    (MAXTGT: forall b ofs
        (VALID: Mem.valid_block mrel0.(tgt) b),
        <<MAX: Mem.perm mrel1.(tgt) b ofs Max <1= Mem.perm mrel0.(tgt) b ofs Max>>)
.

Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
Next Obligation.
  econs; eauto; try reflexivity; try apply Mem.unchanged_on_refl; eauto.
Qed.
Next Obligation.
  ii. inv H; inv H0. des; clarify.
  econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + eapply Mem.unchanged_on_trans.
    { eauto with congruence. }
    eapply Mem.unchanged_on_implies; eauto.
  + eapply Mem.unchanged_on_trans.
    { eauto with congruence. }
    eapply Mem.unchanged_on_implies; eauto.
  + etrans; et.
  + etrans; et.
  + i. r. etransitivity.
    { eapply MAXSRC0; eauto. eapply Plt_Ple_trans; eauto with mem. }
    eapply MAXSRC; eauto.
  + i. r. etransitivity.
    { eapply MAXTGT0; eauto. eapply Plt_Ple_trans; eauto with mem. }
    eapply MAXTGT; eauto.
Qed.

Definition lift_ptt (ptt: partition): partition :=
  fun b ofs =>
    match ptt b ofs with
    | privmod mi => privmod mi
    | external => external
    | priv => external
    | pub => pub
    end
.

Definition lift' (mrel0: t'): t' :=
  (mk mrel0.(src) mrel0.(tgt) mrel0.(inj)
      (lift_ptt (ptt_src mrel0)) (lift_ptt (ptt_tgt mrel0))
  ).

Definition unlift_ptt (ptt0 ptt1: partition): partition :=
  fun b ofs =>
    match ptt1 b ofs with
    | privmod mi => privmod mi
    | external =>
      match ptt0 b ofs with
      | external => external
      | _ => priv (** _ should be "priv". other cases should not happen **)
      end
    | priv => external (** ? **)
    | pub => pub
    end
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mk mrel1.(src) mrel1.(tgt) mrel1.(inj)
      (unlift_ptt (ptt_src mrel0) (ptt_src mrel1)) (unlift_ptt (ptt_tgt mrel0) (ptt_tgt mrel1))
  ).

Hint Unfold lift_ptt unlift_ptt lift' unlift'.

Lemma unlift_spec : forall mrel0 mrel1 : t',
                  le' (lift' mrel0) mrel1 -> wf' mrel0 -> le' mrel0 (unlift' mrel0 mrel1).
Proof.
  i. inv H; ss. econs; ss; eauto; ii; des; ss.
  - eapply Mem.unchanged_on_implies; eauto. ii. unfold external_src in *. ss. unfold lift_ptt. des_ifs.
  - eapply Mem.unchanged_on_implies; eauto. ii. unfold external_tgt in *. ss. unfold lift_ptt. des_ifs.
  - clear - EXTSRC PR. unfold external_src in *. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (EXTSRC x0 x1). ss. rewrite PR in *. rewrite EXTSRC; ss.
  - clear - EXTTGT PR. unfold external_tgt in *. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (EXTTGT x0 x1). ss. rewrite PR in *. rewrite EXTTGT; ss.
  - clear - PMSRC PR. unfold ownership_mem in *. des_sumbool. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (PMSRC mi x0 x1). ss. rewrite PR in *.
    hexploit1 PMSRC. { des_sumbool; ss. } des_sumbool. des_ifs.
  - clear - PMTGT PR. unfold ownership_mem in *. des_sumbool. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (PMTGT mi x0 x1). ss. rewrite PR in *.
    hexploit1 PMTGT. { des_sumbool; ss. } des_sumbool. des_ifs.
Qed.

Lemma unlift_wf : forall mrel0 mrel1 : t',
                wf' mrel0 ->
                wf' mrel1 -> le' (lift' mrel0) mrel1 -> wf' (unlift' mrel0 mrel1).
Proof.
  i. inv H. inv H0. inv H1. des; clarify.
  econs; ss.
  -
    intros b ofs.
    unfold public_src, private_src. ss. split; i.
    + unfold unlift_ptt.
      specialize (PTTSRC0 b ofs).
      apply proj1 in PTTSRC0.
      apply not_and_or in H. des.
      * unfold loc_unmapped in *. unfold ownership_mem. des_sumbool.
        exploit PTTSRC0.
        { unfold public_src. ii. eapply H. unfold private_src in *. des; ss. }
        intro T. unfold ownership_mem in *. des_sumbool. rewrite T. ss.
      * exploit PTTSRC0.
        { unfold public_src. ii. eapply H. unfold private_src in *. des; ss. }
        intro T. unfold ownership_mem in *. des_sumbool. rewrite T. ss.
    + unfold unlift_ptt in *.
      specialize (PTTSRC0 b ofs).
      apply proj2 in PTTSRC0.
      eapply or_not_and.
      unfold loc_unmapped in *. unfold ownership_mem in *. des_sumbool.
      des_ifs.
      hexploit PTTSRC0.
      { des_sumbool. ss. }
      intro T. unfold public_src, private_src in T. apply not_and_or in T. ss.
  -
    intros b ofs.
    unfold public_tgt, private_tgt. ss. split; i.
    + unfold unlift_ptt.
      specialize (PTTTGT0 b ofs).
      apply proj1 in PTTTGT0.
      apply not_and_or in H. des.
      * unfold loc_unmapped in *. unfold ownership_mem. des_sumbool.
        exploit PTTTGT0.
        { unfold public_tgt. ii. eapply H. unfold private_tgt in *. des; ss. }
        intro T. unfold ownership_mem in *. des_sumbool. rewrite T. ss.
      * exploit PTTTGT0.
        { unfold public_tgt. ii. eapply H. unfold private_tgt in *. des; ss. }
        intro T. unfold ownership_mem in *. des_sumbool. rewrite T. ss.
    + unfold unlift_ptt in *.
      specialize (PTTTGT0 b ofs).
      apply proj2 in PTTTGT0.
      eapply or_not_and.
      unfold loc_unmapped in *. unfold ownership_mem in *. des_sumbool.
      des_ifs.
      hexploit PTTTGT0.
      { des_sumbool. ss. }
      intro T. unfold public_tgt, private_tgt in T. apply not_and_or in T. ss.
Qed.

(* Lemma after_private_src *)
(*       sm0 sm1 *)
(*       (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock)) *)
(*       (MLE: le' (lift' sm0) sm1): *)
(*     (src_private sm0) <2= (src_private sm1). *)
(* Proof. *)
(*   inv MLE. inv SRCUNCHANGED. ss. *)
(*   unfold src_private, valid_blocks; ii; des; esplits; eauto. *)
(*   - eapply loc_unmapped_frozen; eauto. *)
(*   - unfold Mem.valid_block in *. xomega. *)
(* Qed. *)

(* Lemma after_private_tgt *)
(*       sm0 sm1 *)
(*       (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock)) *)
(*       (MWF: wf' sm0) *)
(*       (MLE: le' (lift' sm0) sm1): *)
(*     (tgt_private sm0) <2= (tgt_private sm1). *)
(* Proof. *)
(*   inv MLE. inv TGTUNCHANGED. ss. *)
(*   unfold tgt_private, valid_blocks; ii; des; esplits; eauto. *)
(*   - eapply loc_out_of_reach_frozen; eauto. ii. *)
(*     assert(VALID: Mem.valid_block (src sm0) b0). *)
(*     { apply Classical_Prop.NNPP. ii. exploit Mem.mi_freeblocks; try apply MWF; eauto. ii. clarify. } *)
(*     eapply MAXSRC; eauto. *)
(*   - unfold Mem.valid_block in *. xomega. *)
(* Qed. *)

End MEMINJ.

Hint Unfold private_src private_tgt.
Hint Unfold public_src public_tgt.



Section MEMINJ.

Definition update (sm0: t') (src tgt: mem) (inj: meminj): t' :=
  mk src tgt inj (sm0.(ptt_src)) (sm0.(ptt_tgt))
.
Hint Unfold update.
(* Notation "sm0 '.(update_tgt)' tgt" := (sm0.(update) sm0.(src) tgt sm0.(inj)) (at level 50). *)
(* Definition update_tgt (sm0: t') (tgt: mem) := (sm0.(update) sm0.(src) tgt sm0.(inj)). *)
(* Definition update_src (sm0: t') (src: mem) := (sm0.(update) src sm0.(tgt) sm0.(inj)). *)
(* Hint Unfold update_src update_tgt. *)

Hint Unfold private_src private_tgt valid_blocks.

Inductive lepriv (sm0 sm1: t'): Prop :=
| lepriv_intro
    (INCR: inject_incr sm0.(inj) sm1.(inj))
    (PUBSRC: (public_src sm0) <2= (public_src sm1))
    (PUBTGT: (public_tgt sm0) <2= (public_tgt sm1))
    (PMSRC: forall mi, (ownership_mem sm0.(ptt_src) (privmod mi)) <2=
                       (ownership_mem sm1.(ptt_src) (privmod mi)))
    (PMTGT: forall mi, (ownership_mem sm0.(ptt_tgt) (privmod mi)) <2=
                       (ownership_mem sm1.(ptt_tgt) (privmod mi)))
.

Global Program Instance lepriv_PreOrder: RelationClasses.PreOrder lepriv.
Next Obligation.
  ii. econs; eauto.
Qed.
Next Obligation.
  ii. inv H; inv H0. des; clarify. econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + etrans; et.
  + etrans; et.
Qed.

Global Program Instance SimMemSV : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  ptt_src := ptt_src;
  ptt_tgt := ptt_tgt;
  wf := wf';
  le := le';
  (* lift := lift'; *)
  (* unlift := unlift'; *)
  lepriv := lepriv;
  sim_val := fun (mrel: t') => Val.inject mrel.(inj);
  sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
  unchanged_on := Mem.unchanged_on;
}.
Next Obligation. rename H into LE. inv LE. econs; et. Qed.
(* Next Obligation. *)
(*   rename H into VALID. *)
(*   inv VALID. econs; ss; eauto; ii; des; ss; eauto. *)
(*   - eapply Pos.compare_gt_iff in H. xomega. *)
(*   - eapply Pos.compare_gt_iff in H. xomega. *)
(* Qed. *)
(* Next Obligation. *)
(*   eapply unlift_spec; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   eapply unlift_wf; eauto. *)
(* Qed. *)
Next Obligation. ii. inv MLE. eapply val_inject_incr; eauto. Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i). apply prop_ext1. split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. econs; eauto.
  - ginduction x1; ii; inv H; ss. econs; eauto.
Qed.
Next Obligation. inv H. ss. Qed.
Next Obligation. ii. eapply Mem.unchanged_on_implies; et. Qed.






Lemma iff_eta
      (P Q: Prop)
      (EQ: P = Q)
  :
    <<EQ: P <-> Q>>
.
Proof. clarify. Qed.

Lemma and_eta
      (P0 P1 Q0 Q1: Prop)
      (EQ0: P0 = P1)
      (EQ1: Q0 = Q1)
  :
    <<EQ: (P0 /\ Q0) = (P1 /\ Q1)>>
.
Proof. clarify. Qed.

Global Program Instance SimMemSVLift : SimMemLift.class SimMemSV :=
{ lift := lift';
  unlift := unlift';
}.
Next Obligation.
  inv H. econs; et.
  - unfold lift', lift_ptt. ss. unfold public_src, private_src in *. ss. ii. etrans; et.
    unfold ownership_mem. split; i; des_ifs.
  - unfold lift', lift_ptt. ss. unfold public_tgt, private_tgt in *. ss. ii. etrans; et.
    unfold ownership_mem. split; i; des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold lift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold lift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold unlift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold unlift_ptt. des_ifs.
Qed.
Next Obligation. eapply unlift_spec; et. Qed.
Next Obligation. eapply unlift_wf; eauto. Qed.
Next Obligation.
  inv MWF. destruct sm0; ss. econs; ss; et.
  - ii. unfold ownership_mem in *. unfold lift_ptt. des_ifs.
  - ii. unfold ownership_mem in *. unfold lift_ptt. des_ifs.
Qed.
Next Obligation.
  inv MWF. inv MLE. inv MLIFT. econs; ss; et; try congruence.
  - ii. unfold ownership_mem in *. unfold unlift_ptt. des_ifs.
  - ii. unfold ownership_mem in *. unfold unlift_ptt. des_ifs.
Qed.

Global Program Instance SimMemInjOhLift: SimMemOhLift.class (@SimMemOh_default SimMemSV)
  := SimMemOhLift.SimMemOhLift_transform.

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
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.store_mapped_inject; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). apply proj1 in PTTSRC. hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. }
      rr in PTTSRC. unfold external_src. rewrite PTTSRC. ss.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). apply proj1 in PTTTGT. hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold external_tgt. rewrite PTTTGT. ss.
    + unfold public_src, private_src. ss. ii; des; eauto with mem.
    + unfold public_tgt, private_tgt. ss. ii. eapply not_and_or in PR. des; eauto with mem.
      unfold loc_out_of_reach in *. eapply PR; et. ii. eapply H1; et. eauto with mem.
    + ii. eapply Mem.perm_store_2; eauto.
    + ii. eapply Mem.perm_store_2; eauto.
  - des. econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). apply proj1 in PTTSRC. hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. }
      rr in PTTSRC. unfold privmod_others. rewrite PTTSRC. ss.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). apply proj1 in PTTTGT. hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold privmod_others. rewrite PTTTGT. ss.
  - econs; ss; eauto.
    + ii. etrans; try apply PTTSRC; et. unfold public_src, private_src. ss.
      unfold valid_blocks. eapply iff_eta. do 2 apply f_equal. eapply prop_ext. eauto with mem.
    + ii. etrans; try apply PTTTGT; et. unfold public_tgt, private_tgt. ss.
      eapply iff_eta. do 1 apply f_equal. eapply prop_ext.
      unfold valid_blocks, loc_out_of_reach.
      split; ii; des.
      * esplits; eauto with mem.
        { ii. exploit H1; et. eauto with mem. }
      * esplits; eauto with mem.
        { ii. exploit H1; et. eauto with mem. }
Unshelve.
  all: try apply sm0.
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
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.storev_mapped_inject; try apply MWF; eauto. i; des.
  unfold Mem.storev in STRSRC. des_ifs. inv SIMADDR. exploit store_mapped; eauto. i; des.
  exists sm1. esplits; eauto. unfold Mem.storev.
  hexploit (size_chunk_pos chunk); eauto. intro SZ.
  assert(Ptrofs.unsigned i + delta = Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))).
  { rewrite <- Ptrofs.repr_unsigned with (i := i). rewrite Ptrofs.Ptrofs_add_repr.
    rewrite Ptrofs.unsigned_repr; [|eapply Ptrofs.unsigned_range_2]. rewrite Ptrofs.unsigned_repr; eauto.
    eapply Mem.mi_representable; eauto.
    left. eapply Mem.perm_store_1; eauto. eapply Mem.perm_implies; [|eauto with mem]. eapply Mem.perm_cur_max.
    eapply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eapply H1. omega.
  }
  rewrite <- H1. eauto.
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
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.free_parallel_inject; try apply MWF; eauto. i; des. inv MWF.
  assert(exists ptt_tgt: partition, True).
  { esplits; et. exact (fun _ _ => pub). }
  des.
  eexists (mk _ _ _ sm0.(ptt_src) ptt_tgt0). dsplits; ss; eauto; cycle 1.
  (* eexists (mk _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1. *)
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). apply proj1 in PTTSRC. hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. }
      rr in PTTSRC. unfold external_src. rewrite PTTSRC. ss.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). apply proj1 in PTTTGT. hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.free_range_perm in FREESRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold external_tgt. rewrite PTTTGT. ss.
    + unfold public_src, private_src. ss. ii; des; eauto with mem.
    + unfold public_tgt, private_tgt. ss. ii. eapply not_and_or in PR. des; eauto with mem.
      unfold loc_out_of_reach in *. eapply PR; et. ii. eapply H2; et.
    + ii. eapply Mem.perm_free_3; eauto.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVSRC.
      unfold privmod_others in *. des_ifs. eapply PTTSRC; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVTGT.
      unfold privmod_others in *. des_ifs. eapply PTTTGT; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_left
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
      (PRIVSRC: sm0.(src_external) = src_private sm0)
      (PRIVTGT: sm0.(tgt_external) = tgt_private sm0)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.free_left_inject; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ _ _ _ _ _ _ _ _ _). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto.
      ii. apply SRCEXT in H1. red in H1. des. red in H1. clarify.
    + eapply Mem.unchanged_on_refl.
    + eapply frozen_refl.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVSRC.
      unfold privmod_others in *. des_ifs. eapply PTTSRC; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVTGT.
      unfold privmod_others in *. des_ifs. eapply PTTTGT; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_right
      sm0 lo hi blk_tgt m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk_tgt lo hi = Some m_tgt0)
      (PRIVTGT: forall ofs (BDD: lo <= ofs < hi), (tgt_private sm0) blk_tgt ofs)
      (EXTTGT: forall ofs : Z, lo <= ofs < hi -> ~ tgt_external sm0 blk_tgt ofs)
      (PRIVSRC: sm0.(src_external) = src_private sm0)
      (PRIVTGT0: sm0.(tgt_external) = tgt_private sm0)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.free_right_inject; try apply MWF; eauto.
  { ii. eapply PRIVTGT in H1. red in H1. des. red in H1. eapply H1; eauto.
    replace (ofs + delta - delta) with ofs by omega. eauto with mem.
  }
  i; des. inv MWF.
  eexists (mk _ _ _ _ _ _ _ _ _ _ _). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_refl.
    + eapply Mem.free_unchanged_on; eauto.
    + eapply frozen_refl.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVSRC.
      unfold privmod_others in *. des_ifs. eapply PTTSRC; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
    + eapply Mem.unchanged_on_implies; try apply SPLITHINT3. i. rewrite PRIVTGT0.
      unfold privmod_others in *. des_ifs. eapply PTTTGT; et.
      instantiate (1:= Some mi). ss. des_ifs. des_sumbool. ss.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma alloc_parallel
      sm0 lo_src hi_src lo_tgt hi_tgt blk_src m_src0
      (MWF: wf' sm0)
      (ALCSRC: Mem.alloc sm0.(src) lo_src hi_src = (m_src0, blk_src))
      (LO: lo_tgt <= lo_src)
      (HI: hi_src <= hi_tgt):
    exists sm1 blk_tgt ,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<ALCTGT: Mem.alloc sm0.(tgt) lo_tgt hi_tgt = (sm1.(tgt), blk_tgt)>>)
      /\ (<<INJ: sm1.(inj) blk_src = Some (blk_tgt, 0) /\ forall b, b <> blk_src -> sm1.(inj) b = sm0.(inj) b>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.alloc_parallel_inject; try apply MWF; eauto. i; des. inv MWF.
  assert(FROZEN: frozen (inj sm0) f' (src_parent_nb sm0) (tgt_parent_nb sm0)).
  {
    + econs. ii. des. destruct (eq_block b_src blk_src).
      * subst. rewrite H2 in NEW0. clarify. eapply Mem.alloc_result in ALCSRC. rewrite ALCSRC.
        eapply Mem.alloc_result in H. rewrite H. esplits; eauto.
      * rewrite H3 in NEW0; eauto. clarify.
  }
  eexists (mk _ _ f' _ _ _ _ _ _ _ _). exists b2.
  dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply frozen_shortened; eauto.
    + ii. eapply Mem.perm_alloc_4; eauto.
      ii. subst b. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto.
    + ii. eapply Mem.perm_alloc_4; eauto.
      ii. subst b. eapply Mem.fresh_block_alloc; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      { destruct (eq_block x0 blk_src).
        - subst x0. exfalso. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto.
        - r. rewrite H3; eauto. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. destruct (eq_block b0 blk_src).
        - subst b0. clarify. eapply Mem.fresh_block_alloc; eauto.
        - eapply PR. rewrite <- H3; eauto. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. eapply Mem.nextblock_alloc in ALCSRC. rewrite ALCSRC. xomega.
    + etransitivity; eauto. eapply Mem.nextblock_alloc in H. rewrite H. xomega.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      { destruct (eq_block x0 blk_src).
        - subst x0. exfalso. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto.
        - r. rewrite H3; eauto. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. destruct (eq_block b0 blk_src).
        - subst b0. clarify. eapply Mem.fresh_block_alloc; eauto.
        - eapply PR. rewrite <- H3; eauto. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma external_call
      sm0 ef se vargs t vres m_src0 tse vargs' vres' m_tgt0 f'
      (MWF: wf' sm0)
      (EXTCALLSRC: Events.external_call ef se vargs sm0.(src) t vres m_src0)
      (EXTCALLTGT: Events.external_call ef tse vargs' sm0.(tgt) t vres' m_tgt0)
      (MEMINJ: Mem.inject f' m_src0 m_tgt0)
      (UNCHANGSRC: Mem.unchanged_on (loc_unmapped sm0.(inj)) sm0.(src) m_src0)
      (UNCHANGTGT: Mem.unchanged_on (loc_out_of_reach sm0.(inj) sm0.(src)) sm0.(tgt) m_tgt0)
      (INJINCR: inject_incr sm0.(inj) f')
      (INJSEP: inject_separated sm0.(inj) f' sm0.(src) sm0.(tgt)):
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = f'>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  inv MWF.
  assert (LE_LIFTED: le' (lift' sm0)
                               (mk m_src0 m_tgt0 f' sm0.(ptt_src) sm0.(ptt_tgt)
                                   (src_private sm0) (tgt_private sm0)
                                   sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock)
                                   sm0.(src_ge_nb) sm0.(tgt_ge_nb))).
  { econs; ss; eauto.
    - econs; i; eapply UNCHANGSRC; eauto; eapply H.
    - econs; i; eapply UNCHANGTGT; eauto; eapply H.
    - eapply frozen_shortened; try eapply inject_separated_frozen; eauto; try xomega.
    - eapply inject_separated_frozen; eauto.
    - ii. eapply external_call_max_perm; eauto.
    - ii. eapply external_call_max_perm; eauto.
  }
  eexists (mk _ _ _ _ _ sm0.(src_external) sm0.(tgt_external) sm0.(src_parent_nb) sm0.(tgt_parent_nb) _ _); eauto.
  dsplits; ss; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. eapply (after_private_src _ LE_LIFTED).
    + etransitivity; eauto. eapply (after_private_tgt _ _ LE_LIFTED).
    + eapply Ple_trans; eauto. eapply UNCHANGSRC.
    + eapply Ple_trans; eauto; eapply UNCHANGTGT.
    + etransitivity; eauto. eapply (after_private_src _ LE_LIFTED).
    + etransitivity; try apply PTTTGT; eauto. eapply (after_private_tgt _ _ LE_LIFTED).
  - exploit unlift_spec; eauto. econs; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
Unshelve.
  all: by (try eapply inject_separated_frozen; eauto).
Qed.

Lemma free_list
      sm0 l m_src0 l' m_tgt0
      (MWF : wf' sm0)
      (FREESRC: Mem.free_list sm0.(src) l = Some m_src0)
      (FREETGT: Mem.free_list sm0.(tgt) l' = Some m_tgt0)
      (MEMINJ: Mem.inject sm0.(inj) m_src0 m_tgt0)
      (EXTSRC: forall b lo hi i, In (b, lo, hi) l -> lo <= i < hi -> ~ sm0.(src_external) b i)
      (EXTTGT: forall b lo hi i, In (b, lo, hi) l' -> lo <= i < hi -> ~ sm0.(tgt_external) b i):
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  inv MWF. eexists (mk _ _ _ _ _ _ _ _ _ _ _). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.free_list_unchanged_on; eauto.
    + eapply Mem.free_list_unchanged_on; eauto.
    + eapply frozen_refl. + eapply frozen_refl.
    + ii. eapply Mem.perm_free_list; eauto.
    + ii. eapply Mem.perm_free_list; eauto.      
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
    + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ii. ss. des. esplits; eauto.
      red. red. erewrite Mem.free_list_nextblock; eauto.
    + etransitivity; eauto. unfold tgt_private. ii. ss. des. esplits; eauto.
      red. ii. eapply PR; eauto.
      exploit Mem.perm_free_list; try eapply FREESRC; eauto. i; des. ss.
      red. red. erewrite Mem.free_list_nextblock; eauto.
    + erewrite Mem.free_list_nextblock; eauto.
    + erewrite Mem.free_list_nextblock; eauto.
    + etransitivity; eauto. unfold src_private. ii. ss. des. esplits; eauto.
      red. red. erewrite Mem.free_list_nextblock; eauto.
    + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ii. ss. des. esplits; eauto.
      red. ii. eapply PR; eauto.
      exploit Mem.perm_free_list; try eapply FREESRC; eauto. i; des. ss.
      red. red. erewrite Mem.free_list_nextblock; eauto.
Unshelve.
  all: try apply sm0.
Qed.

End ORIGINALS.

Record mcompat (sm0: t') (m_src0 m_tgt0: mem) (F: meminj): Prop := mkmcompat {
  mcompat_src: sm0.(src) = m_src0;
  mcompat_tgt: sm0.(tgt) = m_tgt0;
  mcompat_inj: sm0.(inj) = F;
}.

End MEMINJ.

Hint Unfold valid_blocks.
Hint Unfold src_private tgt_private.

Ltac compat_tac := ss; econs; eauto; try congruence.

Ltac spl := esplits; [|reflexivity].
Ltac spl_approx sm :=
  eexists (mk _ _ _ sm.(src_external) sm.(tgt_external) sm.(src_parent_nb) sm.(tgt_parent_nb) sm.(src_ge_nb) sm.(tgt_ge_nb)); splits; eauto.
Ltac spl_exact sm :=
  exists sm; splits; [|try etransitivity; eauto; try reflexivity; eauto].





Require SimSymbId.

Section SIMSYMB.

Lemma skenv_inject_meminj_preserves_globals
      F V (skenv: Genv.t F V) j
      (INJECT: skenv_inject skenv j):
    <<INJECT: meminj_preserves_globals skenv j>>.
Proof.
  inv INJECT. rr. esplits; ii; ss; eauto.
  - eapply DOMAIN; eauto. eapply Genv.genv_symb_range; eauto.
  - eapply DOMAIN; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
  - symmetry. eapply IMAGE; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
Qed.

Inductive sim_skenv_inj (sm: SimMem.t) (__noname__: SimSymbId.t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INJECT: skenv_inject skenv_src sm.(inj))
    (* NOW BELOW IS DERIVABLE FROM WF *)
    (* (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_parent_nb)) *)
    (* (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_parent_nb)) *)
    (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
    (NBSRC: skenv_src.(Genv.genv_next) = sm.(src_ge_nb))
    (NBTGT: skenv_tgt.(Genv.genv_next) = sm.(tgt_ge_nb)).

Section REVIVE.

  Context {F1 V1: Type} {LF: Linker F1} {LV: Linker V1}.
  Context `{HasExternal F1}.
  Variables (p_src: AST.program F1 V1).

  Lemma skenv_inject_revive
        skenv_proj_src ge_src j
        (REVIVESRC: ge_src = SkEnv.revive skenv_proj_src p_src)
        (SIMSKENV: skenv_inject skenv_proj_src j):
      <<SIMSKENV: skenv_inject ge_src j>>.
  Proof. clarify. inv SIMSKENV. econs; eauto. Qed.

End REVIVE.



Global Program Instance SimSymbId: SimSymb.class SimMemSV := {
  t := SimSymbId.t';
  src := SimSymbId.src;
  tgt := SimSymbId.tgt;
  le := SimSymbId.le;
  wf := SimSymbId.wf;
  sim_skenv := sim_skenv_inj;
}.
Next Obligation. rr in SIMSK. r. congruence. Qed.
Next Obligation. eapply SimSymbId.wf_link; eauto. Qed.
Next Obligation. inv SIMSKE. inv SIMSKENV. ss. Qed.
Next Obligation.
  exploit SimSymbId.wf_load_sim_skenv; eauto. i; des.
  eexists. eexists (mk m_src m_src (Mem.flat_inj m_src.(Mem.nextblock)) (fun _ _ => etc) (fun _ _ => etc)
                       bot2 bot2 m_src.(Mem.nextblock) m_src.(Mem.nextblock) m_src.(Mem.nextblock) m_src.(Mem.nextblock)). ss.
  esplits; ss; eauto.
  - econs; ss; eauto.
    + econs; eauto; ii; ss.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
  - econs; ss; try xomega; ii; des; ss; eauto.
    + eapply Genv.initmem_inject; eauto; (u in *; eauto).
    + unfold privmods in *. des_ifs.
    + unfold privmods in *. des_ifs.
  - rewrite MAINSIM. unfold Genv.symbol_address. des_ifs. unfold Mem.flat_inj. econs; eauto.
    + des_ifs. exfalso. apply n. eapply Plt_Ple_trans.
      { eapply Genv.genv_symb_range; et. }
      erewrite Genv.init_mem_genv_next; eauto. refl.
    + psimpl. ss.
Qed.
Next Obligation.
  inv SIMSKENV. inv INJECT. econs; eauto. econs; eauto.
  - ii. exploit DOMAIN; eauto. i. eapply MLE; eauto.
  - ii. inv MLE. eapply IMAGE; eauto. erewrite frozen_preserves_tgt; eauto.
    eapply Plt_Ple_trans; eauto. rewrite <- NBTGT. rr in SIMSKENV0. clarify. refl.
  - inv MLE. eauto with congruence.
  - inv MLE. eauto with congruence.
Qed.
(* Next Obligation. *)
(*   inv MWF. inv SIMSKENV. *)
(*   econs; eauto. *)
(*   - etransitivity; try apply SRCLE; eauto. *)
(*   - etransitivity; try apply TGTLE; eauto. *)
(* Qed. *)
Next Obligation.
  set (SkEnv.project skenv_link_src ss.(SimSymbId.src)) as skenv_proj_src.
  generalize (SkEnv.project_impl_spec INCLSRC); intro LESRC.
  set (SkEnv.project skenv_link_tgt ss.(SimSymbId.tgt)) as skenv_proj_tgt.
  generalize (SkEnv.project_impl_spec INCLTGT); intro LETGT.
  exploit SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. i; des.
  inv SIMSKENV. inv LESRC. inv LETGT. econs; eauto. inv INJECT. econs; ii; eauto.
Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto. { eapply SIMSKENV. } i; des.
  inv H. inv SIMSKENV. inv INJECT. inv SIMSKENV0. econs; eauto.
  ii; ss. eapply FUNCFSIM; eauto. rpapply FUNCSRC. f_equal.
  { inv SIMFPTR; ss. des_ifs. rewrite Ptrofs.add_zero_l.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    exploit DOMAIN; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify. }
Qed.
Next Obligation.
  inv SIMSKENV. econs; eauto.
  - inv INJECT. econs; eauto.
  - eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  destruct sm0, args_src, args_tgt; ss; inv ARGS; ss. inv MWF; ss. clarify.
  (* Note: It may be easier && more natural to use
"external_call_mem_inject" with "external_call_symbols_preserved", instead of "external_call_mem_inject_gen" *)
  (* exploit external_call_mem_inject_gen; eauto. *)
  exploit external_call_mem_inject; eauto.
  { eapply skenv_inject_meminj_preserves_globals; eauto. inv SIMSKENV; ss. }
  i; des. do 2 eexists. dsplits; eauto; ss.
  - instantiate (1:= Retv.mk _ _); ss. eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. eapply SIMSKENV.
  - destruct retv_src; ss. instantiate (1:= mk _ _ _ _ _ _ _ _ _ _ _). econs 1; ss; eauto.
    instantiate (1:= (Retv.m retv_src)). ss.
  - assert(FROZEN: frozen inj0 f' src_parent_nb0 tgt_parent_nb0).
    { eapply inject_separated_frozen in H5. inv H5. econs; eauto. i.
      exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. esplits; xomega. }
    econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. eapply SRCEXT in H6. unfold src_private in *. ss. des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. eapply TGTEXT in H6. unfold tgt_private in *. ss. des; ss.
    + eapply frozen_shortened; et.
    + ii. eapply external_call_max_perm; eauto.
    + ii. eapply external_call_max_perm; eauto.
  (* - econs; ii; ss. *)
  (*   + eapply Mem.unchanged_on_implies. *)
  (*     { eapply Mem_unchanged_on_bot; et. eapply SPLITHINT1. } *)
  (*     ss. *)
  (*   + eapply Mem.unchanged_on_implies. *)
  (*     { eapply Mem_unchanged_on_bot; et. eapply SPLITHINT1. } *)
  (*     ss. *)
  - econs; ss; eauto.
  - apply inject_separated_frozen in H5. econs; ss.
    (* + eapply after_private_src; ss; eauto. *)
    (* + eapply after_private_tgt; ss; eauto. *)
    + etrans; eauto. unfold src_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. destruct (f' x0) eqn:T; ss. destruct p; ss. inv H5.
        exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *. unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + etrans; eauto. unfold tgt_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. ii. destruct (inj0 b0) eqn:T; ss.
        -- destruct p; ss. exploit H4; eauto. i; clarify.
           eapply PR; et. eapply external_call_max_perm; et. eapply Mem.valid_block_inject_1; try apply T; et.
        -- inv H5. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *. unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + inv H2. xomega.
    + inv H3. xomega.
Unshelve.
  all: ss.
Qed.

Local Existing Instance SimMemSV.
Local Existing Instance SimSymbId.

Lemma sim_skenv_symbols_inject
      sm0 ss0 skenv_src skenv_tgt
      (SIMSKE: SimSymb.sim_skenv sm0 ss0 skenv_src skenv_tgt):
    symbols_inject sm0.(SimMemSV.inj) skenv_src skenv_tgt.
Proof.
  inv SIMSKE. inv SIMSKENV. inv INJECT. rr. esplits; ss.
  + i. exploit Genv.genv_symb_range; eauto. intro NB. exploit DOMAIN; eauto. i ;des. clarify.
  + i. exploit Genv.genv_symb_range; eauto.
  + i. unfold Genv.block_is_volatile, Genv.find_var_info. destruct (Genv.find_def skenv_tgt b1) eqn:T.
    * exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des. clarify. des_ifs.
    * des_ifs. exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des.
      exploit (IMAGE b1 b2); eauto. i; clarify.
Qed.

End SIMSYMB.

Arguments skenv_inject_revive [_ _ _].
