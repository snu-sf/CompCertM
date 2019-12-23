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
Require SimSymbId.
Require Import Conventions1.
Require Export SimMemInj.

Set Implicit Arguments.



Section MEMINJ.

Definition update (sm0: t') (src tgt: mem) (inj: meminj): t' :=
  mk src tgt inj sm0.(src_external) sm0.(tgt_external) sm0.(src_parent_nb) sm0.(tgt_parent_nb)
                                                       sm0.(src_ge_nb) sm0.(tgt_ge_nb).
Hint Unfold update.
(* Notation "sm0 '.(update_tgt)' tgt" := (sm0.(update) sm0.(src) tgt sm0.(inj)) (at level 50). *)
(* Definition update_tgt (sm0: t') (tgt: mem) := (sm0.(update) sm0.(src) tgt sm0.(inj)). *)
(* Definition update_src (sm0: t') (src: mem) := (sm0.(update) src sm0.(tgt) sm0.(inj)). *)
(* Hint Unfold update_src update_tgt. *)

Hint Unfold src_private tgt_private valid_blocks.

Lemma update_src_private
      sm0 sm1
      (INJ: sm0.(inj) = sm1.(inj))
      (SRC: sm0.(src).(Mem.nextblock) = sm1.(src).(Mem.nextblock)):
    (src_private sm0) = (src_private (sm1)).
Proof.
  repeat (apply Axioms.functional_extensionality; i). apply prop_ext1.
  u. split; ii; des; esplits; eauto with congruence.
Qed.

Lemma update_tgt_private
      sm0 sm1
      (SRC: sm0.(src) = sm1.(src))
      (TGT: sm0.(tgt).(Mem.nextblock) = sm1.(tgt).(Mem.nextblock))
      (INJ: sm0.(inj) = sm1.(inj)):
    (tgt_private sm0) = (tgt_private sm1).
Proof.
  repeat (apply Axioms.functional_extensionality; i). apply prop_ext1.
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

(* TODO: Let's have this as policy. (giving explicit name) *)
(* TODO: apply this policy for identity/extension *)

(* "Global" is needed as it is inside section *)

Inductive lepriv (sm0 sm1: SimMemInj.t'): Prop :=
| lepriv_intro
    (INCR: inject_incr sm0.(inj) sm1.(inj))
    (* (SRCUNCHANGED: Mem.unchanged_on sm0.(src_external) sm0.(src) sm1.(src)) *)
    (* (TGTUNCHANGED: Mem.unchanged_on sm0.(tgt_external) sm0.(tgt) sm1.(tgt)) *)
    (* (SRCPARENTEQ: sm0.(src_external) = sm1.(src_external)) *)
    (* (TGTPARENTEQ: sm0.(tgt_external) = sm1.(tgt_external)) *)
    (* (SRCPARENTEQNB: (sm0.(src_parent_nb) <= sm1.(src_parent_nb))%positive) *)
    (* (TGTPARENTEQNB: (sm0.(tgt_parent_nb) <= sm1.(tgt_parent_nb))%positive) *)


    (* (SRCPARENTNB: (sm0.(src_ge_nb) <= sm1.(src_parent_nb))%positive) *)
    (* (TGTPARENTNB: (sm0.(tgt_ge_nb) <= sm1.(tgt_parent_nb))%positive) *)
    (SRCGENB: sm0.(src_ge_nb) = sm1.(src_ge_nb))
    (TGTGENB: sm0.(tgt_ge_nb) = sm1.(tgt_ge_nb))
    (FROZEN: frozen sm0.(inj) sm1.(inj) (sm0.(src_ge_nb)) (sm0.(tgt_ge_nb))).

Global Program Instance SimMemInj : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  wf := wf';
  le := le';
  (* lift := lift'; *)
  (* unlift := unlift'; *)
  lepriv := lepriv;
  sim_val := fun (mrel: t') => Val.inject mrel.(inj);
  sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
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





Global Program Instance lepriv_Transitive: RelationClasses.Transitive lepriv.
Next Obligation.
  ii. inv H; inv H0. des; clarify. econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + econs; eauto. ii; des. destruct (inj y b_src) eqn:T.
    * destruct p. exploit INCR0; eauto. i; clarify. inv FROZEN. hexploit NEW_IMPLIES_OUTSIDE; eauto.
    * inv FROZEN0. hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. esplits; congruence.
Qed.


Global Program Instance SimMemInjLift : SimMemLift.class SimMemInj :=
{ lift := lift';
  unlift := unlift';
}.
Next Obligation.
  rename H into VALID. inv VALID. econs; ss; eauto; ii; des; ss; eauto; eapply Pos.compare_gt_iff in H; xomega.
Qed.
Next Obligation. eapply unlift_spec; et. Qed.
Next Obligation. eapply unlift_wf; eauto. Qed.
Next Obligation. inv MWF. destruct sm0; ss. econs; ss; et. eapply frozen_refl. Qed.
Next Obligation. inv MWF. inv MLE. inv MLIFT. econs; ss; et; try congruence. eapply frozen_refl. Qed.


Section ORIGINALS.

Inductive le_excl (excl_src excl_tgt: block -> Z -> Prop) (mrel0 mrel1: t'): Prop :=
| le_excl_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (SRCUNCHANGED: Mem.unchanged_on mrel0.(src_external) mrel0.(src) mrel1.(src))
    (TGTUNCHANGED: Mem.unchanged_on mrel0.(tgt_external) mrel0.(tgt) mrel1.(tgt))
    (SRCPARENTEQ: mrel0.(src_external) = mrel1.(src_external))
    (SRCPARENTEQNB: mrel0.(src_parent_nb) = mrel1.(src_parent_nb))
    (SRCGENB: mrel0.(src_ge_nb) = mrel1.(src_ge_nb))
    (TGTPARENTEQ: mrel0.(tgt_external) = mrel1.(tgt_external))
    (TGTPARENTEQNB: mrel0.(tgt_parent_nb) = mrel1.(tgt_parent_nb))
    (TGTGENB: mrel0.(tgt_ge_nb) = mrel1.(tgt_ge_nb))
    (FROZEN: frozen mrel0.(inj) mrel1.(inj) (mrel0.(src_parent_nb))
                                            (mrel0.(tgt_parent_nb)))
    (MAXSRC: forall b ofs
        (VALID: Mem.valid_block mrel0.(src) b)
        (EXCL: ~ excl_src b ofs),
        <<MAX: Mem.perm mrel1.(src) b ofs Max <1= Mem.perm mrel0.(src) b ofs Max>>)
    (MAXTGT: forall b ofs
        (VALID: Mem.valid_block mrel0.(tgt) b)
        (EXCL: ~ excl_tgt b ofs),
        <<MAX: Mem.perm mrel1.(tgt) b ofs Max <1= Mem.perm mrel0.(tgt) b ofs Max>>).

Inductive has_footprint (excl_src excl_tgt: block -> Z -> Prop) (sm0: t'): Prop :=
| has_footprint_intro
    (FOOTSRC: forall blk ofs
        (EXCL: excl_src blk ofs),
        <<PERM: Mem.perm sm0.(src) blk ofs Cur Freeable>>)
    (FOOTTGT: forall blk ofs
        (EXCL: excl_tgt blk ofs),
        <<PERM: Mem.perm sm0.(tgt) blk ofs Cur Freeable>>).

Lemma unfree_right
      sm0 lo hi blk m_tgt0
      (MWF: wf' sm0)
      (NOPERM: Mem_range_noperm sm0.(tgt) blk lo hi)
      (UNFR: Mem_unfree sm0.(tgt) blk lo hi = Some m_tgt0)
      (RANGE: brange blk lo hi <2= ~2 sm0.(tgt_external)):
    exists sm1,
      (* (<<EXACT: sm1 = sm0.(update_tgt) m_tgt0>>) *)
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le_excl bot2 (brange blk lo hi) sm0 sm1>>).
Proof.
  exists (update (sm0) sm0.(src) m_tgt0 sm0.(inj)).
  exploit Mem_unfree_unchanged_on; et. intro UNCH. esplits; u; ss; eauto.
  - econs; ss; eauto; try (by inv MWF; ss).
    + inv MWF. eapply Mem_unfree_right_inject; eauto.
    + etransitivity; try apply MWF; eauto. u. ii; des; esplits; eauto. erewrite <- Mem_valid_block_unfree; eauto.
    + etransitivity; try apply MWF; eauto. erewrite Mem_nextblock_unfree; eauto. refl.
  - econs; ss; eauto; try refl.
    + eapply Mem.unchanged_on_implies. { eapply Mem_unfree_unchanged_on; eauto. } ii. eapply RANGE; et.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_unchanged_on_2; et.
Qed.

Lemma foot_excl
      sm0 sm1 sm2 excl_src excl_tgt
      (MWF: SimMem.wf sm0)
      (FOOT: has_footprint excl_src excl_tgt sm0)
      (MLE: le' sm0 sm1)
      (MLEEXCL: le_excl excl_src excl_tgt sm1 sm2):
    <<MLE: le' sm0 sm2>>.
Proof.
  inv MLE. inv MLEEXCL.
  assert(FROZENHI: frozen (inj sm0) (inj sm2) (src_parent_nb sm0) (tgt_parent_nb sm0)).
  { - clear - FROZEN FROZEN0 INCR0 SRCPARENTEQNB TGTPARENTEQNB.
      inv FROZEN. inv FROZEN0. econs. i. des. destruct (inj sm1 b_src) eqn:T.
      + destruct p; ss. exploit INCR0; et. i; clarify. exploit NEW_IMPLIES_OUTSIDE; et.
      + exploit NEW_IMPLIES_OUTSIDE0; et. i; des. esplits; eauto with congruence xomega. }
  econs; et; try (by etrans; et).
  - etrans; et. rewrite SRCPARENTEQ. ss.
  - etrans; et. rewrite TGTPARENTEQ. ss.
  - eapply frozen_shortened; et; try apply MWF.
  - ii. destruct (classic (excl_src b ofs)).
    + inv FOOT. eapply Mem.perm_cur_max. eapply Mem.perm_implies with (p1 := Freeable); [|eauto with mem]. eapply FOOTSRC; et.
    + eapply MAXSRC; et. eapply MAXSRC0; et. eapply Mem.valid_block_unchanged_on; et.
  - ii. destruct (classic (excl_tgt b ofs)).
    + inv FOOT. eapply Mem.perm_cur_max. eapply Mem.perm_implies with (p1 := Freeable); [|eauto with mem]. eapply FOOTTGT; et.
    + eapply MAXTGT; et. eapply MAXTGT0; et. eapply Mem.valid_block_unchanged_on; et.
Qed.

End ORIGINALS.

Lemma parallel_gen sm0 m_src1 m_tgt1 j1
      (WF: wf' sm0)
      (INJECT: Mem.inject j1 m_src1 m_tgt1)
      (INCR: inject_incr sm0.(inj) j1)
      (SEP: inject_separated sm0.(inj) j1 sm0.(src) sm0.(tgt))
      (UNCHSRC: Mem.unchanged_on
                  (loc_unmapped sm0.(inj))
                  sm0.(src) m_src1)
      (UNCHTGT: Mem.unchanged_on
                  (loc_out_of_reach sm0.(inj) sm0.(src))
                  sm0.(tgt) m_tgt1)
      (MAXSRC: forall b ofs
          (VALID: Mem.valid_block sm0.(src) b),
          <<MAX: Mem.perm m_src1 b ofs Max <1= Mem.perm sm0.(src) b ofs Max>>)
      (MAXTGT: forall b ofs
          (VALID: Mem.valid_block sm0.(tgt) b),
          <<MAX: Mem.perm m_tgt1 b ofs Max <1= Mem.perm sm0.(tgt) b ofs Max>>):
  (<<MLE: le' sm0 (mk m_src1 m_tgt1 j1
                     (src_external sm0) (tgt_external sm0)
                     (src_parent_nb sm0) (tgt_parent_nb sm0)
                     (src_ge_nb sm0) (tgt_ge_nb sm0))>>) /\
  (<<MWF: wf' (mk m_src1 m_tgt1 j1
                 (src_external sm0) (tgt_external sm0)
                 (src_parent_nb sm0) (tgt_parent_nb sm0)
                 (src_ge_nb sm0) (tgt_ge_nb sm0))>>).
Proof.
  inv WF. split.
  - assert(FROZEN: frozen (inj sm0) j1 (src_parent_nb sm0) (tgt_parent_nb sm0)).
    { econs. ii. des. exploit SEP; eauto. i. des. split; unfold Mem.valid_block in *; red; xomega. }
    econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. ii. eapply SRCEXT; eauto.
    + eapply Mem.unchanged_on_implies; eauto. ii. eapply TGTEXT; eauto.
    + eapply frozen_shortened; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. ii. destruct PR. split; ss.
      * unfold loc_unmapped. destruct (j1 x0) eqn:BLK; eauto. destruct p. exploit SEP; eauto. i. des. clarify.
      * eapply Plt_Ple_trans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    + etransitivity; eauto. ii. destruct PR. split; ss.
      * ii. destruct (inj sm0 b0) eqn:BLK.
        { destruct p. dup BLK. eapply INCR in BLK. clarify.
          exploit H; eauto. eapply MAXSRC; eauto.
          eapply Mem.valid_block_inject_1; eauto. }
        { exploit SEP; eauto. i. des. clarify. }
      * eapply Plt_Ple_trans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    + etransitivity; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    + etransitivity; eauto. eapply Mem.unchanged_on_nextblock; eauto.
Qed.

Lemma alloc_left_zero_simmem
      sm0 blk_src sz m_src1 blk_tgt
      (MWF: SimMem.wf sm0)
      (ALLOC: Mem.alloc sm0.(SimMem.src) 0 sz = (m_src1, blk_src))
      (TGTPRIV: (range 0 sz) <1= (tgt_private sm0) blk_tgt)
      (TGTNOTEXT: ((range 0 sz) /1\ sm0.(tgt_external) blk_tgt) <1= bot1)
      (TGTPERM: forall ofs k p (BOUND: 0 <= ofs < sz), Mem.perm sm0.(SimMem.tgt) blk_tgt ofs k p)
      (* (SZPOS: 0 < sz) *)
      (VALID: Mem.valid_block sm0.(tgt) blk_tgt)
      (PARENT: (sm0.(tgt_parent_nb) <= blk_tgt)%positive):
    let sm1 := (mk m_src1 sm0.(tgt)
                   (fun blk => if eq_block blk blk_src then Some (blk_tgt, 0) else sm0.(inj) blk)
                   sm0.(src_external) sm0.(tgt_external)
                   sm0.(src_parent_nb) sm0.(tgt_parent_nb)
                   sm0.(src_ge_nb) sm0.(tgt_ge_nb)
               ) in
    <<MWF: SimMem.wf sm1>> /\
    <<MLE: SimMem.le sm0 sm1>>.
Proof.
  i. subst_locals. inv MWF; ss.
  exploit Mem.alloc_result; eauto. i; clarify. esplits; eauto.
  * econs; ss; eauto.
    - eapply Mem_alloc_left_inject; eauto. ii. eapply TGTPRIV; eauto.
    - etransitivity; eauto. u. ii; ss. des. esplits; eauto.
      + hnf. des_ifs. exfalso. unfold Mem.valid_block in *. xomega.
      + eauto with mem.
    - u. ii; ss. dup PR. eapply TGTEXT in PR0. u in PR0. des. esplits; eauto. hnf. hnf in PR0. ii. des_ifs; eauto.
      + eapply TGTNOTEXT; eauto. esplits; eauto. u. rewrite Z.sub_0_r in *.
        apply NNPP. ii. eapply Mem_alloc_fresh_perm; eauto.
      + eapply PR0; eauto. eauto with mem.
    - etransitivity; eauto. exploit Mem.nextblock_alloc; eauto. i. rewrite H. xomega.
  * assert(FROZEN: frozen (inj sm0)
       (fun blk => if eq_block blk (Mem.nextblock (src sm0)) then Some (blk_tgt, 0) else inj sm0 blk)
       (src_parent_nb sm0) (tgt_parent_nb sm0)).
    { econs; eauto. ii; ss. des; ss. des_ifs. }
    econs; cbn; eauto with mem; try xomega.
    - ii; ss. des_ifs; ss. exfalso.
      exploit Mem.mi_freeblocks; try apply MWF; eauto.
      { eauto with mem. }
      i; ss. clarify.
    - eapply Mem_unchanged_on_trans_strong; eauto.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eauto with mem.
    - eapply frozen_shortened; et.
    - ii. eauto with mem.
Qed.

Local Opaque Z.mul.

Require StoreArguments.

End MEMINJ.

Hint Unfold valid_blocks src_private tgt_private range.









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



Global Program Instance SimSymbId: SimSymb.class SimMemInj := {
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
  eexists. eexists (mk m_src m_src (Mem.flat_inj m_src.(Mem.nextblock))
                       bot2 bot2 m_src.(Mem.nextblock) m_src.(Mem.nextblock) m_src.(Mem.nextblock) m_src.(Mem.nextblock)). ss.
  esplits; ss; eauto.
  - econs; ss; eauto.
    + econs; eauto; ii; ss.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
  - econs; ss; try xomega; ii; des; ss; eauto. eapply Genv.initmem_inject; eauto; (u in *; eauto).
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
  i; des. do 2 eexists. dsplits; eauto.
  - instantiate (1:= Retv.mk _ _); ss. eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. eapply SIMSKENV.
  - destruct retv_src; ss. instantiate (1:= mk _ _ _ _ _ _ _ _ _). econs 1; ss; eauto.
    instantiate (1:= (Retv.m retv_src)). ss.
  - assert(FROZEN: frozen inj f' src_parent_nb tgt_parent_nb).
    { eapply inject_separated_frozen in H5. inv H5. econs; eauto. i.
      exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. esplits; xomega. }
    econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. eapply SRCEXT in H6. unfold src_private in *. ss. des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. eapply TGTEXT in H6. unfold tgt_private in *. ss. des; ss.
    + eapply frozen_shortened; et.
    + ii. eapply external_call_max_perm; eauto.
    + ii. eapply external_call_max_perm; eauto.
  - apply inject_separated_frozen in H5. econs; ss.
    (* + eapply after_private_src; ss; eauto. *)
    (* + eapply after_private_tgt; ss; eauto. *)
    + etrans; eauto. unfold src_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. destruct (f' x0) eqn:T; ss. destruct p; ss. inv H5.
        exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *. unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + etrans; eauto. unfold tgt_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. ii. destruct (inj b0) eqn:T; ss.
        -- destruct p; ss. exploit H4; eauto. i; clarify.
           eapply PR; et. eapply external_call_max_perm; et. eapply Mem.valid_block_inject_1; try apply T; et.
        -- inv H5. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *. unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + inv H2. xomega.
    + inv H3. xomega.
Qed.

Local Existing Instance SimMemInj.
Local Existing Instance SimSymbId.

Lemma sim_skenv_symbols_inject
      sm0 ss0 skenv_src skenv_tgt
      (SIMSKE: SimSymb.sim_skenv sm0 ss0 skenv_src skenv_tgt):
    symbols_inject sm0.(SimMemInj.inj) skenv_src skenv_tgt.
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





Require Import JunkBlock.

Section JUNK.

Lemma inject_junk_blocks_tgt
      sm0 n m_tgt0
      (MWF: SimMem.wf sm0)
      (JUNKTGT: assign_junk_blocks sm0.(SimMem.tgt) n = m_tgt0):
    exists sm1,
      (<<DEF: sm1 = update sm0 sm0.(SimMem.src) m_tgt0 sm0.(SimMemInj.inj)>>) /\
      (<<MWF: SimMem.wf sm1>>) /\
      (<<MLE: SimMem.le sm0 sm1>>) /\
      (<<PRIVSRC: (SimMemInj.src_private sm0) = (SimMemInj.src_private sm1)>>) /\
      (<<PRIVTGT: (SimMemInj.tgt_private sm0) <2= (SimMemInj.tgt_private sm1)>>).
Proof.
  esplits; eauto.
  - ss. inv MWF. econs; ss; eauto.
    + clear - PUBLIC. destruct sm0; ss. clear_tac. ginduction n; ii; ss. des_ifs.
      eapply IHn; eauto. eapply Mem.alloc_right_inject; eauto.
    + etrans; eauto. clear - n. unfold tgt_private. ss. ii. des. esplits; et.
      unfold valid_blocks, Mem.valid_block in *. rewrite assign_junk_blocks_nextblock. des_ifs. xomega.
    + etrans; eauto. rewrite assign_junk_blocks_nextblock. des_ifs; xomega.
  - clarify. econs; ss; eauto.
    + refl.
    + eapply Mem.unchanged_on_implies; try eapply assign_junk_blocks_unchanged_on; et. ss.
    + econs; eauto. ii. des. des_ifs.
    + econs; eauto. ii. des. des_ifs.
    + i. rewrite assign_junk_blocks_perm. ss.
  - clarify. clear - n. unfold tgt_private. ss. ii. des. esplits; et.
    unfold valid_blocks, Mem.valid_block in *. rewrite assign_junk_blocks_nextblock. des_ifs. xomega.
Qed.

Definition inject_junk_blocks (m_src0 m_tgt0: mem) (n: nat) (j: meminj): meminj :=
  if (Zerob.zerob n) then j else
  fun blk =>
    if negb (plt blk m_src0.(Mem.nextblock)) && (plt blk (Mem.nextblock m_src0 + Pos.of_nat n))
    then Some ((blk + m_tgt0.(Mem.nextblock) - m_src0.(Mem.nextblock))%positive , 0%Z)
    else j blk.

Lemma inject_junk_blocks_parallel
      sm0 n m_tgt0
      (MWF: SimMem.wf sm0)
      (JUNKTGT: assign_junk_blocks sm0.(SimMem.tgt) n = m_tgt0):
    exists sm1,
      (<<DEF: sm1 = update sm0 (assign_junk_blocks sm0.(SimMem.src) n) m_tgt0
                           (inject_junk_blocks sm0.(SimMem.src) sm0.(SimMem.tgt) n sm0.(SimMemInj.inj))>>) /\
      (<<MWF: SimMem.wf sm1>>) /\
      (<<MLE: SimMem.le sm0 sm1>>) /\
      (<<PRIVSRC: (SimMemInj.src_private sm0) = (SimMemInj.src_private sm1)>>) /\
      (<<PRIVTGT: (SimMemInj.tgt_private sm0) <2= (SimMemInj.tgt_private sm1)>>).
Proof.
  unfold inject_junk_blocks. esplits; eauto.
  - ss. inv MWF. econs; ss; eauto.
    + clear - PUBLIC. destruct sm0; ss. clear_tac.
      Local Opaque Pos.of_nat.
      ginduction n; ii; ss.
      * des_ifs_safe.
        exploit Mem.alloc_parallel_inject; try apply Heq; try refl; eauto. intro Q; des. rewrite Q in *. clarify.
        exploit IHn; try apply Q0; eauto. intro P. clear IHn.
        rpapply P. clear P. apply func_ext1. i.
        exploit Mem.alloc_result; try apply Heq; intro X. clarify.
        exploit Mem.nextblock_alloc; try apply Heq; intro X.
        exploit Mem.alloc_result; try apply Q; intro Y. clarify.
        exploit Mem.nextblock_alloc; try apply Q; intro Y.
        rewrite ! X. rewrite ! Y. unfold block in *. destruct n; ss.
        { des_ifs.
          - bsimpl. des. des_sumbool.
            exploit (Plt_succ_inv x0 (Mem.nextblock src)); eauto.
            { Local Transparent Pos.of_nat. unfold Pos.of_nat in *. xomega. Local Opaque Pos.of_nat. }
            intro R. des; clarify; try xomega. rewrite Q2. repeat f_equal; ss. xomega.
          - rewrite Q3; ss. ii; clarify. bsimpl; des; des_sumbool; xomega.
        }
        destruct (classic (x0 = (Mem.nextblock src))).
        { clarify. des_ifs; bsimpl; des; des_sumbool; ss; try xomega.
          rewrite Q2. repeat f_equal. xomega.
        }
        destruct (classic (x0 = Pos.succ (Mem.nextblock src))).
        { clarify. des_ifs; bsimpl; des; des_sumbool; ss; try xomega.
          - do 2 f_equal. xomega.
          - exfalso. Local Transparent Pos.of_nat. ss. des_ifs; try xomega. Local Opaque Pos.of_nat.
        }
        des_ifs; bsimpl; des; des_sumbool; ss; try xomega.
        { do 2 f_equal. xomega. }
        { exfalso. Local Transparent Pos.of_nat. ss. des_ifs; try xomega. Local Opaque Pos.of_nat. }
        { exfalso. Local Transparent Pos.of_nat. ss. des_ifs; try xomega. Local Opaque Pos.of_nat. }
        { rewrite Q3; ss. }
        { rewrite Q3; ss. }
    + etrans; eauto.
      clear - n. unfold src_private. ss. unfold valid_blocks, Mem.valid_block in *. ii. des. esplits; et.
      * des_ifs. rr. rr in PR. des_ifs. destruct n; ss. bsimpl; des; des_sumbool; try xomega.
      * rewrite assign_junk_blocks_nextblock. des_ifs. xomega.
    + etrans; eauto.
      clear - n. unfold tgt_private. ss. unfold valid_blocks, Mem.valid_block in *. ii. des. esplits; et.
      * ii. rewrite assign_junk_blocks_perm in *. rr in PR. des_ifs; eauto.
        destruct n; ss. bsimpl; des; des_sumbool; clarify. xomega.
      * rewrite assign_junk_blocks_nextblock. des_ifs. xomega.
    + etrans; eauto. rewrite assign_junk_blocks_nextblock. des_ifs; xomega.
    + etrans; eauto. rewrite assign_junk_blocks_nextblock. des_ifs; xomega.
  - econs; ss; eauto.
    + ii. des_ifs. bsimpl. des. des_sumbool. inv MWF. inv PUBLIC.
      exploit mi_freeblocks; eauto. i; clarify.
    + eapply Mem.unchanged_on_implies.
      { eapply assign_junk_blocks_unchanged_on; et. }
      ii. ss.
    + clarify. eapply Mem.unchanged_on_implies.
      { eapply assign_junk_blocks_unchanged_on; et. }
      ii. ss.
    + econs; eauto. ii. des. des_ifs. bsimpl. des. des_sumbool. inv MWF. esplits; eauto with xomega.
    + econs; eauto. ii. des. des_ifs. bsimpl. des. des_sumbool. inv MWF. esplits; eauto with xomega.
    + i. rewrite assign_junk_blocks_perm. ss.
    + i. clarify. rewrite assign_junk_blocks_perm. ss.
  - ss. repeat (apply func_ext1; i). apply AxiomsC.prop_ext.
    unfold src_private, loc_unmapped, valid_blocks in *. ss. inv MWF. split; i; des.
    + unfold Mem.valid_block in *. destruct n; ss. des_ifs; bsimpl; des; des_sumbool; try xomega.
      esplits; eauto. rewrite assign_junk_blocks_nextblock; ss.
      erewrite Mem.nextblock_alloc; eauto. destruct n; ss; try xomega.
    + destruct n; ss. unfold Mem.valid_block in *. des_ifs; bsimpl; des; des_sumbool; try xomega; split; ss.
      rewrite assign_junk_blocks_nextblock in *; ss. erewrite Mem.nextblock_alloc in H0; eauto. des_ifs; try xomega.
      contradict Heq0. Local Transparent Pos.of_nat. ss. des_ifs; try xomega. Local Opaque Pos.of_nat.
  - ii. unfold tgt_private, loc_out_of_reach, valid_blocks in *. ss. inv MWF.
    + unfold Mem.valid_block in *. split; ss; cycle 1.
      * rewrite assign_junk_blocks_nextblock in *; ss. des_ifs; xomega.
      * i. rewrite assign_junk_blocks_perm. (* TODO: change lemma into symmetric version *)
        des_ifs; bsimpl; des; des_sumbool; et; try xomega.
Qed.

End JUNK.

Lemma Mem_free_parallel'
      sm0 blk_src blk_tgt ofs_src ofs_tgt sz m_src0
      (MWF: wf' sm0)
      (VAL: Val.inject sm0.(inj) (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
      (FREESRC: Mem.free sm0.(src) blk_src (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned (ofs_src) + sz) = Some m_src0):
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<FREETGT: Mem.free sm0.(tgt) blk_tgt (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned (ofs_tgt) + sz) = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>).
Proof.
  inv VAL. destruct (zlt 0 sz).
  - exploit SimMemInj.free_parallel; eauto. i. des. esplits; eauto. inv MWF. erewrite Mem.address_inject; eauto.
    + replace (Ptrofs.unsigned ofs_src + delta + sz) with
          (Ptrofs.unsigned ofs_src + sz + delta); [eauto|lia].
    + eapply Mem.free_range_perm; eauto. lia.
  - exploit SimMemInj.free_parallel; eauto. i. des. esplits; eauto. erewrite Mem_free_zero_same; eauto; lia.
Qed.

Lemma storebytes_mapped
      sm0 b tb ofs bytes1 bytes2 m_src delta
      (MWF : SimMemInj.wf' sm0)
      (STRSRC: Mem.storebytes (SimMemInj.src sm0) b ofs bytes1 = Some m_src)
      (SIMBLK: (SimMemInj.inj sm0) b = Some (tb, delta))
      (BYTESINJ: list_forall2 (memval_inject (SimMemInj.inj sm0)) bytes1 bytes2):
    exists sm1,
      (<<MSRC: (SimMemInj.src sm1) = m_src>>)
      /\ (<<MINJ: (SimMemInj.inj sm1) = (SimMemInj.inj sm0)>>)
      /\ (<<STRTGT: Mem.storebytes (SimMemInj.tgt sm0) tb (ofs + delta) bytes2 = Some (SimMemInj.tgt sm1)>>)
      /\ (<<MWF: SimMemInj.wf' sm1>>)
      /\ (<<MLE: SimMemInj.le' sm0 sm1>>)
.
Proof.
  exploit Mem.storebytes_mapped_inject; eauto.
  { inv MWF. eauto. }
  i. des. inv MWF. eexists (SimMemInj.mk _ _ _ _ _ _ _ _ _). esplits; ss; eauto; cycle 1.
  - econs; ss; eauto; try (eapply SimMemInj.frozen_refl); try (ii; eapply Mem.perm_storebytes_2; eauto).
    + eapply Mem.storebytes_unchanged_on; eauto. ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
    + eapply Mem.storebytes_unchanged_on; eauto. ii. apply TGTEXT in H2. red in H2. des. red in H2.
      eapply H2; eauto. clear - BYTESINJ STRSRC H1 H4.
      eapply Mem.storebytes_range_perm in STRSRC.
      assert (Datatypes.length bytes2 = Datatypes.length bytes1).
      { exploit list_forall2_length; eauto. }
      rewrite H in *.
      assert (ofs <= i - delta) by nia.
      assert (i - delta < ofs + Z.of_nat (Datatypes.length bytes1)) by nia.
      unfold Mem.range_perm in STRSRC.
      specialize (STRSRC (i - delta)). exploit STRSRC. nia.
      i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. eapply perm_any_N.
  - econs; ss; eauto; try (by etransitivity; eauto; erewrite <- Mem.nextblock_storebytes; eauto; refl).
    + etransitivity; eauto. unfold SimMemInj.src_private. ss. ii; des. esplits; eauto.
      unfold SimMemInj.valid_blocks, Mem.valid_block in *.
      erewrite Mem.nextblock_storebytes; eauto.
    + etransitivity; eauto. unfold SimMemInj.tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR; eauto. eapply Mem.perm_storebytes_2; eauto. }
      unfold SimMemInj.valid_blocks, Mem.valid_block in *.
      erewrite Mem.nextblock_storebytes; eauto.
Qed.




Require Import SeparationC.

Section SEP.

Local Open Scope sep_scope.
Lemma minjection_disjoint_footprint_private
      sm0 P
      (SEP: (SimMemInj.tgt sm0) |= P)
      (DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P):
    P.(m_footprint) <2= (SimMemInj.tgt_private sm0).
Proof.
  u. ii. esplits; eauto.
  - ii. eapply DISJ; eauto. ss. esplits; eauto.
  - destruct P; ss. eapply m_valid; eauto.
Qed.

Lemma minjection_private_disjoint_footprint
      sm0 P
      (PRIV: P.(m_footprint) <2= (SimMemInj.tgt_private sm0)):
    <<DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P>>.
Proof.
  - ii. ss. des. eapply PRIV; eauto.
Qed.

Lemma external_call_parallel_rule_simmem
      (F V: Type) (ge0: Genv.t F V)
      sm_at sm_after P
      (SEP: sm_at.(SimMem.tgt) |= (minjection sm_at.(SimMemInj.inj) sm_at.(SimMem.src))
                             ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P)
      sm_arg sm_ret
      (MWF: SimMem.wf sm_at)
      (MWF0: SimMem.wf sm_arg)
      (MWF1: SimMem.wf sm_ret)
      (MWF2: SimMem.wf sm_after)
      (MWFAFTR : SimMem.wf (SimMemInj.unlift' sm_arg sm_ret))
      (MLE: SimMem.le sm_at sm_arg)
      (MLE0: SimMem.le (SimMemLift.lift sm_arg) sm_ret)
      (MLE1: SimMem.le (SimMemLift.unlift sm_at sm_ret) sm_after)
      (MLEAFTR: SimMem.le sm_arg (SimMemLift.unlift sm_arg sm_ret))
      (PRIV0: (SimMemInj.tgt_private sm_at) = (SimMemInj.tgt_private sm_arg))
      (PRIV1: (SimMemInj.tgt_private sm_ret) = (SimMemInj.tgt_private sm_after))
      (UNCH0: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_at) (SimMemInj.tgt sm_arg))
      (UNCH1: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_ret) (SimMemInj.tgt sm_after)):
    <<SEP: sm_after.(SimMem.tgt) |= (minjection sm_after.(SimMemInj.inj) sm_after.(SimMem.src))
                            ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P>>.
Proof.
  (* See external_call_parallel_rule *)
  destruct SEP as (A & B & C). simpl in A.
  apply disjoint_footprint_sepconj in C. des. ss.
  eapply minjection_disjoint_footprint_private in DISJ1; cycle 1.
  { des. ss. }
  sep_split.
  { ss. eapply MWF2. }
  { apply disjoint_footprint_sepconj. ss. split; ss.
    apply minjection_private_disjoint_footprint. etrans; eauto.
    rewrite PRIV0. rewrite <- PRIV1. inv MLEAFTR. inv MLE0. inv MWF0. inv MWF1. ss.
    etrans; try apply TGTEXT0; eauto. rewrite TGTPARENTEQ0. reflexivity. }
  sep_split.
  { eapply globalenv_inject_incr in B; eauto.
    - apply sep_pick1 in B. ss. des. esplits; eauto.
      etrans; eauto. inv MLE. inv MLE0. inv MLE1. inv MLEAFTR.
      etrans; eauto with mem. etrans; eauto with mem.
    - apply SimMemInj.inject_separated_frozen; eauto.
      eapply SimMemInj.frozen_refl; eauto.
  }
  { ss. }
  destruct B as (X & Y & Z); ss.
  eapply m_invar; eauto. eapply Mem.unchanged_on_implies; cycle 1.
  { ii. exploit DISJ1; eauto. }
  rewrite PRIV0. etrans.
  { instantiate (1:= (SimMemInj.tgt sm_arg)). eauto. }
  etrans; cycle 1.
  { instantiate (1:= (SimMemInj.tgt sm_ret)). eauto. }
  clears sm_after. clear sm_after. clears sm_at. clear sm_at. inv MLE0. ss.
Unshelve.
  all: try apply Mem.empty.
Qed.

Lemma sim_skenv_inj_globalenv_inject
      F `{HasExternal F} V
      ss skenv_proj_src skenv_proj_tgt sm_arg (prog: AST.program F V) m_tgt0
      (SIMSKE: sim_skenv_inj sm_arg ss skenv_proj_src skenv_proj_tgt)
      (NB: Ple (Genv.genv_next skenv_proj_src) (Mem.nextblock m_tgt0)):
    m_tgt0 |= globalenv_inject (SkEnv.revive skenv_proj_src prog) (SimMemInj.inj sm_arg).
Proof.
  ss. inv SIMSKE. inv INJECT. esplits; et.
  - econs; et.
    + ii. exploit Genv.genv_symb_range; eauto.
    + ii. uge0. des_ifs. exploit Genv.genv_defs_range; eauto.
    + ii. uge0. des_ifs. exploit Genv.genv_defs_range; eauto.
Qed.

End SEP.
