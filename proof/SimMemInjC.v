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
Require Import Conventions1.
Require MachC.
Require Export SimMemInj.

Set Implicit Arguments.



Section MEMINJ.

Context `{CTX: Val.meminj_ctx}.

Definition update (sm0: t') (src tgt: mem) (inj: meminj): t' :=
  mk src tgt inj sm0.(src_external) sm0.(tgt_external) sm0.(src_parent_nb) sm0.(tgt_parent_nb)
.
Hint Unfold update.
(* Notation "sm0 '.(update_tgt)' tgt" := (sm0.(update) sm0.(src) tgt sm0.(inj)) (at level 50). *)
(* Definition update_tgt (sm0: t') (tgt: mem) := (sm0.(update) sm0.(src) tgt sm0.(inj)). *)
(* Definition update_src (sm0: t') (src: mem) := (sm0.(update) src sm0.(tgt) sm0.(inj)). *)
(* Hint Unfold update_src update_tgt. *)

Hint Unfold src_private tgt_private valid_blocks.

Lemma update_src_private
      sm0 sm1
      (INJ: sm0.(inj) = sm1.(inj))
      (SRC: sm0.(src).(Mem.nextblock) = sm1.(src).(Mem.nextblock))
  :
    sm0.(src_private) = (sm1).(src_private)
.
Proof.
  repeat (apply Axioms.functional_extensionality; i). apply prop_ext1.
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
  eapply unlift_spec; eauto.
Qed.
Next Obligation.
  eapply unlift_wf; eauto.
Qed.
Next Obligation.
  ii. inv MLE. eapply val_inject_incr; eauto.
Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i).
  apply prop_ext1.
  split; i; ss; clarify.
  - ginduction x; ii; inv H; ss.
    econs; eauto.
  - ginduction x1; ii; inv H; ss.
    econs; eauto.
Qed.

Section ORIGINALS.

Inductive le_excl (excl_src excl_tgt: block -> Z -> Prop) (mrel0 mrel1: t'): Prop :=
| le_excl_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (SRCUNCHANGED: Mem.unchanged_on mrel0.(src_external) mrel0.(src) mrel1.(src))
    (TGTUNCHANGED: Mem.unchanged_on mrel0.(tgt_external) mrel0.(tgt) mrel1.(tgt))
    (SRCPARENTEQ: mrel0.(src_external) = mrel1.(src_external))
    (SRCPARENTEQNB: mrel0.(src_parent_nb) = mrel1.(src_parent_nb))
    (TGTPARENTEQ: mrel0.(tgt_external) = mrel1.(tgt_external))
    (TGTPARENTEQNB: mrel0.(tgt_parent_nb) = mrel1.(tgt_parent_nb))
    (FROZEN: frozen mrel0.(inj) mrel1.(inj) (mrel0.(src_parent_nb))
                                            (mrel0.(tgt_parent_nb)))
    (MAXSRC: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(src) b)
        (EXCL: ~ excl_src b ofs)
      ,
        <<MAX: Mem.perm mrel1.(src) b ofs Max <1= Mem.perm mrel0.(src) b ofs Max>>)
    (MAXTGT: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(tgt) b)
        (EXCL: ~ excl_tgt b ofs)
      ,
        <<MAX: Mem.perm mrel1.(tgt) b ofs Max <1= Mem.perm mrel0.(tgt) b ofs Max>>)
.

Inductive has_footprint (excl_src excl_tgt: block -> Z -> Prop) (sm0: t'): Prop :=
| has_footprint_intro
    (FOOTSRC: forall
        blk ofs
        (EXCL: excl_src blk ofs)
      ,
        <<PERM: Mem.perm sm0.(src) blk ofs Cur Freeable>>)
    (FOOTTGT: forall
        blk ofs
        (EXCL: excl_tgt blk ofs)
      ,
        <<PERM: Mem.perm sm0.(tgt) blk ofs Cur Freeable>>)
.

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
      /\ (<<MLE: le_excl bot2 (brange blk lo hi) sm0 sm1>>)
.
Proof.
  exists (sm0.(update) sm0.(src) m_tgt0 sm0.(inj)).
  exploit Mem_unfree_unchanged_on; et. intro UNCH.
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
    + eapply Mem.unchanged_on_implies. { eapply Mem_unfree_unchanged_on; eauto. } ii. eapply RANGE; et.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_unchanged_on_2; et.
Qed.

Lemma foot_excl
      sm0 sm1 sm2 excl_src excl_tgt
      (FOOT: has_footprint excl_src excl_tgt sm0)
      (MLE: le' sm0 sm1)
      (MLEEXCL: le_excl excl_src excl_tgt sm1 sm2)
  :
    <<MLE: le' sm0 sm2>>
.
Proof.
  inv MLE. inv MLEEXCL.
  econs; et.
  - etrans; et.
  - etrans; et. rewrite SRCPARENTEQ. ss.
  - etrans; et. rewrite TGTPARENTEQ. ss.
  - etrans; et.
  - etrans; et.
  - etrans; et.
  - etrans; et.
  - clear - FROZEN FROZEN0 INCR0 SRCPARENTEQNB TGTPARENTEQNB.
    inv FROZEN. inv FROZEN0. econs.
    i. des.
    destruct (inj sm1 b_src) eqn:T.
    + destruct p; ss. exploit INCR0; et. i; clarify.
      exploit NEW_IMPLIES_OUTSIDE; et.
    + exploit NEW_IMPLIES_OUTSIDE0; et. i; des. esplits; eauto with congruence xomega.
  - ii.
    destruct (classic (excl_src b ofs)).
    + inv FOOT. eapply Mem.perm_cur_max. eapply Mem.perm_implies with (p1 := Freeable); [|eauto with mem].
      eapply FOOTSRC; et.
    + eapply MAXSRC; et.
      eapply MAXSRC0; et.
      eapply Mem.valid_block_unchanged_on; et.
  - ii.
    destruct (classic (excl_tgt b ofs)).
    + inv FOOT. eapply Mem.perm_cur_max. eapply Mem.perm_implies with (p1 := Freeable); [|eauto with mem].
      eapply FOOTTGT; et.
    + eapply MAXTGT; et.
      eapply MAXTGT0; et.
      eapply Mem.valid_block_unchanged_on; et.
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
    - ii. eauto with mem.
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

(*************** TODO: Move to MachExtra.v *********************)
Lemma mach_store_arguments_simmem
      sm0 rs vs sg m_tgt0
      (MWF: SimMem.wf sm0)
      (STORE: StoreArguments.store_arguments sm0.(SimMem.tgt) rs vs sg m_tgt0)
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
  - econs; ss.
    + eauto with mem xomega.
    + inv MWF.
      etrans.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eapply Mem.unchanged_on_implies; eauto.
      i. ss. des_ifs. apply TGTEXT in H0. u in H0. des.
      exfalso. eapply Mem.fresh_block_alloc; eauto.
    + eapply frozen_refl.
    + ii. eauto with mem xomega.
    + i. r.
      etrans; cycle 1.
      {
        ii.
        eapply Mem.perm_alloc_4; et.
        { eauto with mem. }
      }
      { ii. eapply Mem.perm_unchanged_on_2; et.
        - ss. des_ifs. unfold Mem.valid_block in *. xomega.
        - unfold Mem.valid_block in *. xomega.
      }
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

Local Existing Instance Val.mi_normal.
(* Context `{CTX: Val.meminj_ctx}. *)

(* Inductive skenv_inject (skenv: SkEnv.t) (j: meminj): Prop := *)
(* | sken_inject_intro *)
(*     (DOMAIN: forall b, Plt b skenv.(Genv.genv_next) -> j b = Some(b, 0)) *)
(*     (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 skenv.(Genv.genv_next) -> b1 = b2) *)
(* . *)

Lemma skenv_inject_meminj_preserves_globals
      F V (skenv: Genv.t F V) j
      (INJECT: skenv_inject skenv j)
  :
    <<INJECT: meminj_preserves_globals skenv j>>
.
Proof.
  inv INJECT.
  rr. esplits; ii; ss; eauto.
  - eapply DOMAIN; eauto. eapply Genv.genv_symb_range; eauto.
  - eapply DOMAIN; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
  - symmetry. eapply IMAGE; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
Qed.

Inductive sim_skenv_inj (sm: SimMem.t) (__noname__: unit) (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INJECT: skenv_inject skenv_src sm.(inj))
    (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_parent_nb))
    (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_parent_nb))
    (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
.

Section REVIVE.

  Context {F1 V1: Type} {LF: Linker F1} {LV: Linker V1}.
  Context `{HasExternal F1}.
  Variables (p_src: AST.program F1 V1).

  Lemma skenv_inject_revive
        skenv_proj_src
        ge_src
        j
        (REVIVESRC: ge_src = SkEnv.revive skenv_proj_src p_src)
        (SIMSKENV: skenv_inject skenv_proj_src j)
    :
      <<SIMSKENV: skenv_inject ge_src j>>
  .
  Proof.
    clarify. inv SIMSKENV. econs; eauto.
  Qed.

End REVIVE.




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
  rr in SIMSK. clarify.
Qed.
Next Obligation.
  eapply SimSymbId.sim_sk_link; eauto.
Qed.
Next Obligation.
  inv SIMSKE. inv SIMSKENV. ss.
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
  set (SkEnv.project skenv_link_src sk_src) as skenv_proj_src.
  generalize (SkEnv.project_impl_spec INCLSRC); intro LESRC.
  set (SkEnv.project skenv_link_tgt sk_tgt) as skenv_proj_tgt.
  generalize (SkEnv.project_impl_spec INCLTGT); intro LETGT.
  exploit SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto.
  i; des.
  inv SIMSKENV. inv LESRC. inv LETGT.
  econs; eauto.
  { inv INJECT.
    econs; ii; eauto.
  }
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
      exploit IMAGE; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify.
      exploit DOMAIN; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify.
      rewrite e. rewrite Ptrofs.add_zero in *. clarify.
    }
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
  - inv INJECT. econs; eauto.
  - eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  destruct sm0, args_src, args_tgt; ss. inv MWF; ss. inv ARGS; ss. clarify.
  (* Note: It may be easier && more natural to use
"external_call_mem_inject" with "external_call_symbols_preserved", instead of "external_call_mem_inject_gen" *)
  (* exploit external_call_mem_inject_gen; eauto. *)
  exploit external_call_mem_inject; eauto.
  { eapply skenv_inject_meminj_preserves_globals; eauto. inv SIMSKENV; ss. }
  i; des.
  do 2 eexists.
  dsplits; eauto.
  - instantiate (1:= Retv.mk _ _); ss.
    eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. eapply SIMSKENV.
  - instantiate (1:= mk _ _ _ _ _ _ _). econs; ss; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply inject_separated_frozen; eauto.
    + ii. eapply external_call_max_perm; eauto.
    + ii. eapply external_call_max_perm; eauto.
  - apply inject_separated_frozen in H5.
    econs; ss.
    + eapply after_private_src; ss; eauto.
    + eapply after_private_tgt; ss; eauto.
    + inv H2. xomega.
    + inv H3. xomega.
Qed.

Local Existing Instance SimMemInj.
Local Existing Instance SimSymbId.

Lemma sim_skenv_symbols_inject
      sm0 ss0 skenv_src skenv_tgt
      (SIMSKE: SimSymb.sim_skenv sm0 ss0 skenv_src skenv_tgt)
  :
    symbols_inject sm0.(SimMemInj.inj) skenv_src skenv_tgt
.
Proof.
  inv SIMSKE. inv SIMSKENV. inv INJECT. rr. esplits; ss.
  + i. exploit Genv.genv_symb_range; eauto. intro NB. exploit DOMAIN; eauto. i ;des. clarify.
  + i. exploit Genv.genv_symb_range; eauto.
  + i. unfold Genv.block_is_volatile, Genv.find_var_info.
    destruct (Genv.find_def skenv_tgt b1) eqn:T.
    * exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des. clarify. des_ifs.
    * des_ifs. exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des.
      exploit (IMAGE b1 b2); eauto. i; clarify.
Qed.

End SIMSYMB.

Arguments skenv_inject_revive [_ _ _].


