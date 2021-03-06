Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC SimMemLift SimMemInjC.
Require Import Conventions1.
Require Export SimMemInj.
Require StoreArguments.

Set Implicit Arguments.

Local Opaque Z.mul.

Hint Unfold valid_blocks src_private tgt_private range.

Lemma mach_store_arguments_simmem
      sm0 rs vs sg m_tgt0
      (MWF: SimMem.wf sm0)
      (STORE: StoreArguments.store_arguments sm0.(SimMem.tgt) rs vs sg m_tgt0):
      (*** TODO: don't use unchanged_on, it is needlessly complex for our use. just define my own. *)
    exists sm1,
    <<SM: sm1 = (mk sm0.(src) m_tgt0 sm0.(inj)
                         sm0.(src_external) sm0.(tgt_external)
                         sm0.(src_parent_nb) sm0.(tgt_parent_nb)
                         sm0.(src_ge_nb) sm0.(tgt_ge_nb))>> /\
    <<MWF: SimMem.wf sm1>> /\
    <<MLE: SimMem.le sm0 sm1>> /\
    <<PRIV: forall ofs (IN: 0 <= ofs < 4 * size_arguments sg),
             (tgt_private sm1) sm0.(SimMem.tgt).(Mem.nextblock) ofs>>.
Proof.
  i. subst_locals. inv STORE.
  exploit Mem.alloc_right_inject; try apply MWF; eauto. i; des.
  hexpl Mem.alloc_result. clarify.
  hexpl Mem.nextblock_alloc.
  esplits; eauto.
  - econs; ss; try apply MWF; eauto.
    + eapply Mem.inject_extends_compose; eauto. econs; eauto.
      { econs.
        - ii. inv H0. replace (ofs + 0) with ofs by omega.
          destruct (eq_block b2 (Mem.nextblock (tgt sm0))); destruct (zle 0 ofs); destruct (zlt ofs (4 * size_arguments sg));
            try (eapply Mem.perm_unchanged_on; eauto; ss; des_ifs; omega).
          subst b2. exploit (PERM ofs). omega. i. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
        - ii. inv H0. eapply Z.divide_0_r.
        - ii. inv H0. replace (ofs + 0) with ofs by omega.
          destruct (eq_block b2 (Mem.nextblock (tgt sm0))); destruct (zle 0 ofs); destruct (zlt ofs (4 * size_arguments sg));
            try (exploit Mem.unchanged_on_contents; eauto; ss; des_ifs; try omega; i; rewrite H0; eapply memval_inject_Reflexive).
          Transparent Mem.alloc. unfold Mem.alloc in ALC. inv ALC. ss.
          rewrite PMap.gss. rewrite ZMap.gi. eapply memval_inject_undef.
      }
      { i. left. assert(Mem.valid_block m1 b).
        { r. rewrite NB. eapply Mem.perm_valid_block; eauto. }
        destruct (eq_block b (Mem.nextblock (tgt sm0))) eqn:BEQ; destruct (zle 0 ofs); destruct (zlt ofs (4 * size_arguments sg));
          try by (eapply Mem.perm_unchanged_on_2; eauto; ss; rewrite BEQ; eauto; try omega).
        subst b. eapply Mem.perm_cur. eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto. econs.
      }
    + etransitivity; try apply MWF; eauto. unfold tgt_private. ss. u. ii; des. esplits; eauto with congruence.
      unfold Mem.valid_block in *. rewrite <- NB in *. eauto with xomega.
    + etransitivity; try apply MWF; eauto with mem congruence. rewrite <- NB. lia.
  - econs; ss; try eapply frozen_refl.
    + eauto with mem xomega.
    + inv MWF. etrans.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eapply Mem.unchanged_on_implies; eauto. i. ss. des_ifs. apply TGTEXT in H0. u in H0. des.
      exfalso. eapply Mem.fresh_block_alloc; eauto.
    + ii. eauto with mem xomega.
    + i. r. etrans; cycle 1.
      { ii. eapply Mem.perm_alloc_4; et. }
      { ii. eapply Mem.perm_unchanged_on_2; et.
        - ss. des_ifs. unfold Mem.valid_block in *. xomega.
        - unfold Mem.valid_block in *. xomega.
      }
  - ii. u. esplits; eauto.
    + ii. exploit Mem.mi_perm; try apply MWF; eauto. i.
      zsimpl. hexpl Mem_alloc_fresh_perm. eapply NOPERM; eauto.
    + unfold Mem.valid_block. rewrite <- NB. ss. eauto with xomega.
Qed.
