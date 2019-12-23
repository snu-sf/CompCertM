Require Import FunInd.
Require Import Zwf CoqlibC Maps Integers Floats Lattice.
Require Import Compopts AST.
Require Import Values MemoryC Globalenvs Events.
Require Import Registers RTL.
Require Import sflib.
(** newly added **)
Require Export ValueDomain.
Require Import Skeleton.
Require Import Sound UnreachC.
Require Import ModSem.

(* TODO: remove redundancy, move it to ValueDomain maybe *)
Definition bc2su (bc: block_classification) (ge_nb: block) (nb: block): Unreach.t :=
  Unreach.mk (fun blk => if plt blk nb then block_class_eq (bc blk) BCinvalid else false) ge_nb nb.

Lemma sound_state_sound_args
      bc m0 p skenv_link vs_arg rm (ge: genv)
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig p)) p))
      (ARGS: forall v : val, In v vs_arg -> vmatch bc v Vtop)
      (RO: romatch bc m0 rm)
      (MM: mmatch bc m0 mtop)
      (GE: genv_match bc ge)
      (NOSTK: forall b, bc b <> BCstack)
      fptr_arg sg_arg
      (SIG: exists skd, Genv.find_funct skenv_link fptr_arg = Some skd /\ Sk.get_csig skd = sg_arg):
    args' (bc2su bc ge.(Genv.genv_next) m0.(Mem.nextblock)) (Args.mk fptr_arg vs_arg m0).
Proof.
  { r. s. esplits; eauto.
    - des. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. ss. r. ii; clarify. ss.
      r in GE. des. specialize (GE0 blk). exploit GE0; eauto.
      { ss. eapply Genv.genv_defs_range; eauto. }
      i; des.
      (* exploit sound_stack_unreach_compat; eauto. intro CPT. des. *)
      (* inv SU. ss. *)
      esplits; eauto.
      + ii. des_ifs. des_sumbool. congruence.
      + inv MM. eapply mmatch_below; eauto. rewrite H; ss.
    - rewrite Forall_forall. i. spcN 1 ARGS. spc ARGS. ii; clarify.
      assert(BCV: bc blk <> BCinvalid).
      { inv ARGS; ss. inv H1; ss. }
      esplits; eauto.
      + u. ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
    - inv MM. econs; eauto.
      + ii. clarify.
        assert(BCV: bc blk <> BCinvalid).
        { u in PUB. ii. rewrite H in *. ss. exploit Mem.perm_valid_block; eauto. i; des. des_ifs. }
        assert(BCV0: bc blk0 <> BCinvalid).
        {
          exploit mmatch_top; eauto.
          (* spcN 0%nat mmatch_top. spc mmatch_top. inv mmatch_top. *)
          intro SM. inv SM.
          specialize (H0 ofs%Z blk0 ofs0 q n).
          exploit H0.
          { eapply Mem_loadbytes_succeeds; et. }
          intro PM.
          inv PM. ss.
        }
        esplits; eauto.
        { u. des_ifs. i; des_sumbool; ss. }
        s. eapply mmatch_below; eauto.
      + u. ii. des_ifs.
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. { rewrite H0; ss. } i; des. xomega.
    - econs; ss; i; des_ifs. r in GE. des. ss. des_sumbool. apply NNPP. ii.
      exploit (GE0 x0); eauto. { xomega. } i; des. congruence.
  }
Qed.

(* copied from above *)
Lemma sound_state_sound_retv
      bc m_ret p skenv_link v_ret rm (ge: genv)
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig p)) p))
      (RES: vmatch bc v_ret Vtop)
      (RO: romatch bc m_ret rm)
      (MM: mmatch bc m_ret mtop)
      (GE: genv_match bc ge)
      (NOSTK: forall b, bc b <> BCstack):
    Sound.retv (bc2su bc ge.(Genv.genv_next) m_ret.(Mem.nextblock)) (Retv.mk v_ret m_ret).
Proof.
  { r. s. esplits; eauto.
    - ii; clarify.
      assert(BCV: bc blk <> BCinvalid).
      { inv RES; ss. inv H0; ss. }
      esplits; eauto.
      + u. ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
    - inv MM. econs; eauto.
      + ii. clarify.
        assert(BCV: bc blk <> BCinvalid).
        { u in PUB. ii. rewrite H in *. ss. exploit Mem.perm_valid_block; eauto. i; des. des_ifs. }
        assert(BCV0: bc blk0 <> BCinvalid).
        {
          exploit mmatch_top; eauto.
          (* spcN 0%nat mmatch_top. spc mmatch_top. inv mmatch_top. *)
          intro SM. inv SM.
          specialize (H0 ofs blk0 ofs0 q n).
          exploit H0.
          { eapply Mem_loadbytes_succeeds; et. }
          intro PM. inv PM. ss.
        }
        esplits; eauto.
        { u. des_ifs. i; des_sumbool; ss. }
        s. eapply mmatch_below; eauto.
      + u. ii. des_ifs.
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. { rewrite H0; ss. } i; des. xomega.
    - econs; eauto; ss; i; des_ifs. des_sumbool.
      rr in GE. des. apply NNPP. ii.
      exploit (GE0 x0); eauto.
      { unfold fundef in *. xomega. }
      i; des. congruence.
  }
Qed.
