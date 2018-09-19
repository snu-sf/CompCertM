Require Import FunInd.
Require Import CoqlibC Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import Registers Op RTLC.
Require Import ValueDomain ValueAOp Liveness.
Require Import sflib.
(** copied && added C **)
Require Import Skeleton.
Require Export ValueAnalysis.
Require Import Preservation.
Require Import UnreachC.
Require Import Sound.
Require Import ModSem.


Definition bc2su (bc: block_classification) (ge_nb: block) (bound: block): Unreach.t :=
  mk (fun blk => if plt blk bound
                 then block_class_eq (bc blk) BCinvalid
                 else false)
     ge_nb
.
Hint Unfold bc2su.


(* Tactic Notation "spc" hyp(H) := spc H. *)
(* Tactic Notation "spc" hyp(H) constr(n) := spcN H n. *)



Lemma sound_state_sound_args
      bc m0 stack su0 p skenv_link vs_arg cunit
      ge
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (defs p)) p))
      (STK: sound_stack cunit ge su0 bc stack m0 (Mem.nextblock m0))
      (ARGS: forall v : val, In v vs_arg -> vmatch bc v Vtop)
      (RO: romatch bc m0 (romem_for cunit))
      (MM: mmatch bc m0 mtop)
      (GE: genv_match bc ge)
      (NOSTK: bc_nostack bc)
      fptr_arg sg_arg
      (SIG: exists skd, Genv.find_funct skenv_link fptr_arg = Some skd /\ SkEnv.get_sig skd = sg_arg)
  :
    args' (bc2su bc ge.(Genv.genv_next) m0.(Mem.nextblock)) (Args.mk fptr_arg vs_arg m0)
.
Proof.
  { r. s. esplits; eauto.
    - admit "fptr".
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
          specialize (H0 0%Z blk0 ofs0 true q n).
          exploit H0.
          { admit "ez - memory lemma". }
          intro PM.
          inv PM. ss.
        }
        esplits; eauto.
        { u. des_ifs. i; des_sumbool; ss. }
        s. eapply mmatch_below; eauto.
      + u. ii. des_ifs.
    - exploit sound_stack_unreach_compat; eauto. i; des.
      des_ifs. ss. des_sumbool. inv SU.
      r in GE. des. ss. exploit GE0; eauto. i; des. congruence.
  }
Qed.

Section PRSV.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let modsem := RTLC.modsem skenv_link p.

  Local Existing Instance Unreach.

  Theorem sound_state_preservation
    :
      local_preservation_strong modsem get_mem (sound_state p modsem.(globalenv))
  .
  Proof.
    econs; eauto.
    - i. inv INIT. ss.
      esplits; eauto; cycle 1.
      { refl. }
      econs; eauto. i.
      set (ge := (SkEnv.revive (SkEnv.project skenv_link (defs p)) p)) in *.
      set (f := fun b =>
                  if plt b (Genv.genv_next ge) then
                    match Genv.invert_symbol ge b with None => BCother | Some id => BCglob id end
                  else
                    if (plt b args.(Args.m).(Mem.nextblock)) && (negb (su_init b))
                    then BCother
                    else BCinvalid).
      (* set (f := fun b => *)
      (*             if (plt b args.(Args.m).(Mem.nextblock)) *)
      (*             then *)
      (*               match Genv.invert_symbol ge b with *)
      (*               | None => if su_init b then BCinvalid else BCother *)
      (*               | Some id => BCglob id *)
      (*               end *)
      (*             else *)
      (*               BCinvalid). *)
      assert(IMG: exists bc, bc.(bc_img) = f).
      { unshelve eexists (BC _ _ _); s; eauto.
        - ii. subst f. ss. des_ifs.
        - ii. subst f. ss. des_ifs. apply_all_once Genv.invert_find_symbol. clarify.
      }
      subst f. des.
      r in SUARG. des. rewrite Forall_forall in *.
      assert(FP: forall blk, su_init blk -> Ple ge.(Genv.genv_next) blk).
      { admit "forced public". }
      assert(NB: Ple ge.(Genv.genv_next) args.(Args.m).(Mem.nextblock)).
      { admit "forced public". }
      eapply sound_call_state with (bc:= bc); eauto.
      + econs; eauto. econs; eauto.
        * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss.
        * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss.
        * ii. inv MEM. eapply BOUND; eauto.
        * rewrite IMG. ii. des_ifs; ss.
      + ii. repeat spc VALS. destruct v; econs; eauto. destruct b0; econs; eauto. rewrite IMG.
        repeat spc VALS. specialize (VALS eq_refl). (* TODO: fix spc ... *) des.
        des_ifs; ss. bsimpl. des; ss. des_sumbool. ss.
      + admit "forced public".
      + assert(SUMEM: forall b : block, bc b <> BCinvalid -> smatch bc (Args.m args) b Ptop).
        { admit "mem'. this should hold...". }
        econs; s; eauto.
        * rewrite IMG. ii. des_ifs; ss.
        * rewrite IMG. ii. des_ifs; ss. rewrite PTree.gempty in *. ss.
        * intros ? A. rewrite IMG in A. des_ifs; try xomega. bsimpl. des. des_sumbool. xomega.
      + r.
        esplits; eauto.
        * ii. rewrite IMG in *. split; i.
          { exploit Genv.genv_symb_range; eauto. i.
            apply_all_once Genv.find_invert_symbol.
            unfold fundef in *.
            des_ifs.
          }
          des_ifs. apply Genv.invert_find_symbol; eauto.
        * rewrite IMG. ii.
          assert(Plt b (Mem.nextblock (Args.m args))).
          { eapply Plt_Ple_trans; eauto. }
          des_ifs.
      + r. rewrite IMG. i. des_ifs.
    - ii; ss. eapply sound_step; eauto.
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le' (fun su : Unreach.t => args' su args) su_gr).
      { hexploit (Sound.greatest_ex args); eauto.
        specialize (H p (linkorder_refl _)).
        inv AT. inv H; ss.
        exploit sound_state_sound_args; eauto.
      }
      des.
      esplits; eauto.
      ii.
      r in RETV. des.
      esplits; eauto; cycle 1.
      { inv AT; inv AFTER; ss.
        eapply mle_monotone; try apply MLE; eauto.
        specialize (H p (linkorder_refl _)). bar. inv H.
        assert(LE0: su0 <1= (bc2su bc m0.(Mem.nextblock))).
        { ii. exploit sound_stack_unreach_compat; eauto.
          intro CPT. inv CPT. u. repeat spc BOUND. des_ifs. rewrite PRIV; ss.
        }
        assert(LE1: (bc2su bc m0.(Mem.nextblock)) <1= su_gr).
        { ii. eapply GR; eauto. eapply sound_state_sound_args; eauto. }
        i; ss. eauto.
      }
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
        assert(BCARGS: (bc2su bc m_arg.(Mem.nextblock)).(Sound.args) args).
        { ss. inv AT; ss. eapply sound_state_sound_args; eauto. }
        assert(BCLE: Sound.le (bc2su bc m_arg.(Mem.nextblock)) su_gr).
        { ii. eapply GR; eauto. }
        exploit sound_stack_unreach_compat; eauto. intros CPT. des.
        (* set (f := fun b => if plt b retv.(Retv.m).(Mem.nextblock) *)
        (*                    then *)
        (*                      if su_ret b *)
        (*                      then BCinvalid *)
        (*                      else BCother *)
        (*                    else *)
        (*                      BCinvalid *)
        (*     ). *)
        (* set (f := fun b => if plt b (Mem.nextblock m_arg) *)
        (*                    then bc b *)
        (*                    else *)
        (*                      if su_ret b *)
        (*                      then BCinvalid *)
        (*                      else BCother). *)
        (* set (f := fun b => if plt b (Mem.nextblock m_arg) *)
        (*                    then bc b *)
        (*                    else *)
        (*                      if plt b (Mem.nextblock retv.(Retv.m)) *)
        (*                      then *)
        (*                        if su_ret b *)
        (*                        then BCinvalid *)
        (*                        else BCother *)
        (*                      else BCinvalid). *)
        set (f := fun b => if su_ret b
                           then BCinvalid
                           else
                             if plt b (Mem.nextblock m_arg)
                             then bc b
                             else
                               if plt b (Mem.nextblock retv.(Retv.m))
                               then BCother
                               else BCinvalid).
        assert(exists bc', <<IMG: bc'.(bc_img) = f>>).
        { unshelve eexists (BC _ _ _); ss.
          - admit "ez".
          - admit "ez".
        } des.

        assert (VMTOP: forall v, val' su_ret (Mem.nextblock retv.(Retv.m)) v -> vmatch bc' v Vtop).
        { i. r in H. destruct v; econs; eauto. destruct b0; econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs.
          assert(NSU: ~su_gr b).
          { ii. exploit LE; eauto. i; ss. congruence. }
          assert(NBC: ~ (bc2su bc m_arg.(Mem.nextblock)) b).
          { ii. exploit BCLE; eauto. }
          clear - NBC p0.
          ii. unfold bc2su in *. rewrite H in *. ss. des_ifs.
        }
        assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' retv.(Retv.m) b Ptop).
        {
          intros; split; intros.
          - eapply VMTOP; eauto. eapply mem'_load_val'; eauto. rewrite IMG in *. subst f. ss. des_ifs.
          - admit "ez".
        }

        eapply sound_return_state with (bc := bc'); eauto.
        * admit "sonud_stack".
        * admit "ez - RO".
        *

          {
            constructor; simpl; intros.
            + apply ablock_init_sound. apply SMTOP. simpl; congruence.
            + rewrite PTree.gempty in H0; discriminate.
            + apply SMTOP; auto.
            + apply SMTOP; auto.
            + red; simpl; intros. destruct (plt b (Mem.nextblock m_arg)).
              * eapply Pos.lt_le_trans. eauto. { inv AT. apply MLE. }
              * rewrite IMG in *. subst f. ss. des_ifs.
          }
        * admit "ez".
        * red; simpl; intros. rewrite IMG. unfold f. des_ifs.
          eapply NOSTK; auto.
    - admit "final".
  Qed.

End PRSV.

