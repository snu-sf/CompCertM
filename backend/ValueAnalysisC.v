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
    - admit "init".
    - admit "step".
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le' (fun su : Unreach.t => args' su args) su_gr).
      { admit "". }
      des.
      esplits; eauto.
      { admit "ez". }
      ii.
      r in RETV. des.
      esplits; eauto.
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
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
        set (f := fun b => if plt b (Mem.nextblock m_arg)
                           then bc b
                           else
                             if plt b (Mem.nextblock retv.(Retv.m))
                             then
                               if su_ret b
                               then BCinvalid
                               else BCother
                             else BCinvalid).
        assert(exists bc', <<IMG: bc'.(bc_img) = f>>).
        { unshelve eexists (BC _ _ _); ss.
          - admit "ez".
          - admit "ez".
        } des.

        assert (VMTOP: forall v, val' su_ret (Mem.nextblock retv.(Retv.m)) v -> vmatch bc' v Vtop).
        { i. r in H. destruct v; econs; eauto. destruct b0; econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs.
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
        * ii. rewrite IMG in *. subst f. ss. des_ifs.
      + inv AT; inv AFTER; ss.
        eapply mle_monotone; try apply MLE; eauto.
        admit "ez".
    - admit "final".
  Qed.

End PRSV.

