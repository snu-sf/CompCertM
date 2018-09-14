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


Definition bc2su (bc: block_classification) (bound: block): Unreach.t :=
  (fun blk => if plt blk bound
              then block_class_eq (bc blk) BCinvalid
              else false)
.
Hint Unfold bc2su.

Ltac spc H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
    | [a0: A, a1: A, a2: A, a3: A |- _] => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
    | [a0: A, a1: A, a2: A |- _] => fail 2 "3 candidates!" a0 "," a1 "," a2
    | [a0: A, a1: A |- _] => fail 2 "2 candidates!" a0 "," a1
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end
.

Ltac spcN n H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match type of n with
  | nat => idtac
  | _ => fail "second argument should be 'nat'"
  end;
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] =>
      match n with
      | 0%nat => specialize (H a0)
      | 1%nat => specialize (H a1)
      | 2%nat => specialize (H a2)
      | 3%nat => specialize (H a3)
      | 4%nat => specialize (H a4)
      | 5%nat => specialize (H a5)
      | _ => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
      end
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] =>
      match n with
      | 0%nat => specialize (H a0)
      | 1%nat => specialize (H a1)
      | 2%nat => specialize (H a2)
      | 3%nat => specialize (H a3)
      | 4%nat => specialize (H a4)
      | _ => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
      end
    | [a0: A, a1: A, a2: A, a3: A |- _] =>
      match n with
      | 0%nat => specialize (H a0)
      | 1%nat => specialize (H a1)
      | 2%nat => specialize (H a2)
      | 3%nat => specialize (H a3)
      | _ => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
      end
    | [a0: A, a1: A, a2: A |- _] =>
      match n with
      | 0%nat => specialize (H a0)
      | 1%nat => specialize (H a1)
      | 2%nat => specialize (H a2)
      | _ => fail 2 "3 candidates!" a0 "," a1 "," a2
      end
    | [a0: A, a1: A |- _] =>
      match n with
      | 0%nat => specialize (H a0)
      | 1%nat => specialize (H a1)
      | _ => fail 2 "2 candidates!" a0 "," a1
      end
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end
.

(* Tactic Notation "spc" hyp(H) := spc H. *)
(* Tactic Notation "spc" hyp(H) constr(n) := spcN H n. *)

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
    - ii; ss. eapply sound_step; eauto.
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le' (fun su : Unreach.t => args' su args) su_gr).
      { admit "". }
      assert(SUARGS: su0.(Sound.args) args).
      { admit "". }
      des.
      esplits; eauto.
      ii.
      r in RETV. des.
      esplits; eauto; cycle 1.
      { inv AT; inv AFTER; ss.
        eapply mle_monotone; try apply MLE; eauto.
        eapply GR. eauto.
      }
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
        assert(BCARGS: (bc2su bc m_arg.(Mem.nextblock)).(Sound.args) args).
        { ss. r. esplits; eauto.
          - admit "fptr".
          - rewrite Forall_forall. i. spcN 1%nat ARGS. inv AT. ss. spc ARGS. ii; clarify.
            assert(BCV: bc blk <> BCinvalid).
            { inv ARGS; ss. inv H1; ss. }
            esplits; eauto.
            + u. ii. des_ifs. des_sumbool. ss.
            + inv MM. eapply mmatch_below; eauto.
          - inv MM. econs; eauto.
            + ii. clarify.
              assert(BCV: bc blk <> BCinvalid).
              { u in PUB. ii. rewrite H in *. ss. exploit Mem.perm_valid_block; eauto. i; des. inv AT. des_ifs. }
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
              inv AT. s. eapply mmatch_below; eauto.
            + u. ii. des_ifs. des_sumbool; clarify. inv AT; ss.
        }
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

