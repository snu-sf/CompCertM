Require Import CoqlibC.
Require Import ASTC.
Require Import ValuesC.
Require Import GlobalenvsC.
Require Import LocationsC.
From compcertr Require Import
     Integers
     Memory
     Events
     Op
     Machregs
     Conventions
     LTL
     Linear
     sflib.
(** newly added **)
From compcertr Require Export Lineartyping.
Require SoundTop.
Require Import Preservation.
Require Import ModSem.
Require Import LinearC.

Set Implicit Arguments.



Lemma ls_init_has_type
      ls_init sg vs
      (LEN: length vs = length sg)
      ir fr ofs
      (LOCSET: typify_list vs sg = map (fun p => Locmap.getpair p ls_init) (loc_arguments_elf64 sg ir fr ofs))
      sl pos ty
      (IN: In (S sl pos ty) (regs_of_rpairs (loc_arguments_elf64 sg ir fr ofs)))
      (ONES: forall lp, In lp (loc_arguments_elf64 sg ir fr ofs) -> is_one lp):
    <<TY: Val.has_type (ls_init (S sl pos ty)) ty>>.
Proof.
  remember (loc_arguments_elf64 sg ir fr ofs) as locs in *.
  Local Opaque Z.add Z.mul Z.sub Z.div.
  Local Opaque loc_arguments_elf64.
  ginduction locs; ii; ss. destruct vs; ss. destruct sg; ss. clarify. unfold typify_list in *.
  exploit ONES; eauto. i. destruct a; ss. clarify. des; cycle 1.
  - Local Transparent loc_arguments_elf64.
    ss. des_ifs; eapply IHlocs; eauto.
  - clarify. rewrite <- H3.
    assert(t = ty).
    { clear - Heqlocs. ss. des_ifs. }
    clarify.
    eapply typify_has_type.
Qed.


Section SOUNDNESS.

  Variable prog: program.

  Hypothesis wt_prog:
    forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

  Lemma mreg_type_any: forall mr, <<ANY: mreg_type mr = Tany64>>.
  Proof. i. rr. unfold mreg_type. des_ifs. Qed.

  Lemma has_type_any: forall v, <<ANY: Val.has_type v Tany64>>.
  Proof. i. rr. destruct v; ss. Qed.

  Theorem wt_state_local_preservation: forall skenv_link,
      local_preservation (modsem skenv_link prog) (fun _ _ st => wt_state st).
  Proof.
    econs; ii; ss; eauto.
    - (* init *)
      inv INIT.
      assert(WTLS: wt_locset ls_init).
      { ii.
        destruct l; ss.
        { rewrite mreg_type_any. apply has_type_any. }
        destruct (classic (In (S sl pos ty) (regs_of_rpairs (loc_arguments (fn_sig fd))))).
        - clear - TYP H. inv TYP.
          abstr (fn_sig fd) sg. abstr (Args.vs args) vs. clear_tac.
          generalize (loc_arguments_one sg). intro ONES.
          destruct sg; ss. unfold loc_arguments in *. ss. des_ifs. clear_tac.
          eapply ls_init_has_type; eauto.
        - erewrite SLOT; eauto.
      }
      econs; ss; eauto. econs; eauto. econs; eauto.
    - inv STEP. eapply step_type_preservation; eauto.
      ii. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
      unfold Skeleton.SkEnv.revive in *.
      eapply Genv_map_defs_def in Heq. des. u in MAP. des_ifs_safe. bsimpl.
      esplits. eapply in_prog_defmap; eauto.
    - inv AT; ss. esplits; eauto.
      { rr. esplits; ss; eauto. rr. rewrite Forall_forall. ii; ss. }
      ii. inv AFTER. inv SUST.

      hexploit (loc_result_caller_save sg); eauto. intro RES.
      hexploit (loc_result_one sg); eauto. intro ONE. des.

      econs; eauto.
      + destruct stack; ss. des_ifs. inv WTSTK.
        econs; eauto. unfold undef_outgoing_slots. ii. des_ifs.
      + ii. unfold Locmap.setpair. des_ifs. ss.
        apply wt_setreg; ss; cycle 1.
        { apply wt_undef_caller_save_regs; ss. }
        rewrite mreg_type_any. apply has_type_any.
      + ii. destruct l; ss.
        { rewrite locmap_get_set_loc_result; ss. des_ifs. rewrite AGCS; ss.
          hexploit (parent_locset_after_external stack); et. i; des; clarify. rewrite AFTER.
          (* TODO: we can remove spurious case by strengthening wt_callstack -> *)
          (* we know stack >= 1, because of dummy stack *)
          unfold undef_caller_save_regs. des_ifs.
        }
        { rewrite locmap_get_set_loc_result; ss. rewrite AGCS; ss.
          hexploit (parent_locset_after_external stack); et. i.
          des_ifs; des; clarify; rewrite AFTER; ss.
        }
      + ii. rewrite locmap_get_set_loc_result; ss.
    - inv FINAL. esplits; eauto. ss.
  Unshelve.
    all: ss.
  Qed.

End SOUNDNESS.
