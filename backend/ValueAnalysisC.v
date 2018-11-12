Require Import FunInd.
Require Import CoqlibC Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import ValuesC Memory Globalenvs Events.
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
    - des. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. ss. r. ii; clarify. ss.
      r in GE. des. specialize (GE0 blk). exploit GE0; eauto.
      { ss. eapply Genv.genv_defs_range; eauto. }
      i; des.
      (* exploit sound_stack_unreach_compat; eauto. intro CPT. des. *)
      (* inv SU. ss. *)
      esplits; eauto.
      + ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
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
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. i; des.
        xomega.
    - exploit sound_stack_unreach_compat; eauto. i; des.
      des_ifs. ss. des_sumbool. inv SU.
      r in GE. des. ss. exploit GE0; eauto. i; des. congruence.
  }
Qed.

(* copied from above *)
Lemma sound_state_sound_retv
      bc m_ret su0 p skenv_link v_ret cunit
      ge
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (defs p)) p))
      (STK: sound_stack cunit ge su0 bc [] m_ret (Mem.nextblock m_ret))
      (RES: vmatch bc v_ret Vtop)
      (RO: romatch bc m_ret (romem_for cunit))
      (MM: mmatch bc m_ret mtop)
      (GE: genv_match bc ge)
      (NOSTK: bc_nostack bc)
  :
    retv' (bc2su bc ge.(Genv.genv_next) m_ret.(Mem.nextblock)) (Retv.mk v_ret m_ret)
.
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
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. i; des.
        xomega.
  }
Qed.









Section PRSV.

  Variable skenv_link: SkEnv.t.
  Variable p: program.

  Hypothesis INCLUDE: include_defs
                        (fun fdef skdef => skdef_of_gdef fn_sig fdef = skdef)
                        p skenv_link.

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
      { inv SKENV. ss. i. inv MEM. rewrite <- PUB. apply NNPP. ii. exploit WF; eauto. xomega. }
      assert(NB: Ple ge.(Genv.genv_next) args.(Args.m).(Mem.nextblock)).
      { inv SKENV. ss. }
      assert(GE: genv_match bc ge).
      { r.
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
      }
      eapply sound_call_state with (bc:= bc); eauto.
      + econs; eauto; cycle 1.
        { inv SKENV. ss. }
        econs; eauto.
        * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss.
        * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss.
        * ii. inv MEM. eapply BOUND; eauto.
        * rewrite IMG. ii. des_ifs; ss. inv SKENV. rewrite PUB0 in *; ss.
        * inv SKENV. rewrite PUB in *. ss.
      + ii. repeat spc VALS. destruct v; econs; eauto. destruct b0; econs; eauto. rewrite IMG.
        inv TYP. ss.
        apply in_zip_iff in H0. des. unfold typify in *. des_ifs.
        hexploit1 VALS.
        { eapply nth_error_In; eauto. }
        repeat spc VALS. specialize (VALS eq_refl). (* TODO: fix spc ... *) des.
        des_ifs; ss. bsimpl. des; ss. des_sumbool. ss.
      + ii. rewrite IMG in *. des_ifs.
        hexploit romem_for_consistent_2; eauto. intro ROM; des.
        exploit ROM; eauto. intro ROMEM; des.
        clarify.
        esplits; eauto.
        * eapply store_init_data_list_summary. ss. econs; eauto.
        *
          (* hexploit (@SkEnv.revive_precise _ _ (SkEnv.project skenv_link (defs p)) p); eauto. *)
          (* { intros jd IN. dup IN. rewrite prog_defmap_spec in IN. des. *)
          (*   hexploit (SkEnv.project_impl_spec skenv_link (defs p)). intro SPEC. *)
          (*   inv SPEC. *)
          (*   rewrite SYMBKEEP; ss. *)
          (*   { erewrite Genv.invert_find_symbol; ss. eauto. *)
          (*     apply Genv.find_def_symbol in IN. des. ss. *)
          (*     exploit Genv.invert_find_symbol; eauto. intro SYMB. *)
          (*     unfold ge in SYMB. unfold SkEnv.revive in SYMB. rewrite Genv_map_defs_symb in SYMB. *)
          (*     admit "idk". *)
          (*   } *)
          (*   { u. destruct (in_dec ident_eq jd (prog_defs_names p)) eqn:T; ss. } *)
          (* } *)
          (* { admit "ez". } *)
          (* intro PRC; des. *)

          (* inv PRC. *)
          (* exploit FIND_MAP; eauto. i; des. des_ifs. clear_tac. *)
          (* folder. *)

          assert(CONTAINS: forall
                    id
                    (IN: p.(defs) id)
                    gv
                    (DEF: (Sk.of_program fn_sig p).(prog_defmap) ! id = Some (Gvar gv))
                  ,
                    exists blk, <<SYMB: skenv_link.(Genv.find_symbol) id = Some blk>> /\
                                        <<DEF: skenv_link.(Genv.find_def) blk = Some (Gvar gv)>>).
          { i. exploit (INCLUDE id0); cycle 1; eauto.
            - i. des. esplits; eauto. instantiate (1:=Gvar gv) in MATCH.
              ss. clarify. ss. destruct gv. ss. destruct gvar_info. ss.
            - clear - DEF.
              exploit Sk.of_program_prog_defmap. i. inv H.
              + rewrite DEF in *. clarify.
              + rewrite DEF in *. clarify. inv H2. inv H3. ss.
                destruct i2, i1. ss.
          }

          exploit Genv.invert_find_symbol; eauto. intro SYMB. clarify.
          hexploit (Sk.of_program_prog_defmap p fn_sig id); eauto. intro REL.
          unfold fundef in *. inv REL.
          {  rewrite ROMEM in *. clarify. }
          symmetry in H0. clarify. symmetry in H2. inv H3. inv H5. ss. clear_tac.
          exploit (CONTAINS id); eauto.
          { u.
            des_sumbool.
            eapply prog_defmap_spec; eauto.
          }
          i; des.

          inv SKENV.
          set (gv := {| gvar_info := i2; gvar_init := init; gvar_readonly := true; gvar_volatile := false |}).
          exploit (RO b gv); eauto; ss.
          { unfold Genv.find_var_info.
            admit "ez".
          }
          i; des.

          r. esplits; eauto.
          { admit "this should hold". }
          { admit "this should hold". }
        * inv SKENV.
          exploit RO; eauto.
          { admit "copy from above". }
          { rewrite ROMEM1. ss. }
          i; des.
          ii. exploit PERM; eauto. i; des. inv ORD.
      + assert(SUMEM: forall b : block, bc b <> BCinvalid -> smatch bc (Args.m args) b Ptop).
        { admit "mem'. this should hold...". }
        econs; s; eauto.
        * rewrite IMG. ii. des_ifs; ss.
        * rewrite IMG. ii. des_ifs; ss. rewrite PTree.gempty in *. ss.
        * intros ? A. rewrite IMG in A. des_ifs; try xomega. bsimpl. des. des_sumbool. xomega.
      + r. rewrite IMG. i. des_ifs.
    - ii; ss. eapply sound_step; eauto.
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le'
                                                    (* (fun su => su0.(UnreachC.ge_nb) = su.(UnreachC.ge_nb) /\ args' su args) *)
                                                    (fun su =>  le' su0 su /\ args' su args)
                                                    su_gr).
      { specialize (H p (linkorder_refl _)).
        set (args0 := args).
        inv AT. inv H; ss.
        exploit sound_state_sound_args; eauto. i.
        hexploit (Sound.greatest_ex (bc2su bc (Genv.genv_next skenv_link) (Mem.nextblock m0)) args0); eauto.
        { esplits; eauto. ss. refl. }
        i; des. ss.
        esplits; eauto.

        (* eapply SemiLattice.greatest_le_irr with (lub := UnreachC.lub); eauto. *)
        (* - typeclasses eauto. *)
        (* - ii. eapply lubsucc; eauto. *)
        (* - ii. eapply lubspec; eauto. *)
        (* - ii. eapply lubclosed; try apply LUB; eauto. *)
        (* - exploit sound_stack_unreach_compat; eauto. i; des. ss. *)
        (*   r; u; ss. esplits; eauto. i. inv SU. exploit BOUND; eauto. i; des. des_ifs. rewrite PRIV; ss. *)
        exploit Sound.get_greatest_le; ss; eauto.
        - exploit sound_stack_unreach_compat; eauto. i; des. ss.
          r; u; ss. esplits; eauto. i. inv SU. exploit BOUND; eauto. i; des. des_ifs. rewrite PRIV; ss.
      }
      des.
      esplits; eauto.
      { inv AT; ss. refl. }
      ii.
      r in RETV. des.
      esplits; eauto; cycle 1.
      { inv AT; inv AFTER; ss. refl. }
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
        exploit sound_stack_unreach_compat; eauto. intro CPT. des.
        assert(BCARGS: (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)).(Sound.args) args).
        { ss. inv AT; ss. rpapply sound_state_sound_args; eauto. }
        assert(BCLE0: Sound.le su0 (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock))).
        { split; ss. ii. inv SU. repeat spc BOUND. des_ifs. rewrite PRIV; ss. }
        assert(BCLE1: Sound.le (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) su_gr).
        { eapply GR; eauto. }
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
          - ii. subst f. ss. des_ifs. eapply bc_stack; eauto.
          - ii. subst f. ss. des_ifs. eapply bc_glob; eauto.
        } des.

        assert (VMTOP: forall v, val' su_ret (Mem.nextblock retv.(Retv.m)) v -> vmatch bc' v Vtop).
        { i. r in H. destruct v; econs; eauto. destruct b0; econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs.
          assert(NSU: ~su_gr b).
          { ii. r in LE. des. exploit PRIV; eauto. i; ss. congruence. }
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) b).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          clear - NBC p0.
          ii. unfold bc2su in *. ss. rewrite H in *. ss. des_ifs.
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
    - ii.
      inv FINAL. s.
      inv SUST. specialize (H p (linkorder_refl _)). inv H.
      exists (bc2su bc (Genv.genv_next skenv_link) m_ret.(Mem.nextblock)).
      esplits; try refl; ss; eauto.
      { r.
        exploit sound_stack_unreach_compat; eauto. intro CPT; des. inv SU.
        split; ss.
        ii.
        exploit PRIV; eauto. i.
        exploit BOUND; eauto. i.
        des_ifs.
        des_sumbool; ss.
      }
      rp; [eapply sound_state_sound_retv; eauto|..]; eauto.
  Qed.

End PRSV.
