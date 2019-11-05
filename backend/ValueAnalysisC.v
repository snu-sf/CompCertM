Require Import FunInd.
Require Import CoqlibC Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import ValuesC MemoryC Globalenvs Events.
Require Import Registers Op RTLC.
Require Import ValueDomainC ValueAOp Liveness.
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

  Hypothesis INCL: SkEnv.includes skenv_link (Sk.of_program fn_sig p).

  Let modsem := RTLC.modsem skenv_link p.

  Local Existing Instance Unreach.

  Theorem sound_state_preservation:
    local_preservation_strong modsem get_mem le' (sound_state p modsem.(globalenv)).
  Proof.
    econs; eauto.
    { ss. eapply UnreachC.liftspec; et. }
    - i. inv INIT. ss. esplits; eauto; cycle 1.
      { destruct args; ss. refl. }
      econs; eauto. i.
      set (ge := (SkEnv.revive (SkEnv.project skenv_link p.(Sk.of_program fn_sig)) p)) in *.
      set (f := fun b =>
                  if plt b (Genv.genv_next ge) then
                    match Genv.invert_symbol ge b with None => BCglob None | Some id => BCglob (Some id) end
                  else
                    if (plt b args.(Args.m).(Mem.nextblock)) && (negb (su_init b))
                    then BCother else BCinvalid).
      assert(IMG: exists bc, bc.(bc_img) = f).
      { unshelve eexists (BC _ _ _); s; eauto.
        - ii. subst f. ss. des_ifs.
        - ii. subst f. ss. des_ifs. apply_all_once Genv.invert_find_symbol. clarify.
      }
      subst f. des.
      assert(T: <<VAL: val' su_init (Args.fptr args)>> /\ <<VALS: Sound.vals su_init (Args.vs args)>> /\ <<MEM: mem' su_init (Args.m args)>> /\ <<WF: Unreach.wf su_init>>).
      { r in SUARG. des_ifs. }
      clear SUARG. des. ss. unfold Sound.vals in *. rewrite Forall_forall in *.
      assert(FP: forall blk, su_init blk -> Ple ge.(Genv.genv_next) blk).
      { inv SKENV. ss. i. inv MEM. rewrite <- PUB. apply NNPP. ii. inv WF. exploit WFHI; eauto. }
      assert(NB: Ple ge.(Genv.genv_next) args.(Args.m).(Mem.nextblock)).
      { inv SKENV. ss. destruct args; ss. }
      assert(GE: genv_match bc ge).
      { r. esplits; eauto.
        * ii. rewrite IMG in *. split; i.
          { exploit Genv.genv_symb_range; eauto. i.
            apply_all_once Genv.find_invert_symbol.
            unfold fundef in *. des_ifs.
          }
          des_ifs. apply Genv.invert_find_symbol; eauto.
        * rewrite IMG. ii.
          assert(Plt b (Mem.nextblock (Args.m args))).
          { eapply Plt_Ple_trans; eauto. }
          des_ifs; eauto.
        * rewrite IMG. ii. des_ifs.
      }
      eapply sound_call_state with (bc:= bc); eauto.
      + econs; eauto; cycle 1.
        { inv MEM; ss. rewrite NB0. xomega. }
      + ii. repeat spc VALS. destruct v; econs; eauto. econs; eauto. rewrite IMG. inv TYP. ss.
        apply in_zip_iff in H0. des. unfold typify in *. des_ifs.
        hexploit1 VALS.
        { eapply nth_error_In; eauto. }
        repeat spc VALS. specialize (VALS eq_refl). (* TODO: fix spc ... *) des.
        des_ifs; ss. bsimpl. des; ss. des_sumbool. inv MEM. congruence.
      + inv SKENV. ss. clear - IMG ROMATCH H INCL CSTYLE.
        ii. exploit (ROMATCH b id ab); eauto.
        { rewrite IMG in *. des_ifs. ss. des_ifs.
          - clear - Heq Heq0. eapply Genv.invert_find_symbol in Heq. subst ge. unfold SkEnv.revive in *.
            rewrite Genv_map_defs_symb in Heq. eapply Genv.find_invert_symbol in Heq. clarify.
          - clear - Heq Heq0. eapply Genv.invert_find_symbol in Heq. subst ge. unfold SkEnv.revive in *.
            rewrite Genv_map_defs_symb in Heq. eapply Genv.find_invert_symbol in Heq. clarify.
        }
        { hexploit (romem_for_consistent_2 _ _ H); eauto. intro LO.
          exploit LO; eauto. intro LOA; des. clarify.
          rewrite IMG in *. des_ifs. apply Genv.invert_find_symbol in Heq.
          eapply romem_for_ske_complete; et.
          clear - LOA LOA0 LOA1 LOA2 Heq INCL.
          exploit SkEnv.project_impl_spec; et. intro PROJ.
          exploit SkEnv.project_revive_precise; et. intro PRECISE. inv PRECISE.
          exploit P2GE; et. i; des. ss. unfold fundef in *. folder. clarify.
          assert(INTSID: internals (Sk.of_program fn_sig p) id).
          { rewrite Sk.of_program_internals. unfold internals. des_ifs. }
          assert(DEFSID: defs (Sk.of_program fn_sig p) id).
          { eapply internals_defs; et. }
          assert(BIG: Genv.find_def skenv_link b = Some (Gvar v)).
          { generalize (Sk.of_program_prog_defmap p fn_sig id). intro REL.
            inv REL; try congruence. rewrite LOA in *. clarify.
            assert(y = Gvar v).
            { inv H1. inv H2. ss. destruct i1, i2; ss. }
            clarify. inv INCL. exploit DEFS; et. i; des.
            assert(blk = b).
            { inv PROJ. exploit (SYMBKEEP id); et.
              i; des. rewrite SYMB0 in *. clear - H SYMB. subst ge. unfold SkEnv.revive in *.
              rewrite Genv_map_defs_symb in *. clarify.
            }
            clarify. rewrite DEF0. clear - MATCH LOA2.
            (*** TODO: make lemma!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! ***)
            inv MATCH. inv H0. destruct info1, info2; ss.
            inv H1; ss.
          }
          assert(SMALL: Genv.find_def (SkEnv.project skenv_link (Sk.of_program fn_sig p)) b = Some (Gvar v)).
          { inv PROJ.
            exploit DEFKEEP; et.
            { apply Genv.find_invert_symbol; et. rewrite <- SYMBKEEP; et. }
            i; des.
            assert(gd_small = (Gvar v)).
            { (* TODO: make lemma!!!!!!!!!!!!!!!!! *)
              clear - PROG LOA. generalize (Sk.of_program_prog_defmap p fn_sig id). intro REL.
              inv REL; try congruence.
              rewrite LOA in *. rewrite PROG in *. clarify.
              inv H1. inv H0. repeat f_equal. destruct i1, i2; ss.
            }
            clarify.
          }
          unfold Genv.find_var_info. des_ifs.
        }
        rewrite Args.get_m_m in *; ss.
        intro RO; des. esplits; et. eapply bmatch_incr; et.
        ii. ss. rewrite IMG. des_ifs.
        * clear - Heq Heq0. eapply Genv.invert_find_symbol in Heq. subst ge. unfold SkEnv.revive in *.
          rewrite Genv_map_defs_symb in Heq. eapply Genv.find_invert_symbol in Heq. clarify.
        * clear - Heq Heq0. eapply Genv.invert_find_symbol in Heq. subst ge. unfold SkEnv.revive in *.
          rewrite Genv_map_defs_symb in Heq. eapply Genv.find_invert_symbol in Heq. clarify.
        * clear - Heq0 Heq H0.
          apply_all_once Genv.invert_find_symbol.
          assert(Genv.find_symbol ge i = Some b0).
          { subst ge. unfold SkEnv.revive. rewrite Genv_map_defs_symb. ss. }
          apply Genv.find_invert_symbol in H. clarify.
      + assert(BCSU: forall b, bc b <> BCinvalid -> ~ su_init b).
        { intros ? BC. rewrite IMG in BC.
          destruct (plt b (Genv.genv_next skenv_link)).
          - inv SKENV. ss. inv WF. ii. hexploit WFLO; eauto. i. Unreach.nb_tac. xomega.
          - des_ifs. bsimpl. des. ii. congruence.
        }
        assert(SUBC: forall b (VALID: Plt b (Mem.nextblock (Args.m args))), ~ su_init b -> bc b <> BCinvalid).
        { intros ? ? SU. rewrite IMG. des_ifs. bsimpl. des; ss. des_sumbool.
          inv SKENV. ss.
        }
        assert(SUMEM: forall b : block, bc b <> BCinvalid -> smatch bc (Args.m args) b Ptop).
        { i. rr. rename H0 into SU.
          hexploit BCSU; eauto. intro SU0. split; i.
          - hexploit mem'_load_val'; eauto. intro SUV.
            { destruct v; econs; et. econs; et. exploit SUV; et. i; des. ii.
              exploit BCSU; et.
              exploit SUBC; try apply H1; et.
              { inv MEM. Unreach.nb_tac. ss. }
              ss.
            }
          - hexploit mem'_loadbytes_val'; eauto. intro SUV.
            { econs; et. exploit SUV; et. i; des. ii.
              exploit BCSU; et.
              exploit SUBC; try apply H1; et.
              { inv MEM. Unreach.nb_tac. ss. }
              ss.
            }
        }
        econs; s; eauto.
        * rewrite IMG. ii. des_ifs; ss.
        * rewrite IMG. ii. des_ifs; ss. rewrite PTree.gempty in *. ss.
        * intros ? A. rewrite IMG in A. inv SKENV. ss. des_ifs; try xomega. bsimpl. des. des_sumbool. xomega.
      + r. rewrite IMG. i. des_ifs.
      + rr. ss. inv MEM. inv SKENV. ss. rewrite NB0. esplits; eauto.
        * i. des_ifs; try xomega. rewrite IMG. rewrite <- PUB. inv WF.
          destruct (su_init blk) eqn:T; des_sumbool.
          { hexploit WFLO; eauto. i. des_ifs; try xomega. bsimpl. ss. }
          des_ifs. bsimpl. exfalso. des_sumbool. xomega.
        * refl.
    - ii; ss. eapply sound_step with (se := skenv_link); eauto.
      eapply SkEnv.senv_genv_compat; eauto.
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le'
                                                    (* (fun su => su0.(UnreachC.ge_nb) = su.(UnreachC.ge_nb) /\ args' su args) *)
                                                    (fun su =>  le' su0 su /\ args' su args)
                                                    su_gr /\ le' su0 su_gr).
      { specialize (H p (linkorder_refl _)).
        set (args0 := args).
        inv AT. inv H; ss. des.
        exploit sound_state_sound_args; eauto. i.
        hexploit (@UnreachC.greatest_ex (bc2su bc (Genv.genv_next skenv_link) (Mem.nextblock m0)) args0); eauto.
        { subst args0. r in H. des. esplits; eauto; cycle 1. { r. ss. esplits; eauto. } ss. refl. }
        i; des. ss. esplits; eauto.
        - exploit (@UnreachC.get_greatest_le); ss; eauto.
          { subst args0; ss. }
          + eapply UnreachC.hle_lift; eauto.
        - rr in GR. des. etrans; eauto. eapply UnreachC.hle_lift; eauto.
      }
      des. esplits; eauto.
      { inv AT; ss. refl. }
      { exploit H; eauto. { apply linkorder_refl. } intro T; des. inv T; ss. }
      { r in GR. inv AT. ss. des. r in PROP0. des. esplits; et. }
      { refl. }
      ii. r in RETV. des. esplits; eauto; cycle 1.
      { inv AT; inv AFTER; ss. rewrite Retv.get_m_m; ss. refl. }
      { inv GR0. inv LE. des. red. symmetry. etrans; eauto. }
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
        assert(BCARGS: (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)).(Sound.args) args).
        { ss. inv AT; ss. s. des. rpapply sound_state_sound_args; eauto. }
        assert(BCLE0: le' su0 (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock))).
        { eapply UnreachC.hle_lift; eauto. }
        assert(BCLE1: le' (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) su_gr).
        { eapply GR; eauto. esplits; eauto. inv AT. ss. }
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
          - ii. subst f. ss. des_ifs. eapply bc_stack; eauto.
          - ii. subst f. ss. des_ifs. eapply bc_glob; eauto.
        } des.

        assert(HLEAFTER: Unreach.hle (bc2su bc (Genv.genv_next skenv_link) (Mem.nextblock m_arg))
                                     (bc2su bc' (Genv.genv_next skenv_link) (Mem.nextblock (Retv.m retv)))).
        { rr. ss. rewrite IMG. unfold f.
          assert(NB: Ple (Mem.nextblock m_arg) (Mem.nextblock (Retv.m retv))).
          { inv AT; ss. rewrite Retv.get_m_m in *; ss. inv MLE. inv RO0. ss. }
          esplits; ss.
          - i. des_ifs. xomega.
        }

        assert(GRARGS: Sound.args su_gr args).
        { rr in GR. des. inv AT; ss. }
        exploit Unreach.hle_hle_old; try apply LE; eauto.
        { rr in GRARGS. des. inv AT; ss. des; ss. }
        intro LEOLD.
        assert (VMTOP0: forall v, Sound.val su_gr v -> vmatch bc' v Vtop).
        { i. ss. r in H. destruct v; econs; eauto. econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs_safe.
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) b).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. des. inv MEM. rr in GRARGS. inv AT; ss. des. inv MEM. ss.
          rewrite NB0 in *. des_ifs; try xomega.
          intro BC. unfold bc2su in *. ss. rewrite BC in *. ss.
        }
        assert (VMTOP: forall v, val' su_ret v -> vmatch bc' v Vtop).
        { i. r in H. destruct v; econs; eauto. econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs_safe.
          assert(NSU: ~su_gr b).
          { ii. r in LEOLD. des. exploit PRIV; eauto. i; ss. congruence. }
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) b).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. des. inv MEM. rewrite NB in *. des_ifs.
          clear - NBC p0.
          ii. unfold bc2su in *. ss. rewrite H in *. ss.
        }
        assert (VMTOP1: forall v (BELOW: bc_below bc (Mem.nextblock m_arg)),
                   vmatch bc v Vtop -> vmatch bc' v Vtop).
        { i. inv H; econs; eauto. inv H2; econs; eauto.
          exploit BELOW; eauto. i.
          rewrite IMG. unfold f.
          des_ifs.
        }
        assert (PMTOP: forall blk ofs, ~ su_ret blk -> Plt blk (Mem.nextblock (Retv.m retv)) -> pmatch bc' blk ofs Ptop).
        { i. r in H. econs; eauto.
          assert(NSU: ~su_gr blk).
          { ii. r in LEOLD. des. exploit PRIV; eauto. }
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) blk).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. rewrite IMG. unfold f. des_ifs.
          ii. rewrite H1 in *. ss.
        }
        assert (PMTOP1: forall blk ofs
                          (BELOW: bc_below bc (Mem.nextblock m_arg)),
                   pmatch bc blk ofs Ptop -> pmatch bc' blk ofs Ptop).
        { i. inv H; econs; eauto.
          exploit BELOW; eauto. i.
          ss. rewrite IMG. unfold f. des_ifs.
        }
        assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' retv.(Retv.m) b Ptop).
        { intros; split; intros.
          - destruct (su_gr b) eqn:T.
            + assert(Plt b (Mem.nextblock m_arg)).
              { rr in GRARGS. inv AT; ss. des. inv MEM.
                inv WF0. exploit WFHI; try apply T. eauto. i. Unreach.nb_tac. ss.
              }
              rewrite IMG in *. subst f. ss. des_ifs.

              inv MM. exploit mmatch_top; eauto. intro SM. rr in SM. des.
              assert(LD: Mem.load chunk m_arg b ofs = Some v).
              { inv MLE. inv AT. ss. erewrite <- Mem.load_unchanged_on_1; try apply PRIV; eauto. }
              exploit SM; eauto.
            + assert(~ su_ret b).
              { rewrite IMG in *. subst f. ss. des_ifs.
                rr in LE. des. ss. erewrite <- OLD; eauto.
                { congruence. }
                rr in GRARGS. inv AT; ss. des. inv MEM0. Unreach.nb_tac. ss.
              }
              eapply VMTOP; eauto. eapply mem'_load_val'; eauto. inv AT; ss. des_ifs; des; ss.
          - destruct (su_gr b) eqn:T.
            + assert(Plt b (Mem.nextblock m_arg)).
              { rr in GRARGS. inv AT; ss. des. inv MEM.
                inv WF0. exploit WFHI; eauto. i.
                Unreach.nb_tac. ss.
              }
              rewrite IMG in *. subst f. ss. des_ifs.

              inv MM. exploit mmatch_top; eauto. intro SM. rr in SM. des.
              assert(LD: Mem.loadbytes m_arg b ofs 1 = Some [Fragment (Vptr b' ofs') q i]).
              { inv MLE. inv AT. ss. erewrite <- Mem.loadbytes_unchanged_on_1; try apply PRIV; eauto. }
              exploit SM0; eauto.
            + try (by econs; eauto).
              assert(~ su_ret b).
              { rewrite IMG in *. subst f. ss. des_ifs.
                rr in LE. des. ss. erewrite <- OLD; eauto; try congruence.
                rr in GRARGS. des. inv AT; ss. des. inv MEM0. Unreach.nb_tac. ss.
              }
              eapply PMTOP; eauto; cycle 1.
              { inv AT; ss. des_ifs; des. inv MEM1.
                Local Transparent Mem.loadbytes.
                unfold Mem.loadbytes in *. des_ifs.
                exploit (SOUND b ofs); eauto.
                { eapply r. xomega. }
                i; des. ss. Unreach.nb_tac. xomega.
              }
              eapply mem'_loadbytes_val'; eauto.
              des_ifs; des; ss.
        }

        rewrite Retv.get_m_m in *; ss.
        eapply sound_return_state with (bc := bc'); eauto.
        * apply sound_stack_new_bound with (Mem.nextblock m_arg); cycle 1.
          { inv HLEAFTER. des. ss. }
          apply sound_stack_exten with bc; auto; cycle 1.
          { i. rewrite IMG. unfold f. des_ifs. }
          apply sound_stack_inv with m_arg; auto.
          i. inv MLE. inv AT. ss.
          eapply Mem.loadbytes_unchanged_on_1; try apply PRIV; eauto.
          u. i. eapply BCLE1; et. ss. des_ifs. des_sumbool. ss.
        * eapply VMTOP; et. unfold typify. des_ifs. des; ss.
        * eapply romatch_exten; cycle 1.
          { instantiate (1 := bc). rewrite IMG. subst f. split; i; try by des_ifs.
            des_ifs_safe. exfalso. eapply n. eapply mmatch_below. eauto. congruence.
          }
          inv AT. ss. inv MLE. eapply romatch_ext; et; i.
          { assert(RANGE_PERM: Mem.range_perm (Retv.m retv) b ofs (ofs + n) Cur Readable).
            { eapply Mem.loadbytes_range_perm; et. }
            erewrite <- Mem.loadbytes_unchanged_on_1; try eapply RO0; et.
            - eapply mmatch_below; et. congruence.
            - i. inv SKENV. ss. rr in ROMATCH. des.
              exploit (romem_for_consistent cunit); eauto. intro X; des.

              inv GE. hexploit (H3 id b); eauto. intro Y. des.
              hexploit1 Y0; eauto.

              eapply (ROMATCH b id); eauto.
              + unfold ske2bc. s. rename b into blk. exploit Genv.genv_symb_range; et. intro BNB. des_ifs_safe.
                dup Y0. unfold SkEnv.revive in Y1. ss. rewrite Genv_map_defs_symb in Y1.
                exploit Genv.find_invert_symbol; et. intro INV. rewrite INV. ss.
              + eapply romem_for_ske_complete; et. clear - LO X INCL Y0 X2. inv INCL.
                exploit (prog_defmap_linkorder cunit); et. intro Z; des.
                hexploit (Sk.of_program_prog_defmap p fn_sig id); et. intro REL.
                unfold fundef in *. rewrite Z in REL. inv REL. symmetry in H0.
                exploit DEFS; et. intro W; des.
                assert(b = blk).
                { clear - Y0 SYMB. unfold SkEnv.revive, SkEnv.project in *. uge. ss.
                  rewrite MapsC.PTree_filter_key_spec in *. des_ifs.
                  (* TODO: make lemma *)
                } clarify.
                unfold SkEnv.project. ss. unfold Genv.find_var_info.
                erewrite Genv_map_defs_def_inv; et; cycle 1.
                exploit Genv.find_invert_symbol; et. intro INV.
                rewrite INV. unfold o_bind. s. rewrite H0. s. unfold internals. rewrite H0. s.
                inv Z0. inv H1. ss. inv H2. inv H3. inv MATCH. inv H3. inv H9. destruct info1, i3; ss. repeat f_equal; ss.

                (* TODO: make lemma *)
                clear - X2 H1. unfold ValueAnalysis.definitive_initializer in *. des_ifs; inv H1; ss.
          }
          { apply PERM; et. eapply mmatch_below; et. congruence. }
        * { constructor; simpl; intros.
            + apply ablock_init_sound. apply SMTOP. simpl; congruence.
            + rewrite PTree.gempty in H0; discriminate.
            + apply SMTOP; auto.
            + apply SMTOP; auto.
            + red; simpl; intros. destruct (plt b (Mem.nextblock m_arg)).
              * eapply Pos.lt_le_trans. eauto. { inv AT. apply MLE. }
              * rewrite IMG in *. subst f. ss. des_ifs.
          }
        * eapply genv_match_exten; eauto.
          { rewrite IMG. subst f. split; i; try by des_ifs.
            des_ifs_safe. exfalso. eapply n. eapply mmatch_below. eauto. congruence.
          }
          { i. rewrite IMG. unfold f. des_ifs_safe.
            exfalso. eapply n. eapply mmatch_below. eauto. congruence.
          }
        * red; simpl; intros. rewrite IMG. unfold f. des_ifs.
          eapply NOSTK; auto.
        * ss. etrans; eauto.
    - ii. inv FINAL. s.
      inv SUST. specialize (H p (linkorder_refl _)). inv H.
      exists (bc2su bc (Genv.genv_next skenv_link) m_ret.(Mem.nextblock)).
      exploit sound_state_sound_retv; try apply STK; eauto; ss; eauto. i; des.
      esplits; try refl; ss; eauto.
  Qed.

End PRSV.
