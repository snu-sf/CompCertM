Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import MutrecAspec MutrecBspec MutrecABspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SimMemId.
Require SoundTop.
Require Import Clightdefs.
Require Import CtypesC.
Require Import BehaviorsC.
Require Import LinkingC2.
Require Import Simulation Sem SemProps LinkingC.

Set Implicit Arguments.

Lemma link_sk_same_aux1
      A B C
      (NOEMPTY: A <> [] /\ B <> [])
      (SAME: link_sk A = link_sk B):
    link_sk (C ++ A) = link_sk (C ++ B).
Proof.
  ginduction C; ss.
  ii. unfold link_sk in *. ss.
  exploit IHC; eauto. i.
  clear - NOEMPTY H. unfold link_list in H. des_ifs; ss.
  - unfold link_list. ss. rewrite Heq. rewrite Heq0. ss.
  - des. eapply link_list_aux_empty_inv in Heq. destruct C; destruct A; ss.
  - des. eapply link_list_aux_empty_inv in Heq0. destruct C; destruct B; ss.
  - unfold link_list. ss. rewrite Heq, Heq0. auto.
  - unfold link_list. ss. rewrite Heq, Heq0. auto.
Qed.

Lemma link_sk_same_aux2 ctx:
    link_sk ([(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx)
    = link_sk ([module] ++ ctx).
Proof.
  Local Transparent Linker_prog Linker_def Linker_skfundef Linker_vardef Linker_unit Linker_varinit. ss.
  assert (LINKSK: link_sk [MutrecAspec.module; MutrecBspec.module] = Some sk_link); ss.
  destruct (link_list_aux (List.map Mod.sk ctx)) eqn:CTXLINK.
  - eapply link_list_aux_empty_inv in CTXLINK. rr in CTXLINK.
    destruct ctx; ss.
  - unfold link_sk, link_list. ss. rewrite CTXLINK. auto.
  - unfold link_sk, link_list in LINKSK; ss. des_ifs.
    unfold link_sk, link_list; ss. rewrite CTXLINK.
    des_ifs.
    + clear - Heq0 Heq2 Heq3.
      hexploit (link_prog_inv _ _ _ Heq0). i. des.
      hexploit (link_prog_inv _ _ _ Heq2). i. des.
      dup Heq3.
      unfold link_prog in Heq3. des_ifs.
      assert (EQ: (AST.prog_main (Sk.of_program Asm.fn_sig MutrecB.prog)) = (AST.prog_main t)).
      { rewrite <- H2. rewrite <- H. rewrite H1 in *. ss. }
      exploit (link_prog_succeeds _ _ EQ).
      { ii.
        assert (exists gd, (prog_defmap sk_link) ! id = Some gd).
        { rewrite H1. rewrite prog_defmap_elements.
          rewrite PTree.gcombine; cycle 1. ss.
          exploit prog_defmap_image. eapply H4. i.
          rr in H6. simpl in H6. des; subst; clarify; simpl; des_ifs; eauto. }
        des. exploit H3; eauto. i. des; eauto.
        rewrite H1 in H7. simpl in H7. esplits; eauto.
        { simpl. des; eauto. }
        destruct (classic (id = f_id)).
        { subst. clear H7. rewrite H1 in H6. rewrite prog_defmap_elements, PTree.gcombine in H6; cycle 1.
          auto. ii. simpl in H6, H4. clarify. des_ifs. simpl in H9. des_ifs. }
        destruct (classic (id = g_id)).
        { subst. clear H7. rewrite H1 in H6. rewrite prog_defmap_elements, PTree.gcombine in H6; cycle 1.
          auto. ii. simpl in H6, H4. clarify. des_ifs. }
        clear -H7 H10 H11. des; clarify. }
      i. rewrite H4 in *. clarify.
    + hexploit (link_prog_inv _ _ _ Heq0). i. des.
      hexploit (link_prog_inv _ _ _ Heq2). i. des.
      hexploit (link_prog_inv _ _ _ Heq4). i. des.
      dup Heq3. unfold link_prog in Heq3.
      assert (EQ: (AST.prog_main (CSk.of_program signature_of_function MutrecA.prog)) = AST.prog_main t1).
      { des_ifs. }
      exploit (link_prog_succeeds _ _ EQ).
      { ii. assert (exists gd, (prog_defmap sk_link) ! id = Some gd).
        { rewrite H1. rewrite prog_defmap_elements.
          rewrite PTree.gcombine; cycle 1. ss.
          exploit prog_defmap_image. eapply H8. i.
          rr in H10. simpl in H10. des; subst; clarify; simpl; des_ifs; eauto. }
        des. simpl. rewrite H7 in H9. rewrite H7.
        rewrite prog_defmap_elements, PTree.gcombine in H9; cycle 1. auto.
        unfold link_prog_merge in H9. des_ifs; simpl.
        - exploit H6; eauto. splits; des; eauto.
          exploit H3; eauto. i. des. rewrite H1 in H10.
          rewrite prog_defmap_elements, PTree.gcombine in H10; cycle 1. auto.
          unfold link_prog_merge in H10. des_ifs.
          ii. destruct (classic (id = f_id)).
          { subst. simpl. esplits; eauto.
            simpl in H8, H10, H11, H14. simpl in Heq8, Heq9. clarify.
            unfold link_def in H10, H11, H14. des_ifs. simpl in Heq9, Heq8. destruct f0; des_ifs. }
          destruct (classic (id = g_id)).
          { subst. simpl. esplits; eauto.
            simpl in H8, H10, H11, H14. simpl in Heq8, Heq9. clarify.
            unfold link_def in H10, H11, H14. des_ifs. simpl in Heq9, Heq8. destruct f0; des_ifs. }
          exploit prog_defmap_image. eapply Heq8. ii. rr in H16. simpl in H16. des; clarify.
        - exploit H0; eauto. i. des. esplits; eauto.
          { simpl in H4, H7. des; eauto. clarify. }
          ii. exploit prog_defmap_image. eapply H8. ii. rr in H12. simpl in H12. des; clarify.
          simpl in Heq5, H8. clarify. simpl in Heq5, H8. clarify.
        - ii. exploit prog_defmap_image. eapply H8. ii. rr in H4. simpl in H4. des; clarify.
          exploit H3; eauto. i. des. rewrite H1 in H4. simpl in H4. des; clarify. }
      ii. rewrite H8 in *. clarify.
    + hexploit (link_prog_inv _ _ _ Heq0). i. des.
      hexploit (link_prog_inv _ _ _ Heq). i. des.
      hexploit (link_prog_inv _ _ _ Heq4). i. des.
      dup Heq2. unfold link_prog in Heq2.
      assert (EQ: (AST.prog_main sk_link) = AST.prog_main t).
      { rewrite H1. simpl. des_ifs. }
      exploit (link_prog_succeeds _ _ EQ).
      { ii. rewrite H1 in H8.
        rewrite prog_defmap_elements, PTree.gcombine in H8; cycle 1. auto.
        unfold link_prog_merge in H8. des_ifs.
        - exploit H3; eauto. i. des. simpl in H4, H7. des; clarify.
          + esplits. rewrite H1. simpl. auto. simpl. auto.
            ii. simpl in Heq5, Heq6. clarify. simpl in H8. des_ifs. simpl in H10, H4. des_ifs.
            exploit H6; eauto. instantiate (2:=f_id). simpl. eauto.
            rewrite prog_defmap_elements, PTree.gcombine. rewrite H9. simpl. des_ifs. auto. ii. des. simpl in H11. clarify.
          + esplits. rewrite H1. simpl. auto. simpl. auto.
            ii. simpl in Heq5, Heq6. clarify. simpl in H8. des_ifs.
        - exploit prog_defmap_image. eapply Heq5. ii. rr in H4. simpl in H4. des; clarify.
          exploit H6. eauto.
          rewrite prog_defmap_elements, PTree.gcombine. rewrite H9. simpl. eauto. auto. ii. des. simpl in H4. des; clarify.
        - exploit prog_defmap_image. eapply H8. ii. rr in H4. simpl in H4. des; clarify.
          exploit H3; eauto. ii. des. simpl in H4. des; clarify. }
      ii. rewrite H8 in *. clarify.
    + hexploit (link_prog_inv _ _ _ Heq). i. des.
      hexploit (link_prog_inv _ _ _ Heq0). i. des.
      hexploit (link_prog_inv _ _ _ Heq2). i. des.
      hexploit (link_prog_inv _ _ _ Heq3). i. des.
      rewrite H1 in *. rewrite H4 in *. rewrite H7 in *. rewrite H10 in *.
      f_equal. f_equal. eapply PTree.elements_extensional. ii.
      repeat rewrite prog_defmap_elements.
      repeat rewrite PTree.gcombine; (try by ss).
      repeat rewrite prog_defmap_elements.
      repeat rewrite PTree.gcombine; (try by ss).
      destruct ((prog_defmap (CSk.of_program signature_of_function MutrecA.prog)) ! i) eqn:DMAPA; cycle 1.
      { destruct ((prog_defmap (Sk.of_program Asm.fn_sig MutrecB.prog)) ! i) eqn: DMAPB; cycle 1.
        { destruct ((prog_defmap t) ! i) eqn: DMAPC; ss. }
        { destruct ((prog_defmap t) ! i) eqn: DMAPC; ss. }
      }
      destruct ((prog_defmap (Sk.of_program Asm.fn_sig MutrecB.prog)) ! i) eqn: DMAPB; cycle 1.
      { destruct ((prog_defmap t) ! i) eqn: DMAPC; ss. }
      { destruct ((prog_defmap t) ! i) eqn: DMAPC.
        - unfold link_prog_merge. des_ifs.
          + simpl in Heq1, Heq4. unfold link_def in *. des_ifs.
            * simpl in Heq4, Heq5. unfold link_skfundef in *. des_ifs.
            * simpl in Heq4, Heq5. unfold link_vardef in *. des_ifs.
              Local Transparent Linker_def. simpl. des_ifs.
              { unfold link_vardef in *. des_ifs.
                simpl in Heq14, Heq12, Heq6, Heq8. unfold link_varinit in *.
                simpl in Heq5, Heq8, Heq9, Heq6. unfold link_varinit in *. destruct u1, u2. clarify.
                clear -Heq8 Heq6 Heq14 Heq12 Heq11. des_ifs. }
              { unfold link_vardef in *. des_ifs.
                - simpl in Heq16, Heq13. rewrite andb_true_iff in *.
                  repeat rewrite eqb_true_iff in *. repeat rewrite andb_false_iff in *. repeat rewrite eqb_false_iff in *. des.
                  rewrite Heq9 in *. clarify. rewrite Heq4 in *. clarify.
                - simpl in Heq14, Heq12, Heq6, Heq8. unfold link_varinit in *.
                  simpl in Heq5, Heq8, Heq9, Heq6. unfold link_varinit in *. destruct u1, u2. clarify.
                  clear -Heq8 Heq6 Heq14 Heq12 Heq11. des_ifs. }
              { unfold link_vardef in *. des_ifs.
                - simpl in Heq15, Heq13. rewrite andb_true_iff in *.
                  repeat rewrite eqb_true_iff in *. repeat rewrite andb_false_iff in *. repeat rewrite eqb_false_iff in *. des; clarify.
                - simpl in Heq14, Heq12, Heq6, Heq8. unfold link_varinit in *.
                  simpl in Heq5, Heq8, Heq9, Heq6. unfold link_varinit in *. destruct u1, u2. des_ifs.
                  + simpl in n.
                    destruct (classic (sz1 >= 0)).
                    { exploit Zmax_left; eauto. i. rewrite H7 in n. rewrite Z.add_0_r in n. nia. }
                    { eapply Znot_ge_lt in H1. rewrite Z.max_l in n. nia. nia. }
                  + simpl in n. exploit Zmax_left. eapply init_data_list_size_pos. i. rewrite H1 in n. nia. }
          + exploit H3; eauto. i. des. clarify.
          + exploit H0; eauto. i. des. clarify.
          + exploit H0; eauto. i. des. clarify.
        - unfold link_prog_merge. des_ifs. }
Qed.

Lemma link_sk_same ctx1 ctx2 :
    link_sk (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2)
    = link_sk (ctx1 ++ [module] ++ ctx2).
Proof.
  assert ([(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2 <> [] /\ [module] ++ ctx2 <> []) by ss.
  exploit (link_sk_same_aux1 ctx1 H). { eapply link_sk_same_aux2. } i. eauto.
Qed.

Lemma wf_module_Aspec: Sk.wf MutrecAspec.module.
Proof.
  ss. unfold MutrecA.prog. econs.
  - unfold prog_defs_names; ss.
    repeat (econs; ss; ii; des; clarify).
  - ss. i. des; clarify.
    unfold update_snd in *. ss. clarify. ss. des; clarify.
  - ii. ss. des; clarify; eauto.
  - i. ss. des; clarify; inv IN; ss; clarify.
Qed.

Lemma wf_module_Bspec: Sk.wf MutrecBspec.module.
Proof.
  ss. unfold MutrecB.prog. econs.
  - unfold prog_defs_names; ss.
    repeat (econs; ss; ii; des; clarify).
  - ss. i. des; clarify.
    unfold update_snd in *. ss. clarify. ss. des; clarify.
  - ii. ss. des; clarify; eauto.
  - i. ss. des; clarify; inv IN; ss; clarify.
Qed.

Definition is_focus (x: Mod.t) := x = MutrecAspec.module \/ x = MutrecBspec.module.

Section LXSIM.

  Variable ctx1: Syntax.program.
  Variable ctx2: Syntax.program.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk (ctx1 ++ [module] ++ ctx2) = Some sk_link).
  Let LINKTGT: link_sk (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2) = Some sk_link.
  Proof. rewrite link_sk_same. ss. Qed.
  Hypothesis WFCTX1: forall md : Mod.t, In md ctx1 -> Sk.wf md.
  Hypothesis WFCTX2: forall md : Mod.t, In md ctx2 -> Sk.wf md.

  Let INCLA: SkEnv.includes skenv_link (CSk.of_program signature_of_function MutrecA.prog).
  Proof.
    unfold skenv_link.
    exploit link_includes.
    eapply LINKTGT.
    instantiate (1:=MutrecAspec.module).
    eapply in_or_app; ss. auto. i. ss.
  Qed.

  Let INCLB: SkEnv.includes skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog).
  Proof.
    unfold skenv_link.
    exploit link_includes.
    eapply LINKTGT.
    instantiate (1:=MutrecBspec.module).
    eapply in_or_app; ss. auto. i. ss.
  Qed.

  Hypothesis SKWF: Sk.wf sk_link.
  Let SKEWF: SkEnv.wf skenv_link.
  Proof. eapply SkEnv.load_skenv_wf; et. Qed.

  Lemma genv_sim fptr if_sig :
      (<<FINDF: Genv.find_funct (SkEnv.project skenv_link MutrecABspec.sk_link) fptr = Some (AST.Internal if_sig)>>)
      <-> (<<FINDF: exists md, (<<FOCUS: is_focus md>>)
         /\ (<<FINDF: Genv.find_funct (ModSem.skenv (flip Mod.modsem skenv_link md)) fptr = Some (AST.Internal if_sig)>>)>>).
  Proof.
    split; i.
    - rr in H.
      unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *. unfold Genv.find_def in *. ss.
      rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in H.
      des_ifs.
      destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss.
      unfold o_bind in H. ss. des_ifs.
      destruct ((prog_defmap MutrecABspec.sk_link) ! i) eqn:Hdefmap; ss; clarify.
      unfold MutrecABspec.sk_link in *. ss. des_ifs.

      Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.

      exploit Genv.invert_find_symbol; eauto. i.
      unfold Genv.find_symbol, skenv_link, Sk.load_skenv in H.

      hexploit (link_prog_inv _ _ _ Heq1). i. des.
      subst p. dup Heq0.

      unfold prog_defmap in Hdefmap. simpl in Hdefmap.
      rewrite PTree_Properties.of_list_elements in *. des_ifs.
      simpl in Hdefmap. exploit PTree.elements_correct. eapply Hdefmap. i.
      unfold PTree.elements, PTree.xelements in H2. simpl in H2. des_ifs.
      destruct (classic (i = f_id)).
      { subst. ss.
        clarify. des; clarify.
        red. exists (MutrecAspec.module). split.
        - unfold is_focus. ss. auto.
        - ss. red. rewrite Genv.find_funct_ptr_iff.
          des_ifs; clarify. des; clarify. inv H2.
          exploit SkEnv.project_impl_spec. eapply INCLA. i. inv H. ss.
          exploit DEFKEEP. eauto. eauto. eauto. i. des. ss. clarify. }
      destruct (classic (i = g_id)).
      { subst. ss.
        clarify. des; clarify.
        red. exists (MutrecBspec.module). split.
        - unfold is_focus. ss. auto.
        - ss. red. rewrite Genv.find_funct_ptr_iff.
          des_ifs; clarify. des; clarify. inv H2.
          exploit SkEnv.project_impl_spec. eapply INCLB. i. inv H. ss.
          exploit DEFKEEP. eauto. eauto. eauto. i. des. ss. clarify. }
      clarify. ss. des; clarify.
      inv H2; clarify. inv H5; clarify.
      inv H2; clarify. inv H5; clarify.
    - rr in H. des.
      unfold Genv.find_funct in *. ss. des_ifs. rr. rewrite Genv.find_funct_ptr_iff in *.
      unfold Genv.find_def in *. ss.
      unfold Genv.find_funct in *.
      inv FOCUS; ss.
      + rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *. des_ifs.
        destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. unfold o_bind in *. ss.
        des_ifs; cycle 1.
        { unfold MutrecABspec.sk_link in Heq0. ss. des_ifs.
          Local Transparent Linker_program. ss.
          unfold link_program in *. des_ifs.
          Local Transparent Linker_prog. ss.

          exploit Genv.invert_find_symbol; eauto. i.
          unfold Genv.find_symbol, skenv_link, Sk.load_skenv in H.

          hexploit (link_prog_inv _ _ _ Heq2). i. des.
          subst p. ss.
          clear -Heq0 Heq1.
          rewrite CSk.of_program_internals in *.
          destruct (classic (i = f_id)).
          { subst. ss. }
          destruct (classic (i = g_id)).
          { subst. ss. }
          unfold internals in *. ss. des_ifs.
          { unfold MutrecA.prog, prog_defmap in *. ss.
            unfold MutrecA.global_definitions in *. ss.
            rewrite PTree_Properties.of_list_elements in *. des_ifs.
            simpl in Heq. exploit PTree.elements_correct. eapply Heq. i.
            unfold PTree.elements, PTree.xelements in H1. simpl in H1.
            inv H1; clarify. ss. des; clarify. }
          { unfold MutrecA.prog, prog_defmap in *. ss.
            unfold MutrecA.global_definitions in *. ss.
            rewrite PTree_Properties.of_list_elements in *. des_ifs.
            simpl in Heq2. exploit PTree.elements_correct. eapply Heq2. i.
            unfold PTree.elements, PTree.xelements in H1. simpl in H1.
            inv H1; clarify. ss. des; clarify. }
        }
        destruct ((prog_defmap (CSk.of_program signature_of_function MutrecA.prog)) ! i) eqn:DMAP; ss; clarify.
        unfold MutrecABspec.sk_link in *. ss. des_ifs.
        Local Transparent Linker_program. ss.
        unfold link_program in *. des_ifs.
        Local Transparent Linker_prog. ss.

        exploit Genv.invert_find_symbol; eauto. i.
        unfold Genv.find_symbol, skenv_link, Sk.load_skenv in H.

        hexploit (link_prog_inv _ _ _ Heq2). i. des.
        subst p.
        destruct (classic (i = f_id)).
        { subst. ss. }
        destruct (classic (i = g_id)).
        { subst. ss. }

        clear -DMAP H2 H3.
        exfalso.
        exploit (CSk.of_program_prog_defmap MutrecA.prog signature_of_function).
        i. inv H; rewrite DMAP in *. clarify.
        clarify. inv H4. unfold CtypesC.CSk.match_fundef in H6. des_ifs. symmetry in H0.
        clear DMAP.
        unfold MutrecA.prog, prog_defmap in *. ss.
        unfold MutrecA.global_definitions in *. ss.
        eapply PTree_Properties.in_of_list in H0. ss. simpl in H0.
        inv H0; clarify. ss. des; clarify.
      + rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *. des_ifs.
        destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. unfold o_bind in *. ss.
        des_ifs; cycle 1.
        { unfold MutrecABspec.sk_link in Heq0. ss. des_ifs.
          Local Transparent Linker_program. ss.
          unfold link_program in *. des_ifs.
          Local Transparent Linker_prog. ss.

          exploit Genv.invert_find_symbol; eauto. i.
          unfold Genv.find_symbol, skenv_link, Sk.load_skenv in H.

          hexploit (link_prog_inv _ _ _ Heq2). i. des.
          subst p. ss.
          clear -Heq0 Heq1.
          rewrite Sk.of_program_internals in *.
          destruct (classic (i = f_id)).
          { subst. ss. }
          destruct (classic (i = g_id)).
          { subst. ss. }
          unfold internals in *. ss. des_ifs.
          { unfold MutrecB.prog, prog_defmap in *. ss.
            unfold MutrecB.global_definitions in *. ss.
            rewrite PTree_Properties.of_list_elements in *. des_ifs.
            simpl in Heq. exploit PTree.elements_correct. eapply Heq. i.
            unfold PTree.elements, PTree.xelements in H1. simpl in H1.
            inv H1; clarify. ss. des; clarify. }
          { unfold MutrecB.prog, prog_defmap in *. ss.
            unfold MutrecA.global_definitions in *. ss.
            rewrite PTree_Properties.of_list_elements in *. des_ifs.
            simpl in Heq2. exploit PTree.elements_correct. eapply Heq2. i.
            unfold PTree.elements, PTree.xelements in H1. simpl in H1.
            inv H1; clarify. ss. des; clarify. }
        }
        destruct ((prog_defmap (Sk.of_program Asm.fn_sig MutrecB.prog)) ! i) eqn:DMAP; ss; clarify.
        unfold MutrecABspec.sk_link in *. ss. des_ifs.
        Local Transparent Linker_program. ss.
        unfold link_program in *. des_ifs.
        Local Transparent Linker_prog. ss.

        exploit Genv.invert_find_symbol; eauto. i.
        unfold Genv.find_symbol, skenv_link, Sk.load_skenv in H.

        hexploit (link_prog_inv _ _ _ Heq2). i. des.
        subst p.
        destruct (classic (i = f_id)).
        { subst. ss. }
        destruct (classic (i = g_id)).
        { subst. ss. }

        clear -DMAP H2 H3.
        exfalso.
        exploit (Sk.of_program_prog_defmap MutrecB.prog Asm.fn_sig).
        i. inv H; rewrite DMAP in *. clarify.
        clarify. inv H4. unfold CtypesC.CSk.match_fundef in H6. des_ifs. symmetry in H0.
        clear DMAP.
        unfold MutrecA.prog, prog_defmap in *. ss.
        unfold MutrecA.global_definitions in *. ss.
        eapply PTree_Properties.in_of_list in H0. ss. simpl in H0.
        inv H0; clarify. ss. des; clarify.
  Qed.

  Lemma find_f_id :
    exists blk, (<<SYMBBIG: Genv.find_symbol skenv_link f_id = Some blk>>)
            /\ (<<SYMBA: Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog)) f_id = Some blk>>)
            /\ (<<SYMBB: Genv.find_symbol (SkEnv.project skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog)) f_id = Some blk>>).
  Proof.
   inv INCLA. ss.
   inv SKEWF. ss.
   unfold prog_defmap in DEFS. ss.
   specialize (DEFS f_id). ss.
   exploit DEFS; eauto. i. des.
   esplits; eauto.
   - unfold Genv.find_symbol in *. ss. des_ifs.
     exploit MapsC.PTree_filter_key_spec.
     instantiate (6:=(fun id : ident => defs (CSk.of_program signature_of_function MutrecA.prog) id)).
     instantiate (2:=(PTree.Node
                        (PTree.Node t12 o8
                                    (PTree.Node
                                       (PTree.Node t13 o10
                                                   (PTree.Node t7 o11 (PTree.Node (PTree.Node (PTree.Node t15 (Some blk) t19) o13 t18) o12 t17))) o9 t14)) o7
                        t11)).
     instantiate (1:=f_id). rewrite Heq. ss.
   - unfold Genv.find_symbol in *. ss. des_ifs.
     exploit MapsC.PTree_filter_key_spec.
     instantiate (6:=(fun id : ident => defs (Sk.of_program Asm.fn_sig MutrecB.prog) id)).
     instantiate (2:=(PTree.Node
                        (PTree.Node t12 o8
                                    (PTree.Node
                                       (PTree.Node t13 o10
                                                   (PTree.Node t7 o11 (PTree.Node (PTree.Node (PTree.Node t15 (Some blk) t19) o13 t18) o12 t17))) o9 t14)) o7
                        t11)).
     instantiate (1:=f_id). rewrite Heq. ss.
  Qed.

  Lemma find_g_id :
    exists blk, (<<SYMBBIG: Genv.find_symbol skenv_link g_id = Some blk>>)
           /\ (<<SYMBA: Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog)) g_id = Some blk>>)
           /\ (<<SYMBB: Genv.find_symbol (SkEnv.project skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog)) g_id = Some blk>>)
  .
  Proof.
    inv INCLB. ss. inv SKEWF. ss.
    unfold prog_defmap in DEFS. ss.
    specialize (DEFS g_id). ss.
    exploit DEFS; eauto. i. des.
    esplits; eauto.
    - unfold Genv.find_symbol in *. ss. des_ifs.
      exploit MapsC.PTree_filter_key_spec.
      instantiate (6:=(fun id : ident => defs (CSk.of_program signature_of_function MutrecA.prog) id)).
      instantiate (2:=(PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node (PTree.Node t7 o11 (PTree.Node t12 o12 (PTree.Node (PTree.Node t17 (Some blk) t19) o13 t18))) o10
                      t15) o9 t14) o8 t13) o7 t11)).
      instantiate (1:=g_id). rewrite Heq. ss.
    - unfold Genv.find_symbol in *. ss. des_ifs.
      exploit MapsC.PTree_filter_key_spec.
      instantiate (6:=(fun id : ident => defs (Sk.of_program Asm.fn_sig MutrecB.prog) id)).
      instantiate (2:=(PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node (PTree.Node t7 o11 (PTree.Node t12 o12 (PTree.Node (PTree.Node t17 (Some blk) t19) o13 t18))) o10
                      t15) o9 t14) o8 t13) o7 t11)).
      instantiate (1:=g_id). rewrite Heq. ss.
  Qed.

  Inductive match_focus: mem -> int -> int -> list Frame.t -> Prop :=
  | match_focus_nil
      cur max m
      (OVER: cur.(Int.intval) > max.(Int.intval)):
      match_focus m cur max []
  | match_focus_cons_A
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z):
      match_focus m cur max ((Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Interstate cur m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z):
      match_focus m cur max ((Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Interstate cur m)) :: tl_tgt).

  Lemma add_one_same
        i
        (BOUND: 0 <= Int.intval i + 1 <= Int.max_unsigned):
      Int.intval (Int.add i Int.one) = Int.intval i + 1.
  Proof.
    unfold Int.add. unfold Int.unsigned.
    unfold Int.one.
    Local Transparent Int.repr.
    unfold Int.repr. ss.
    rewrite Int.Z_mod_modulus_eq.
    unfold Int.Z_mod_modulus. des_ifs.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.unsigned_repr. auto. split; omega.
  Qed.

  Lemma match_focus_over_nil
        m max hds_tgt
        (RANGE: max.(Int.intval) < MAX)
        (FOCUS: match_focus m (Int.add max Int.one) max hds_tgt):
      hds_tgt = nil.
  Proof.
    clear - RANGE FOCUS.
    inv FOCUS; ss.
    - exfalso.
      assert (Int.intval (Int.add max Int.one) = (Int.intval max) + 1); destruct max.
      { rewrite add_one_same; ss.
        unfold MAX, Int.max_unsigned in *; ss. split; omega. }
      ss. rewrite H in LE. omega.
    - exfalso.
      assert (Int.intval (Int.add max Int.one) = (Int.intval max) + 1); destruct max.
      { rewrite add_one_same; ss.
        unfold MAX, Int.max_unsigned in *; ss. split; omega. }
      ss. rewrite H in LE. omega.
  Qed.

  Inductive match_stacks (fromcall: bool) (idx: Z): list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_ctx
      ctx_stk
      (IDX: idx = 0%Z):
      match_stacks fromcall idx ctx_stk ctx_stk
  | match_stacks_focus_top_call
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate max m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = 2 * cur.(Int.intval))
      (RANGE: max.(Int.intval) < MAX):
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar
  | match_stacks_focus_top_return
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Returnstate (sum max) m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Returnstate (sum cur) m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Returnstate (sum cur) m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = max.(Int.intval) - cur.(Int.intval))
      (RANGE: max.(Int.intval) < MAX):
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar.

  Inductive match_states (i: Z): Sem.state -> Sem.state -> Prop :=
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks true i frs_src frs_tgt):
      match_states i (Callstate args frs_src) (Callstate args frs_tgt)
  | match_states_normal
      frs_src frs_tgt
      (STK: match_stacks false i frs_src frs_tgt):
      match_states i (State frs_src) (State frs_tgt).

  Lemma int_zero_intval: Int.intval Int.zero = 0%Z.
  Proof. unfold Int.intval. ss. Qed.

  Lemma int_sub_add: forall cur x, (Int.add (Int.sub cur x) x) = cur.
  Proof.
    i.
    rewrite Int.sub_add_opp. rewrite Int.add_assoc.
    rewrite Int.add_commut with (y := x).
    rewrite Int.add_neg_zero. rewrite Int.add_zero. ss.
  Qed.

  Hint Unfold Frame.update_st.

  Lemma match_states_xsim
        i st_src0 st_tgt0
        (MATCH: match_states i st_src0 st_tgt0):
    xsim (sem (ctx1 ++ [module] ++ ctx2)) (sem (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)) (Zwf.Zwf 0) top1 top1 i st_src0 st_tgt0.
  Proof.
    revert_until SKEWF. pcofix CIH. i.
    inv MATCH.
    - (* call *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; et.
        i. econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. rewrite LINKTGT. rewrite LINKSRC in *. ss. des.
          - inv SAFESRC.
          - inv SAFESRC. right. inv MSFIND. ss. des; clarify.
            { esplits; eauto. econs; eauto. econs; eauto. ss. eauto. }
            unfold load_modsems in *. rewrite in_map_iff in *. des. clarify. rewrite in_app_iff in *.
            ss. des; clarify.
            { esplits; eauto. econs; eauto. econs; eauto. ss. right. unfold load_modsems.
              rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. }
            apply genv_sim in INTERNAL. des. rr in FOCUS. inv INIT.
            unfold Genv.find_funct in *. des_ifs.
            des; clarify.
            { esplits; eauto. econs.
              { econs; eauto; cycle 1.
                { unfold Genv.find_funct. des_ifs. eauto. }
                ss. right. unfold load_modsems. rewrite in_map_iff.
                esplits; eauto. rewrite in_app_iff. ss. eauto. }
              econs; ss; eauto.
              - unfold Args.get_fptr in *. des_ifs. ss. clarify.
                eapply MutrecAspec.find_symbol_find_funct_ptr; et. }
            { esplits; eauto. econs.
              { econs; eauto; cycle 1.
                { unfold Genv.find_funct. des_ifs. eauto. }
                ss. right. unfold load_modsems. rewrite in_map_iff.
                esplits; eauto. rewrite in_app_iff. ss. eauto. }
              econs; ss; eauto.
              - unfold Args.get_fptr in *. des_ifs. ss. clarify.
                eapply MutrecBspec.find_symbol_find_funct_ptr; et.
            }
            { esplits; eauto. econs; eauto. econs; eauto. ss. right. unfold load_modsems.
              rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. ss. auto. } }
        { i; ss. des_ifs. inv FINALTGT. }
        i. ss. rewrite LINKSRC, LINKTGT in *. inv STEPTGT. inv MSFIND. ss.
        unfold load_modsems in *. des; clarify.
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
        rewrite in_map_iff in *. des; clarify. rewrite in_app_iff in *. des; clarify.
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. right.
            unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
        ss. des; clarify.
        { inv INIT. ss. esplits; eauto.
          - left. apply plus_one. econs.
            { econs.
              { ss. right. unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff.
                ss. eauto. }
              eapply genv_sim. exists MutrecAspec.module. esplits; ss; eauto. rr. eauto. }
            econs; ss; eauto.
            + eapply genv_sim. destruct args; ss. clarify. exists MutrecAspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            { econs; eauto.
              rewrite add_one_same. nia.
              unfold MAX, Int.max_unsigned in *; ss. omega. }
            { des; ss. } }
        { inv INIT. ss. esplits; eauto.
          - left. apply plus_one. econs.
            { econs.
              { ss. right. unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff.
                ss. eauto. }
              eapply genv_sim. exists MutrecBspec.module. esplits; ss; eauto. rr. eauto. }
            econs; ss; eauto.
            + eapply genv_sim. destruct args; ss. clarify. exists MutrecBspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            { econs; eauto.
              rewrite add_one_same. nia.
              unfold MAX, Int.max_unsigned in *; ss. omega. }
            { des; ss. } }
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. right.
            unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. ss. eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
      + (* focus-call *)
        ss.
      + (* focus-return *)
        ss.
    - (* normal *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; eauto.
        i. ss. econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss; des_ifs. des; ss.
          - left. esplits; eauto.
          - right. inv SAFESRC; ss.
            { esplits; eauto. econs 1; eauto. }
            { esplits; eauto. econs 3; eauto. }
            { esplits; eauto. econs 4; eauto. } }
        { ii; ss. inv FINALTGT. des_ifs. esplits; eauto. { apply star_refl. } econs; eauto. }
        i. ss. des_ifs.
        inv STEPTGT; ss.
        * esplits; eauto.
          { left. apply plus_one. econs 1; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
        * esplits; eauto.
          { left. apply plus_one. econs 3; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
        * esplits; eauto.
          { left. apply plus_one. econs 4; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
      + (* focus-call *)
        pfold. right. econs; et.
        i. econs; ss; try rewrite LINKSRC, LINKTGT in *; eauto; cycle 1; ss.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. des.
          - inv SAFESRC. inv FINAL.
          - des_ifs. inv SAFESRC; ss.
            + inv STEP. right.
              unsguard TGT. des; clarify; ss; esplits; eauto; econs 3; ss; eauto; econs; eauto.
            + unsguard TGT. des; clarify; ss; inv FINAL. }
        { ii; ss. inv FINALTGT. unsguard TGT. des; clarify; ss; inv FINAL. }
        i. inv STEPTGT; ss; swap 2 3.
        { unsguard TGT; des; clarify; inv AT. }
        { unsguard TGT; des; clarify; inv FINAL. }
        unsguard TGT; des; clarify; ss.
        { - inv STEP; ss.
            + esplits; eauto.
              * left. apply plus_one. econs 3; ss; et.
              * right. eapply CIH. unfold Frame.update_st. ss. econs; et. econs 3; et; ss. unfold __GUARD__. eauto.
            + esplits; eauto.
              * right. esplits; eauto.
                { apply star_refl. }
                { instantiate (1:= 2 * (Int.intval cur) - 1). rr. esplits; eauto; try lia.
                  destruct cur. ss. omega. }
              * left. pfold. left. right. econs; eauto.
                hexploit find_g_id; eauto. i; des.
                hexploit (MutrecBspec.find_symbol_find_funct_ptr); eauto. instantiate (1:= blk). i; des.
                exploit SYMB; eauto. intro T; des. clear SYMB FINDF.
                econs 2; eauto; esplits.
                -- eapply plus_two with (t1 := []) (t2 := []); ss.
                   ++ econs; eauto.
                      { eapply lift_determinate_at; ss; des_ifs; eauto.
                        econs; eauto.
                        - ii; ss. inv H; inv H0; ss.
                        - econs; eauto. inv H. }
                      econs; ss; eauto. econs; eauto.
                   ++ unfold Frame.update_st. ss. econs; eauto.
                      { econs; ss; des_ifs.
                        - i. inv H; inv H0; ss.
                          esplits; eauto.
                          { econs. }
                          { i.
                            assert (Ge.find_fptr_owner (load_genv (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2) (Sk.load_skenv sk_link))
                                                       (Vptr blk Ptrofs.zero) (Mod.get_modsem MutrecBspec.module skenv_link tt)).
                            { ss. econs.
                              - ss. right. unfold load_modsems. rewrite list_append_map. ss.
                                unfold MutrecBspec.module, flip, Mod.modsem. ss.
                                eapply in_or_app. ss. auto.
                              - ss. des_ifs. eauto. }
                            exploit find_fptr_owner_determ.
                            instantiate (1 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                            i. eapply in_app_or in IN. ss. des; clarify.
                            { eapply WFCTX1; eauto. }
                            { eapply wf_module_Aspec. }
                            { eapply wf_module_Bspec. }
                            { eapply WFCTX2; eauto. }
                            ss. des_ifs. eapply MSFIND.
                            ss. des_ifs. eapply MSFIND0.
                            i. subst ms.
                            exploit find_fptr_owner_determ.
                            instantiate (1 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                            i. eapply in_app_or in IN. ss. des; clarify.
                            { eapply WFCTX1; eauto. }
                            { eapply wf_module_Aspec. }
                            { eapply wf_module_Bspec. }
                            { eapply WFCTX2; eauto. }
                            ss. des_ifs. eapply MSFIND.
                            ss. des_ifs. eapply H0.
                            i. subst ms0. ss.
                            inv INIT; inv INIT0. ss. clarify. }
                        - i. inv FINAL; inv STEP.
                        - econs. inv H; ss. }
                      econs; ss; eauto.
                      ** des_ifs. econs; ss.
                         { right. unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. right. right. ss. eauto. }
                         des_ifs; eauto.
                      ** econs; ss; eauto.
                         { destruct cur,  max. ss. esplits; try omega.
                           exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                           assert (intval - 1 < MAX) by nia.
                           rewrite Int.Z_mod_modulus_eq.
                           rewrite <- Int.unsigned_repr_eq.
                           rewrite Int.unsigned_repr. auto. unfold Int.max_unsigned. split; nia. }
                -- instantiate (1:= 2 * Int.intval cur - 2). rr. esplits; try lia.
                   destruct cur. ss. nia.
                -- right. eapply CIH. u. econs; eauto.
                   econs.
                   { f_equal. }
                   { f_equal. rewrite cons_app. rewrite app_assoc. f_equal. }
                   { unfold __GUARD__. eauto. }
                   { destruct cur,  max. ss. esplits; try omega.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. rewrite int_sub_add. econs 2; eauto. }
                   { ss. }
                   { destruct cur. ss.
                     exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. } }
        { - inv STEP; ss.
            + esplits; eauto.
              * left. apply plus_one. econs 3; ss; et.
              * right. eapply CIH. unfold Frame.update_st. ss. econs; et. econs 3; et; ss. unfold __GUARD__. eauto.
            + esplits; eauto.
              * right. esplits; eauto.
                { apply star_refl. }
                { instantiate (1:= 2 * (Int.intval cur) - 1). rr. esplits; eauto; try lia.
                  destruct cur. ss. omega. }
              * left. pfold. left. right. econs; eauto.
                hexploit find_f_id; eauto. i; des.
                hexploit (MutrecAspec.find_symbol_find_funct_ptr); eauto. instantiate (1:= blk). i; des.
                exploit SYMB; eauto. intro T; des. clear SYMB FINDF.
                econs 2; eauto; esplits.
                -- eapply plus_two with (t1 := []) (t2 := []); ss.
                   ++ econs; eauto.
                      { 
                        eapply lift_determinate_at; ss; des_ifs; eauto.
                        econs; eauto.
                        - ii; ss. inv H; inv H0; ss.
                        - econs; eauto. inv H.
                      }
                      econs; ss; eauto. econs; eauto.
                   ++ unfold Frame.update_st. ss. econs; eauto.
                      { econs; ss; des_ifs.
                        - i. inv H; inv H0; ss.
                          esplits; eauto.
                          { econs. }
                          { i.
                            assert (Ge.find_fptr_owner (load_genv (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2) (Sk.load_skenv sk_link))
                                                       (Vptr blk Ptrofs.zero) (Mod.get_modsem MutrecAspec.module skenv_link tt)).
                            { ss. econs.
                              - ss. right. unfold load_modsems. rewrite list_append_map. ss.
                                unfold MutrecBspec.module, flip, Mod.modsem. ss.
                                eapply in_or_app. ss. auto.
                              - ss. des_ifs. eauto. }
                            exploit find_fptr_owner_determ.
                            instantiate (1 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                            i. eapply in_app_or in IN. ss. des; clarify.
                            { eapply WFCTX1; eauto. }
                            { eapply wf_module_Aspec. }
                            { eapply wf_module_Bspec. }
                            { eapply WFCTX2; eauto. }
                            ss. des_ifs. eapply MSFIND.
                            ss. des_ifs. eapply MSFIND0.
                            i. subst ms.
                            exploit find_fptr_owner_determ.
                            instantiate (1 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                            i. eapply in_app_or in IN. ss. des; clarify.
                            { eapply WFCTX1; eauto. }
                            { eapply wf_module_Aspec. }
                            { eapply wf_module_Bspec. }
                            { eapply WFCTX2; eauto. }
                            ss. des_ifs. eapply MSFIND.
                            ss. des_ifs. eapply H0.
                            i. subst ms0. ss.
                            inv INIT; inv INIT0. ss. clarify. }
                        - i. inv FINAL; inv STEP.
                        - econs. inv H; ss. }
                      econs; ss; eauto.
                      ** des_ifs. econs; ss.
                         { right. unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. right. left. ss. }
                         des_ifs; eauto.
                      ** econs; ss; eauto.
                         { destruct cur,  max. ss. esplits; try omega.
                           exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                           assert (intval - 1 < MAX) by nia.
                           rewrite Int.Z_mod_modulus_eq.
                           rewrite <- Int.unsigned_repr_eq.
                           rewrite Int.unsigned_repr. auto. unfold Int.max_unsigned. split; nia. }
                -- instantiate (1:= 2 * Int.intval cur - 2). rr. esplits; try lia.
                   destruct cur. ss. nia.
                -- right. eapply CIH. u. econs; eauto.
                   econs.
                   { f_equal. }
                   { f_equal. rewrite cons_app. rewrite app_assoc. f_equal. }
                   { unfold __GUARD__. eauto. }
                   { destruct cur,  max. ss. esplits; try omega.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. rewrite int_sub_add. econs 3; eauto. }
                   { ss. }
                   { destruct cur. ss.
                     exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. } }
      + (* focus - return *)
        destruct (classic (cur = max)).
        * clarify. exploit match_focus_over_nil; eauto.
          i; clarify.
          pfold. right. econs; eauto.
          i. econs; eauto; cycle 1.
          { i. specialize (SAFESRC _ (star_refl _ _ _ _)). desH SAFESRC; ss.
            - inv SAFESRC; ss. inv FINAL. ss. clarify. left.
              unsguard TGT. des; clarify.
              { esplits; eauto. econs; ss; eauto. }
              { esplits; eauto. econs; ss; eauto. }
            - des_ifs. right. inv SAFESRC; ss.
              { inv STEP. }
              inv FINAL. esplits; eauto. econs 4; eauto.
              unsguard TGT. des; clarify. }
          { i. ss. inv FINALTGT.
            unsguard TGT. des; clarify; ss.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto. }
          i. ss. des_ifs. inv STEPTGT; ss.
          { unsguard TGT. des; clarify; inv AT. }
          { unsguard TGT. des; clarify; inv STEP. }
          esplits; eauto.
          -- left. apply plus_one. econs 4; eauto. ss. unsguard TGT. des; clarify; ss; inv FINAL; econs; eauto.
          -- right. eapply CIH. econs; eauto. econs; eauto.
        * pfold. left. right. econs; eauto.
          unsguard TGT. des; clarify.
          { inv FOCUS; ss.
            { exfalso.
              exploit Int.eq_false; eauto. i.
              destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
              exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
              assert (intval - 1 < MAX) by nia.
              rewrite Int.Z_mod_modulus_eq in OVER.
              rewrite <- Int.unsigned_repr_eq in OVER.
              rewrite Int.unsigned_repr in OVER. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. } }
          { inv FOCUS; ss.
            { exfalso.
              exploit Int.eq_false; eauto. i.
              destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
              exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
              assert (intval - 1 < MAX) by nia.
              rewrite Int.Z_mod_modulus_eq in OVER.
              rewrite <- Int.unsigned_repr_eq in OVER.
              rewrite Int.unsigned_repr in OVER. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. } }
  Qed.

End LXSIM.


Theorem mutrecABcorrect ctx1 ctx2 :
    (<<REFINE: improves (Sem.sem (ctx1 ++ [(MutrecABspec.module)] ++ ctx2))
                        (Sem.sem (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2))>>).
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  econs; eauto.
  econs; try apply progress_top; eauto; swap 2 3.
  { instantiate (1:= Zwf.Zwf 0%Z). eapply Zwf.Zwf_well_founded. }
  { i; des. ss. inv SAFESRC. rewrite INITSK.
    exploit link_sk_same; ss. i. erewrite H. des_ifs. }
  econs; eauto.
  i. ss. inv INITSRC.
  esplits; eauto.
  { econs; ss; eauto.
    - econs; eauto.
      + exploit link_sk_same; ss. i. erewrite H. des_ifs.
      + ii; ss. rewrite in_app_iff in *. des; ss.
        { eapply WF; et. rewrite in_app_iff. et. }
        des; cycle 2; subst.
        { eapply WF; et. rewrite in_app_iff. ss. et. }
        * eapply wf_module_Aspec; et.
        * eapply wf_module_Bspec; et.
    - i; ss. inv INIT0. inv INIT1. clarify. }
  eapply match_states_xsim; eauto.
  { ii. eapply WF. ss. eapply in_or_app. auto. }
  { ii. eapply WF. ss. eapply in_or_app. ss. auto. }
  { eapply link_list_preserves_wf_sk; eauto. }
  econs; eauto. econs; eauto.
Qed.
