Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib StoreArguments AsmC Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC Lia LinkingC2 mktac MemdataC LocationsC AsmStepInj LowerBoundExtra IdSimExtra.


Set Implicit Arguments.

Local Opaque Z.mul.

Record sub_match_genvs A B V W (R: globdef A V -> globdef B W -> Prop)
       (ge1: Genv.t A V) (ge2: Genv.t B W): Prop :=
  {
    sub_mge_next : Ple (Genv.genv_next ge1) (Genv.genv_next ge2);
    sub_mge_symb id b (FIND: Genv.find_symbol ge1 id = Some b):
      Genv.find_symbol ge2 id = Some b;
    sub_mge_defs b d0 (FIND: Genv.find_def ge1 b = Some d0):
      exists d1, <<FIND: Genv.find_def ge2 b = Some d1>> /\ <<MATCHDEF: R d0 d1>>;
  }.

Definition match_prog (sk: Sk.t) (tprog: Asm.program) : Prop
  := @match_program
       _ _ _ _ (Linking.Linker_fundef signature) Linker_unit
       (fun cu tf f => tf = AST.transf_fundef fn_sig f) eq sk tprog.

Lemma module_match_prog p
  :
    match_prog (AsmC.module p) p.
Proof.
  specialize (@match_transform_program _ _ unit _ _ (transf_fundef fn_sig) p).
  unfold match_prog.
  replace (Mod.sk (module p)) with
      (transform_program (transf_fundef fn_sig) p); cycle 1.
  { unfold module, Sk.of_program, transform_program, transf_fundef. ss. f_equal.
    unfold skdefs_of_gdefs, skdef_of_gdef, update_snd. f_equal.
    extensionality i. destruct i. ss. des_ifs. destruct v. repeat f_equal.
    destruct gvar_info. refl.
  }
  generalize (transform_program (transf_fundef fn_sig) p). i.

  inv H. des. econs; eauto.
  eapply list_forall2_rev. eapply list_forall2_imply; eauto.

  i. inv H4. inv H6; splits; eauto; ss.
  - econs; eauto.
    instantiate (1:=mkprogram nil nil p0.(prog_main)).
    econs; splits; eauto; ss.
    i. eapply in_prog_defmap in H6. ss.
  - econs; eauto. inv H8. ss.
Qed.

Lemma link_success progs sk
      (LINK_SK: link_sk (List.map AsmC.module progs) = Some sk)
  :
    exists tprog, link_list progs = Some tprog /\ match_prog sk tprog.
Proof.
  assert((@link_list _ (@Linker_prog _ _ (Linking.Linker_fundef signature) _)
                     (map Mod.sk (map module progs))) = Some sk).
  { unfold link_sk, link_list in *. des_ifs_safe.
    eapply (@stricter_link_list_aux _ (@Linker_prog (AST.fundef signature) unit (Linking.Linker_fundef signature) Linker_unit) (@Linker_prog (AST.fundef signature) unit Linker_skfundef Linker_unit)) in Heq.
    - rewrite Heq. auto.
    - clear Heq.
      Local Transparent Linker_prog Linker_def Linking.Linker_fundef Linker_skfundef.
      i. ss. unfold link_prog, proj_sumbool, andb in *. des_ifs_safe.
      assert (FORALL: @PTree_Properties.for_all
                        _ (prog_defmap x0) (@link_prog_check _ _ (Linking.Linker_fundef signature) _ x0 x1)
                      = true).
      + rewrite PTree_Properties.for_all_correct in Heq0.
        rewrite PTree_Properties.for_all_correct.
        i. unfold link_prog_check, proj_sumbool, andb in *. des_ifs_safe.
        exploit Heq0; eauto. i. des_ifs.
        ss. unfold link_def in *. des_ifs.
        ss. unfold link_skfundef, Linking.link_fundef in *. des_ifs.
      + rewrite FORALL. f_equal. f_equal. eapply PTree.elements_extensional.
        i. erewrite PTree.gcombine; eauto. erewrite PTree.gcombine; eauto.
        rewrite PTree_Properties.for_all_correct in Heq0.
        rewrite PTree_Properties.for_all_correct in FORALL.
        unfold link_prog_merge. des_ifs.
        exploit Heq0; eauto. i. exploit FORALL; eauto. i. clear Heq0 FORALL.
        unfold link_prog_check, proj_sumbool, andb in *. des_ifs.
        ss. unfold link_def in *. des_ifs.
        ss. unfold link_skfundef, Linking.link_fundef in *. des_ifs. }
  clear LINK_SK. rename H into LINK_SK.
  eapply (@link_list_match (AST.program (AST.fundef signature) unit) Asm.program (@Linker_prog (AST.fundef signature) unit (Linking.Linker_fundef signature)
                                                                                               Linker_unit)); eauto.
  - eapply (@TransfTotalLink_rev function signature unit Linker_unit fn_sig).
  - rewrite list_map_compose. clear LINK_SK.
    induction progs; ss.
    + econs.
    + econs; ss.
      eapply module_match_prog.
Qed.

Section PRESERVATION.

(** ********************* linking *********************************)

  Variable progs : list Asm.program.
  Let prog : Syntax.program := List.map AsmC.module progs.
  Hypothesis (WFSK: forall md (IN: In md prog), <<WF: Sk.wf md>>).

  Variable tprog : Asm.program.
  Hypothesis LINK : link_list progs = Some tprog.

(** ********************* genv *********************************)

  Variable sk : Sk.t.
  Hypothesis LINK_SK : link_sk prog = Some sk.
  Let skenv_link := Sk.load_skenv sk.
  Let ge := load_genv prog skenv_link.
  Let tge := Genv.globalenv tprog.
  Let WFSKLINK: Sk.wf sk. eapply link_list_preserves_wf_sk; et. Qed.
  Let WFSKELINK: SkEnv.wf skenv_link.
  Proof.
    eapply SkEnv.load_skenv_wf.
    ss.
  Qed.

  Let ININCL: forall p (IN: In p prog), <<INCL: SkEnv.includes skenv_link p.(Mod.sk)>>.
  Proof.
    eapply link_includes; et.
  Qed.

  Definition local_genv (p : Asm.program) :=
    (skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig)).(SkEnv.revive) p.

  Lemma match_genvs_sub A B V W R (ge1: Genv.t A V) (ge2: Genv.t B W)
        (MATCHGE: Genv.match_genvs R ge1 ge2)
    :
      sub_match_genvs R ge1 ge2.
  Proof.
    inv MATCHGE. econs; i; ss; eauto.
    - rewrite mge_next. refl.
    - etrans; eauto.
    - unfold Genv.find_def in *. specialize (mge_defs b).
      inv mge_defs; eq_closure_tac. eauto.
  Qed.

  Lemma match_genvs_le A B V W R1 R2 (ge1: Genv.t A V) (ge2: Genv.t B W)
        (MATCHGE: Genv.match_genvs R1 ge1 ge2)
        (LE: R1 <2= R2)
    :
      Genv.match_genvs R2 ge1 ge2.
  Proof.
    inv MATCHGE. econs; i; ss; eauto.
    cinv (mge_defs b).
    - econs 1.
    - econs 2. eapply LE; eauto.
  Qed.

  Definition genv_le (ge_src ge_tgt: Genv.t fundef unit): Prop :=
    (* sub_match_genvs eq ge_src ge_tgt. *)
    sub_match_genvs (@def_match _ _) ge_src ge_tgt.

  Lemma senv_definition_FILLIT id
    :
      Genv.public_symbol skenv_link id = Senv.public_symbol (symbolenv (sem prog)) id.
  Proof.
    ss. des_ifs.
  Qed.

  Lemma MATCH_PROG
    :
      match_prog sk tprog.
  Proof.
    exploit link_success; eauto. i. des. clarify.
  Qed.

  Lemma public_eq
    :
      prog_public sk = prog_public tprog.
  Proof.
    cinv MATCH_PROG. des. eauto.
  Qed.

  Lemma genv_public_eq
    :
      Genv.genv_public skenv_link = Genv.genv_public tge.
  Proof.
    unfold skenv_link, tge.
    repeat rewrite Genv.globalenv_public.
    eapply public_eq.
  Qed.

  Lemma main_eq
    :
      prog_main sk = prog_main tprog.
  Proof.
    cinv MATCH_PROG. des. eauto.
  Qed.

  Lemma match_skenv_link_tge :
    Genv.match_genvs (fun skdef fdef => skdef_of_gdef fn_sig fdef = skdef) skenv_link tge.
  Proof.
    set (Genv.globalenvs_match MATCH_PROG).
    eapply match_genvs_le; eauto.
    ii. inv PR; ss.
    - des_ifs.
    - inv H. ss. repeat f_equal. destruct i2. auto.
  Qed.

  Lemma sub_match_local_genv ge_local
        (MATCHGE: genv_le ge_local tge)
    :
      sub_match_genvs (fun fdef skdef => def_match (skdef_of_gdef fn_sig fdef) (skdef)) ge_local skenv_link.
  Proof.
    destruct match_skenv_link_tge. inv MATCHGE.
    unfold Genv.find_symbol, Genv.find_def in *. econs.
    - rewrite <- mge_next. eauto.
    - i. eapply sub_mge_symb0 in FIND.
      rewrite mge_symb in FIND. eauto.
    - i. eapply sub_mge_defs0 in FIND. des.
      specialize (mge_defs b). inv mge_defs.
      + eq_closure_tac.
      + eq_closure_tac. esplits; eauto.
        inv MATCHDEF; ss; des_ifs; econs.
  Qed.

  Inductive valid_owner fptr (p: Asm.program) : Prop :=
  | valid_owner_intro
      fd
      (MSFIND: ge.(Ge.find_fptr_owner) fptr (AsmC.modsem skenv_link p))
      (FINDF: Genv.find_funct (local_genv p) fptr = Some (Internal fd))
      (SIZEWF: 4 * size_arguments (fn_sig fd) <= Ptrofs.max_unsigned)
      (PROGIN: In (AsmC.module p) prog)
  .

  Lemma owner_genv_le p
      (IN: In (AsmC.module p) prog)
    :
      genv_le (local_genv p) tge.
  Proof.
    unfold ge in *.
    unfold load_modsems, flip, Mod.modsem, skenv_link, Sk.load_skenv, prog in *. ss.
    eapply in_map_iff in IN. des. clarify. apply inj_pair2 in H0. destruct H0. unfold local_genv.
    assert(INCL: SkEnv.includes (Genv.globalenv sk) (Sk.of_program fn_sig x)).
    { exploit link_includes; et.
      { rewrite in_map_iff. esplits; et. }
      i. ss.
    }

    cinv match_skenv_link_tge.
    cinv (@SkEnv.project_impl_spec skenv_link x.(Sk.of_program fn_sig) INCL).
    unfold skenv_link in *.

    assert (SKWF: SkEnv.wf_proj (SkEnv.project (Genv.globalenv sk) x.(Sk.of_program fn_sig))).
    { eapply SkEnv.project_spec_preserves_wf.
      - eapply SkEnv.load_skenv_wf.
        et.
      - eapply SkEnv.project_impl_spec; et.
    }

    exploit SkEnv.project_revive_precise; eauto.
    { eapply SkEnv.project_impl_spec; et. }
    i. inv H. econs; ss; i.

    - unfold fundef in *. rewrite mge_next. refl.

    - unfold Genv.find_symbol in *. rewrite mge_symb.
      destruct (classic (defs x id)).
      + exploit SYMBKEEP; et.
        { erewrite Sk.of_program_defs; et. }
        i; des.
        ss. congruence.
      + exploit SYMBDROP; et.
        { erewrite Sk.of_program_defs; et. }
        i; des.
        ss. congruence.

    - dup FIND. unfold SkEnv.revive in FIND.
      eapply Genv_map_defs_def in FIND. des.
      gesimpl.

      destruct (Genv.invert_symbol skenv_link b) eqn:EQ; cycle 1.
      { eapply DEFORPHAN in EQ. des. clarify. }

      exploit GE2P; et. i; des. uo. des_ifs.
      assert(TMP: Genv.find_symbol (SkEnv.project (Genv.globalenv sk) (Sk.of_program fn_sig x)) id = Some b).
      { uge. unfold SkEnv.revive in SYMB. ss. (* TODO: make lemma!!!!!! *) }
      assert(TMP0: Genv.find_symbol (Genv.globalenv sk) id = Some b).
      { unfold SkEnv.project in TMP. rewrite Genv_map_defs_symb in TMP. ss.
        unfold Genv.find_symbol in TMP. ss. (* TODO: make lemma!!!!!!!!!!!!!!!!!!!!!!! *)
        rewrite MapsC.PTree_filter_key_spec in *. des_ifs.
      }
      assert(id = i0).
      { apply Genv.find_invert_symbol in TMP. clarify. }
      clarify.
      assert(i = i0).
      { apply Genv.find_invert_symbol in TMP0. unfold skenv_link in EQ. clarify. }
      clarify.

      hexploit (link_list_linkorder _ LINK); et. intro LO; des. rewrite Forall_forall in *.
      specialize (LO x IN0).
      Local Transparent Linker_prog.
      ss.
      Local Opaque Linker_prog.
      des.
      exploit LO1; et. i; des.
      assert(INT: ~ASTC.is_external d0).
      { ss. }
      assert(INT0: ~ASTC.is_external gd2).
      { Local Transparent Linker_def. inv H0.
        - inv H2.
          + ss.
          + ss.
        - inv H2; ss.
      }
      exists gd2. splits; eauto.
      + apply Genv.find_def_symbol in H. des.
        assert(b0 = b).
        { apply Genv.invert_find_symbol in EQ. uge. rewrite mge_symb in H. unfold skenv_link in EQ. clarify. }
        clarify.
      + inv H0; ss.
        * inv H2; ss.
        * inv H2; ss. destruct info1, info2. econs.
  Qed.

  Lemma symb_preserved id
    :
      Senv.public_symbol (symbolenv (semantics tprog)) id =
      Senv.public_symbol (symbolenv (sem prog)) id.
  Proof.
    rewrite <- senv_definition_FILLIT. ss.
    unfold Genv.public_symbol in *.
    cinv match_skenv_link_tge.
    fold tge. ss. unfold fundef.
    unfold Genv.find_symbol in *. rewrite mge_symb.
    des_ifs. rewrite genv_public_eq. auto.
  Qed.

  Lemma symb_main :
    Genv.find_symbol skenv_link (prog_main sk) =
    Genv.find_symbol tge (prog_main tprog).
  Proof.
    unfold Genv.find_symbol in *.
    cinv match_skenv_link_tge.
    rewrite mge_symb. f_equal.
    eapply main_eq.
  Qed.

  Lemma local_global_consistent
        ge_local
        (LE: genv_le ge_local tge)
        fptr fd
        (LOCAL: Genv.find_funct ge_local fptr = Some (Internal fd))
        skd
        (GLOBAL: Genv.find_funct skenv_link fptr = Some skd)
    :
      SkEnv.get_sig skd = fd.(fn_sig)
  .
  Proof.
    inv LE.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs.
    cset sub_mge_defs0 Heq0. des.
    cinv match_skenv_link_tge.
    cinv (mge_defs b).
    - rewrite Heq in *. clarify.
    - rewrite Heq in *. clarify.
      unfold skdef_of_gdef, fundef in *. rewrite FIND in *. inv MATCHDEF. des_ifs.
  Qed.

(** ********************* initial memory *********************************)

  Variable m_init : mem.
  Hypothesis INIT_MEM: sk.(Sk.load_mem) = Some m_init.

  Definition m_tgt_init := m_init.

  Lemma TGT_INIT_MEM: Genv.init_mem tprog = Some m_tgt_init.
  Proof.
    Local Transparent Linker_prog.
    unfold Sk.load_mem in *.
    eapply (Genv.init_mem_match MATCH_PROG). eauto.
  Qed.

  Definition init_inject := Mem.flat_inj (Mem.nextblock m_init).

  Lemma initmem_inject: Mem.inject init_inject m_init m_tgt_init.
  Proof.
    eapply Genv.initmem_inject. unfold Sk.load_mem in INIT_MEM. eauto.
  Qed.

  Lemma init_inject_ge :
    skenv_inject skenv_link init_inject m_init.
  Proof.
    unfold init_inject, Mem.flat_inj. econs; i; ss.
    - unfold Sk.load_mem in *.
      erewrite <- Genv.init_mem_genv_next; eauto.
      unfold skenv_link, Sk.load_skenv in *. des_ifs.
    - des_ifs; eauto.
  Qed.

  (* TODO: remove redundancy with from UpperBound_B.v. *)
  Lemma senv_same
    :
      (tge: Senv.t) = (skenv_link: Senv.t)
  .
  Proof.
    generalize match_skenv_link_tge; intro MGE.
    clear - MGE.
    subst skenv_link. ss. unfold Sk.load_skenv in *. subst tge. unfold link_sk in *. ss.
    inv MGE.
    unfold fundef in *.
    apply senv_eta; ss.
    - uge. apply func_ext1. i. ss.
    - unfold Genv.public_symbol. uge. apply func_ext1. i. specialize (mge_symb x0).
      rewrite mge_symb. des_ifs. rewrite mge_pubs. ss.
    - apply func_ext1. i.
      destruct ((Genv.invert_symbol (@Genv.globalenv (AST.fundef function) unit tprog) x0)) eqn:T.
      + apply Genv.invert_find_symbol in T. symmetry. apply Genv.find_invert_symbol. uge. rewrite <- mge_symb. ss.
      + destruct (Genv.invert_symbol (Genv.globalenv sk) x0) eqn:U; ss.
        apply Genv.invert_find_symbol in U. specialize (mge_symb i). uge. rewrite <- mge_symb in *.
        apply Genv.find_invert_symbol in U. congruence.
    - unfold Genv.block_is_volatile, Genv.find_var_info. apply func_ext1. i.
      specialize (mge_defs x0). uge. inv mge_defs; ss.
      destruct y; ss. des_ifs.
  Qed.

  Lemma system_symbols_inject j m
        (SKINJ: skenv_inject skenv_link j m)
    :
      symbols_inject_weak j (System.globalenv skenv_link) skenv_link m.
  Proof.
    destruct match_skenv_link_tge. inv SKINJ.
    unfold System.globalenv.
    rr. esplits; ss.
    - i. exploit Genv.genv_symb_range; eauto. intro NB.
      exploit DOMAIN; et. i; clarify.
    - i. exploit Genv.genv_symb_range; eauto.
    - ii. destruct (Genv.block_is_volatile skenv_link b1) eqn:VEQ0.
      + eauto.
      + destruct (Genv.block_is_volatile skenv_link b2) eqn:VEQ1; auto.
        right. split; auto. ii.
        exploit IMAGE; eauto.
        * right. exists ofs. eapply Mem.perm_max.
          eapply Mem.perm_implies; eauto. econs.
        * i. clarify.
  Qed.

  Lemma external_function_sig
        v skd ef
        (FIND0: Genv.find_funct (System.globalenv skenv_link) v = Some (External ef))
        (FIND1: Genv.find_funct skenv_link v = Some skd)
    :
      SkEnv.get_sig skd = ef_sig ef
  .
  Proof.
    unfold System.globalenv in *. clarify.
  Qed.

  Section SYSTEM.

    Lemma system_function_ofs j b_src b_tgt delta fd m
          (SKINJ: skenv_inject skenv_link j m)
          (FIND: Genv.find_funct_ptr (System.globalenv skenv_link) b_src = Some fd)
          (INJ: j b_src = Some (b_tgt, delta))
    :
      delta = 0.
    Proof.
      inv SKINJ. exploit DOMAIN.
      - instantiate (1:=b_src). clear - FIND WFSKLINK.
        unfold System.globalenv in *.
        unfold Genv.find_funct_ptr in *. des_ifs.
        assert (SkEnv.wf skenv_link).
        { apply SkEnv.load_skenv_wf; et. }
        inv H. unfold Genv.find_symbol in *.
        exploit DEFSYMB; eauto. i. des.
        eapply Genv.genv_symb_range; eauto.
      - i. clarify.
    Qed.

    Lemma system_sig j b_src b_tgt delta ef m
          (SKINJ: skenv_inject skenv_link j m)
          (FIND: Genv.find_funct_ptr (System.globalenv skenv_link) b_src = Some (External ef))
          (INJ: j b_src = Some (b_tgt, delta))
      :
        Genv.find_funct_ptr tge b_tgt = Some (External ef).
    Proof.
      unfold System.globalenv in *.
      cinv match_skenv_link_tge.

      replace b_tgt with b_src; cycle 1.
      { unfold Genv.find_funct_ptr in FIND. des_ifs.
        cinv SKINJ. exploit DOMAIN.
        - instantiate (1:= b_src).
          assert (SkEnv.wf skenv_link).
          { apply SkEnv.load_skenv_wf; et. }
          inv H. unfold Genv.find_symbol in *.
          exploit DEFSYMB; eauto.
          i. des. eapply Genv.genv_symb_range; eauto.
        - i. clarify.
      }

      unfold Genv.find_funct_ptr, Genv.find_def, skdef_of_gdef, fundef in *.
      cinv (mge_defs b_src); des_ifs.
    Qed.

    Lemma system_receptive_at st frs
      :
        receptive_at (sem prog)
                     (State ((Frame.mk (System.modsem skenv_link) st) :: frs)).
    Proof.
      econs.
      - i. Local Opaque symbolenv.
        ss. rewrite LINK_SK in *.
        inv H; ss.
        + inv STEP. ss.
          exploit external_call_receptive; eauto; cycle 1.
          * i. des.
            eexists. econs; eauto. ss. econs; eauto.
            instantiate (1:=Retv.mk _ _); eauto.
          * unfold System.globalenv in *.
            unfold SkEnv.t in *.
            eapply match_traces_preserved; [| eauto].
            i. unfold Senv.public_symbol at 1. ss.
            eapply senv_definition_FILLIT.
        + inv FINAL. ss. inv H0.
          eexists. econs 4; ss; eauto.
      - ss. unfold single_events_at. i.
        inv H; ss; try lia.
        inv STEP.
        exploit ec_trace_length; eauto.
        eapply external_call_spec.
    Qed.

  End SYSTEM.

  Definition no_extern_fun (ge: Genv.t fundef unit): Prop :=
    forall b ef, ~ (is_external_ef ef = true /\ Genv.find_funct_ptr ge b = Some (External ef)).

  Section ASMLEMMAS.

    Lemma asm_determinate_at p st
    :
      determinate_at (semantics p) st.
    Proof.
      generalize (semantics_determinate p); intro P. inv P. econs; ii; ss; eauto. eapply sd_final_nostep; eauto.
    Qed.

  End ASMLEMMAS.

  Lemma local_genv_no_extern_fun p :
    forall (IN: In (AsmC.module p) prog),
      no_extern_fun (local_genv p).
  Proof.
    unfold no_extern_fun. ii. unfold local_genv in *. des.
    unfold Genv.find_funct_ptr in *. des_ifs.
    exploit SkEnv.project_revive_no_external; eauto.
    exploit ININCL; eauto.
  Qed.

  Lemma ALLOC_NEXT_INCR F V (gen: Genv.t F V) x m0 m1
        (ALLOC: Genv.alloc_global gen m0 x = Some m1)
    :
      Plt (Mem.nextblock m0) (Mem.nextblock m1).
  Proof.
    destruct x. ss. destruct g; des_ifs.
    - apply Mem.nextblock_alloc in Heq.
      eapply Mem.nextblock_drop in ALLOC.
      rewrite ALLOC. rewrite Heq. apply Plt_succ.
    - apply Mem.nextblock_alloc in Heq.
      apply Genv.store_zeros_nextblock in Heq0.
      apply Genv.store_init_data_list_nextblock in Heq1.
      eapply Mem.nextblock_drop in ALLOC.
      rewrite ALLOC. rewrite Heq1. rewrite Heq0. rewrite Heq.
      apply Plt_succ.
  Qed.

  Lemma ALLOCS_NEXT_INCR F V (gen: Genv.t F V) l m0 m1
        (ALLOC: Genv.alloc_globals gen m0 l = Some m1)
    :
      Ple (Mem.nextblock m0) (Mem.nextblock m1).
  Proof.
    revert l gen m0 m1 ALLOC. induction l; i; ss; clarify.
    - reflexivity.
    - des_ifs. etrans.
      + apply Plt_Ple. eapply ALLOC_NEXT_INCR; eauto.
      + eapply IHl; eauto.
  Qed.

  Lemma init_mem_nextblock F V (p: AST.program F V) m
        (INIT: Genv.init_mem p = Some m)
    :
      Plt 1 (Mem.nextblock m).
  Proof.
    unfold Genv.init_mem in *.
    eapply ALLOCS_NEXT_INCR in INIT.
    ss. apply Pos.le_succ_l. ss.
  Qed.

(** ********************* regset *********************************)

  Definition initial_regset : regset :=
    (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
      # RA <- Vnullptr
      # RSP <- (Vptr 1%positive Ptrofs.zero).

  Definition initial_tgt_regset := initial_regset.

  Lemma update_agree j rs_src rs_tgt pr v
        (AGREE: agree j rs_src rs_tgt)
        (UPDATE: Val.inject j v (rs_tgt # pr))
    :
      agree j (rs_src # pr <- v) rs_tgt.
  Proof.
    destruct pr; intros pr0; specialize (AGREE pr0); destruct pr0; eauto.
    - destruct i, i0; eauto.
    - destruct f, f0; eauto.
    - destruct c, c0; eauto.
  Qed.

  Lemma initial_regset_agree: agree init_inject initial_regset initial_tgt_regset.
  Proof.
    unfold initial_tgt_regset, initial_regset.
    repeat eapply agree_step; ss; eauto.
    - unfold Genv.symbol_address; des_ifs. econs; eauto.
      unfold init_inject, Mem.flat_inj. des_ifs.
      exfalso. eapply Genv.genv_symb_range in Heq.
      unfold tge in *. erewrite Genv.init_mem_genv_next in Heq. eauto.
      apply TGT_INIT_MEM. symmetry. apply Ptrofs.add_zero.
    - econs.
    - econs.
      + unfold init_inject, Mem.flat_inj; des_ifs.
        exfalso. apply n. eapply init_mem_nextblock.
        unfold Sk.load_mem in INIT_MEM. apply INIT_MEM.
      + symmetry. apply Ptrofs.add_zero.
  Qed.

(** ********************* calee initial *********************************)

  Inductive wf_init_rs (j: meminj) (rs_caller rs_callee: regset) : Prop :=
  | wf_init_rs_intro
      (PCSAME: rs_caller # PC = rs_callee # PC)
      (* (RAPTR: wf_RA (rs_callee # RA)) *)
      (RANOTFPTR: forall blk ofs (RAVAL: rs_callee RA = Vptr blk ofs),
          ~ Plt blk (Genv.genv_next skenv_link))
      (RASAME: inj_same j (rs_caller # RA) (rs_callee # RA))
      (RSPSAME: inj_same j (rs_caller # RSP) (rs_callee # RSP))
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              inj_same j (rs_caller (to_preg mr))
                                       (rs_callee (to_preg mr)))
  .

  Lemma preg_case pr :
    (exists mr, pr = to_preg mr) \/
    (pr = PC) \/ (exists c, pr = CR c) \/ (pr = RSP) \/ (pr = RA)
  .
  Proof.
    destruct (to_mreg pr) eqn:EQ.
    - left. exists m. unfold to_mreg in *.
      destruct pr; clarify.
      destruct i; clarify; auto.
      destruct f; clarify; auto.
    - right. unfold to_mreg in *.
      destruct pr; clarify; eauto.
      destruct i; clarify; auto.
      destruct f; clarify; auto.
  Qed.

  Lemma callee_save_agree j rs_caller init_rs rs_callee rs_tgt sg mr rs
        (WF: wf_init_rs j rs_caller init_rs)
        (AGREE: agree j rs_callee rs_tgt)
        (RETV: loc_result sg = One mr)
        (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                                Val.lessdef (init_rs mr.(to_preg)) (rs_callee mr.(to_preg)))
        (RSRA: rs_callee # PC = init_rs # RA)
        (RSRSP: rs_callee # RSP = init_rs # RSP)
        (RS: rs = (set_pair (loc_external_result sg) (rs_callee mr.(to_preg)) (Asm.regset_after_external rs_caller)) #PC <- (rs_caller RA))
    :
        agree j rs rs_tgt.
  Proof.
    inv WF. clarify.
    - unfold loc_external_result. rewrite RETV. ss.
      eapply update_agree; eauto; cycle 1.
      { eapply inj_same_inj; eauto. rewrite <- RSRA. auto. }
      eapply update_agree; eauto.
      unfold Asm.regset_after_external in *. intros pr. specialize (AGREE pr).
      destruct (preg_case pr); des; clarify; ss.
      + rewrite to_preg_to_mreg. des_ifs.
        specialize (CALLEESAVE mr0). specialize (CALLEESAVE0 mr0).
        rewrite Heq in *. eapply inj_same_inj; eauto.
        eapply Mem.val_lessdef_inject_compose; try apply CALLEESAVE; eauto.
      + rewrite RSRSP in *. eapply inj_same_inj; eauto.
  Qed.

(** ********************* match stack *********************************)

  Inductive match_stack (j: meminj) : (Values.block -> Z -> Prop) -> regset -> list Frame.t -> Prop :=
  | match_stack_init
      init_rs P
      (RSRA: init_rs # RA = Vnullptr)
      (RSPC: init_rs # PC = Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
      (SIG: skenv_link.(Genv.find_funct) (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero) = Some (Internal signature_main))
    :
      match_stack j P init_rs nil
  | match_stack_cons
      fr frs p st init_rs0 init_rs1 P0 P1 sg blk ofs
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate init_rs1 st))
      (STACK: match_stack j P0 init_rs1 frs)
      (WF: wf_init_rs j st.(st_rs) init_rs0)
      (GELE: genv_le (local_genv p) tge)
      (PROGIN: In (AsmC.module p) prog)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (init_rs0 # PC)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSPPTR: st.(st_rs) # RSP = Vptr blk ofs)
      (RANGE: P0 \2/ (brange blk (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 4 * size_arguments sg)) <2= P1)
    :
      match_stack j P1 init_rs0 (fr::frs)
  .

  Inductive match_stack_call (j: meminj) : mem -> (Values.block -> Z -> Prop) -> regset -> list Frame.t -> Prop :=
  | match_stack_call_init
      init_rs m P
      (MEM: m = m_init)
      (INITRS: init_rs = initial_regset)
      (SIG: skenv_link.(Genv.find_funct) (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero) = Some (Internal signature_main))
    :
      match_stack_call j m P init_rs nil
  | match_stack_call_cons
      fr frs p st init_rs0 init_rs1 m P0 P1 sg blk ofs
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs1 st))
      (INITRS: init_rs0 = st.(st_rs))
      (STACK: match_stack j P0 init_rs1 frs)
      (MEM: m = st.(st_m))
      (GELE: genv_le (local_genv p) tge)
      (PROGIN: In (AsmC.module p) prog)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (init_rs0 # PC)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSPPTR: init_rs0 # RSP = Vptr blk ofs)
      (RANGE: P0 \2/ (brange blk (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 4 * size_arguments sg)) <2= P1)
    :
      match_stack_call j m P1 init_rs0 (fr::frs)
  .

  Lemma match_stack_incr j1 j2 init_rs l P0 P1
        (INCR: inject_incr j1 j2)
        (PLE: P0 <2= P1)
        (MATCH: match_stack j1 P0 init_rs l)
    :
      match_stack j2 P1 init_rs l.
  Proof.
    revert init_rs INCR P0 P1 PLE MATCH. induction l; ss; ii.
    - inv MATCH; econs; ss; eauto.
    - inv MATCH. econs; ss; auto.
      + eapply IHl; cycle 2; eauto.
      + inv WF. econs; eauto.
        * eapply inj_same_incr; eauto.
        * eapply inj_same_incr; eauto.
        * ii. eapply inj_same_incr; eauto.
      + eauto.
      + eauto.
      + eauto.
  Qed.

  Lemma frame_inj a0 b0 a1 b1
        (EQ: Frame.mk a0 b0 = Frame.mk a1 b1)
    : b0 ~= b1.
  Proof. inv EQ. eauto. Qed.

  Lemma asm_frame_inj se1 se2 p1 p2 st1 st2
        (EQ : Frame.mk (modsem se1 p1) st1 = Frame.mk (modsem se2 p2) st2)
    :
      st1 = st2.
  Proof. apply frame_inj in EQ. apply JMeq_eq. eauto. Qed.

  Lemma asm_frame_inj2 p1 p2 st1 st2
        (EQ : Frame.mk (modsem skenv_link p1) st1
              = Frame.mk (modsem skenv_link p2) st2)
    :
      local_genv p1 = local_genv p2.
  Proof.
    apply f_equal with (f := Frame.ms) in EQ. ss.
    apply f_hequal with (f := ModSem.globalenv) in EQ.
    apply JMeq_eq in EQ. ss.
  Qed.

  Lemma skenv_inject_memory j m m_tgt
        (GEINJECT: skenv_inject skenv_link j m)
        (INJ: Mem.inject j m m_tgt)
    :
      Ple (Genv.genv_next skenv_link) (Mem.nextblock m).
  Proof.
    assert (~ Plt
              (Mem.nextblock m)
              (Genv.genv_next skenv_link)); [|xomega].
    ii. inv GEINJECT. exploit DOMAIN; eauto. i.
    eapply Mem.valid_block_inject_1 in H0; eauto.
    eapply Plt_strict; eauto.
  Qed.

  (** ********************* arguments *********************************)

  Lemma arguments_loc sg sl delta ty
        (IN: In (S sl delta ty) (regs_of_rpairs (loc_arguments sg)))
    :
      sl = Outgoing /\
      0 <= delta /\
      4 * delta + size_chunk (chunk_of_type ty) <= 4 * size_arguments sg.
  Proof.
    generalize (loc_arguments_acceptable_2 _ _ IN). i. ss. des_ifs.
    set (loc_arguments_bounded _ _ _ IN).
    splits; eauto; [omega|].
    unfold typesize in *. des_ifs; ss; lia.
  Qed.

  Lemma tail_In A l0 l1 (a: A)
        (IN: In a l0)
        (TAIL: is_tail l0 l1)
    :
      In a l1.
  Proof.
    induction TAIL; auto.
    econs 2; eauto.
  Qed.

  Lemma regs_of_rpair_In A (l: list (rpair A))
    :
      (forall r (IN: In (One r) l), In r (regs_of_rpairs l))
      /\ (forall r0 r1 (IN: In (Twolong r0 r1) l),
             In r0 (regs_of_rpairs l) /\ In r1 (regs_of_rpairs l)).
  Proof.
    induction l; i; ss; split; i; des; clarify; ss; eauto.
    - eapply in_or_app. eauto.
    - split; eapply in_or_app; right; eapply (IHl0 _ _ IN).
  Qed.

  Program Definition callee_initial_mem' (blk: Values.block) (ofs: ptrofs)
          (m0: mem) (m: mem) (sg: signature) (args: list val): mem :=
    Mem.mkmem
      (PMap.set
         (m.(Mem.nextblock))
         (_FillArgsParallel.fill_args_src_blk
            (m0.(Mem.mem_contents) !! blk)
            ((fst (Mem.alloc m 0 (4 * size_arguments sg))).(Mem.mem_contents) !! (Mem.nextblock m))
            (Ptrofs.unsigned ofs) 0 args (loc_arguments sg)) ((fst (Mem.alloc m 0 (4 * size_arguments sg))).(Mem.mem_contents)))
      ((fst (Mem.alloc m 0 (4 * size_arguments sg))).(Mem.mem_access))
      ((fst (Mem.alloc m 0 (4 * size_arguments sg))).(Mem.nextblock)) _ _ _.
  Next Obligation.
    eapply Mem.access_max; eauto.
  Qed.
  Next Obligation.
    eapply Mem.nextblock_noaccess; eauto.
  Qed.
  Next Obligation.
    rewrite PMap.gsspec. des_ifs.
    - rewrite _FillArgsParallel.fill_args_src_blk_default.
      eapply Mem.contents_default.
    - eapply Mem.contents_default.
  Qed.

  (* TODO it's from LowerBoundExtra *)
  Definition extcall_args_reg (mr: mreg) (sg: signature):
    {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
    {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
  Proof.
    generalize (regs_of_rpairs (loc_arguments sg)). induction l.
    - ss. tauto.
    - ss. inv IHl; [tauto|].
      destruct a.
      + destruct (mreg_eq r mr); [clarify; eauto|].
        right. intros []; clarify.
      + right. intros []; clarify.
  Qed.

  Definition callee_initial_reg' (sg: signature) (args: list val): Mach.regset :=
    fun mr => if extcall_args_reg mr sg
              then _FillArgsParallel.fill_args_src_reg args (loc_arguments sg) mr
              else Vundef.

  Definition callee_initial_inj' (blk: Values.block) (ofs: ptrofs)
             (j: meminj) (m_src: mem): meminj :=
    fun blk' => if (peq blk' (Mem.nextblock m_src))
                then
                  match (j blk) with
                  | Some (blk_tgt, delta) => Some (blk_tgt, delta + Ptrofs.unsigned ofs)
                  | None => None
                  end
                else j blk'.

  Lemma typify_list_lessdef args typs
        (LEN: Datatypes.length args = Datatypes.length typs)
    :
      Val.lessdef_list (typify_list args typs) args.
  Proof.
    revert typs LEN. induction args; ss. ii. destruct typs; inv LEN.
    unfold typify_list, zip, typify. des_ifs; eauto.
  Qed.

  Lemma typify_list_length args typs
        (LEN: Datatypes.length args = Datatypes.length typs)
    :
      Datatypes.length (typify_list args typs) = Datatypes.length typs.
  Proof.
    revert typs LEN. induction args; ss. ii. destruct typs; inv LEN.
    unfold typify_list, zip, typify. ss. f_equal. eauto.
  Qed.

  Lemma asm_extcall_arguments_mach rs m
    :
      Asm.extcall_arguments rs m <2=
      Mach.extcall_arguments (AsmregsC.to_mregset rs) m (rs RSP).
  Proof.
    ii. eapply list_forall2_imply; eauto.
    i. inv H1; econs.
    - inv H2; econs. ss.
    - inv H2; inv H3; econs; ss.
    - inv H2; inv H3; econs; ss.
  Qed.

  Lemma callee_initial_arguments (rs: regset) m0 m1 blk ofs sg args targs
        (ARGS: Asm.extcall_arguments rs m0 sg args)
        (RSRSP: rs RSP = Vptr blk ofs)
        (ARGRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (TYP: typecheck args sg targs)
    :
      Mach.extcall_arguments
        (callee_initial_reg' sg targs)
        (callee_initial_mem' blk ofs m0 m1 sg targs)
        (Vptr (Mem.nextblock m1) Ptrofs.zero)
        sg
        targs.
  Proof.
    inv TYP.
    eapply extcall_arguments_same; cycle 1.
    { instantiate (1:=_FillArgsParallel.fill_args_src_reg _ (loc_arguments sg)).
      unfold callee_initial_reg'. ii. des_ifs. }
    eapply extcall_arg_in_stack_in_reg_extcall_argument; ss; eauto.
    - rewrite PMap.gss.
      exploit _FillArgsParallel.fill_args_src_blk_args; [..|eauto].
      + apply val_inject_list_lessdef. apply typify_list_lessdef. eauto.
      + eapply loc_arguments_norepet.
      + rewrite typify_list_length; eauto. eapply sig_args_length.
      + eapply extcall_arguments_extcall_arg_in_stack; eauto.
        * set (Ptrofs.unsigned_range_2 ofs). lia.
        * erewrite Ptrofs.repr_unsigned. rewrite <- RSRSP.
          eapply asm_extcall_arguments_mach; eauto.
    - exploit _FillArgsParallel.fill_args_src_reg_args; [..|eauto].
      + eapply loc_arguments_norepet.
      + eapply loc_arguments_one.
      + erewrite typify_list_length; eauto.
        eapply sig_args_length.
    - destruct (Mem.alloc m1 0 (4 * size_arguments sg)) eqn:MEQ.
      hexploit Mem_alloc_range_perm; eauto. ii. exploit H; eauto. i.
      unfold Mem.perm, callee_initial_mem' in *. ss. rewrite MEQ. ss.
      eapply Mem.alloc_result in MEQ. clarify.
    -
  Qed.

  Lemma callee_initial_inj_incr blk ofs j m_src
        (NONE: j (Mem.nextblock m_src) = None)
    :
      inject_incr j (callee_initial_inj' blk ofs j m_src).
  Proof.
    ii. unfold callee_initial_inj'. des_ifs; eauto.
  Qed.

  Lemma callee_initial_mem_nextblock m0 m1 blk ofs sg targs
    :
      Mem.nextblock (callee_initial_mem' blk ofs m0 m1 sg targs) =
      Pos.succ (Mem.nextblock m1).
  Proof.
    unfold callee_initial_mem'. ss.
  Qed.

  Lemma callee_initial_mem_perm m0 m1 blk ofs sg targs blk' ofs' p k
    :
      Mem.perm (callee_initial_mem' blk ofs m0 m1 sg targs) blk' ofs' p k
      <->
      if (peq (Mem.nextblock m1) blk')
      then (zle 0 ofs' && zlt ofs' (4 * size_arguments sg))
      else Mem.perm m1 blk' ofs' p k.
  Proof.
    unfold callee_initial_mem', Mem.perm. ss.
    destruct (Mem.alloc m1 0 (4 * size_arguments sg)) eqn:MEQ.
    exploit Mem.alloc_result; eauto. i. clarify.
    split; i.
    - eapply Mem.perm_alloc_inv in H; eauto. unfold proj_sumbool. des_ifs; lia.
    - des_ifs.
      + eapply Mem.perm_cur.
        eapply Mem.perm_implies.
        * try eapply Mem_alloc_range_perm; eauto.
          unfold proj_sumbool in *. des_ifs.
        * econs.
      + eapply Mem.perm_alloc_1; eauto.
  Qed.

  Lemma callee_initial_inject' (rs: regset) m_src0 m_src1 m_tgt j blk ofs sg args targs
        (INJECT: Mem.inject j m_src0 m_tgt)
        (ARGS: Asm.extcall_arguments rs m_src0 sg args)
        (RSRSP: rs RSP = Vptr blk ofs)
        (FREE: freed_from m_src0 m_src1 blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)))
        (ARGRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (TYP: typecheck args sg targs)
        (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | ofs.(Ptrofs.unsigned)))
    :
      Mem.inject
        (callee_initial_inj' blk ofs j m_src1)
        (callee_initial_mem' blk ofs m_src0 m_src1 sg targs)
        m_tgt.
  Proof.
    inv TYP. dup FREE. inv FREE. inv freed_from_unchanged.
    set (ARGRANGE0:= Ptrofs.unsigned_range_2 ofs).
    assert (INCR: inject_incr j (callee_initial_inj' blk ofs j m_src1)).
    { eapply callee_initial_inj_incr; eauto. eapply Mem.mi_freeblocks; eauto.
      rewrite freed_from_nextblock. apply Plt_strict. }
    econs; [econs|..].

    - i. eapply callee_initial_mem_perm in H0. unfold proj_sumbool in *.
      unfold callee_initial_inj' in H. des_ifs.
      + exploit Mem.mi_perm; eauto.
        * apply INJECT.
        * eapply freed_from_perm. instantiate (1:=Ptrofs.unsigned ofs + ofs0). lia.
        * i.
          replace (ofs0 + (z + Ptrofs.unsigned ofs)) with (Ptrofs.unsigned ofs + ofs0 + z); try lia.
          eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
      + eapply Mem.perm_inject; eauto.
        eapply freed_from_perm_greater; eauto.

    - i. unfold callee_initial_inj' in H. des_ifs.
      + unfold Mem.range_perm in H0.
        setoid_rewrite callee_initial_mem_perm in H0. des_ifs.
        assert (RANGE: 0 <= ofs0 /\ ofs0 + size_chunk chunk <= 4 * size_arguments sg).
        { clear - H0. unfold proj_sumbool in *.
          set (size_chunk_pos chunk). split.
          - specialize (H0 ofs0). exploit H0; try lia. des_ifs.
          - specialize (H0 (ofs0 + size_chunk chunk - 1)).
            exploit H0; try lia. des_ifs. i. lia. }
        apply Z.divide_add_r.
        { eapply Mem.mi_align; try apply INJECT; eauto.
          ii. apply Mem.perm_cur. eapply freed_from_perm.
          instantiate (1:=Ptrofs.unsigned ofs) in H. lia.
        }
        { eapply ALIGN. lia. }

      + unfold Mem.range_perm in H0.
        setoid_rewrite callee_initial_mem_perm in H0. des_ifs.
        eapply Mem.mi_align; try apply INJECT; eauto.
        instantiate (2:=ofs0). ii. specialize (H0 _ H1).
        eapply freed_from_perm_greater; eauto.

    - i. unfold callee_initial_inj' in H.
      rewrite callee_initial_mem_perm in H0. des_ifs.
      + exploit _FillArgsParallel.fill_args_src_blk_inject.
        { apply val_inject_list_lessdef. apply typify_list_lessdef. eauto. }
        { rewrite typify_list_length; eauto. eapply sig_args_length. }
        { instantiate (1:=Ptrofs.unsigned ofs).
          instantiate (1:=(Mem.mem_contents m_src0) !! blk).
          eapply extcall_arguments_extcall_arg_in_stack; eauto.
          - lia.
          - rewrite Ptrofs.repr_unsigned. rewrite <- RSRSP.
            eapply asm_extcall_arguments_mach; eauto.
        }
        { i.
          exploit Mem.mi_memval; try apply INJECT; eauto.
          - instantiate (1:=ofs0 + Ptrofs.unsigned ofs).
            eapply Mem.perm_implies; [try eapply freed_from_perm|econs].
            unfold proj_sumbool in *. des_ifs. lia.
          - i.
            replace (callee_initial_inj' blk ofs j m_src0) with
                (compose_meminj (fun b => Some (b, 0)) (callee_initial_inj' blk ofs j m_src0)); cycle 1.
            { extensionality b. unfold compose_meminj. des_ifs. }
            exploit memval_inject_compose.
            + eapply H.
            + instantiate (1:=(ZMap.get (ofs0 + Ptrofs.unsigned ofs + z) (Mem.mem_contents m_tgt) !! b2)).
                instantiate (2:=(callee_initial_inj' blk ofs j m_src1)).
                eapply memval_inject_incr.
                { instantiate (1:=ofs0). rpapply H2. f_equal. lia. }
                { eapply callee_initial_inj_incr; eauto. eapply Mem.mi_freeblocks; eauto.
                  rewrite freed_from_nextblock. apply Plt_strict. }
            + i. unfold callee_initial_mem'. ss. rewrite PMap.gss.
              instantiate (1:=0) in H3. zsimpl. clear - H3.
              rpapply H3.
              * extensionality b. unfold compose_meminj. des_ifs.
              * f_equal. f_equal.
                Local Transparent Mem.alloc. ss. rewrite PMap.gss. auto.
              * f_equal. lia.
        }
      + eapply memval_inject_incr; eauto.
        Local Transparent Mem.alloc.
        unfold callee_initial_mem', Mem.alloc. ss. rewrite PMap.gso; eauto.
        dup H0. eapply freed_from_perm_greater in H0; eauto.
        eapply Mem.mi_memval in H0; try apply INJECT; eauto.
        rewrite PMap.gso; eauto. rewrite unchanged_on_contents; eauto.
        * des_ifs. ii. eapply freed_from_noperm; eauto. apply Mem.perm_cur.
          eapply Mem.perm_implies; eauto. econs.
        * eapply freed_from_perm_greater; eauto.
        Local Opaque Mem.alloc.
    - ii. unfold Mem.valid_block in *. rewrite callee_initial_mem_nextblock in *.
      unfold callee_initial_inj'. des_ifs.
      + exfalso. clear - H. xomega.
      + eapply Mem.mi_freeblocks; eauto.
        unfold Mem.valid_block. rewrite <- freed_from_nextblock. xomega.

    - ii. unfold callee_initial_inj' in H. des_ifs.
      + eapply Mem.mi_mappedblocks; eauto.
      + eapply Mem.mi_mappedblocks; eauto.

    - ii. erewrite callee_initial_mem_perm in *. unfold proj_sumbool in *.
      unfold callee_initial_inj' in H0, H1. des_ifs.
      + destruct (peq b1 blk); clarify.
        { right. ii. eapply freed_from_noperm.
          - instantiate (1:=ofs2 + Ptrofs.unsigned ofs). lia.
          - replace (ofs2 + Ptrofs.unsigned ofs) with ofs1; try lia. eauto. }
        { exploit Mem.mi_no_overlap; try apply INJECT; try exact n1; eauto.
          - eapply freed_from_perm_greater; eauto.
          - instantiate (1:=Ptrofs.unsigned ofs + ofs2).
            apply Mem.perm_cur. eapply Mem.perm_implies.
            + eapply freed_from_perm. lia.
            + econs.
          - i. des; eauto. right. lia. }
      + destruct (peq blk b2); clarify.
        { right. ii. eapply freed_from_noperm.
          - instantiate (1:=ofs1 + Ptrofs.unsigned ofs). lia.
          - replace (ofs1 + Ptrofs.unsigned ofs) with ofs2; try lia. eauto. }
        { exploit Mem.mi_no_overlap; try apply INJECT; try exact n1; eauto.
          - instantiate (1:=Ptrofs.unsigned ofs + ofs1).
            apply Mem.perm_cur. eapply Mem.perm_implies.
            + eapply freed_from_perm. lia.
            + econs.
          - eapply freed_from_perm_greater; eauto.
          - i. des; eauto. right. lia. }
      + exploit Mem.mi_no_overlap; try apply INJECT; try exact H; eauto.
        * eapply freed_from_perm_greater; eauto.
        * eapply freed_from_perm_greater; eauto.

    - ii. unfold callee_initial_inj' in H.
      repeat erewrite callee_initial_mem_perm in *. des_ifs.
      + exploit Mem.mi_representable.
        * eauto.
        * eauto.
        * instantiate (1:=Ptrofs.add ofs ofs0).
          unfold proj_sumbool in *. des; des_ifs_safe.
          { left. apply Mem.perm_cur. eapply Mem.perm_implies.
            - eapply freed_from_perm. rewrite Ptrofs.add_unsigned.
              erewrite Ptrofs.unsigned_repr; lia.
            - econs. }
          { right. apply Mem.perm_cur. eapply Mem.perm_implies.
            - eapply freed_from_perm. rewrite Ptrofs.add_unsigned.
              erewrite Ptrofs.unsigned_repr; lia.
            - econs. }
        * i. split.
          { set (Ptrofs.unsigned_range_2 ofs).  clear - a H. lia. }
          { rewrite Ptrofs.add_unsigned in H.
            erewrite Ptrofs.unsigned_repr in H.
            - clear - H. lia.
            - unfold proj_sumbool in *. des; des_ifs_safe; lia. }
      + eapply Mem.mi_representable; try eapply INJECT; eauto.
        des; eapply freed_from_perm_greater in H0; eauto.

    - ii. unfold callee_initial_inj' in H.
      repeat erewrite callee_initial_mem_perm in *. des_ifs.
      + clear. tauto.
      + exploit Mem.mi_perm_inv; try apply INJECT; eauto.
        i. destruct (peq b1 blk); clarify.
        { destruct (zle (Ptrofs.unsigned ofs) ofs0 && zlt ofs0 (Ptrofs.unsigned ofs + 4 * size_arguments sg))
                   eqn:BOUND; unfold proj_sumbool in *; des_ifs.
          - right. eapply freed_from_noperm; eauto.
          - repeat erewrite <- unchanged_on_perm; eauto; des_ifs; try lia.
            + eapply Mem.valid_block_inject_1; eauto.
            + eapply Mem.valid_block_inject_1; eauto.
          - repeat erewrite <- unchanged_on_perm; eauto; des_ifs; try lia.
            + eapply Mem.valid_block_inject_1; eauto.
            + eapply Mem.valid_block_inject_1; eauto.
          - repeat erewrite <- unchanged_on_perm; eauto; des_ifs; try lia.
            + eapply Mem.valid_block_inject_1; eauto.
            + eapply Mem.valid_block_inject_1; eauto. }
        { repeat erewrite <- unchanged_on_perm; eauto; des_ifs.
          - eapply Mem.valid_block_inject_1; eauto.
          - eapply Mem.valid_block_inject_1; eauto. }
  Qed.

  Lemma callee_initial_rsp_inj_same blk ofs j m
        (VALID: j (Mem.nextblock m) = None)
        (MAPPED: j blk <> None)
    :
      inj_same
        (callee_initial_inj' blk ofs j m)
        (Vptr blk ofs)
        (Vptr (Mem.nextblock m) Ptrofs.zero).
  Proof.
    unfold callee_initial_inj'.
    destruct (j blk) as [[]|] eqn:EQ; clarify.
    econs; eauto.
    - instantiate (1:=z). instantiate (1:=b).
      des_ifs.
    - des_ifs.
    - rewrite Ptrofs.unsigned_zero. lia.
  Qed.

  Require Import JunkBlock.

  Definition pos_nat_add (p: positive) (n: nat) : positive :=
    if Zerob.zerob n
    then p
    else (p + Pos.of_nat n)%positive.

  Fixpoint callee_initial_junk' (rs: regset) (nb: Values.block) (j: meminj) (l: list preg)
    : regset * nat * meminj :=
    match l with
    | [] => (rs, 0%nat, j)
    | hd::tl =>
      match callee_initial_junk' rs nb j tl with
      | (rs', n, j') =>
        match rs' hd with
        | Vptr blk ofs =>
          (Pregmap.set hd (Vptr (pos_nat_add nb n) ofs) rs',
           Datatypes.S n,
           (fun blk' => if peq blk' (pos_nat_add nb n)
                        then (j' blk)
                        else (j' blk')))
        | _ => (rs', n, j')
        end
      end
    end.

  Lemma assign_junk_blocks_contents m n b
        (VALID: Mem.valid_block m b)
    :
      (Mem.mem_contents (assign_junk_blocks m n)) !! b = (Mem.mem_contents m) !! b.
  Proof.
    revert n b m VALID. induction n; ss. i. des_ifs.
    erewrite IHn in *.
    Local Transparent Mem.alloc.
    - unfold Mem.alloc in *. clarify. ss. eapply PMap.gso.
      ii. unfold Mem.valid_block in *. clarify. eapply Plt_strict. eauto.
    - eapply Mem.valid_block_alloc; eauto.
  Qed.

  Lemma callee_initial_junk_spec rs_src rs_tgt rs' m_src m_tgt j j' l n
        (AGREE: agree j rs_src rs_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
        (INITIAL: callee_initial_junk' rs_src m_src.(Mem.nextblock) j l = (rs', n, j'))
    :
      (<<AGREE: agree j' rs' rs_tgt>>) /\
      (<<INJECT: Mem.inject j' (assign_junk_blocks m_src n) m_tgt>>) /\
      (<<SEP: forall b p (NOTMAP: j b = None) (MAP: j' b = Some p),
          ~ Mem.valid_block m_src b>>) /\
      (* (<<SEP: inject_separated j j' (assign_junk_blocks m_src n) m_tgt>>) /\ *)
      (<<INCR: inject_incr j j'>>) /\
      (<<JUNK: forall r (IN: In r l),
          is_junk_value m_src (assign_junk_blocks m_src n) (rs' r)>>) /\
      (<<SAME: forall r, inj_same j' (rs_src r) (rs' r)>>) /\
      (<<EQ: forall r (NIN: ~ In r l), rs_src r = rs' r>>)
  .
  Proof.
    revert l rs' j' n INITIAL. induction l; ss; i; clarify.
    - esplits; eauto.
      + ii. clarify.
      + i. clarify.
    - des_ifs_safe.
      exploit IHl; eauto. i. des.
      assert ((exists blk ofs, r a = Vptr blk ofs) \/ (forall blk ofs, r a <> Vptr blk ofs)).
      { clear. destruct (r a); eauto; try by (right; ii; clarify). }
      des.
      { des_ifs.
        assert (INCR0: inject_incr
                         m
                         (fun blk' =>
                            if peq blk' (pos_nat_add (Mem.nextblock m_src) n0)
                            then m blk else m blk')).
        { ii. des_ifs_safe; eauto. des_ifs_safe. exfalso.
          eapply Mem.valid_block_inject_1 in H; eauto.
          unfold Mem.valid_block in *. clear - H.
          rewrite assign_junk_blocks_nextblock in *. eapply Plt_strict; eauto. }

        esplits; eauto.
        - ii. unfold Pregmap.set. des_ifs.
          + cinv (AGREE0 a); rewrite Heq0 in *; clarify.
            econs; des_ifs.
          + eapply val_inject_incr; eauto.

        - econs; [econs|..]; i; try erewrite assign_junk_blocks_perm in *.
          + des_ifs.
            * exfalso. eapply Mem.perm_valid_block in H0. clear - H0.
              unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * eapply Mem.mi_perm; try apply INJECT0; eauto.
              erewrite assign_junk_blocks_perm in *. auto.
          + des_ifs.
            * unfold Mem.range_perm in *. exfalso. exploit H0; eauto.
              { instantiate (1:=ofs0). set (size_chunk_pos chunk). lia. }
              erewrite assign_junk_blocks_perm. i.
              eapply Mem.perm_valid_block in H1.
              clear - H1. unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * eapply Mem.mi_align; try apply INJECT0; eauto.
              unfold Mem.range_perm in *. try erewrite assign_junk_blocks_perm in *. eauto.
          + des_ifs.
            * exfalso. eapply Mem.perm_valid_block in H0.
              clear - H0. unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * replace (ZMap.get ofs0 (Mem.mem_contents (assign_junk_blocks m_src (Datatypes.S n0))) !! b1) with (ZMap.get ofs0 (Mem.mem_contents (assign_junk_blocks m_src n0)) !! b1).
              { exploit Mem.mi_memval; try apply INJECT0; eauto.
                - try erewrite assign_junk_blocks_perm in *. eauto.
                - i. eapply memval_inject_incr; eauto. }
              { repeat erewrite assign_junk_blocks_contents; auto.
                - eapply Mem.perm_valid_block; eauto.
                - eapply Mem.perm_valid_block; eauto. }
          + des_ifs.
            * unfold pos_nat_add, Mem.valid_block in *. rewrite assign_junk_blocks_nextblock in *.
              exfalso. apply H. clear. ss. des_ifs; try xomega.
            * eapply Mem.mi_freeblocks; try apply INJECT0. ii. apply H.
              unfold Mem.valid_block in *.
              rewrite assign_junk_blocks_nextblock in *.
              clear - H0. eapply Plt_Ple_trans; eauto. unfold Zerob.zerob in *. ss.
              des_ifs; try xomega.
          + des_ifs.
            * eapply Mem.mi_mappedblocks; try apply INJECT0; eauto.
            * eapply Mem.mi_mappedblocks; try apply INJECT0; eauto.
          + ii. try erewrite assign_junk_blocks_perm in *.
            eapply Mem.mi_no_overlap; try apply INJECT0; eauto.
            * clear H1. des_ifs. exfalso.
              eapply Mem.perm_valid_block in H2. clear - H2.
              unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * clear H2. des_ifs. exfalso.
              eapply Mem.perm_valid_block in H3. clear - H3.
              unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * erewrite assign_junk_blocks_perm in *. auto.
            * erewrite assign_junk_blocks_perm in *. auto.
          + des_ifs.
            * exfalso. des.
              { eapply Mem.perm_valid_block in H0. clear - H0.
                unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega. }
              { eapply Mem.perm_valid_block in H0. clear - H0.
                unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega. }
            * eapply Mem.mi_representable; try eapply INJECT0; eauto.
              try erewrite assign_junk_blocks_perm in *. eauto.
          + des_ifs.
            * right. ii. eapply Mem.perm_valid_block in H1. clear - H1.
              unfold pos_nat_add, Mem.valid_block in *. des_ifs; xomega.
            * exploit Mem.mi_perm_inv; try apply INJECT0; eauto. i.
              try erewrite assign_junk_blocks_perm in *. eauto.

        - ii. unfold Mem.valid_block in *. des_ifs.
          + clear - H. unfold pos_nat_add in *. des_ifs; xomega.
          + exploit SEP; eauto.

        - des_ifs. etrans; eauto.

        - ii. des.
          + clarify. rewrite Pregmap.gss. unfold is_junk_value, Mem.valid_block.
            rewrite assign_junk_blocks_nextblock. split.
            * clear. unfold pos_nat_add. des_ifs; xomega.
            * clear. unfold pos_nat_add. ss. des_ifs; xomega.

          + exploit JUNK; eauto. i. unfold is_junk_value, Mem.valid_block in *.
            rewrite assign_junk_blocks_nextblock in *.
            unfold Pregmap.set.
            clear - H Heq0. unfold pos_nat_add. ss. des_ifs; split; try xomega.
            des. destruct n0; clarify; ss; xomega.

        - ii. unfold Pregmap.set. des_ifs.
          + cinv (SAME a).
            * rewrite VAL1 in *; clarify; eauto. econs; eauto. des_ifs.
            * rewrite Heq0 in *. cinv (AGREE0 a); rewrite Heq0 in *; clarify.
              econs; eauto. des_ifs.
          + eapply inj_same_incr; eauto.

        - i. unfold Pregmap.set. des_ifs.
          + exfalso. eauto.
          + eapply EQ; eauto.
      }
      { assert ((r, n0, m) = (rs', n, j')).
        { des_ifs. exfalso. eapply H; eauto. }
        clear INITIAL. clarify.
        esplits; eauto. i. des; clarify; eauto.
        unfold is_junk_value. des_ifs.
        exfalso. eapply H; eauto.
      }
  Qed.

  Definition callee_save_registers : list preg :=
    [RA; IR RBX; IR RBP; IR R12; IR R13; IR R14; IR R15].

  Lemma callee_save_registers_spec r:
    In r callee_save_registers <->
    ((exists mr (MR: to_preg mr = r), is_callee_save mr) \/
     (r = RA)).
  Proof.
    split.
    - i. ss. destruct H; eauto.
      destruct (to_mreg r) eqn:MR.
      + left. exists m. des; clarify; eexists; ss; clarify.
      + des; clarify.
    - unfold is_callee_save. i. des.
      + des_ifs; ss; eauto 10.
      + ss. eauto.
  Qed.

(** ********************* match states *********************************)

  Definition different_owner (v0 v1 : val): Prop :=
    forall mod0 mod1
      (OWNER0: ge.(Ge.find_fptr_owner) v0 mod0)
      (OWNER1: ge.(Ge.find_fptr_owner) v1 mod1),
      mod0 <> mod1.

  Inductive match_states : Sem.state -> Asm.state -> nat -> Prop :=
  | match_states_intro
      j fr frs p init_rs rs_src rs_tgt m_src m_tgt n P
      (AGREE: agree j rs_src rs_tgt)
      (INJ: Mem.inject j m_src m_tgt)
      (MEMWF: Mem.unchanged_on (loc_not_writable m_init) m_init m_src)
      (GELE: genv_le (local_genv p) tge)
      (PROGIN: In (AsmC.module p) prog)
      (GEINJECT: skenv_inject skenv_link j m_src)
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs (Asm.State rs_src m_src)))
      (STACK: match_stack j P init_rs frs)
      (PWF: P <2= ~2 (SimMemInj.valid_blocks m_init /2\ loc_not_writable m_init))
      (WFINJ: inj_range_wf skenv_link j m_src P)
      (ORD: n = if (external_state (local_genv p) (rs_src # PC))
                then (length frs + 2)%nat else 0%nat)
    :
      match_states (State (fr::frs)) (Asm.State rs_tgt m_tgt) n
  | match_states_call
      j init_rs frs args m_src rs_tgt m_tgt ofs blk sg P n
      (STACK: match_stack_call j m_src P init_rs frs)
      (PWF: P <2= ~2 (SimMemInj.valid_blocks m_init /2\ loc_not_writable m_init))
      (AGREE: agree j init_rs rs_tgt)
      (INJECT: Mem.inject j m_src m_tgt)
      (MEMWF: Mem.unchanged_on (loc_not_writable m_init) m_init m_src)
      (GEINJECT: skenv_inject skenv_link j m_src)
      (FPTR: args.(Args.fptr) = init_rs # PC)
      (ARGRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (SIG: exists skd, skenv_link.(Genv.find_funct) args.(Args.fptr)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | ofs.(Ptrofs.unsigned)))
      (ARGS: Asm.extcall_arguments init_rs m_src sg args.(Args.vs))
      (RSPPTR: init_rs # RSP = Vptr blk ofs)
      (WFINJ: inj_range_wf skenv_link j args.(Args.m) P)
      (* (RAPTR: wf_RA (init_rs RA)) *)
      (RAPTR: <<TPTR: Val.has_type (init_rs RA) Tptr>> /\ <<RADEF: init_rs RA <> Vundef>>)
      (FREE: freed_from m_src args.(Args.m) blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)))
      (ORD: n = 1%nat)
    :
      match_states (Callstate args frs) (Asm.State rs_tgt m_tgt) n.

  Lemma init_volatile_readonly blk
        (VOL: Genv.block_is_volatile skenv_link blk)
        ofs
    :
      loc_not_writable m_init blk ofs.
  Proof.
    dup INIT_MEM. unfold Sk.load_mem in INIT_MEM0.
    eapply Genv.init_mem_characterization_gen in INIT_MEM0.
    unfold Genv.block_is_volatile, Genv.globals_initialized, Genv.find_var_info in *.
    des_ifs. exploit INIT_MEM0; eauto. ss. i. des.
    ii. eapply H0 in H3. unfold Genv.perm_globvar in *. des_ifs. des. inv H4.
  Qed.

  Lemma volatile_readonly m blk
        (MEMWF: Mem.unchanged_on (loc_not_writable m_init) m_init m)
        (VOL: Genv.block_is_volatile skenv_link blk)
        ofs
    :
      loc_not_writable m blk ofs.
  Proof.
    dup INIT_MEM. unfold Sk.load_mem in INIT_MEM0.
    dup VOL. eapply init_volatile_readonly in VOL0.
    ii. eapply Mem.perm_unchanged_on_2 in H; eauto.
    eapply Genv.block_is_volatile_below in VOL.
    unfold Mem.valid_block. erewrite <- Genv.init_mem_genv_next; eauto; ss.
  Qed.

  Lemma asm_step_init_simulation
        args frs st_tgt p n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
        (OWNER: valid_owner args.(Args.fptr) p)
        (PROGIN: In (AsmC.module p) prog)
    :
      exists rs m,
        (AsmC.initial_frame skenv_link p args (AsmC.mkstate rs (Asm.State rs m))) /\
        (match_states (State ((Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate rs (Asm.State rs m))) :: frs)) st_tgt 0).
  Proof.

    inv MTCHST. dup OWNER. inv OWNER.
    exploit owner_genv_le; eauto. intros GELE.
    des. ss.
    destruct (Mem.alloc args.(Args.m) 0 (4 * size_arguments (fn_sig fd))) eqn:MEQ.
    exploit Mem.alloc_result; eauto. i. clarify.
    assert (Genv.find_funct skenv_link (Args.fptr args) =
            Some (Internal (fn_sig fd))).
    { dup OWNER0. Local Transparent Genv.find_funct.
      unfold Genv.find_funct, Genv.find_funct_ptr in *.
      exploit sub_match_local_genv; eauto. intros MATCHGE.
      set (sub_mge_defs MATCHGE).
      des_ifs. specialize (e _ _ Heq1). des; clarify.
      inv MATCHDEF. ss.
    }
    clarify. ss.

    assert (TYPCHK: typecheck (Args.vs args) (fn_sig fd) (typify_list (Args.vs args) (sig_args (fn_sig fd)))).
    { econs; eauto. rewrite sig_args_length.
      symmetry. eapply list_forall2_length; eauto. }


    exploit callee_initial_inject'; try eapply FREE; eauto.
    intros INJECT0.

    hexploit callee_initial_inj_incr.
    { instantiate (1:=Args.m args).
      inv FREE. rewrite freed_from_nextblock.
      eapply Mem.mi_freeblocks; try apply INJECT.
      apply Plt_strict. }
    instantiate (1:= ofs). instantiate (1:= blk). intros INCR.

    hexploit callee_initial_arguments; eauto.
    intros ARGS0. instantiate (1:=Args.m args) in ARGS0.

    hexploit callee_initial_rsp_inj_same.
    { instantiate (1:=Args.m args).
      inv FREE. rewrite freed_from_nextblock.
      eapply Mem.mi_freeblocks; try apply INJECT.
      apply Plt_strict. }
    { instantiate (1:=blk). ii. cinv (AGREE RSP); rewrite RSPPTR in *; clarify. }
    instantiate (1:=ofs). intros SAME.

    set (callee_initial_reg :=
           fun pr => match Asm.to_mreg pr with
                     | Some mr =>
                       if (is_callee_save mr)
                       then (init_rs pr)
                       else
                         (callee_initial_reg' (fn_sig fd)
                                              (typify_list (Args.vs args) (sig_args (fn_sig fd))))
                           mr
                     | None =>
                       match pr with
                       | IR RSP => (Vptr (Mem.nextblock m_src) Ptrofs.zero)
                       | PC => init_rs PC
                       | RA => init_rs RA
                       | _ => Vundef
                       end
                     end).

    destruct (callee_initial_junk'
                callee_initial_reg
                (Mem.nextblock (callee_initial_mem' blk ofs m_src (Args.m args)
                                                    (fn_sig fd) (typify_list (Args.vs args) (sig_args (fn_sig fd)))))
                (callee_initial_inj' blk ofs j (Args.m args))
                callee_save_registers) as [[rs_callee n] j_callee] eqn:JUNKED.
    exploit callee_initial_junk_spec; try apply JUNKED; eauto.
    { instantiate (1:=rs_tgt). ii.
      unfold callee_initial_reg. des_ifs; eauto.
      - unfold callee_initial_reg'. des_ifs.
        eapply Mem.val_lessdef_inject_compose.
        + eapply val_inject_id.
          eapply _FillArgsParallel.fill_args_src_reg_agree.
          * eapply val_inject_list_lessdef.
            apply typify_list_lessdef; eauto.
            inv TYPCHK. auto.
          * inv TYPCHK. rewrite typify_list_length; auto. apply sig_args_length.
          * eapply extcall_arguments_extcall_arg_in_reg; eauto.
            { instantiate (1:=Ptrofs.unsigned ofs).
              set (Ptrofs.unsigned_range_2 ofs). lia. }
            { rewrite Ptrofs.repr_unsigned. rewrite <- RSPPTR.
              eapply asm_extcall_arguments_mach; eauto. }
        + eapply val_inject_incr; eauto.
          unfold AsmregsC.to_mregset. erewrite to_mreg_preg_of; eauto.
    - eapply inj_same_inj.
        + symmetry. dup SAME.
          inv FREE. rewrite <- freed_from_nextblock. eassumption.
        + rewrite <- RSPPTR. eauto. }

    i. des.

    exists rs_callee.
    exists (assign_junk_blocks
              (callee_initial_mem' blk ofs m_src (Args.m args)
                                   (fn_sig fd) (typify_list (Args.vs args) (sig_args (fn_sig fd)))) n).

    assert (UNCH: Mem.unchanged_on
                    (fun (b : Values.block) (ofs0 : Z) =>
                       if eq_block b (Mem.nextblock (Args.m args))
                       then ~ 0 <= ofs0 < 4 * size_arguments (fn_sig fd)
                       else True) m
                    (callee_initial_mem' blk ofs m_src (Args.m args) (fn_sig fd)
                                         (typify_list (Args.vs args) (sig_args (fn_sig fd))))).
    {
      econs; ss.
      - erewrite Mem.nextblock_alloc; eauto. refl.
      - i. Local Opaque Mem.alloc. unfold Mem.perm. ss. rewrite MEQ. ss.
      - i. clear - MEQ H0 H1. des_ifs.
        + exfalso. eapply Mem.perm_alloc_3 in H1; eauto.
        + repeat rewrite PMap.gso; eauto.
          symmetry. eapply Mem.unchanged_on_contents; eauto.
          * eapply Mem.alloc_unchanged_on; eauto.
          * instantiate (1:=top2). auto.
          * eapply Mem.perm_alloc_4; eauto. }
    split.

    { econs; eauto.

      - erewrite <- EQ.
        + unfold callee_initial_reg. ss.
        + ss. ii. des; clarify.

      - econs.
        + econs; eauto.
          * eapply extcall_arguments_same; eauto.
            i. hexploit Conventions1C.loc_args_callee_save_disjoint; eauto. i.
            unfold AsmregsC.to_mregset. erewrite <- EQ.
            { unfold callee_initial_reg.
              rewrite to_preg_to_mreg. des_ifs. }
            { ii. eapply callee_save_registers_spec in H1. des.
              - apply f_equal with (f:=to_mreg) in MR.
                repeat rewrite to_preg_to_mreg in *. clarify.
              - apply f_equal with (f:=to_mreg) in H1.
                repeat rewrite to_preg_to_mreg in *. ss. }

          * clear JUNKED.
            assert (LEN: Datatypes.length (Args.vs args) = Datatypes.length (sig_args (fn_sig fd))).
            { rewrite sig_args_length. symmetry.
              eapply list_forall2_length; eauto. }

            hexploit _FillArgsParallel.fill_args_src_blk_only_args.
            { eapply val_inject_list_lessdef.
              eapply typify_list_lessdef; eauto. }
            { eapply loc_arguments_norepet. }
            { erewrite typify_list_length; eauto.
              eapply sig_args_length. }
            { eapply loc_arguments_one. }
            { eapply extcall_arguments_extcall_arg_in_stack.
              - instantiate (1:=Ptrofs.unsigned ofs).
                set (Ptrofs.unsigned_range ofs). lia.
              - erewrite Ptrofs.repr_unsigned. erewrite <- RSPPTR.
                eapply asm_extcall_arguments_mach; eauto. }

            intros ONLY ofs0. specialize (ONLY ofs0).
            Local Transparent Mem.alloc Mem.load.
            unfold callee_initial_mem', Mem.alloc. ss. des.
            { left. repeat rewrite PMap.gss. eauto. }
            { right. esplits; eauto. unfold Mem.load. ss.
              hexploit loc_arguments_bounded; eauto. i.
              hexploit loc_arguments_acceptable; eauto.
              { instantiate (1:=fn_sig fd).
                instantiate (1:=One (S Outgoing ofs1 ty)).
                exploit in_regs_of_rpairs_inv; eauto. i. des.
                rpapply H1.
                eapply loc_arguments_one in H1. unfold is_one in *. des_ifs.
                ss. des; clarify. } i. inv H1.
              rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr; cycle 1.
              { rewrite typesize_chunk in *. lia. } des_ifs.
              - repeat erewrite PMap.gss. auto.
              - exfalso. eapply n0.
                unfold Mem.valid_access, Mem.range_perm, Mem.perm. ss. split.
                + ii. rewrite PMap.gss. rewrite typesize_chunk in *.
                  unfold proj_sumbool; des_ifs; (try by econs); try lia.
                + clear - H3.
                  destruct ty; ss; try by eapply Z.divide_factor_l.
                  eapply Z.mul_divide_mono_l with (p:=4) in H3. eauto. }

          * ss. eapply Mem.nextblock_alloc; eauto.
          * unfold Mem.range_perm. i. erewrite callee_initial_mem_perm. des_ifs.
            unfold proj_sumbool. clear - H0. des_ifs; lia.
        + erewrite <- EQ.
          * unfold callee_initial_reg. ss.
            inv FREE. rewrite freed_from_nextblock. auto.
          * ss. ii. des; clarify.

      - clear - TPTR RADEF SAME0.
        cinv (SAME0 RA).
        + rewrite VAL1. econs; ss.
        + rewrite <- EQ. unfold callee_initial_reg. ss.

      - ii. exploit JUNK.
        + instantiate (1:=RA). ss. eauto.
        + i. unfold is_junk_value in *. rewrite RAVAL in *. apply H1.
          unfold Mem.valid_block. eapply Plt_Ple_trans; eauto.
          erewrite callee_initial_mem_nextblock.
          hexploit skenv_inject_memory; eauto. i.
          inv FREE. rewrite freed_from_nextblock in *. ss. clear - H2. xomega.
      - ii.
        assert (NIN: ~ In pr callee_save_registers); eauto.
        dup NIN. erewrite callee_save_registers_spec in NIN.
        rewrite <- EQ in PTR; auto.
        unfold callee_initial_reg in PTR.
        destruct (to_mreg pr) eqn:MR.
        + des_ifs.
          * exfalso. apply NIN. left. esplits; eauto.
            eapply AsmregsC.to_mreg_some_to_preg; eauto.
          * unfold callee_initial_reg' in PTR. des_ifs; ss.
            left. esplits; eauto.
        + right. des_ifs; ss; eauto. exfalso. eauto.
    }

    { econs.
      - eapply AGREE0.
      - eapply INJECT1.
      - clear JUNKED.
        apply mem_readonly_trans with m_src; eauto.
        apply mem_readonly_trans with (Args.m args).
        { inv FREE. eapply Mem.unchanged_on_implies; eauto.
          ii. ss. des_ifs. ii. eapply H0. eapply Mem.perm_implies.
          - eapply Mem.perm_cur. eapply freed_from_perm. auto.
          - econs. }
        apply mem_readonly_trans with m.
        { eapply Mem.alloc_unchanged_on. eauto. }
        apply mem_readonly_trans with (callee_initial_mem'
                                         blk ofs m_src (Args.m args) (fn_sig fd)
                                         (typify_list (Args.vs args) (sig_args (fn_sig fd)))).
        { inv FREE. eapply Mem.unchanged_on_implies; try eassumption.
          ii. ss. des_ifs. ii. apply H0. eapply Mem.perm_implies.
          - eapply Mem.perm_cur. eapply Mem_alloc_range_perm; eauto.
          - econs. }
        eapply Mem.unchanged_on_implies.
        { eapply assign_junk_blocks_unchanged_on. }
        ss.
      - eauto.
      - eauto.
      - dup GEINJECT. inv GEINJECT. econs.
        + ii. exploit DOMAIN; eauto.
        + ii. des.
          * dup PERM. eapply Senv.block_is_volatile_below in PERM.
            apply DOMAIN in PERM. eapply IMAGE; eauto. instantiate (1:=0).
            rewrite PERM. apply INCR in PERM. apply INCR0 in PERM. clarify.
          * rewrite assign_junk_blocks_perm in PERM.
            rewrite callee_initial_mem_perm in PERM. des_ifs.
            { destruct (callee_initial_inj' blk ofs j (Args.m args) (Mem.nextblock (Args.m args))) as [[]|] eqn:DELTA.
              - dup DELTA. apply INCR0 in DELTA0. clarify.
                unfold callee_initial_inj' in DELTA. des_ifs.
                eapply IMAGE in Heq.
                + rewrite Heq. ss.
                  destruct (Genv.block_is_volatile skenv_link blk) eqn:VEQ0.
                  { exfalso. eapply volatile_readonly in VEQ0; eauto.
                    eapply VEQ0. eapply Mem.perm_cur. eapply Mem.perm_implies.
                    - eapply freed_from_perm; eauto.
                      instantiate (1:=Ptrofs.unsigned ofs + ofs0).
                      unfold proj_sumbool in *. clear JUNKED. des_ifs. lia.
                    - econs. }
                  destruct (Genv.block_is_volatile skenv_link (Mem.nextblock (Args.m args))) eqn: VEQ1; auto.
                  apply Genv.block_is_volatile_below in VEQ1.
                  hexploit skenv_inject_memory; try eassumption. i.
                  inv FREE. rewrite freed_from_nextblock in *. clear - VEQ1 H1. xomega.
                + right. exists (Ptrofs.unsigned ofs + ofs0).
                  eapply Mem.perm_cur. eapply Mem.perm_implies.
                  * inv FREE. eapply freed_from_perm.
                    unfold proj_sumbool in *. des_ifs. clear - l0 l. lia.
                  * econs.

              - hexploit SEP; try eassumption. i.
                unfold Mem.valid_block in *. rewrite callee_initial_mem_nextblock in *.
                clear - H1. xomega.
            }
            { destruct (callee_initial_inj' blk ofs j (Args.m args) b1) as [[]|] eqn:DELTA.
              - unfold callee_initial_inj' in DELTA. des_ifs.
                dup DELTA. eapply INCR in DELTA. eapply INCR0 in DELTA. clarify.
                eapply IMAGE; try eassumption. right. exists ofs0.
                eapply freed_from_perm_greater; eauto.
              - hexploit SEP; try eassumption. i.
                unfold Mem.valid_block in *. rewrite callee_initial_mem_nextblock in *.
                eapply Mem.perm_valid_block in PERM. exfalso. apply H0.
                unfold Mem.valid_block in PERM. clear - PERM. xomega. }

      - ss.

      - instantiate (1:=P).
        inv STACK.
        + econs; eauto.
          * specialize (SAME0 RA). unfold callee_initial_reg in SAME0. ss.
            unfold initial_regset, Pregmap.set in SAME0. des_ifs.
          * erewrite <- EQ. unfold callee_initial_reg. ss.
            clear. ii. ss; des; clarify.
        + econs; eauto.
          * eapply match_stack_incr; try apply STACK0; eauto. etrans; eauto.
          * econs.
            { rewrite <- EQ. unfold callee_initial_reg. ss.
              clear. ii. ss; des; clarify. }
            { ii. exploit JUNK.
              - instantiate (1:=RA). ss. eauto.
              - unfold is_junk_value. rewrite RAVAL. i. apply H1.
                unfold Mem.valid_block. ss.
                hexploit skenv_inject_memory; eauto. i.
                inv FREE. rewrite freed_from_nextblock in *.
                eapply Plt_Ple_trans; eauto. clear - H2. xomega. }
            { etrans; try eapply SAME0.
              unfold callee_initial_reg. ss. refl. }
            { etrans; try eapply SAME0.
              unfold callee_initial_reg. ss. rewrite RSPPTR0.
              rewrite RSPPTR in *. clarify.
              inv FREE. rewrite <- freed_from_nextblock.
              eapply inj_same_incr; eauto. }
            { ii. etrans; try apply SAME0.
              unfold callee_initial_reg. rewrite to_preg_to_mreg.
              des_ifs_safe. refl. }
          * replace (rs_callee PC) with (st_rs st PC); eauto.
            erewrite <- EQ; ss.
            clear. ii. des; clarify.

      - auto.

      - ii. cinv (WFINJ blk0).
        + destruct (j_callee blk0) as [[]|]eqn:BLK.
          * econs 2; eauto.
            { ii. eapply Mem.mi_align; try apply INJECT1; eauto.
              ii. eapply H0 in H1. des; clarify.
              - eapply Mem.perm_max. eauto.
              - exfalso. eapply BOT; eauto. }
            { ii. eapply Mem.mi_representable; try apply INJECT1; eauto.
              exfalso. des; eapply BOT; eauto. }
            { ii. exfalso. eapply BOT. eauto. }

          * econs 1; eauto.

        + econs 2; eauto. i. eapply ALIGN0.
          ii. apply H0 in PR. des; eauto. left.
          rewrite assign_junk_blocks_perm in PR.
          rewrite callee_initial_mem_perm in PR. des_ifs; eauto.
          exfalso. eapply Mem.valid_block_inject_1 in DELTA; eauto.
          inv FREE. rewrite freed_from_nextblock in *. eapply Plt_strict; eauto.

      - des_ifs. exfalso. unfold external_state in *.
        erewrite <- EQ in Heq.
        + unfold callee_initial_reg in *. ss. rewrite <- FPTR in *.
          unfold Genv.find_funct in FINDF. clear - Heq FINDF. des_ifs.
        + clear. ii. ss. des; clarify.
    }

  Qed.


(** ********************* transf initial final  *********************************)

  Lemma transf_initial_states:
    forall st1, Sem.initial_state prog st1 ->
                exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2 1.
  Proof.
    generalize TGT_INIT_MEM.
    generalize initial_regset_agree.
    generalize initmem_inject.
    intros initmem_inject initial_regset_agree TGT_INT_MEM.
    intros st1 INIT. inv INIT. move INITSK at top. clarify. esplits.
    - econs; eauto.
    - symmetry in H0. subst. econs; ss; try eassumption.
      + econs; ss; eauto.
        unfold Genv.symbol_address in *. erewrite <- symb_main. unfold skenv_link in *. des_ifs.
      + instantiate (1:=bot2). ss.
      + refl.
      + eapply init_inject_ge.
      + unfold initial_regset.
        rewrite Pregmap.gso; clarify.
        rewrite Pregmap.gso; clarify. ss.
        rewrite Pregmap.gss. unfold tge.
        set (MAIN:= symb_main).
        unfold Genv.symbol_address. unfold skenv_link, tge in *. rewrite MAIN. auto.
      + instantiate (1:=signature_main). ss.
      + eauto.
      + rewrite Ptrofs.unsigned_zero. i. eapply Z.divide_0_r.
      + econs.
      + inv initmem_inject. inv mi_inj.
        ii. destruct (init_inject blk) eqn:EQ.
        { destruct p. econs 2; i; eauto.
          - eapply mi_align; eauto. ii.
            specialize (H _ H0). ss. destruct H.
            + eapply Mem.perm_max.
              clarify. eauto.
            + destruct H.
          - eapply mi_representable; eauto. des; contradiction.
          - clarify. }
        { econs 1; eauto. }
      + clarify. apply init_mem_freed_from.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r n,
      match_states st1 st2 n -> Sem.final_state st1 r -> Asm.final_state st2 r.
  Proof.
    intros st_src st_tgt r n MTCHST FINAL. inv FINAL. inv MTCHST. ss.
    inv FINAL0. clarify. inv STACK. econs.
    - specialize (AGREE PC). rewrite RSRA in *. rewrite RSRA0 in *.
      inv AGREE; ss.
    - des. rewrite RSPC in *. exploit local_global_consistent; eauto.
      intro SGEQ. rewrite <- SGEQ in *. clarify.
      ss. unfold signature_main, loc_arguments, loc_result in *.
      Transparent Archi.ptr64. ss. unfold loc_result_64 in *. ss. clarify.
      ss. specialize (AGREE RAX). rewrite INT in *. inv AGREE; auto.
  Qed.

(** ********************* transf step  *********************************)

  Lemma inj_range_wf_step j0 j1 m0 m1 P
        (MEMPERM: forall blk ofs p, Mem.perm m1 blk ofs Max p -> Mem.perm m0 blk ofs Max p \/ j0 blk = None)
        (INCR: inject_incr j0 j1)
        (RANGEWF: inj_range_wf skenv_link j0 m0 P)
        (INJ: exists m_tgt, Mem.inject j1 m1 m_tgt)
    :
      inj_range_wf skenv_link j1 m1 P.
  Proof.
    ii. des. inv INJ. inv mi_inj.
    destruct (RANGEWF blk).
    - destruct (j1 blk) eqn:EQ.
      + destruct p. econs 2; eauto; ii.
        * eapply mi_align; eauto. ii.
          specialize (H _ H0). ss. des.
          -- eapply Mem.perm_max; eauto.
          -- exfalso. eapply BOT. eauto.
        * des; exfalso; eapply BOT; eauto.
        * exfalso. eapply BOT. eauto.
      + econs 1; eauto.
    - econs 2; eauto. ii.
      eapply ALIGN. ii. specialize (H x0 PR). ss. des; eauto.
      eapply Mem.perm_max in H. eapply MEMPERM in H. des; clarify. eauto.
  Qed.

  Lemma asm_step_internal_simulation
        st_src0 st_src1 st_tgt0 tr frs p init_rs n0
        (STEP: Asm.step skenv_link (local_genv p) st_src0 tr st_src1)
        (PROGIN: In (AsmC.module p) prog)
        (MTCHST: match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                                (AsmC.mkstate init_rs st_src0))::frs))
                              st_tgt0 n0)
    :
      exists st_tgt1 n1,
        Asm.step skenv_link tge st_tgt0 tr st_tgt1 /\
        match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                       (AsmC.mkstate init_rs st_src1))::frs))
                     st_tgt1 n1.
  Proof.
    inv MTCHST. dup FRAME. dup FRAME.
    apply asm_frame_inj in FRAME0.
    apply asm_frame_inj2 in FRAME. inv FRAME0. destruct st_src1.
    eapply owner_genv_le in PROGIN.
    rewrite FRAME in *.

    exploit asm_step_preserve_injection; eauto.

    { clear FRAME1 FRAME. inv GELE. inv GEINJECT. econs.
      - i. exploit sub_mge_defs0; eauto. i. des.
        inv WFSKELINK.
        exploit DOMAIN.
        + erewrite <- Genv.mge_next; try apply match_skenv_link_tge.
          instantiate (1:= b_src).
          exploit Genv.genv_defs_range; eauto.
        + i. clarify. esplits; eauto.
      - i. exploit sub_mge_symb0; eauto. i. esplits; eauto.
        exploit DOMAIN; eauto.
        erewrite <- Genv.mge_next; try apply match_skenv_link_tge.
        exploit Genv.genv_symb_range; eauto. }

    { eapply system_symbols_inject; eauto. }

    - ii. des. rewrite <- senv_same in *. esplits; eauto. econs; eauto.
      + eapply mem_readonly_trans; eauto.
        eapply asm_step_readonly; eauto.
      + {
          inv GEINJECT. econs.
          - i. unfold inject_incr in *.
            eapply INCR. eapply DOMAIN. eauto.
          - i. ss.
            destruct (Genv.block_is_volatile skenv_link b2) eqn:EQ1;
            destruct (Genv.block_is_volatile skenv_link b1) eqn:EQ2;
            auto; rewrite <- EQ1; rewrite <- EQ2; eapply IMAGE.

            + destruct PERM as [n|[ofs PERM]].
              { inv n. }
              set (Genv.block_is_volatile_below _ _ EQ1).
              destruct (j b1) eqn : EQ.
              * destruct p2. apply INCR in EQ. clarify.
              * exfalso. eapply SEP in EQ. specialize (EQ INJ1). des.
                inv INJ. unfold Mem.valid_block in *. eauto.
            + clear FRAME1. des; auto.
              destruct (j b1) as[[]|] eqn:BEQ.
              * right. exists ofs. eapply asm_step_max_perm; eauto.
                eapply Mem.valid_block_inject_1. apply BEQ. eauto.
              * exfalso. exploit SEP; eauto.
                i. des. eapply Genv.block_is_volatile_below in EQ1.
                apply H0. eapply Mem.valid_block_inject_2; cycle 1; eauto.
            + eapply Genv.block_is_volatile_below in EQ2.
              set (DOMAIN _ EQ2).
              set (INCR _ _ _ e). clarify. auto.
            + clear FRAME1. des; auto.
        }
      + instantiate (1:=init_rs0).
        assert (JEQ: @JMeq
                       (ModSem.state (modsem skenv_link p))
                       {| init_rs := init_rs0; st := Asm.State r m |}
                       (ModSem.state (modsem skenv_link p0))
                       {| init_rs := init_rs0; st := Asm.State r m |}).
        { econs. }
        revert JEQ.
        generalize ({| init_rs := init_rs0; st := Asm.State r m |} : ModSem.state (modsem skenv_link p0)) at 2 4.
        generalize ({| init_rs := init_rs0; st := Asm.State r m |} : ModSem.state (modsem skenv_link p)).
        apply f_equal with (f:=Frame.ms) in FRAME1. simpl in FRAME1.
        clear - FRAME1. destruct FRAME1.
        ii. f_equal. apply JMeq_eq. eauto.
      + eapply match_stack_incr; eauto.
      + eapply inj_range_wf_step; cycle 2; eauto.
        i. destruct (j blk) eqn: EQ; eauto. destruct p2. left.
        eapply asm_step_max_perm in STEP; eauto.
        eapply Mem.valid_block_inject_1; eauto.
  Qed.

  Lemma step_internal_simulation
        fr0 frs tr st0 st_tgt0 n0
        (STEP: fr0.(Frame.ms).(ModSem.step) skenv_link fr0.(Frame.ms).(ModSem.globalenv) fr0.(Frame.st) tr st0)
        (MTCHST: match_states (State (fr0 :: frs)) st_tgt0 n0)
    :
      exists st_tgt1 n1,
        Asm.step skenv_link tge st_tgt0 tr st_tgt1 /\
        match_states (State ((fr0.(Frame.update_st) st0) :: frs)) st_tgt1 n1.
  Proof.
    inv MTCHST. inv STEP.
    exploit asm_step_internal_simulation; ss; eauto.
    - econs; eauto.
    - ii. des. esplits; ss; eauto.
      destruct st0; ss; clarify. eassumption.
  Qed.

  Lemma Mem_unchanged_on_strengthen P m0 m1
    :
      Mem.unchanged_on P m0 m1 <-> Mem.unchanged_on (SimMemInj.valid_blocks m0 /2\ P) m0 m1.
  Proof.
    split; i.
    - eapply Mem.unchanged_on_implies; eauto. i. des. auto.
    - eapply Mem.unchanged_on_implies; eauto. ss.
  Qed.

  Lemma step_return_simulation
        fr0 fr1 frs retv st0 st_tgt n0
        (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
        (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) retv st0)
        (MTCHST: match_states (State (fr0 :: fr1 :: frs)) st_tgt n0)
    :
      exists n1, match_states (State ((fr1.(Frame.update_st) st0) :: frs)) st_tgt n1
                 /\ (n1 < n0)%nat.
  Proof.
    inv MTCHST. inv STACK. ss. inv FINAL. inv AFTER. set WF as WF2. inv WF2. ss.
    rewrite PCSAME in *. des. rewrite RSPPTR in *. clarify.
    assert (SG: fn_sig fd = SkEnv.get_sig skd0).
    { exploit local_global_consistent; try apply GELE; eauto. }
    exploit unfree_free_inj_inj_wf; ss; try apply INJ.
    { rewrite Ptrofs.unsigned_zero. rewrite Z.add_0_l. eauto. }
    { rewrite SG. eauto. }
    { eauto. }
    { rewrite INITRSP in *. auto. }
    { rewrite INITRSP in *. ii. cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      inv RSPSAME; clarify. }
    { ii. eapply RANGE. right. rewrite <- SG. eauto. }
    i. des.
    esplits; eauto.
    - econs; unfold Frame.update_st; simpl; cycle 5; eauto.
      + eapply inj_range_wf_le; eauto.
      + eapply callee_save_agree; eauto. repeat f_equal. eauto.
      + rewrite Mem_unchanged_on_strengthen. transitivity m1.
        * rewrite <- Mem_unchanged_on_strengthen.
          eapply mem_readonly_trans; eauto. eapply mem_free_readonly; eauto.
        * eapply Mem.unchanged_on_implies; try eapply Mem_unfree_unchanged_on; eauto.
          ii. eapply PWF; eauto.
    - des_ifs; lia.
  Qed.

  Lemma step_call_simulation
        fr0 frs args st_tgt n
        (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) args)
        (MTCHST: match_states (State (fr0 :: frs)) st_tgt n)
    :
      match_states (Callstate args (fr0 :: frs)) st_tgt 1%nat.
  Proof.

    inv MTCHST. ss. inv AT.
    econstructor 2 with (P := (P \2/ brange blk1 (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 4 * size_arguments sg))); ss; eauto.
    - econs; ss; eauto. rewrite FPTR. eauto.
    - intros blk ofs0. i. des; eauto. ii.
      unfold brange in *. des. clarify. eapply H0.
      eapply Mem.perm_unchanged_on_2; eauto. eapply Mem.perm_cur.
      eapply Mem.perm_implies.
      + eapply Mem.free_range_perm; eauto.
      + econs.
    - ii. destruct (eq_block blk1 blk); clarify.
      + destruct (j blk) eqn:EQ.
        * destruct p0. destruct (WFINJ blk); clarify.
          econs 2; eauto; ii.
          -- eapply ALIGN0. ii.
             instantiate (1:= Nonempty). instantiate (1:=Max).
             eapply H in PR. des; eauto.
             ++ left. eapply Mem.perm_free_3 in PR; eauto.
                eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
             ++ left. eapply Mem.free_range_perm in FREE.
                exploit FREE. instantiate (1:=x0).
                ** eapply PR.
                ** i. eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
          -- inv INJ; des; eauto.
             ++ eapply mi_representable; eauto. left.
                eapply Mem.free_range_perm in FREE. exploit FREE.
                ** eapply H.
                ** i. eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
             ++ eapply mi_representable; eauto. right.
                eapply Mem.free_range_perm in FREE. exploit FREE.
                ** eapply H.
                ** i. eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
          -- des.
             ++ eapply VOLATILE; eauto.
             ++ inv GEINJECT. eapply IMAGE; try eassumption.
                right. exists ofs0. apply Mem.perm_cur.
                eapply Mem.perm_implies.
                ** eapply Mem.free_range_perm; eauto. destruct IN. auto.
                ** econs.
        * exfalso. specialize (AGREE (IR Asm.RSP)). rewrite RSP in AGREE. inv AGREE. clarify.
      + destruct (j blk) eqn:EQ.
        * destruct p0. destruct (WFINJ blk); clarify.
          econs 2; eauto; ii.
          { eapply ALIGN0. ii. eapply H in PR. unfold brange in *. des; eauto; clarify.
            left. eapply Mem.perm_free_3; eauto. }
          { unfold brange in *. des; eauto; clarify. }
          { des.
            - eapply VOLATILE; eauto.
            - destruct IN. clarify. }
        * econs 1; eauto. destruct (WFINJ blk); clarify.
          ii. des; eauto. clarify. unfold brange in *. des. clarify.
    - eapply free_freed_from; eauto.
  Qed.

  Lemma below_block_is_volatile F V (ge': Genv.t F V) b
        (LE: ~ Plt b (Genv.genv_next ge'))
    :
      Genv.block_is_volatile ge' b = false.
  Proof.
    destruct (Genv.block_is_volatile ge' b) eqn: EQ; auto.
    apply Genv.block_is_volatile_below in EQ.
    exfalso. auto.
  Qed.

  Lemma step_init_simulation
        args frs st_tgt p n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
        (OWNER: valid_owner args.(Args.fptr) p)
        (PROGIN: In (AsmC.module p) prog)
    :
      exists st_src,
        step ge (Callstate args frs) E0 st_src /\ match_states st_src st_tgt 0.
  Proof.
    exploit asm_step_init_simulation; eauto. inv OWNER.
    i. des. esplits; try eassumption.
    econs; eauto.
  Qed.

  Lemma at_external_external p st frs st_tgt n args
        (MTCHST: match_states
                   (State
                      ((Frame.mk (AsmC.modsem skenv_link p) st)::frs))
                   st_tgt n)
        (ATEXTERNAL: at_external skenv_link p st args)
    :
      (1 < n)%nat.
  Proof.
    inv MTCHST.
    replace (at_external skenv_link p) with (at_external skenv_link p0) in *.
    - inv ATEXTERNAL. apply asm_frame_inj in FRAME. clarify.
      unfold external_state. des_ifs. omega.
      unfold local_genv, fundef in *. clarify.
    - apply f_equal with (f := Frame.ms) in FRAME. ss.
      inv FRAME. apply Eqdep.EqdepTheory.inj_pair2 in H0. auto.
  Qed.

  Lemma normal_state_fsim_step frs st_src1 st_tgt0 t n0
        (MTCHST: match_states (State frs) st_tgt0 n0)
        (STEP: step ge (State frs) t st_src1)
    :
      (exists st_tgt1 n1,
          Asm.step skenv_link tge st_tgt0 t st_tgt1 /\ match_states st_src1 st_tgt1 n1) \/
      (exists n1,
          match_states st_src1 st_tgt0 n1 /\ n1 < n0)%nat /\ (t = E0).
  Proof.
    inv STEP.
    - right. exploit step_call_simulation; eauto.
      i. esplits; eauto.
      inv MTCHST; ss.
      exploit at_external_external; eauto.
      econs; try eassumption; ss.
    - left. exploit step_internal_simulation; eauto.
      inv MTCHST. ss.
    - right. exploit step_return_simulation; eauto.
  Qed.

  Lemma owner_asm_or_system fptr ms
        (OWNER: Ge.find_fptr_owner ge fptr ms)
    :
      (<<ASMMOD: exists p, ms = AsmC.modsem skenv_link p /\ In (AsmC.module p) prog>>)\/
      (<<SYSMOD: ms = System.modsem skenv_link>>).
  Proof.
    inv OWNER. clear - MODSEM. unfold ge in *.
    unfold load_genv, load_modsems, prog, flip in *.
    ss. des; auto.
    left. generalize progs ms MODSEM.
    intros l. induction l; ss; i. des; eauto.
    rewrite in_map_iff in *. des. clarify.
    rewrite in_map_iff in *. des. clarify.
    exists x1.
    esplits; eauto. right. apply in_map_iff. esplits; et.
  Qed.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner ge fptr ms0)
        (FIND1: Ge.find_fptr_owner ge fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    eapply SemProps.find_fptr_owner_determ; et; ss;
      rewrite LINK_SK; eauto.
  Qed.

  Lemma init_case st args frs fptr
        (STATE: st = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
    :
      (<<ASMMOD: exists p, valid_owner fptr p>>) \/
      (<<SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link)>>) \/
      (<<UNSAFE: ~ safe (sem prog) st>>).
  Proof.
    destruct (classic (exists p, Ge.find_fptr_owner ge args.(Args.fptr) (modsem skenv_link p)
                                 /\ In (AsmC.module p) prog)) as [[p OWNER] | NOOWNER].
    - des. simpl_depind.
      destruct (classic (valid_owner args.(Args.fptr) p)); eauto.
      right. right. intros SAFE. exploit SAFE; [econs|].
      i. des.
      + inv H0.
      + inv H0. apply H.
        revert MSFIND st_init INIT. intros MSFIND.
        ss. rewrite LINK_SK in *.
        rewrite <- (find_fptr_owner_determ OWNER MSFIND) in *. i.
        inv INIT. econs; eauto.
        inv TYP. eauto.
    - destruct (classic (Ge.find_fptr_owner ge fptr (System.modsem skenv_link))).
      { right. left. esplits; eauto. }
      right. right. intros SAFE. clarify. exploit SAFE; [econs|].
      i. des.
      { inv H0. }
      inv H0. ss. rewrite LINK_SK in *.
      destruct (owner_asm_or_system MSFIND); des; clarify.
      eapply NOOWNER. esplits; et.
  Qed.

  Lemma call_step_noevent ge' args frs st1 tr
        (STEP: step ge' (Callstate args frs) tr st1)
    :
      E0 = tr.
  Proof. inv STEP. auto. Qed.

  Lemma syscall_receptive
        st_src0 st_src1 st_tgt0 args frs fptr tr0 n0
        (STATE: st_src0 = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
        (SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link))
        (MTCHST: match_states st_src0 st_tgt0 n0)
        (STEP0: Sem.step ge st_src0 tr0 st_src1)
    :
      receptive_at (sem prog) st_src1.
  Proof.
    clarify. inv STEP0.
    destruct (find_fptr_owner_determ SYSMOD MSFIND).
    eapply system_receptive_at.
  Qed.

  Lemma syscall_simulation
        st_src0 st_src1 st_src2 st_tgt0 args frs fptr tr0 tr1 n0
        (STATE: st_src0 = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
        (SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link))
        (MTCHST: match_states st_src0 st_tgt0 n0)
        (STEP0: Sem.step ge st_src0 tr0 st_src1)
        (STEP1: Sem.step ge st_src1 tr1 st_src2)
    :
      receptive_at (sem prog) st_src2 /\
      exists st_tgt1 n1,
        (<< STEPTGT: Asm.step skenv_link tge st_tgt0 tr1 st_tgt1 >>) /\
        (<< MTCHST: forall st_src3 tr2
                           (STEP2: Sem.step ge st_src2 tr2 st_src3),
            match_states st_src3 st_tgt1 n1 /\ tr2 = E0>>) /\
        (n1 < length frs + 3)%nat.
  Proof.
    clarify; inv MTCHST. inv STEP0; ss.
    destruct (find_fptr_owner_determ SYSMOD MSFIND). ss. inv INIT.
    inv STEP1; ss; [|inv FINAL]. inv STEP.
    exploit extcall_arguments_inject; eauto.
    i. des.
    exploit ec_mem_inject_weak; eauto.
    - apply external_call_spec.
    - eapply system_symbols_inject; eauto. eapply skenv_inject_max_perm; eauto.
      i. eapply freed_from_perm_greater; eauto.
    - eapply freed_from_inject; eauto.
    - i. des.
      unfold Frame.update_st. ss.
      split.
      { eapply system_receptive_at. }
      exists (Asm.State
                ((set_pair (loc_external_result (ef_sig ef)) vres'
                           (regset_after_external rs_tgt)) #PC <- (rs_tgt RA))
                m2').
      inv STACK.
      { exfalso. clarify.
        rewrite FPTR in *.
        unfold System.globalenv, initial_regset in *. unfold Pregmap.set in *. ss. clarify.
      }
      assert (SIGEQ: SkEnv.get_sig skd = ef_sig ef).
      { eapply external_function_sig; eauto. }
      exists (
        if
          external_state (local_genv p)
                         ((set_pair (loc_external_result (ef_sig ef)) (Retv.v retv)
                                    (regset_after_external st.(st_rs))) # PC <- (st.(st_rs) RA) PC)
        then (length frs0 + 2)%nat
        else 0%nat).
      splits.
      + set (AGREEPC:= AGREE PC). rewrite <- FPTR in *.
        destruct (Args.fptr args) eqn:EQ; ss; des_ifs; clarify. inv AGREEPC.
        econs 3.
        * instantiate (1 := b2).
          assert (delta = 0); clarify.
          eapply system_function_ofs; eauto.
        * instantiate (1 := ef).
          eapply system_sig; eauto.
        * instantiate (1 := args2).
          rewrite <- SIGEQ. auto.
        * eapply H.
        * auto.
      + i. inv STEP2; [inv AT|inv STEP|]. inv FINAL. split; auto.
        ss. unfold Frame.update_st. ss. inv AFTER. ss. clarify.
        assert (SGEQ: sg = ef_sig ef).
        { des. rewrite FPTR in *. clarify. } clarify.
        set (AGREE RSP). rewrite RSPPTR in *. clarify. inv i.
        exploit private_unfree_inj_inj_wf; [eauto|eauto|..].
        { instantiate (2:=Ptrofs.unsigned ofs0).
          instantiate (1:=Ptrofs.unsigned ofs0+4 * size_arguments (ef_sig ef)).
          ii. exploit Mem.unchanged_on_perm; eauto.
          - eapply freed_from_out_of_reach; eauto.
            rewrite SIGEQ. eauto.
            instantiate (1:= ofs). lia.
          - eapply Mem.mi_mappedblocks; eauto.
          - intros PERM. eapply PERM.
            exploit Mem.perm_inject; eauto.
            eapply freed_from_perm; eauto. instantiate (1:=ofs-delta).
            rewrite SIGEQ. omega.
            i. replace ofs with (ofs - delta + delta); [auto|omega]. }
        { intros delta' BOUND. eapply separated_out_of_reach; cycle 2; eauto.
          - eapply Mem.mi_mappedblocks; eauto.
          - eapply freed_from_out_of_reach; eauto.
            rewrite SIGEQ. unfold range in *. lia.
          - i. eapply ec_max_perm; eauto. eapply external_call_spec.
          - eapply freed_from_inject; eauto. }
        { eauto. }
        { inv GEINJECT. econs; [eauto|].
          i. destruct (j b1) as [[]|] eqn:DELTA.
          + dup DELTA. apply H4 in DELTA. clarify.
            exploit IMAGE; [eauto| |auto]. des; auto.
            right. exists ofs. eapply freed_from_perm_greater; eauto.
            eapply external_call_max_perm; eauto. unfold Mem.valid_block.
            inv FREE. rewrite freed_from_nextblock.
            eapply Mem.valid_block_inject_1; eauto.
          + des.
            * eapply Senv.block_is_volatile_below in PERM.
              eapply DOMAIN in PERM. clear - PERM DELTA. clarify.
            * destruct (Senv.block_is_volatile skenv_link b0) eqn:VEQ0.
              { eapply Senv.block_is_volatile_below in VEQ0.
                exploit H5; try eassumption. i. des. exfalso. apply H7.
                eapply DOMAIN in VEQ0. eapply Mem.valid_block_inject_2; eauto. }
              destruct (Senv.block_is_volatile skenv_link b1) eqn:VEQ1; auto.
              { eapply Senv.block_is_volatile_below in VEQ1.
                eapply DOMAIN in VEQ1. clarify. }
        }
        { eapply inj_range_wf_step; try apply WFINJ; eauto.
          i. destruct (classic (Mem.valid_block (Args.m args) blk)).
          - eapply external_call_max_perm in EXTCALL; eauto.
          - right. eapply Mem.mi_freeblocks; eauto.
            unfold Mem.valid_block in *. inv FREE.
            rewrite <- freed_from_nextblock. ss. }
        { ii. eapply RANGE. right. split; eauto.
          unfold range in *. des. rewrite FPTR in *. clarify. rewrite SIGEQ. lia. }
        i. des.
        econs; cycle 4.
        * eauto.
        * eauto.
        * ss.
        * instantiate (1:=P). eapply match_stack_incr; [| |eauto]; eauto.
        * tauto.
        * ss.
        * ss.
        * unfold set_pair. des_ifs; repeat (eapply agree_step; eauto).
          -- unfold regset_after_external.
             intros []; des_ifs; try econs; eauto.
          -- unfold regset_after_external.
             intros []; des_ifs; try econs; eauto.
          -- eapply Val.hiword_inject; eauto.
          -- eapply Val.loword_inject; eauto.
        * tauto.
        * rewrite Mem_unchanged_on_strengthen. transitivity (Retv.m retv0).
          { rewrite <- Mem_unchanged_on_strengthen.
            eapply mem_readonly_trans; eauto.
            apply mem_readonly_trans with (Args.m args); eauto.
            - eapply Mem.unchanged_on_implies.
              + eapply freed_from_unchanged; eauto.
              + ii. ss. des_ifs. ii. eapply H6. eapply Mem.perm_implies.
                * eapply Mem.perm_cur. eapply freed_from_perm; eauto.
                * econs.
            - eapply external_call_readonly; eauto. }
          { eapply Mem.unchanged_on_implies; try eapply Mem_unfree_unchanged_on; eauto.
            ii. eapply PWF; eauto. eapply RANGE. right.
            rewrite FPTR in *. clarify. rewrite SIGEQ in *. eauto. }
        * ss.
      + ss. des_ifs; omega.
  Qed.

  Lemma match_states_call_ord_1 args frs st_tgt n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
    :
      1%nat = n.
  Proof. inv MTCHST. auto. Qed.

  Lemma src_receptive_at st_src st_tgt n
        (MTCHST: match_states st_src st_tgt n)
    :
      receptive_at (sem prog) st_src.
  Proof.
    inv MTCHST; ss.
    - eapply SemProps.lift_receptive_at.
      { ss. des_ifs. }
      ss.
      eapply modsem_receptive.
    - econs; i.
      + set (STEP := H). inv STEP. inv H0. eexists. eauto.
      + ii. inv H. ss. omega.
  Qed.

  Lemma match_state_xsim
    :
      forall st_src st_tgt n (MTCHST: match_states st_src st_tgt n),
        xsim (sem prog) (semantics tprog) lt n st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold. destruct st_src.
    - exploit init_case; ss.
      instantiate (1:=frs). instantiate (2:=args). i. des.
      + destruct (match_states_call_ord_1 MTCHST).
        right. econs; i.
        * exfalso. inv MTCHST. inv FINALTGT. inv ASMMOD.
          inv MSFIND. unfold Genv.find_funct in *. des_ifs.
          specialize (AGREE PC). rewrite <- FPTR in *.
          inv AGREE. unfold Vnullptr in *. des_ifs. congruence.
        * exploit step_init_simulation; try eassumption.
          { inv ASMMOD. eauto. }
          i. des. econs 2; ss; eauto. rewrite LINK_SK.
          split; auto. apply star_one. eauto.
      + left. right. econs. econs 1; et; cycle 1.
        { i. exfalso. inv FINALSRC. }
        i.
        destruct (call_step_noevent STEPSRC).
        destruct (match_states_call_ord_1 MTCHST).
        exists 0%nat. exists st_tgt. split.
        { right. split; auto. }
        left. pfold. left. right.
        econs. econs; et; cycle 1.
        { i. exfalso. inv STEPSRC. ss. rewrite LINK_SK in *.
          destruct (find_fptr_owner_determ SYSMOD MSFIND).
          inv INIT. inv FINALSRC. inv FINAL.
        }
        i. exists (length frs + 3)%nat. ss. rewrite LINK_SK in *.
        exploit syscall_simulation; eauto.
        i. des. exists st_tgt1. split.
        { left. split; cycle 1.
          { inv STEPSRC. ss.
            destruct (find_fptr_owner_determ SYSMOD MSFIND). ss.
            eapply system_receptive_at.
          }
          apply plus_one. econs; [apply asm_determinate_at|]. s. folder. rewrite senv_same. auto. }
        left. pfold. left. right.
        econs. econs; et; cycle 1.
        {
          i. exfalso. inv STEPSRC. ss.
          destruct (find_fptr_owner_determ SYSMOD MSFIND).
          inv INIT. inv STEPSRC0; ss; [|inv FINAL].
          inv STEP. inv FINALSRC. ss. inv MTCHST.
          inv STACK. inv SYSMOD. ss.
          unfold System.globalenv in *.
          clear - FPTR SIG0 FPTR0.
          unfold initial_regset, Pregmap.set in *. des_ifs.
          rewrite FPTR0 in *. clarify.
        }
        i.
        ss. rewrite LINK_SK in *. apply MTCHST0 in STEPSRC1. des. clarify.
        exists n1, st_tgt1. split.
        { right. split; auto. }
        right. eauto.
      + right. econs; i; try (exfalso; eauto).
    - left. right. econs. econs; cycle 1.
      + i. econs.
        * exploit transf_final_states; eauto.
        * i. inv FINAL0. inv FINAL1. eq_closure_tac.
        * ii. inv FINAL. inv H; eq_closure_tac.
      + * i. ss. rewrite LINK_SK in *.
          exploit normal_state_fsim_step; eauto.
          i. des; esplits; eauto.
          -- left. split; cycle 1.
             { eapply src_receptive_at; eauto. }
             econs; ss.
             ++ econs; eauto.
                { apply asm_determinate_at. }
                s. folder. rewrite senv_same. et.
             ++ econs 1.
             ++ rewrite E0_right. auto.
  Qed.

  Lemma transf_xsim_properties
    :
        xsim_properties (sem prog) (semantics tprog) nat lt.
  Proof.
    econs; [apply lt_wf| |i; apply symb_preserved].
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - i. inv INIT0. inv INIT1. clarify.
    - apply match_state_xsim; eauto.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Sem.sem prog) (Asm.semantics tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.

End PRESERVATION.


Require Import BehaviorsC.

Theorem lower_bound_correct
        (asms: list Asm.program)
  :
    (<<INITUB: program_behaves (sem (map AsmC.module asms)) (Goes_wrong E0)>>) \/
    exists link_tgt,
      (<<TGT: link_list asms = Some link_tgt>>)
      /\ (<<REFINE: improves (sem (map AsmC.module asms)) (Asm.semantics link_tgt)>>)
.
Proof.
  destruct (link_sk (map module asms)) eqn:T; cycle 1.
  { left. econs 2. ii. ss. inv H. clarify. }
  destruct (Sk.load_mem t) eqn:T2; cycle 1.
  { left. econs 2. ii. ss. inv H. clarify. }
  destruct (classic (forall md, In md (map module asms) -> <<WF: Sk.wf md >>)); cycle 1.
  { left. econs 2. ii. ss. inv H0. clarify. }
  right.
  exploit link_success; eauto. i. des.
  esplits; eauto.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  eapply transf_program_correct; eauto.
Qed.
