Require Import CoqlibC.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Smallstep.
Require Import Simulation.
Require Import Integers.
Require Import EventsC.
Require Import MapsC.
Require Import BehaviorsC.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem.

Require Import ModSemProps.

Set Implicit Arguments.


(* TODO: better namespace? *)
Lemma includes_refl
      sk
  :
    <<INCL: SkEnv.includes (Sk.load_skenv sk) sk>>
.
Proof.
  econs; eauto.
  - ii. eapply Genv.find_def_symbol in DEF. des. esplits; eauto. apply linkorder_refl.
  - rewrite Genv.globalenv_public. ss.
Qed.




Lemma link_includes
      p sk_link_src
      (LINK: link_sk p = Some sk_link_src)
      md
      (IN: In md p)
  :
    SkEnv.includes (Sk.load_skenv sk_link_src) md.(Mod.sk)
.
Proof.
  unfold link_sk in *.
  (* TODO: can we remove `_ LINK` ? *)
  (* Arguments link_list_linkorder [_]. *)
  (* Arguments link_list_linkorder: default implicits. *)
  hexploit (link_list_linkorder _ LINK); et. intro LOS; des.
  rewrite Forall_forall in *.
  exploit (LOS md); et.
  { rewrite in_map_iff. esplits; et. }
  intro LO.
  Local Transparent Linker_prog.
  ss. des.
  Local Opaque Linker_prog.
  econs; et.
  - i. exploit LO1; et. i; des. eapply Genv.find_def_symbol in H. des. esplits; et.
  - rewrite Genv.globalenv_public. ss.
Qed.

(* Remove redundancy with CompCert/ValueAnalysis.v && UnreachC.v *)
Definition definitive_initializer (init: list init_data) : bool :=
  match init with
  | nil => false
  | Init_space _ :: nil => false
  | _ => true
  end.

Local Transparent Linker_def Linker_vardef Linker_varinit Linker_unit.
Lemma definitive_initializer_is_definitive_left
      gv1 gv0
      (sk0 sk1: Sk.t) id_fr
      (LINK: link_prog_merge (prog_defmap sk0) ! id_fr (prog_defmap sk1) ! id_fr = Some (Gvar gv1))
      (IN: (prog_defmap sk0) ! id_fr = Some (Gvar gv0))
      (DEF: definitive_initializer (gvar_init gv0))
  :
    gv0 = gv1
.
Proof.
  {
    unfold link_prog_merge in *. des_ifs_safe.
    ss.
    des_ifs_safe.
    unfold link_vardef in *. des_ifs_safe. ss. destruct gv0; ss. unfold link_varinit in *. des_ifs_safe.
    bsimpl. des. rewrite eqb_true_iff in *.
    f_equal.
    { destruct gvar_info; ss. }
    des_ifs.
  }
Qed.

Lemma definitive_initializer_is_definitive_right
      gv1 gv0
      (sk0 sk1: Sk.t) id_fr
      (LINK: link_prog_merge (prog_defmap sk0) ! id_fr (prog_defmap sk1) ! id_fr = Some (Gvar gv1))
      (IN: (prog_defmap sk1) ! id_fr = Some (Gvar gv0))
      (DEF: definitive_initializer (gvar_init gv0))
  :
    gv0 = gv1
.
Proof.
  {
    unfold link_prog_merge in *. des_ifs_safe. ss.
    unfold link_def in *. des_ifs. ss.
    unfold link_vardef in *. des_ifs_safe. ss.
    clarify. destruct gv0; ss. unfold link_varinit in *. des_ifs_safe.
    bsimpl. des. rewrite eqb_true_iff in *.
    f_equal; ss.
    { destruct gvar_info; ss. }
    des_ifs.
  }
Qed.

Lemma definitive_initializer_split
      (g0 g1 g: globvar unit)
      (DEF: definitive_initializer g.(gvar_init))
      (LINK: link g0 g1 = Some g)
  :
    <<DEF: definitive_initializer g0.(gvar_init) \/ definitive_initializer g1.(gvar_init)>>
.
Proof.
  ss. unfold link_vardef in *. des_ifs. ss. clarify. unfold link_varinit in *.
  des_ifs; ss; et.
Qed.
Local Opaque Linker_def Linker_vardef Linker_varinit Linker_unit.

Theorem link_preserves_wf_sk
        sk0 sk1 sk_link
        (WFSK0: Sk.wf sk0)
        (WFSK1: Sk.wf sk1)
        (LINK: link sk0 sk1 = Some sk_link)
  :
    <<WF: Sk.wf sk_link>>
.
Proof.
  Local Transparent Linker_prog.
  ss.
  Local Opaque Linker_prog.
  hexploit (link_prog_inv _ _ _ LINK); et. intro INV; des. clarify. clear LINK.
  econs; et; ss.
  - unfold prog_defs_names. ss. eapply NoDup_norepet. eapply PTree.elements_keys_norepet; et.
  - i. unfold prog_defs_names. ss.
    apply PTree.elements_complete in IN.
    rewrite PTree.gcombine in *; ss.
    apply in_map_iff.
    assert((exists x, (prog_defmap sk0) ! id_to = Some x)
           \/ (exists x, (prog_defmap sk1) ! id_to = Some x)); cycle 1.
    { des.
      - destruct ((prog_defmap sk1) ! id_to) eqn:T.
        + exploit (INV0 id_to); eauto. intro X; des.
          eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
        + eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
      - destruct ((prog_defmap sk0) ! id_to) eqn:T.
        + exploit (INV0 id_to); eauto. intro X; des.
          eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
        + eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
    }
    assert((exists gv, (prog_defmap sk0) ! id_fr = Some (Gvar gv) /\ definitive_initializer gv.(gvar_init))
           \/
           (exists gv, (prog_defmap sk1) ! id_fr = Some (Gvar gv) /\ definitive_initializer gv.(gvar_init))).
    { unfold link_prog_merge in *. des_ifs.
      - exploit (INV0 id_fr); et. intro X; des.
        Local Transparent Linker_def.
        ss.
        Local Opaque Linker_def.
        destruct g, g0; ss; des_ifs.
        exploit (@definitive_initializer_split v v0 gv); et.
        { unfold definitive_initializer. des_ifs; ss; des; clarify. }
        i; des; et.
      - left. esplits; et.
        unfold definitive_initializer. des_ifs; ss; des; clarify.
      - right. esplits; et.
        unfold definitive_initializer. des_ifs; ss; des; clarify.
    }
    des.
    + assert(gv0 = gv).
      { eapply (definitive_initializer_is_definitive_left); eauto. }
      clarify.
      left.
      inv WFSK0. exploit (WFPTR id_fr); et.
      { apply in_prog_defmap; et. }
      intro X; des.
      eapply prog_defmap_dom; et.
    + assert(gv0 = gv).
      { eapply (definitive_initializer_is_definitive_right); eauto. }
      clarify.
      right.
      inv WFSK1. exploit (WFPTR id_fr); et.
      { apply in_prog_defmap; et. }
      intro X; des.
      eapply prog_defmap_dom; et.
  - ii.
    assert(exists gd, link_prog_merge (prog_defmap sk0) ! a (prog_defmap sk1) ! a = Some gd).
    { unfold link_prog_merge. des_ifs; eauto.
      - exploit INV0; eauto. i; des. esplits; et.
      - rewrite in_app_iff in *. des.
        + inv WFSK0. exploit PUBINCL; eauto. intro T. exploit prog_defmap_dom; et. i; des. clarify.
        + inv WFSK1. exploit PUBINCL; eauto. intro T. exploit prog_defmap_dom; et.
    }
    unfold prog_defs_names. ss. rewrite in_map_iff. des. eexists (_, _). s. esplits; eauto.
    eapply PTree.elements_correct. rewrite PTree.gcombine; ss.
    unfold link_prog_merge. des_ifs; eauto.
  - i. eapply PTree.elements_complete in IN.
    rewrite PTree.gcombine in IN; ss.
    unfold link_prog_merge in IN. des_ifs.
    + Local Transparent Linker_def. ss. unfold link_def in IN. des_ifs.
      Local Transparent Linker_skfundef. ss.
      inv WFSK0; inv WFSK1.
      unfold link_skfundef in Heq1. des_ifs.
      * eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
      * eapply WFPARAM0; eauto. eapply in_prog_defmap; eauto.
      * eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
    + inv WFSK0.
      eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
    + inv WFSK1.
      eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
Qed.

Theorem link_list_preserves_wf_sk
        p sk_link
        (LINK: link_sk p = Some sk_link)
        (WFSK: forall md, In md p -> <<WF: Sk.wf md >>)
  :
    <<WF: Sk.wf sk_link>>
.
Proof.
  unfold link_sk in *.
  (* unfold Mod.sk in *. *)
  ginduction p; ii; ss.
  unfold link_list in LINK. des_ifs_safe. ss.
  destruct (link_list_aux (map Mod.sk p)) eqn:T; ss.
  { clarify. destruct p; ss; des_ifs. eapply WFSK. eauto. }
  des_ifs.
  rename t into tl. rename a into hd.
  specialize (IHp tl).
  exploit IHp; eauto.
  { unfold link_list. des_ifs. }
  i; des.
  eapply (@link_preserves_wf_sk hd tl); et.
  eapply WFSK; et.
Qed.



Section INITDTM.

  Print fsim_properties.
  Print determinate.

  Lemma link_sk_disjoint
        md0 md1 p0 id skenv_link b if_sig if_sig0 restl sk_link gd_big0
        (IN : In md0 p0)
        (NOTSAME : md0 <> md1)
        (DEFS1 : defs (Mod.get_sk md1 (Mod.data md1)) id)
        (DEFS0 : defs (Mod.get_sk md0 (Mod.data md0)) id)
        (DEFBIG0 : Genv.find_def skenv_link b = Some gd_big0)
        (SYMBBIG0 : Genv.find_symbol skenv_link id = Some b)
        (WFBIG : SkEnv.wf skenv_link)
        (DEF0 : Genv.find_def (ModSem.skenv (Mod.get_modsem md0 skenv_link (Mod.data md0))) b = Some (Gfun (Internal if_sig)))
        (DEF1 : Genv.find_def (ModSem.skenv (Mod.get_modsem md1 skenv_link (Mod.data md1))) b = Some (Gfun (Internal if_sig0)))
        (INCLS : forall md : Mod.t, md1 = md \/ In md p0 -> SkEnv.includes skenv_link (Mod.get_sk md (Mod.data md)))
        (TL : link_list (map (fun md : Mod.t => Mod.get_sk md (Mod.data md)) p0) = Some restl)
        (HD : link (Mod.get_sk md1 (Mod.data md1)) restl = Some sk_link)
        (SKLINK : link_list (Mod.get_sk md1 (Mod.data md1) :: map (fun md : Mod.t => Mod.get_sk md (Mod.data md)) p0) = Some sk_link)
        (TLORD : Forall (fun x : Sk.t => linkorder x restl) (map (fun md : Mod.t => Mod.get_sk md (Mod.data md)) p0))
        (HDORD : linkorder (Mod.get_sk md1 (Mod.data md1)) sk_link)
        (HDORD0 : linkorder restl sk_link)
    :
      False.
  Proof.
    rewrite <- Mod.get_modsem_skenv_spec in *.
    rewrite Forall_forall in TLORD.
    assert (In (Mod.get_sk md0 (Mod.data md0)) (map (fun md : Mod.t => Mod.get_sk md (Mod.data md)) p0)).
    { rewrite in_map_iff. exists md0. auto. }
    assert (linkorder (Mod.get_sk md0 (Mod.data md0)) restl).
    { exploit TLORD; eauto. }
    Local Transparent Linker_prog.

    exploit INCLS; eauto. intros INCL0.
    inversion WFBIG.
    exploit DEFSYMB; eauto. i. des.
    exploit SkEnv.project_impl_spec; eauto. i. inv H2.
    exploit SYMBKEEP; eauto. i.

    assert (INTERN0: exists int_sig, Maps.PTree.get id (prog_defmap (Mod.get_sk md0 (Mod.data md0))) = Some (Gfun (Internal int_sig))).
    { rewrite SYMBBIG0 in H2.
      exploit DEFKEPT. eapply Genv.find_invert_symbol. eapply SYMBBIG0. eauto. i. des.
      eauto. } des.

    exploit (@prog_defmap_linkorder (fundef signature) unit). eapply H0.
    instantiate (2:=id).
    eauto. i. des.

    exploit INCLS. instantiate (1:=md1). auto. intros INCL1.
    exploit SkEnv.project_impl_spec; eauto. i. inv H5.
    exploit SYMBKEEP; eauto. i.

    assert (INTERN1: exists int_sig, Maps.PTree.get id (prog_defmap (Mod.get_sk md1 (Mod.data md1))) = Some (Gfun (Internal int_sig))).
    { rewrite SYMBBIG0 in H5.
      exploit DEFKEPT0. eapply Genv.find_invert_symbol. eapply SYMBBIG0. eauto. i. des.
      eauto. } des.

    exploit (@prog_defmap_linkorder (fundef signature) unit). eapply HDORD.
    instantiate (2:=id).
    eauto. i. des.

    Local Transparent Linker_def.
    simpl in *.
    inv H4. inv H9.
    Local Transparent Linker_fundef.
    simpl in *.
    inv H7. inv H8.

    inv HD. unfold link_prog in H7.
    des_ifs.
    symmetry in Heq.
    eapply andb_true_eq in Heq. des.
    symmetry in Heq0.
    rewrite Maps.PTree_Properties.for_all_correct in Heq0.
    unfold defs in *.
    exploit Heq0. eauto. i.
    unfold link_prog_check in H8.
    des_ifs. ss.
    rewrite andb_false_r in H8. clarify.
  Qed.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable p: program.
  Hypothesis (WFSK: forall md (IN: In md p), <<WF: Sk.wf md>>).
  Let sem := Sem.sem p.

  Lemma skenv_fill_internals_preserves_wf
        skenv0 skenv1
        (WF: SkEnv.wf skenv0)
        (FILL: skenv0.(skenv_fill_internals) = skenv1)
    :
      <<WF: SkEnv.wf skenv1>>
  .
  Proof.
    inv WF. unfold skenv_fill_internals.
    econs; i; ss; eauto.
    - rewrite Genv_map_defs_symb in *. exploit SYMBDEF; eauto. i; des.
      hexploit Genv_map_defs_def_inv; eauto. i; des. esplits; eauto.
      rewrite H0; ss.
    - eapply Genv_map_defs_def in DEF; eauto. des. des_ifs.
      exploit DEFSYMB; eauto.
    - unfold Genv_map_defs, Genv.find_def in *; ss.
      rewrite PTree_filter_map_spec in DEF.
      destruct ((Genv.genv_defs skenv0) ! blk) eqn:DMAP; ss.
      unfold o_bind in DEF; ss. des_ifs.
      { eapply WFPARAM in DMAP; eauto. }
      { eapply WFPARAM in DMAP; eauto. }
  Qed.

  Lemma system_disjoint
        skenv_link
        (WFBIG: SkEnv.wf skenv_link)
        sys_def
        fptr
        (SYSTEM: Genv.find_funct (System.skenv skenv_link) fptr = Some (Internal sys_def))
        md md_def
        (MOD: In md p)
        (MODSEM: Genv.find_funct (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) fptr =
                 Some (Internal md_def))
        (INCL: SkEnv.includes skenv_link md.(Mod.sk))
    :
      False
  .
  Proof.
    hexploit (@Mod.get_modsem_projected_sk md skenv_link); eauto. intro SPEC; des.
    remember (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) as skenv_proj eqn:T in *.
    assert(WFSMALL: skenv_proj.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; eauto. }
    clarify. des. inv SPEC.
    exploit Genv.find_funct_inv; eauto. i; des. clarify. ss. des_ifs.
    unfold Genv.find_funct_ptr in *. des_ifs.
    inv WFSMALL. exploit DEFSYMB; eauto. intro SYMBSMALL; des.
    assert((defs (Mod.get_sk md (Mod.data md))) id).
    { apply NNPP. ii.
      exploit SYMBDROP; eauto. i; des. clarify.
    }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des.
    rewrite SYMB in *. symmetry in SYMBBIG.
    exploit DEFKEPT; eauto.
    { apply Genv.find_invert_symbol; eauto. }
    i; des.
    exploit DEFKEEP; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    intro DEFSMALL; des. rewrite Heq in *. symmetry in DEFSMALL0.
    unfold System.skenv in *. ss.
    exploit Genv_map_defs_def; eauto. i; des. des_ifs. inv LO. inv H3.
  Qed.

  Theorem genv_disjoint
    :
      <<DISJ: sem.(globalenv).(Ge.disjoint)>>
  .
  Proof.
    ss. des_ifs; cycle 1.
    { econs; eauto. ii; ss. inv FIND0. ss. }
    assert(WFBIG: t.(Sk.load_skenv).(SkEnv.wf)).
    { eapply SkEnv.load_skenv_wf. eapply link_list_preserves_wf_sk; et. }
    econs; eauto.
    ii; ss.
    inv FIND0; inv FIND1.
    generalize (link_includes p Heq). intro INCLS.
    unfold Sk.load_skenv in *. unfold load_genv in *. unfold load_modsems in *. ss.
    abstr (Genv.globalenv t) skenv_link. rename t into sk_link.  rename Heq into SKLINK.
    rewrite in_map_iff in *.
    u in *.
    destruct MODSEM.
    { clarify. des; ss. exfalso. clarify. eapply system_disjoint; eauto. }
    des; ss.
    { clarify. ss. exfalso. eapply system_disjoint; eauto. }

    rename x into md0. rename x0 into md1.
    clarify.
    destruct fptr; ss. des_ifs. unfold Genv.find_funct_ptr in *. des_ifs.
    rename Heq0 into DEF0. rename Heq into DEF1.

    hexploit (@Mod.get_modsem_projected_sk md0 skenv_link); eauto. intro SPEC0; des.
    hexploit (@Mod.get_modsem_projected_sk md1 skenv_link); eauto. intro SPEC1; des.
    remember (ModSem.skenv (Mod.get_modsem md0 skenv_link (Mod.data md0))) as skenv_proj0 eqn:T0 in *.
    remember (ModSem.skenv (Mod.get_modsem md1 skenv_link (Mod.data md1))) as skenv_proj1 eqn:T1 in *.

    assert(WFSMALL0: skenv_proj0.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC0; eauto. }
    assert(WFSMALL1: skenv_proj1.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC1; eauto. }

    bar.
    inv WFSMALL0. exploit DEFSYMB; eauto. i; des.
    inv WFSMALL1. exploit DEFSYMB0; eauto. i; des.
    rename SYMB0 into SYMB1. rename SYMB into SYMB0. rename id0 into id1. rename id into id0.
    move SYMB0 at top. move SYMB1 at top. clear_until_bar.

    inv SPEC0.
    assert(DEFS0: defs (Mod.get_sk md0 (Mod.data md0)) id0).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG0; des. rewrite SYMB0 in *. symmetry in SYMBBIG0.
    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    move SYMBBIG0 at top.
    move DEFBIG at top.
    move DEFS0 at top.
    clear_until_bar.

    inv SPEC1.
    assert(DEFS1: defs (Mod.get_sk md1 (Mod.data md1)) id1).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG1; des. rewrite SYMB1 in *. symmetry in SYMBBIG1.
    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    move SYMBBIG1 at top.
    move DEFBIG0 at top.
    move DEFS1 at top.
    clear_until_bar.

    assert(id0 = id1).
    { eapply Genv.genv_vars_inj.
      { apply SYMBBIG0. }
      { apply SYMBBIG1. }
    } clarify.
    rename id1 into id.

    clear - SYMBBIG0 WFBIG INCLS DEF0 DEF1 DEFBIG DEFS0 DEFS1 SKLINK H0 MODSEM1.
    destruct (classic (md0 = md1)); ss.
    { clarify. }

    exfalso.

    clear_tac.
    generalize dependent sk_link.
    ginduction p; i; ss.
    dup SKLINK.
    eapply link_list_cons_inv in SKLINK; cycle 1.
    { destruct p0; ss.
      inv H0; inv MODSEM1; clarify.
    }
    des_safe.
    hexploit (link_list_linkorder _ TL); eauto. intro TLORD; des_safe.
    hexploit (link_linkorder _ _ _ HD); eauto. intro HDORD; des_safe.

    des; clarify.
    - eapply link_sk_disjoint; try eapply DEFBIG; eauto.
    - eapply link_sk_disjoint; try eapply DEFBIG; eauto.
    - eapply IHp0; try eapply DEFS1; try eapply DEFS0; try eapply DEFBIG; eauto.
  Qed.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner sem.(globalenv) fptr ms0)
        (FIND1: Ge.find_fptr_owner sem.(globalenv) fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    inv FIND0; inv FIND1. ss. des_ifs.
    unfold load_genv in *. ss.
    generalize genv_disjoint; i. inv H.
    eapply DISJOINT; eauto.
    - econs; eauto. ss. des_ifs.
    - econs; eauto. ss. des_ifs.
  Qed.

  Theorem initial_state_determ
          st_init0 st_init1
          (INIT0: sem.(Smallstep.initial_state) st_init0)
          (INIT1: sem.(Smallstep.initial_state) st_init1)
    :
      st_init0 = st_init1
  .
  Proof.
    ss.
    inv INIT0; inv INIT1; ss.
    clarify.
  Qed.

End INITDTM.




Lemma lift_step
      (ms: ModSem.t) st0 tr st1
      (STEP: Step ms st0 tr st1)
  :
    forall prog tail,
    <<STEP: Step (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. econs 3; eauto.
Qed.

Lemma lift_star
      (ms: ModSem.t) st0 tr st1
      (STAR: Star ms st0 tr st1)
  :
    forall prog tail,
    <<STAR: Star (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. ginduction STAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_step; eauto.
    + eapply IHSTAR; eauto.
Qed.

Lemma lift_plus
      (ms: ModSem.t) st0 tr st1
      (PLUS: Plus ms st0 tr st1)
  :
    forall prog tail,
    <<PLUS: Plus (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv PLUS; ii; ss.
  econs; eauto.
  - eapply lift_step; eauto.
  - eapply lift_star; eauto.
Qed.

Lemma lift_dstep
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTEP: DStep ms st0 tr st1)
  :
    forall tail,
    <<DSTEP: DStep (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. destruct DSTEP as [DTM STEP].
  econs; eauto; cycle 1.
  - econs; ss; eauto.
  - inv DTM.
    econs; eauto.
    + ii. ss.
      inv H; ss; ModSem.tac.
      inv H0; ss; ModSem.tac.
      clear STEP.
      determ_tac sd_determ_at.
      esplits; auto.
      * eapply match_traces_preserved; try apply H. i. s. congruence.
      * ii. clarify. special H0; ss. clarify.
    + ii. ss.
      inv STEP0; ss; ModSem.tac.
      inv FINAL; ss; ModSem.tac.
    + ii. inv H; ss; ModSem.tac.
      exploit sd_traces_at; eauto.
Qed.

Lemma lift_dstar
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTAR: DStar ms st0 tr st1)
  :
    forall tail,
    <<DSTAR: DStar (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. ginduction DSTAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_dstep; eauto.
    + eapply IHDSTAR; eauto.
Qed.

Lemma lift_dplus
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DPLUS: DPlus ms st0 tr st1)
  :
    forall tail,
    <<DPLUS: DPlus (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv DPLUS; ii; ss.
  econs; eauto.
  - eapply lift_dstep; eauto.
  - eapply lift_dstar; eauto.
Qed.

Lemma lift_receptive_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (RECEP: receptive_at ms st0)
  :
    forall tail,
    <<RECEP: receptive_at (Sem.sem prog)
                          (State ((Frame.mk ms st0) :: tail))>>
.
Proof.
  ii. inv RECEP. ss.
  econs; eauto; ii.
  - inv H.
    + inv H0. esplits; eauto. econs 1; eauto.
    + ss.
      exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try apply H0. i. s. congruence. }
      i; des.
      esplits; eauto.
      econs; eauto.
    + inv H0. esplits; eauto. econs 4; eauto.
  - inv H; s; try omega.
    exploit sr_traces_at; eauto.
Qed.

Lemma lift_determinate_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DTM: determinate_at ms st0)
  :
    forall tail,
    <<DTM: determinate_at (Sem.sem prog)
                            (State ((Frame.mk ms st0) :: tail))>>
.
Proof.
  ii. inv DTM. ss.
  econs; eauto; ii.
  - inv H; inv H0; ModSem.tac.
    + esplits; et.
      { econs; et. }
      i. f_equal. eapply ModSem.at_external_dtm; et.
    + ss. determ_tac sd_determ_at. esplits; et.
      { eapply match_traces_preserved; try apply H. i. s. congruence. }
      i. clarify. repeat f_equal. eauto.
    + ss. esplits; et.
      { econs; et. }
      i. repeat f_equal.
      determ_tac ModSem.final_frame_dtm. eapply ModSem.after_external_dtm; et.
  - ss. inv FINAL. ss. inv STEP; ss; ModSem.tac.
  - inv H; s; try omega.
    exploit sd_traces_at; eauto.
Qed.

(* Lemma callstate_receptive_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: receptive_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. econs; eauto. *)
(*     + inv H. inv MSFIND. ss. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

(* Lemma callstate_determinate_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: determinate_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. *)
(*       * econs; eauto. *)
(*       * i. repeat f_equal. clear_tac. *)
(*         exploit find_fptr_owner_determ; eauto. *)
(*         { ss. rewrite Heq. eapply MSFIND. } *)
(*         { ss. rewrite Heq. eapply MSFIND0. } *)
(*         i; clarify. *)
(*         determ_tac ModSem.initial_frame_dtm. *)
(*     + exfalso. inv H. inv MSFIND. ss. *)
(*   - ii. ss. des_ifs. *)
(*     + inv FINAL. *)
(*     + inv FINAL. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

Require Import MemoryC.

Section WFMEM.

(* TODO: move to proper place *)
Lemma Genv_bytes_of_init_data_length
      F V (ge: Genv.t F V) a
  :
    Datatypes.length (Genv.bytes_of_init_data ge a) = nat_of_Z (init_data_size a)
.
Proof.
  { clear - a .
    destruct a; ss.
    - rewrite length_list_repeat. rewrite Z2Nat.inj_max. ss. xomega.
    - des_ifs.
  }
Qed.

Inductive wf_mem_weak (skenv ge0: SkEnv.t) (sk: Sk.t) (m0: mem): Prop :=
| wf_mem_weak_intro
    (WFPTR: forall
        blk_fr _ofs_fr
        blk_to _ofs_to
        id_fr
        _q _n
        (SYMB: ge0.(Genv.find_symbol) id_fr = Some blk_fr)
        (* (IN: In id_fr sk.(prog_defs_names)) *)
        gv
        (IN: In (id_fr, (Gvar gv)) sk.(prog_defs))
        (NONVOL: gv.(gvar_volatile) = false)
        (DEFINITIVE: classify_init gv.(gvar_init) = Init_definitive gv.(gvar_init))
        (* (IN: sk.(prog_defmap) ! id_fr = Some (Gvar gv)) *)
        (LOAD: Mem.loadbytes m0 blk_fr _ofs_fr 1 = Some [Fragment (Vptr blk_to _ofs_to) _q _n])
      ,
        exists id_to, (<<SYMB: skenv.(Genv.invert_symbol) blk_to = Some id_to>>)
                      /\ (<<IN: In id_to sk.(prog_defs_names)>>)
    )
.

Let link_load_skenv_wf_sem_one: forall
    md sk_link
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    m0 m1
    id gd
    (* (IN: sk_link.(prog_defmap) ! id = Some gd) *)
    (IN: In (id, gd) sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (LOADM: Genv.alloc_global (Sk.load_skenv sk_link) m0 (id, gd) = Some m1)
    ge0
    (NOTIN: Genv.find_symbol ge0 id = None)
    (WFM: wf_mem_weak (Sk.load_skenv sk_link) ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0)
  ,
    (<<WFM: wf_mem_weak (Sk.load_skenv sk_link) (Genv.add_global ge0 (id, gd)) md m1>>)
    /\ (<<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) (Genv.add_global ge0 (id, gd)) m1>>)
    /\ (<<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>)
.
Proof.
  i.
  exploit Genv.alloc_global_initialized; et. intro FREETHM; des.
  esplits; et.
  econs; et. i. ss.
  des_ifs.
  - (* func *)
    assert(VALID: Mem.valid_block m0 blk_fr).
    { assert(NEQ: blk_fr <> b).
      { ii. clarify. clear - LOAD LOADM Heq. eapply Mem_alloc_fresh_perm in Heq. des.
        eapply Mem.loadbytes_range_perm in LOAD. unfold Mem.range_perm in LOAD. exploit (LOAD _ofs_fr). omega. i.
        destruct (zeq _ofs_fr 0).
        - subst. exploit Mem.perm_drop_2. eauto. instantiate (1 := 0). omega. eauto. i. inv H0.
        - eapply NOPERM0. instantiate (1 := _ofs_fr). omega. eapply Mem.perm_drop_4; eauto.
      }
      assert(VAL: Mem.valid_block m1 blk_fr).
      { clear - LOAD. exploit (Mem.loadbytes_range_perm); eauto. split. eapply Z.le_refl. omega. eapply Mem.perm_valid_block. }
      clear - Heq LOADM NEQ VAL. exploit Mem.drop_perm_valid_block_2; eauto. i.
      exploit Mem.valid_block_alloc_inv; eauto. i; des; des_ifs.
    }
    uge. unfold Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs.
    + Local Transparent Linker_prog.
      ss.
      Local Opaque Linker_prog.
      des.
      exploit prog_defmap_norepet; try apply IN; et.
      { apply NoDup_norepet. ss. }
      intro MAP; des.
      exploit prog_defmap_norepet; try apply IN0; et.
      { apply NoDup_norepet. ss. }
      intro MAP0; des.
      exploit LO1; et. i; des. clarify. inv H0.
    + inv WFM.
      assert(VAL: Mem.valid_block m0 blk_fr).
      { assert(NEQ: blk_fr <> b).
        { ii. clarify. clear - LOAD LOADM Heq. eapply Mem_alloc_fresh_perm in Heq. des.
        eapply Mem.loadbytes_range_perm in LOAD. unfold Mem.range_perm in LOAD. exploit (LOAD _ofs_fr). omega. i.
        destruct (zeq _ofs_fr 0).
        - subst. exploit Mem.perm_drop_2. eauto. instantiate (1 := 0). omega. eauto. i. inv H0.
        - eapply NOPERM0. instantiate (1 := _ofs_fr). omega. eapply Mem.perm_drop_4; eauto. }
        assert(VAL: Mem.valid_block m1 blk_fr).
        { clear - LOAD. exploit (Mem.loadbytes_range_perm); eauto. split. eapply Z.le_refl. omega. eapply Mem.perm_valid_block. }
        clear - Heq LOADM NEQ VAL. exploit Mem.drop_perm_valid_block_2; eauto. i.
        exploit Mem.valid_block_alloc_inv; eauto. i; des; des_ifs.
      }
      exploit WFPTR; et.
      erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
      { etrans.
        - eapply Mem.alloc_unchanged_on; et.
        - eapply Mem.drop_perm_unchanged_on; et. intros ? ? TTT. clear - Heq TTT. eapply Mem.fresh_block_alloc; eauto.
      }
  - (* gvar *)
    rename b into blk.
    unfold Genv.find_symbol, Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs; cycle 1.
    + assert(blk <> blk_fr).
      { ii; clarify. clear - WFMB Heq SYMB. exploit GlobalenvsC.Genv_update_publics_obligation_1; eauto. i.
        eapply Mem.alloc_result in Heq. subst. rewrite WFMB in H. xomega. }
      inv WFM. exploit WFPTR; et.
      assert(VAL: Mem.valid_block m0 blk_fr).
      { clear - Heq WFMB FREETHM0 H LOAD. rewrite WFMB in FREETHM0. exploit Mem.alloc_result; eauto. i. subst blk.
        eapply Mem.loadbytes_range_perm in LOAD. exploit Mem.perm_valid_block. eapply LOAD. instantiate (1 := _ofs_fr). omega. i.
        unfold Mem.valid_block in *. rewrite <- FREETHM0 in H0. exploit Plt_succ_inv; eauto. i. des; des_ifs. }
      assert(NVAL: ~ Mem.valid_block m0 blk).
      { clear - Heq. eauto with mem. }
      erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
      { etrans.
        { eapply Mem.alloc_unchanged_on; et. }
        etrans.
        { eapply Genv.store_zeros_unchanged; et. }
        etrans.
        { eapply Genv.store_init_data_list_unchanged; et. }
        { eapply Mem.drop_perm_unchanged_on; et. }
      }
    + r in FREETHM.
      exploit (FREETHM (Genv.genv_next ge0)); et.
      { unfold Genv.find_def, Genv.add_global. s. rewrite PTree.gsspec. des_ifs. }
      clear FREETHM. intro FREETHM; des. ss. des.
      (* assert(gv.(gvar_init) = v.(gvar_init)). *)
      assert(LOA: linkorder gv v /\ gvar_volatile v = false).
      {
        Local Transparent Linker_prog.
        ss.
        Local Opaque Linker_prog.
        des.
        exploit LO1; et.
        { apply prog_defmap_norepet; et. apply NoDup_norepet; et. }
        i; des.
        apply prog_defmap_norepet in IN; cycle 1. { apply NoDup_norepet; et. }
        clarify.
        inv H0. inv H4. ss.
      }
      des.
      exploit FREETHM3; et. intro LOADA; des.
      assert(DAT: exists id_to _ofs,
                (<<IN: In (Init_addrof id_to _ofs) (gvar_init gv)>>)
                /\ (<<SYMB: Genv.find_symbol (Sk.load_skenv sk_link) id_to = Some blk_to>>)
                (* /\ (<<PLT :Plt blk_to (Genv.genv_next ge0)>>) *)
            ).
      { assert(EQ: gv.(gvar_init) = v.(gvar_init)).
        { inv LOA. ss. inv H0; ss. }
        rewrite EQ in *.
        abstr (gvar_init v) dts.
        clear - LOAD LOADA FREETHM1.
        abstr (Genv.genv_next ge0) blk. clear_tac.
        abstr ((Sk.load_skenv sk_link)) skenv_link. clear_tac.
        destruct (classic (0 <= _ofs_fr < init_data_list_size dts)); cycle 1.
        {
          hexploit Mem.loadbytes_range_perm; try apply LOAD; et. intro PERM.
          exploit FREETHM1; et.
          { r in PERM. eapply PERM; et. instantiate (1:= _ofs_fr). xomega. }
          i; des. xomega.
        }
        rename H into RANGE.
        clear FREETHM1.
        assert(POS: 0 <= 0) by xomega.
        change (init_data_list_size dts) with (0 + init_data_list_size dts) in RANGE.
        revert_until skenv_link.
        generalize 0 at 1 2 3 5 as ofs. i.
        (* generalize 0 at 1 2 4 as ofs. i. *)
        ginduction dts; ii; ss.
        { xomega. }
        try rewrite Z.add_assoc in *.
        assert(LOADB: Mem.loadbytes m1 blk (ofs + init_data_size a) (init_data_list_size dts) =
                      Some (Genv.bytes_of_init_data_list skenv_link dts) /\
                      <<LOADC: Mem.loadbytes m1 blk ofs (init_data_size a) =
                               Some (Genv.bytes_of_init_data skenv_link a)>>).
        { exploit Mem.loadbytes_split; et; try xomega.
          { eapply init_data_size_pos. }
          { eapply init_data_list_size_pos. }
          i; des.
          exploit Mem.loadbytes_length; try apply H; et. intro LEN0.
          exploit Mem.loadbytes_length; try apply H0; et. intro LEN1.
          rewrite H. rewrite H0. clear - LEN0 LEN1 H1.
          generalize (Genv_bytes_of_init_data_length skenv_link a); intro LEN2.
          assert(Genv.bytes_of_init_data skenv_link a = bytes1).
          { do 2 (rewrite <- app_nil_r; erewrite <- firstn_O; sym; rewrite <- firstn_app_2).
            rewrite H1. rewrite LEN0. rewrite LEN2. eauto.
          }
          split; des_ifs. eapply app_inv_head in H1. des_ifs.
        }
        des.

        Ltac break_Z :=
          try replace 2 with (1 + 1) in * by omega;
          try replace 3 with (1 + 1 + 1) in * by omega;
          try replace 4 with (1 + 1 + 1 + 1) in * by omega;
          try replace 5 with (1 + 1 + 1 + 1 + 1) in * by omega;
          try replace 6 with (1 + 1 + 1 + 1 + 1 + 1) in * by omega;
          try replace 7 with (1 + 1 + 1 + 1 + 1 + 1 + 1) in * by omega.

        destruct (classic ((ofs + init_data_size a) <= _ofs_fr)).
        - exploit IHdts; et; try xomega.
          { eapply OMEGA2; eauto. eapply Z.ge_le. eapply init_data_size_pos. }
          i; des. esplits; et.
        - clear IHdts LOADB LOADA.
          rename a into aa.
          clear RANGE0.
          Local Opaque Z.add.
          Local Transparent Mem.loadbytes.
          rename ofs into ofs_bound.
          rename _ofs_fr into ofs_mid.
          assert(T: ofs_mid < ofs_bound + init_data_size aa) by omega. clear H.

          destruct aa; ss.
          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                  ).
            { omega. }
            des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss.

          + exfalso.
            unfold Mem.loadbytes in *. des_ifs.
            rename H0 into P. rename H1 into Q.
            clear - P Q T RANGE POS.
            abstr ((Mem.mem_contents m1) !! blk) MC. clear_tac.
            assert(POS0: 0 <= Z.max z 0) by xomega.
            exploit (@Mem.getN_in MC ofs_mid (Z.max z 0).(Z.to_nat) ofs_bound); eauto.
            { split; try xomega. rewrite Z2Nat.id; ss. }
            intro R.
            rewrite Q in *. unfold nat_of_Z in *. rewrite P in *.
            clear - R.
            apply in_list_repeat in R. ss.

          + des_ifs; cycle 1.
            { exfalso. unfold Mem.loadbytes in *. des_ifs.
              assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                     \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                     \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                    ).
              { omega. }
              des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H8 in *; ss.
            }
            esplits; et.
            unfold inj_value in *. ss. unfold Mem.loadbytes in *. des_ifs.
              assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                     \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                     \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7
                    ).
              { omega. }
              des; subst; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H8 in *; congruence.
          Local Opaque Mem.loadbytes.
      }
      des.
      bar. inv WF. exploit WFPTR; et. i ;des. esplits; et.
      apply Genv.find_invert_symbol. ss.
Qed.


Let link_load_skenv_wf_sem_mult: forall
    md sk_link
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    idgs
    (INCL: incl idgs sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (NODUP: NoDup (map fst idgs))
    m0 m1
    (LOADM: Genv.alloc_globals (Sk.load_skenv sk_link) m0 idgs = Some m1)
    ge0
    (NOTIN: forall id (IN: In id (map fst idgs)), Genv.find_symbol ge0 id = None)
    (WFM: wf_mem_weak (Sk.load_skenv sk_link) ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0)
  ,
    <<WFM: wf_mem_weak (Sk.load_skenv sk_link) (Genv.add_globals ge0 idgs) md m1>>
           /\ <<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link)
                                               (Genv.add_globals ge0 idgs) m1>>
                                               /\ <<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>
.
Proof.
  i.
  generalize dependent ge0.
  generalize dependent m0.
  generalize dependent m1.
  (* generalize dependent FRESH. *)
  induction idgs; ii; ss.
  { clarify. }
  des_ifs.
  destruct a.
  exploit link_load_skenv_wf_sem_one; et.
  { eapply INCL; et. s. et. }
  i; des.
  exploit IHidgs; try apply WFM0; et.
  { ii. eapply INCL; et. s. et. }
  { ss. inv NODUP1. ss. }
  { i. uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs.
    - inv NODUP1. ss.
    - apply NOTIN. right. ss. }
  { s. clear - WFMB0 Heq. exploit Genv.alloc_global_nextblock; eauto. congruence. }
  i; des.
  esplits; et.
Qed.

Lemma link_load_skenv_wf_mem
      p sk_link m_init
      (LINK: link_sk p = Some sk_link)
      (WF: forall md (IN: In md p), Sk.wf md)
      (LOADM: Sk.load_mem sk_link = Some m_init)
  :
    let skenv_link := Sk.load_skenv sk_link in
    <<WFM: forall md (IN: In md p), SkEnv.wf_mem skenv_link md m_init>>
.
Proof.
  econs. i.
  unfold link_sk in *.
  hexploit (link_list_linkorder _ LINK); et. intro LO. des.
  rewrite Forall_forall in *.
  exploit LO; et.
  { rewrite in_map_iff. esplits; et. }
  clear LO.
  intro LO.
  exploit WF; et. clear WF. intro WF; des.
  assert(NODUP: NoDup (prog_defs_names sk_link)).
  { clear - LINK IN WF. destruct p; ss. destruct p; ss.
    - des; ss. clarify. unfold link_list in *. des_ifs. ss. clarify. apply WF.
    - clear IN WF.
      exploit (link_list_cons_inv _ LINK); et.
      { ss. }
      i; des.
      clear - HD.
      Local Transparent Linker_prog.
      ss.
      Local Opaque Linker_prog.
      unfold link_prog in *. des_ifs.
      apply NoDup_norepet.
      unfold prog_defs_names.
      apply PTree.elements_keys_norepet.
  }
  clear LINK IN.


  {
    eapply link_load_skenv_wf_sem_mult; et.
    { refl. }
    { apply WF. }
    { i. uge. ss. rewrite PTree.gempty. ss. }
    { econs; et. i. exfalso. clear - LOAD0. eapply Mem.loadbytes_range_perm in LOAD0.
      exploit (LOAD0 _ofs_fr0). omega. eapply Mem.perm_empty.
    }
    { rr. ii. exfalso. clear - H. unfold Genv.find_def in H. rewrite PTree.gempty in H. des_ifs. }
    { ss. }
  }
Qed.

End WFMEM.


Require Import Sem SimModSem.
Theorem safe_implies_safe_modsem
        p sk ms lst tail
        (LINK: link_sk p = Some sk)
        (SAFE: safe (sem p) (State ({| Frame.ms := ms; Frame.st := lst |} :: tail)))
  :
    <<SAFE: safe_modsem ms lst>>
.
Proof.

  {
    ii. ss. exploit SAFE.
    { instantiate (1:= (State ({| Frame.ms := ms; Frame.st := st1 |} :: tail))). eapply lift_star; eauto. }
    i; des.
    - ss. inv H. ss. right. left. eauto.
    - ss. des_ifs. inv H; ss.
      + left. eauto.
      + right. right. eauto.
      + right. left. eauto.
  }
Qed.


Lemma backward_simulation_refl
      SEM
  :
    backward_simulation SEM SEM
.
Proof.
  eapply (@Backward_simulation _ _ unit bot2).
  econs; eauto.
  { apply unit_ord_wf. }
  ii. ss.
  exists tt.
  esplits; eauto.
  clear st_init_src_ INITSRC INITTGT.
  rename st_init_tgt into st. revert st.
  pcofix CIH. i. pfold.
  econs; eauto.
  { ii. esplits; eauto. econs; eauto. }
  ii. econs; eauto.
  { ii. esplits; eauto. left. apply plus_one. ss. }
  i. r in SAFESRC. specialize (SAFESRC st (star_refl _ _ _ _)). ss.
Qed.

Lemma sk_nwf_improves (mds_src mds_tgt: program)
      (NWF: ~ (forall x (IN: In x mds_src), Sk.wf x))
  :
      improves (sem mds_src) (sem mds_tgt).
Proof.
  eapply bsim_improves. econs. econs.
  - eapply unit_ord_wf.
  - i. inv INITSRC. clarify.
  - i. inv INITSRC. clarify.
Qed.
