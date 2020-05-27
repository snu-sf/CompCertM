Require Import CoqlibC MapsC.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC LinkingC2.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program SemProps.
Require Import Equality.
Require Import CtypingC.

Set Implicit Arguments.

Ltac Eq :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
    rewrite H1 in H2; inv H2; Eq
  | [ H1: ?a m= ?b, H2: ?a m= ?c |- _ ] =>
    rewrite H1 in H2; inv H2; Eq
  | _ => idtac
  end.

Fixpoint app_cont (k0 k1: cont) {struct k0}: cont :=
  match k0 with
  | Kstop => k1
  | Kdo k => Kdo (app_cont k k1)
  | Kseq s k => Kseq s (app_cont k k1)
  | Kifthenelse s1 s2 k => Kifthenelse s1 s2 (app_cont k k1)
  | Kwhile1 e s k => Kwhile1 e s (app_cont k k1)
  | Kwhile2 e s k => Kwhile2 e s (app_cont k k1)
  | Kdowhile1 e s k => Kdowhile1 e s (app_cont k k1)
  | Kdowhile2 e s k => Kdowhile2 e s (app_cont k k1)
  | Kfor2 e s1 s2 k => Kfor2 e s1 s2 (app_cont k k1)
  | Kfor3 e s1 s2 k => Kfor3 e s1 s2 (app_cont k k1)
  | Kfor4 e s1 s2 k => Kfor4 e s1 s2 (app_cont k k1)
  | Kswitch1 ls k =>  Kswitch1 ls (app_cont k k1)
  | Kswitch2 k =>  Kswitch2 (app_cont k k1)
  | Kreturn k => Kreturn (app_cont k k1)
  | Kcall f e em ty k => Kcall f e em ty (app_cont k k1)
  end.

Lemma app_cont_stop_right
      k0:
    <<EQ: app_cont k0 Kstop = k0>>.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_stop_left
      k0:
    <<EQ: app_cont Kstop k0 = k0>>.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_kstop_inv
      k0 k1
      (APP: app_cont k0 k1 = Kstop):
    k0 = Kstop /\ k1 = Kstop.
Proof. destruct k0; ss. Qed.

Section SIM.

  Variable cp_link: Csyntax.program.
  Variable cps: list Csyntax.program.
  Variable ctx: Syntax.program.
  Hypothesis FOCUS: link_list cps = Some cp_link.
  Let prog_src := ctx ++ [(CsemC.module cp_link)].
  Let prog_tgt := ctx ++ map CsemC.module cps.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk prog_src = Some sk_link).
  Notation " 'geof' cp" := (Build_genv (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) cp.(prog_comp_env))
                           (at level 50, no associativity, only parsing).
  Let ge_cp_link: genv := geof cp_link.
  Hypothesis WTPROGLINK: wt_program cp_link.
  Hypothesis WTPROGS: forall cp (IN: In cp cps), wt_program cp.

  Hypothesis CSTYLE_EXTERN_LINK:
    forall id ef tyargs ty cc,
      In (id, (Gfun (Ctypes.External ef tyargs ty cc))) cp_link.(prog_defs) ->
      (ef_sig ef).(sig_cstyle).

  Definition is_focus (cp: Csyntax.program): Prop := In cp cps.

  Hypothesis CSTYLE_EXTERN:
    forall id ef tyargs ty cc cp,
      is_focus cp ->
      In (id, (Gfun (Ctypes.External ef tyargs ty cc))) cp.(prog_defs) ->
      (ef_sig ef).(sig_cstyle).

  Lemma link_sk_match:
      <<EQ: link_sk prog_src = link_sk prog_tgt>>.
  Proof.
    subst_locals.
    unfold link_sk.
    rewrite ! map_app. ss.
    symmetry. eapply link_list_app_commut; eauto.

    clear - FOCUS.
    ginduction cps; ii; ss.
    destruct l; ss.
    { unfold link_list, link_list_aux in *. des_ifs. }
    exploit link_list_cons_inv; eauto.
    { ss. }
    intro P; des.
    exploit IHl; eauto. intro P; des.
    exploit (@link_list_cons Sk.t); try apply P.
    { instantiate (1:= CSk.of_program signature_of_function cp_link).
      instantiate (1:= CSk.of_program signature_of_function a).
      clear - HD.
      Local Transparent Linker_prog Linker_program Linker_fundef Linker_types Linker_varinit
            Linker_vardef Linker_def Linking.Linker_fundef. ss.
      rename a into p0. rename restl into p1. fold Csyntax.program in *.
      unfold link_program in *. des_ifs. ss.
      clear - Heq. unfold link_prog in *. ss. des_ifs_safe. bsimpl. des. des_sumbool.
      des_ifs; cycle 1.
      { exfalso. bsimpl. des; des_sumbool; ss.
        rewrite PTree_Properties.for_all_false in *. rewrite PTree_Properties.for_all_correct in *. des.
        generalize (CSk.of_program_prog_defmap p0 signature_of_function x1). intro REL0.
        generalize (CSk.of_program_prog_defmap p1 signature_of_function x1). intro REL1.
        inv REL0; try by congruence.
        rewrite <- H0 in *. clarify. exploit Heq1; eauto. intro CHK; des.
        unfold link_prog_check in *. des_ifs_safe.
        inv REL1. ss. rewrite <- H2 in *.
        bsimpl. des; des_sumbool; ss; clarify.
        clear - Heq2 CHK0 H1 H4. des_ifs. inv H1; inv H4; ss.
        - unfold CtypesC.CSk.match_fundef in *. des_ifs; ss; des_ifs; bsimpl; des; des_sumbool; clarify.
          + unfold signature_of_function in *. ss. unfold signature_of_type in *.
            eapply n. f_equal. rewrite Heq3.
            clear. ginduction t. ss. ss. rewrite IHt. eauto.
          + unfold signature_of_function in *. ss. unfold signature_of_type in *.
            eapply n. f_equal. rewrite Heq3.
            clear. ginduction t. ss. ss. rewrite IHt. eauto.
        - des_ifs. inv H; inv H0; ss. unfold link_vardef in *. ss. des_ifs. }
      bsimpl. des. des_sumbool.
      f_equal. unfold CSk.of_program. ss. f_equal.
      unfold skdefs_of_gdefs.
      rewrite PTree_elements_map.
      rewrite PTree_elements_map.
      eapply PTree.elements_extensional. intro id. rewrite PTree.gcombine; ss.
      rewrite ! PTree.gmap. rewrite PTree.gcombine; ss.
      rename Heq2 into P. rename Heq1 into Q. clear - P Q.
      unfold prog_defmap in *. ss.
      rewrite ! prog_defmap_update_snd.
      rewrite PTree_Properties.for_all_correct in *.
      set ((PTree_Properties.of_list (prog_defs p0)) ! id) as x.
      set ((PTree_Properties.of_list (prog_defs p1)) ! id) as y. clear_tac.
      destruct x eqn:Tx; ss. destruct y eqn:Ty; ss. unfold x in Tx. unfold y in Ty.
      exploit Q; eauto. intro CHK.
      unfold option_map. des_ifs; ss; cycle 1.
      - destruct g, g0; ss; unfold skdef_of_gdef, fundef_of_fundef, link_prog_check, prog_defmap, program_of_program in *;
          des_ifs; ss; des_ifs; bsimpl; des; des_sumbool; clarify.
      - destruct g, g0; ss; unfold skdef_of_gdef, fundef_of_fundef in *; des_ifs; ss;
          unfold fundef_of_fundef in *; des_ifs; bsimpl; des; des_sumbool; clarify.
        + exfalso. unfold signature_of_function in *. ss. unfold signature_of_type in *.
          eapply n. f_equal. rewrite Heq1. clear. ginduction t. ss. ss. rewrite IHt. eauto.
        + exfalso. unfold signature_of_function in *. ss. unfold signature_of_type in *.
          eapply n. f_equal. rewrite Heq1. clear. ginduction t. ss. ss. rewrite IHt. eauto.
        + destruct g; ss. unfold link_vardef in *. des_ifs. ss. bsimpl. des. rewrite eqb_true_iff in *.
          f_equal. destruct gvar_info; ss. f_equal; ss. f_equal; ss. clarify.
        + exfalso.
          destruct v, v0; ss. unfold link_vardef in *. ss. des_ifs. }
    intro Q; des. ss.
  Qed.

  Let LINKTGT: link_sk prog_tgt = Some sk_link.
  Proof. rewrite link_sk_match in *. ss. Qed.

  Let INCL_LINKED: SkEnv.includes skenv_link (CSk.of_program signature_of_function cp_link).
  Proof.
    exploit link_includes. eapply LINKSRC.
    subst prog_src. instantiate (1 := (module cp_link)).
    apply in_or_app. ss. auto. ss. Qed.

  Let INCL_FOCUS: forall pgm, is_focus pgm -> SkEnv.includes skenv_link (CSk.of_program signature_of_function pgm).
  Proof.
    i. exploit link_includes.
    { eapply LINKTGT. }
    { subst prog_tgt. instantiate (1 := (module pgm)).
      rewrite in_app_iff in *. r in H. right. rewrite in_map_iff. esplits; et. }
    i. ss.
  Qed.

  Lemma prog_defmap_func_same_rev
        pgm id func
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gfun func))
        (INTERNAL: negb (is_external_fd func) = true):
      (prog_defmap cp_link) ! id = Some (Gfun func).
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    r in FOC.
    exploit link_list_linkorder; et. intro ORD. r in ORD. rewrite Forall_forall in ORD.
    exploit ORD; eauto. intro ORD0.
    Local Transparent Linker_program.
    ss. rr in ORD0. des.
    hexploit (@prog_defmap_linkorder (Ctypes.fundef function) type); eauto. intro P; des. inv P0.
    inv H0; ss.
  Qed.

  Inductive sum_cont: list Frame.t -> cont -> Prop :=
  | sum_cont_nil :
      sum_cont [] Kstop
  | sum_cont_cons
      _fptr _vs k0 _m
      _targs _tres _cconv
      (CALL: is_call_cont_strong k0)
      tl k1
      (TL: sum_cont tl k1)
      k2
      (K: k2 = app_cont k0 k1)
      cp
      (FOCUS: is_focus cp)
      (K0: exists _f _e _C _k, k0 = (Kcall _f _e _C _tres _k) /\ <<WTYK: wtype_cont (prog_comp_env cp) _k>>)
      (WTTGT: wt_state cp (geof cp) (Csem.Callstate _fptr (Tfunction _targs _tres _cconv) _vs k0 _m)):
      sum_cont ((Frame.mk (CsemC.modsem skenv_link cp)
                          (Csem.Callstate _fptr (Tfunction _targs _tres _cconv) _vs k0 _m)) :: tl) k2.

  Lemma sum_cont_kstop_inv
        frs
        (SUM: sum_cont frs Kstop):
      frs = [].
  Proof.
    clear - SUM.
    inv SUM; ss.
    hexpl app_cont_kstop_inv. clarify.
  Qed.

  Inductive match_focus_state: Csem.state -> Csem.state -> cont -> Prop :=
  | reg_state_similar
      f s k k0 k1 e m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.State f s k e m) (Csem.State f s k1 e m) k0
  | expr_state_similar
      f ex k k0 k1 e m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.ExprState f ex k e m) (Csem.ExprState f ex k1 e m) k0
  | call_sate_similar
      fptr tyf vargs k k0 k1 m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.Callstate fptr tyf vargs k m) (Csem.Callstate fptr tyf vargs k1 m) k0
  | return_sate_similar
      vres k k0 k1 m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.Returnstate vres k m) (Csem.Returnstate vres k1 m) k0
  | stuck_state_similar
      k0:
      match_focus_state Csem.Stuckstate Csem.Stuckstate k0.

  Lemma call_cont_app_cont
        k k0
        tl_tgt (SUM: sum_cont tl_tgt k0):
      (app_cont (call_cont k) k0) = call_cont (app_cont k k0).
  Proof.
    clear - SUM.
    assert(CASE: k0 = Kstop \/ is_call_cont_strong k0).
    { inv SUM; ss; et. des. clarify. ss. et. }
    clear SUM. clear_tac. des.
    { clarify. repeat rewrite app_cont_stop_right. ss. }
    { rr in CASE. des_ifs. clear_tac. clear - c.
      ginduction k; ii; ss; des; repeat rewrite app_cont_stop_right; ss; clarify. }
  Qed.

  Definition matched_state_source (st_tgt: Csem.state) (k0: cont): Csem.state :=
    match st_tgt with
    | Csem.State f s k1 e m => Csem.State f s (app_cont k1 k0) e m
    | Csem.ExprState f ex k1 e m => Csem.ExprState f ex (app_cont k1 k0) e m
    | Csem.Callstate fptr tyf vargs k1 m => Csem.Callstate fptr tyf vargs (app_cont k1 k0) m
    | Csem.Returnstate vres k1 m => Csem.Returnstate vres (app_cont k1 k0) m
    | Csem.Stuckstate => Csem.Stuckstate
    end.

  Lemma match_focus_state_iff
        st_src0 st_tgt0 k0 :
      <<MATCH: match_focus_state st_src0 st_tgt0 k0>> <-> <<MATCH: st_src0 = matched_state_source st_tgt0 k0>>.
  Proof.
    split; i.
    - inv H; ss.
    - des. clarify. r. destruct st_tgt0; ss; try (by econs; eauto).
  Qed.

  (** Same Lemmas *)

  Lemma defmap_with_signature
        (cp:Csyntax.program) i g
        (DMAP: (prog_defmap cp) ! i = Some g) :
      exists gd, (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some gd.
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H. rewrite DMAP in *. clarify. eauto.
  Qed.

  Lemma defmap_with_signature_internal
        (cp:Csyntax.program) i if_sig
        (DMAP: (prog_defmap cp) ! i = Some (Gfun (Internal if_sig))) :
      exists if_sig0, (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some (Gfun (AST.Internal if_sig0)).
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H; rewrite DMAP in *; clarify.
    inv H2. unfold CtypesC.CSk.match_fundef in H3. destruct f2; ss.
    rewrite <- H1. eauto.
  Qed.

  Lemma invert_symbol_lemma1
        b i0 i cp
        (FOC: is_focus cp)
        (SYMBSKENV : Genv.invert_symbol skenv_link b = Some i0)
        (DEFS: defs (CSk.of_program signature_of_function cp) i)
        (SYMB : Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b = Some i) :
      i = i0.
  Proof.
    exploit Genv.invert_find_symbol. eauto. i. exploit Genv.invert_find_symbol. eapply SYMBSKENV. i.
    exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H1.
    exploit SYMBKEEP; eauto. i.
    rewrite H1 in H.
    exploit Genv.find_invert_symbol. eapply H. i. exploit Genv.find_invert_symbol. eapply H0. i.
    rewrite H2 in H3. clarify.
  Qed.

  Lemma prog_defmap_same_rev
        pgm id func
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gfun (Internal func))):
      (prog_defmap cp_link) ! id = Some (Gfun (Internal func)).
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    r in FOC.
    exploit link_list_linkorder; et. intro ORD. r in ORD. rewrite Forall_forall in ORD.
    exploit ORD; eauto. intro ORD0.
    Local Transparent Linker_program.
    ss. rr in ORD0. des.
    hexploit (@prog_defmap_linkorder (Ctypes.fundef function) type); eauto. intro P; des. inv P0.
    inv H0.
    esplits; eauto.
  Qed.

  Lemma prog_defmap_gvar_exists_rev
        pgm id var
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gvar var)):
      exists var', (prog_defmap cp_link) ! id = Some (Gvar var').
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    r in FOC.
    exploit link_list_linkorder; et. intro ORD. r in ORD. rewrite Forall_forall in ORD.
    exploit ORD; eauto. intro ORD0.
    Local Transparent Linker_program.
    ss. rr in ORD0. des.
    hexploit (@prog_defmap_linkorder (Ctypes.fundef function) type); eauto. intro P; des. inv P0.
    inv H0; ss. inv H; inv H1; eauto.
  Qed.

  Lemma prog_defmap_exists_rev
        pgm id func
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gfun func)):
      exists func', (prog_defmap cp_link) ! id = Some (Gfun func').
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    r in FOC.
    exploit link_list_linkorder; et. intro ORD. r in ORD. rewrite Forall_forall in ORD.
    exploit ORD; eauto. intro ORD0.
    Local Transparent Linker_program.
    ss. rr in ORD0. des.
    hexploit (@prog_defmap_linkorder (Ctypes.fundef function) type); eauto. intro P; des. inv P0.
    esplits; eauto.
  Qed.

  Lemma invert_symbol_lemma2
        b i0 i
        (SYMBSKENV : Genv.invert_symbol skenv_link b = Some i0)
        (DEFS: defs (CSk.of_program signature_of_function cp_link) i)
        (SYMB : Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b = Some i):
    i = i0.
  Proof.
    exploit Genv.invert_find_symbol. eauto. i. exploit Genv.invert_find_symbol. eapply SYMBSKENV. i.
    exploit SkEnv.project_impl_spec. eapply INCL_LINKED. i. inv H1.
    exploit SYMBKEEP; eauto. i.
    rewrite H1 in H.
    exploit Genv.find_invert_symbol. eapply H. i. exploit Genv.find_invert_symbol. eapply H0. i.
    rewrite H2 in H3. clarify.
  Qed.

  Lemma internals_linking
        cp i
        (FOC: is_focus cp)
        (INTERNALS : internals (CSk.of_program signature_of_function cp) i = true):
      internals (CSk.of_program signature_of_function cp_link) i = true.
  Proof.
    rewrite CSk.of_program_internals in *.
    unfold internals in INTERNALS.
    destruct ((prog_defmap cp) ! i) eqn:DMAP; ss.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    destruct g.
    - ss. exploit prog_defmap_func_same_rev; eauto. i.
      unfold internals. rewrite H. ss.
    - ss. exploit prog_defmap_gvar_exists_rev; eauto. i. des_safe.
      unfold internals. rewrite H. ss.
  Qed.

  Lemma prog_find_defs_same_rev2
        cp b func
        (FOC: is_focus cp)
        (INTERNAL: negb (is_external_fd (fundef_of_fundef func)) = true)
        (FIND: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) b = Some (Gfun func)):
      Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) b = Some (Gfun func).
  Proof.
    unfold Genv.find_def in FIND. ss. rewrite MapsC.PTree_filter_map_spec in FIND. rewrite o_bind_ignore in FIND. des_ifs.
    destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:SYMB; ss.
    unfold o_bind in FIND. ss. destruct ((prog_defmap cp) ! i) eqn:DMAP; ss. clarify.
    rewrite MapsC.PTree_filter_map_spec in Heq. rewrite o_bind_ignore in Heq. destruct ((Genv.genv_defs skenv_link) ! b) eqn:GENVDEF; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:SYMBSKENV; ss. unfold o_bind in Heq. ss. des_ifs.
    exploit invert_symbol_lemma1; eauto. rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i. subst.
    unfold Genv.find_def. ss. do 2 rewrite MapsC.PTree_filter_map_spec.
    do 2 rewrite o_bind_ignore. rewrite GENVDEF. rewrite SYMBSKENV. unfold o_bind. ss.
    exploit prog_defmap_func_same_rev; eauto. i. des_safe.
    des_ifs; cycle 1.
    - exploit defmap_with_signature; eauto. i. des_safe. rewrite H0 in Heq1. ss.
    - exploit internals_linking; eauto. i. rewrite H0 in *; clarify.
    - exploit SkEnv.project_impl_spec. eapply INCL_LINKED. i. inv H0.
      exploit SYMBKEEP. rewrite <- defs_prog_defmap. exploit defmap_with_signature. eapply H. i. eauto. i.
      exploit Genv.invert_find_symbol. eapply SYMBSKENV. i. rewrite <- H0 in H1.
      exploit Genv.find_invert_symbol. eauto. i. rewrite H2. ss. rewrite H. eauto.
  Qed.

  Lemma prog_find_defs_same_rev
        cp b if_sig
        (FOC: is_focus cp)
        (FIND: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) b = Some (Gfun (Internal if_sig))) :
      Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) b = Some (Gfun (Internal if_sig)).
  Proof.
    exploit prog_find_defs_same_rev2; eauto. ss.
  Qed.

  Lemma field_offset_same
        cp f0 co delta
        (FOC : linkorder_program cp cp_link)
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (COMPLETE : complete_members (prog_comp_env cp) (co_members co) = true) :
      field_offset (prog_comp_env cp) f0 (co_members co) = Errors.OK delta <->
      field_offset (prog_comp_env cp_link) f0 (co_members co) = Errors.OK delta.
  Proof.
    unfold field_offset in *.
    remember 0 as n. clear Heqn.
    revert COMPLETE FOC EXTENDS.
    revert cp delta f0 n.
    induction (co_members co) as [| mhd mtl]; try (by ss); i.
    ss. destruct mhd.
    assert (ALIGN: (align n (alignof (prog_comp_env cp) t)) = (align n (alignof (prog_comp_env cp_link) t))).
    { clear -COMPLETE EXTENDS.
      revert t n cp cp_link COMPLETE EXTENDS.
      induction t; ss; i; unfold align_attr; des_ifs; auto.
      - exploit EXTENDS; eauto. i. Eq. auto.
      - exploit EXTENDS; eauto. i. Eq.
      - exploit EXTENDS; eauto. i. Eq. auto.
      - exploit EXTENDS; eauto. i. Eq. }
    des_ifs.
    - rewrite ALIGN. auto.
    - rewrite ALIGN in *.
      eapply andb_prop in COMPLETE. des; auto.
      exploit IHmtl; eauto.
      intros. erewrite H.
      erewrite <- sizeof_stable; eauto.
  Qed.

  Lemma sem_add_ptr_int_same1
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 ty0 si v
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Oadd (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC)
        (CLASSADD : classify_add ty1 ty2 = add_case_pi ty0 si):
    sem_add_ptr_int (prog_comp_env cp) ty0 si v1 v2 = Some v
    <-> sem_add_ptr_int (prog_comp_env cp_link) ty0 si v1 v2 = Some v.
  Proof.
    exploit types_of_context1; eauto. intros [tys [A B]].
    unfold classify_add in CLASSADD; des_ifs; try (des; clarify); unfold sem_add_ptr_int in *; des_ifs.
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
  Qed.

  Lemma sem_add_ptr_int_same2
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 ty0 si v
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Oadd (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC)
        (CLASSADD : classify_add ty1 ty2 = add_case_ip si ty0):
    sem_add_ptr_int (prog_comp_env cp) ty0 si v2 v1 = Some v
    <-> sem_add_ptr_int (prog_comp_env cp_link) ty0 si v2 v1 = Some v.
  Proof.
    exploit types_of_context1; eauto. intros [tys [A B]].
    unfold classify_add in CLASSADD; des_ifs; try (des; clarify); unfold sem_add_ptr_int in *; des_ifs.
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq0; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq0; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
  Qed.

  Lemma sem_add_ptr_long_same1
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 ty0 v
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Oadd (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC)
        (CLASSADD : classify_add ty1 ty2 = add_case_pl ty0):
    sem_add_ptr_long (prog_comp_env cp) ty0 v1 v2 = Some v
    <-> sem_add_ptr_long (prog_comp_env cp_link) ty0 v1 v2 = Some v.
  Proof.
    exploit types_of_context1; eauto. intros [tys [A B]].
    unfold classify_add in CLASSADD; des_ifs; try (des; clarify); unfold sem_add_ptr_long in *; des_ifs.
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
    - erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
  Qed.

  Lemma sem_add_ptr_long_same2
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 ty0 v
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Oadd (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC)
        (CLASSADD : classify_add ty1 ty2 = add_case_lp ty0):
    sem_add_ptr_long (prog_comp_env cp) ty0 v2 v1 = Some v
    <-> sem_add_ptr_long (prog_comp_env cp_link) ty0 v2 v1 = Some v.
  Proof.
    exploit types_of_context1; eauto. intros [tys [A B]].
    unfold classify_add in CLASSADD; des_ifs; try (des; clarify); unfold sem_add_ptr_long in *; des_ifs.
    - des_ifs; erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq0; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
    - des_ifs; erewrite wt_type_sizeof_stable; eauto; inv WTTGT; ss.
      unfold typeconv in Heq0; des_ifs; ss; clarify.
      { exploit (WTYE (Tpointer ty0 a1)). eapply B. ss. auto. i. ss. }
      { exploit (WTYE (Tarray ty0 z a1)). eapply B. ss. auto. i. ss. }
  Qed.

  Lemma sem_sub_same
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 k0 v
        (WTSRC : wt_state cp_link ge_cp_link (ExprState f (CC (Ebinop Osub (Eval v1 ty1) (Eval v2 ty2) ty)) (app_cont k k0) e m'))
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Osub (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC):
    sem_sub (prog_comp_env cp) v1 ty1 v2 ty2 m' = Some v
    <-> sem_sub (prog_comp_env cp_link) v1 ty1 v2 ty2 m' = Some v.
  Proof.
    exploit types_of_context1; eauto. intros [tys [A B]].
    unfold sem_sub.
    inv WTTGT; inv WTSRC; ss.
    destruct (classify_sub ty1 ty2) eqn:ClASSIFY; unfold classify_sub in *.
    all: try erewrite wt_type_sizeof_stable in *; eauto.
    - unfold typeconv in *.
      des_ifs; ss; clarify;
        try (by exploit (WTYE (Tpointer ty0 a0)); try eapply B; ss; auto; i; ss);
        try (by exploit (WTYE (Tarray ty0 z a0)); try eapply B; ss; auto; i; ss).
      exploit (WTYE (Tpointer ty0 a2)); try eapply B; ss; auto; i; ss.
      exploit (WTYE (Tarray ty0 z a2)); try eapply B; ss; auto; i; ss.
    - des_ifs; ss; clarify.
      unfold typeconv in *. des_ifs; ss; clarify;
        try (by exploit (WTYE (Tpointer ty0 a0)); try eapply B; ss; auto; i; ss);
        try (by exploit (WTYE (Tarray ty0 z0 a0)); try eapply B; ss; auto; i; ss).
      exploit (WTYE (Tpointer ty0 a2)); try eapply B; ss; auto; i; ss.
      exploit (WTYE (Tarray ty0 z a2)); try eapply B; ss; auto; i; ss.
      exploit (WTYE (Tarray ty0 z a0)); try eapply B; ss; auto; i; ss.
    - des_ifs; ss; clarify.
      unfold typeconv in *. des_ifs; ss; clarify.
      exploit (WTYE (Tpointer ty0 a2)); try eapply B; ss; auto; i; ss.
      exploit (WTYE (Tarray ty0 z a2)); try eapply B; ss; auto; i; ss.
  Qed.

  Lemma sem_add_same
        cp f v1 ty1 v2 ty2 ty CC k e m' k1 k2 v
        (WTTGT : wt_state cp (geof cp) (ExprState f (CC (Ebinop Oadd (Eval v1 ty1) (Eval v2 ty2) ty)) k e m'))
        (EXTENDS : forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (CTX : context k1 k2 CC):
    sem_add (prog_comp_env cp) v1 ty1 v2 ty2 m' = Some v
    <-> sem_add (prog_comp_env cp_link) v1 ty1 v2 ty2 m' = Some v.
  Proof.
    unfold sem_add in *. des_ifs.
    - exploit sem_add_ptr_int_same1; eauto.
    - exploit sem_add_ptr_long_same1; eauto.
    - exploit sem_add_ptr_int_same2; eauto.
    - exploit sem_add_ptr_long_same2; eauto.
  Qed.

  Lemma free_list_exists
        cp m e m'
        (WTENV: forall id blk ty, e ! id = Some (blk, ty) -> wt_type (prog_comp_env cp) ty)
        (EXTENDS : forall (id : positive) (cmp : composite),
            (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (FREE : Mem.free_list m (blocks_of_env (geof cp_link) e) = Some m') :
      Mem.free_list m (blocks_of_env (geof cp) e) = Some m'.
  Proof.
    unfold blocks_of_env, block_of_binding in *. ss.
    assert (WTENV0: forall p blk ty, In (p, (blk, ty)) (PTree.elements e) -> wt_type (prog_comp_env cp) ty).
    { i. exploit PTree.elements_complete; eauto. }
    revert FREE EXTENDS WTENV WTENV0. revert m' cp m.
    induction (PTree.elements e); ss. ii; eauto.
    i. des_ifs.
    - erewrite wt_type_sizeof_stable in Heq0; eauto. Eq.
      exploit IHl; eauto.
      { specialize (WTENV0 p b t). exploit WTENV0; eauto. }
    - erewrite wt_type_sizeof_stable in Heq0; eauto. Eq.
      { specialize (WTENV0 p b t). exploit WTENV0; eauto. }
  Qed.

  Lemma free_list_same
        cp m e m'
        (WTENV: forall id blk ty, e ! id = Some (blk, ty) -> wt_type (prog_comp_env cp) ty)
        (EXTENDS : forall (id : positive) (cmp : composite),
            (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (FREE : Mem.free_list m (blocks_of_env (geof cp) e) = Some m'):
      Mem.free_list m (blocks_of_env ge_cp_link e) = Some m'.
  Proof.
    unfold blocks_of_env, block_of_binding in *. ss.
    assert (WTENV0: forall p blk ty, In (p, (blk, ty)) (PTree.elements e) -> wt_type (prog_comp_env cp) ty).
    { i. exploit PTree.elements_complete; eauto. }
    revert FREE EXTENDS WTENV WTENV0. revert m' cp m.
    induction (PTree.elements e); ss. ii.
    des_ifs.
    - erewrite <- wt_type_sizeof_stable in Heq0; eauto. Eq.
      exploit IHl; eauto.
      { specialize (WTENV0 p b t). exploit WTENV0; eauto. }
    - erewrite <- wt_type_sizeof_stable in Heq0; eauto. Eq.
      { specialize (WTENV0 p b t). exploit WTENV0; eauto. }
  Qed.

  Lemma alignof_blockcopy_wt_stable:
    forall t ce ce' (extends: forall id co, ce!id = Some co -> ce'!id = Some co),
    wt_type ce t = true ->
    alignof_blockcopy ce t = alignof_blockcopy ce' t.
  Proof.
    induction t; simpl; intros; auto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
  Qed.

  Lemma alloc_variables_same
        cp f m e m1
        (WT : Forall (fun t : type => wt_type (prog_comp_env cp) t) (map snd (fn_params f ++ fn_vars f)))
        (EXTENDS: forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (ALLOC : alloc_variables (geof cp) empty_env m (fn_params f ++ fn_vars f) e m1):
      alloc_variables ge_cp_link empty_env m (fn_params f ++ fn_vars f) e m1.
  Proof.
    assert (EMPTY:forall i blk ty, empty_env ! i = Some (blk, ty) -> wt_type (prog_comp_env cp) ty).
    { ii. erewrite PTree.gempty in H. clarify. }
    remember (fn_params f ++ fn_vars f) as l.
    remember empty_env as ev.
    clear Heqev Heql.
    ginduction l; i; ss; inv ALLOC.
    - econs.
    - econs; eauto.
      + ss. erewrite <- wt_type_sizeof_stable; eauto.
        inv WT. eauto.
      + eapply IHl; eauto.
        { inv WT; eauto. }
        i. destruct (classic (id = i)).
        { subst. rewrite PTree.gss in H. clarify. inv WT; auto. }
        rewrite PTree.gso in H; eauto.
  Qed.

  Lemma bind_parameters_same
        cp f vargs  m1 e m2
        (WT : Forall (fun t : type => wt_type (prog_comp_env cp) t) (map snd (fn_params f ++ fn_vars f)))
        (EXTENDS: forall id cmp, (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (BIND : bind_parameters skenv_link (geof cp) e m1 (fn_params f) vargs m2):
      bind_parameters skenv_link ge_cp_link e m1 (fn_params f) vargs m2.
  Proof.
    assert (EMPTY:forall i blk ty, empty_env ! i = Some (blk, ty) -> wt_type (prog_comp_env cp) ty).
    { ii. erewrite PTree.gempty in H. clarify. }
    remember (fn_params f) as l.
    clear Heql.
    ginduction l; i; ss; inv BIND.
    - econs.
    - econs; eauto.
      + inv H3; try (by econs; eauto).
        inv WT.
        econs 3; ss; eauto;
          try (by (erewrite <- alignof_blockcopy_wt_stable; eauto));
          try (by (erewrite <- wt_type_sizeof_stable; eauto)).
      + exploit IHl; eauto.
        { instantiate (1:=f). ss. inv WT. eauto. }
  Qed.

  Lemma preservation_alloc
        cp_top m1 e l m0
        (FOCUS1 : is_focus cp_top)
        (ALLOC : alloc_variables ge_cp_link empty_env m0 l e m1)
        (COMP : Forall (fun t : type => wt_type (prog_comp_env cp_top) t) (map snd l)):
      alloc_variables (geof cp_top) empty_env m0 l e m1.
  Proof.
    induction ALLOC.
    - econs.
    - ss. inv COMP.
      assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
      { i. exploit link_list_linkorder; eauto. intro ORD. r in ORD. rewrite Forall_forall in ORD.
        exploit ORD; et. intro ORD0. ss. rr in ORD0. des. et. }
      exploit wt_type_sizeof_stable; eauto.
      i. eapply IHALLOC in H3.
      econs; eauto. ss. rewrite H1. eauto.
  Qed.

  Lemma preservation_bind_param
        cp_top m1 e l l' m2 vs_arg
        (FOCUS1 : is_focus cp_top)
        (PARAM : bind_parameters skenv_link ge_cp_link e m1 l vs_arg m2)
        (COMP : Forall (fun t : type => wt_type (prog_comp_env cp_top) t) (map snd (l ++ l'))):
      bind_parameters skenv_link (geof cp_top) e m1 l vs_arg m2.
  Proof.
    induction PARAM.
    - econs.
    - ss. inv COMP.
      exploit IHPARAM; eauto. i. econs; eauto. inv H0.
      * econs; eauto.
      * econs 2; eauto.
      * assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
        { i. exploit link_list_linkorder; eauto. intro ORD. r in ORD. rewrite Forall_forall in ORD.
          exploit ORD; et. intro ORD0. ss. rr in ORD0. des_safe. et. }
        des; econs 3; eauto; ss;
          destruct ty; ss; des_ifs; exploit H0; eauto; i; rewrite Heq0 in H10; inv H10; eauto.
  Qed.

  Scheme statement_ind2 := Induction for statement Sort Prop
    with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.

  Lemma find_label_same_None
        tl_tgt k0 lbl s k
        (SUM : sum_cont tl_tgt k0)
        (LABEL : find_label lbl s k = None) :
      find_label lbl s (app_cont k k0) = None.
  Proof.
    revert_until s. revert s lbl k0 tl_tgt.
    eapply (statement_ind2 (fun s => forall lbl k0 tl_tgt k,
                               sum_cont tl_tgt k0 ->
                               find_label lbl s k = None -> find_label lbl s (app_cont k k0) = None)
                          (fun sl => forall K lbl k0 tl_tgt k,
                               sum_cont tl_tgt k0 ->
                               find_label_ls lbl sl k = None -> find_label_ls lbl sl (app_cont k k0) = None)
           ); ss; i; ss; des_ifs; (try exploit H; eauto; ss; i; try Eq).
    - exploit H1; eauto. i. ss. Eq.
    - exploit H0; eauto.
  Qed.

  Lemma find_label_same_None'
        tl_tgt k0 lbl s k k'
        (SUM : sum_cont tl_tgt k0)
        (LABEL : find_label lbl s k = None) :
      find_label lbl s k' = None.
  Proof.
    revert_until s. revert s lbl k0 tl_tgt.
    eapply (statement_ind2 (fun s => forall lbl k0 tl_tgt k k',
                               sum_cont tl_tgt k0 ->
                               find_label lbl s k = None -> find_label lbl s k' = None)
                          (fun sl => forall K lbl k0 tl_tgt k k',
                               sum_cont tl_tgt k0 ->
                               find_label_ls lbl sl k = None -> find_label_ls lbl sl k' = None)
           ); ss; i; ss; des_ifs; (try exploit H; eauto; ss; i; try Eq).
    - rewrite H3 in Heq. clarify.
    - rewrite H3 in Heq. clarify.
    - rewrite H4 in Heq. clarify.
    - exploit H1; eauto. i. rewrite H5 in Heq0. clarify.
    - rewrite H3 in Heq. clarify.
      Unshelve. all:auto.
  Qed.

  Lemma find_label_exists
        tl_tgt k0 lbl s k s' k' k1
        (SUM : sum_cont tl_tgt k0)
        (LABEL : find_label lbl s k = Some (s', k')) :
      exists k1', find_label lbl s k1 = Some (s', k1').
  Proof.
    revert SUM. revert_until s.
    revert lbl k0 tl_tgt. clear INCL_FOCUS.
    eapply (statement_ind2 (fun s =>  forall lbl k0 tl_tgt k s' k' k1,
                               find_label lbl s k = Some (s', k') ->
                               sum_cont tl_tgt k0 -> exists k1', find_label lbl s k1 = Some (s', k1'))
                          (fun sl => forall lbl k0 tl_tgt k s' k' k1,
                               sum_cont tl_tgt k0 ->
                               find_label_ls lbl sl k = Some (s', k') -> exists k1', find_label_ls lbl sl k1 = Some (s', k1'))
           ); ss; ii;
      try (by (i; des_ifs; eauto));
      try (by (des_ifs; exploit H; eauto)).
    - i. des_ifs.
      + exploit H; eauto. i. des. rewrite H1 in Heq. clarify. eauto.
      + exploit find_label_same_None'; eauto. i. rewrite H3 in Heq. clarify.
      + exploit find_label_same_None'; eauto. i. rewrite H1 in Heq0. clarify.
      + exploit H0; eauto.
    - i. des_ifs.
      + exploit H; eauto. i. des. rewrite H1 in *. clarify. eauto.
      + exploit find_label_same_None'; eauto. i. rewrite H3 in Heq. clarify.
      + exploit find_label_same_None'; eauto. i. rewrite H1 in Heq0. clarify.
      + exploit H0; eauto.
    - i. des_ifs.
      + i. exploit H; eauto. ss. i. des. rewrite H2 in *. eauto.
      + exploit find_label_same_None'; eauto; ss. i. rewrite H2 in *. clarify.
      + exploit find_label_same_None'; try eapply Heq0; eauto; ss. i. rewrite H4 in *. clarify.
      + i. exploit H; eauto. ss. i. des. rewrite H2 in *. clarify.
      + i. exploit H1; eauto. ss. i. des. rewrite H2 in *. clarify. eauto.
      + exploit find_label_same_None'; try eapply Heq2; eauto; ss. i. rewrite H4 in *. clarify.
      + i. exploit H; eauto. ss. i. des. rewrite H2 in *. clarify.
      + i. exploit H1; eauto. ss. i. des. rewrite H2 in *. clarify.
      + i. exploit H0; eauto.
    - i. des_ifs; eauto.
      + exploit H; eauto. i. des. rewrite H2 in *. clarify. eauto.
      + exploit find_label_same_None'; eauto. i. rewrite H3 in *. clarify.
      + exploit H; eauto. i. des. rewrite H2 in *. clarify.
  Qed.

  Lemma find_label_same
        tl_tgt k0 lbl s k s' k'
        (SUM : sum_cont tl_tgt k0)
        (LABEL : find_label lbl s k = Some (s', k')) :
      find_label lbl s (app_cont k k0) = Some (s', app_cont k' k0).
  Proof.
    revert SUM. revert_until s.
    revert lbl k0 tl_tgt. clear INCL_FOCUS.
    eapply (statement_ind2 (fun s =>  forall lbl k0 tl_tgt k s' k',
                               find_label lbl s k = Some (s', k') ->
                               sum_cont tl_tgt k0 -> find_label lbl s (app_cont k k0) = Some (s', app_cont k' k0))
                          (fun sl => forall lbl k0 tl_tgt k s' k',
                               sum_cont tl_tgt k0 ->
                               find_label_ls lbl sl k = Some (s', k') -> find_label_ls lbl sl (app_cont k k0) = Some (s', app_cont k' k0))
           ); ss; ii;
      try (by (i; des_ifs; eauto));
      try (by (des_ifs; exploit H; eauto)).
    - i. des_ifs.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit find_label_same_None; eauto; ss. i. Eq.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit H0; eauto; ss; i; Eq; auto.
    - i. des_ifs.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit find_label_same_None; eauto; ss. i. Eq.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit H0; eauto; ss; i; Eq; auto.
    - i. des_ifs.
      + i. exploit H; eauto. ss. i. Eq. auto.
      + exploit find_label_same_None; eauto; ss. i. Eq.
      + exploit find_label_same_None; try eapply Heq0; eauto; ss. i. Eq.
      + i. exploit H; eauto. ss. i. Eq.
      + i. exploit H1; eauto. ss. i. Eq. auto.
      + exploit find_label_same_None; try eapply Heq2; eauto; ss. i. Eq.
      + i. exploit H; eauto. ss. i. Eq.
      + i. exploit H1; eauto. ss. i. Eq.
      + i. exploit H0; eauto.
    - i. des_ifs.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit find_label_same_None; eauto; ss. i. Eq.
      + exploit H; eauto; ss; i; Eq; auto.
      + exploit H0; eauto; ss; i; Eq; auto.
  Qed.

  Hypothesis WFSRC: forall md : Mod.t, In md prog_src -> Sk.wf md.
  Hypothesis WFTGT: forall md : Mod.t, In md prog_tgt -> Sk.wf md.

  Lemma lred_progress
        cp f C a k3 k0 e m a' m'
        (FOC: is_focus cp)
        (CTX: context LV RV C)
        (WTSRC: wt_state cp_link ge_cp_link (ExprState f (C a) (app_cont k3 k0) e m))
        (WTTGT: wt_state cp (geof cp) (ExprState f (C a) k3 e m))
        (EXTENDS: forall (id : positive) (cmp : composite),
            (prog_comp_env cp) ! id = Some cmp -> (prog_comp_env cp_link) ! id = Some cmp)
        (LRED: lred ge_cp_link e a m a' m'):
      exists a1 m1, lred (geof cp) e a m a1 m1.
  Proof.
    inv LRED.
    - do 2 eexists. econs; eauto.
    - ss. inv WTTGT; ss.
      exploit wt_rvalue_wt_expr; eauto. ss. eauto. i.
      inv H1. ss. eapply WTTENV in H3. des; Eq.
      do 2 eexists. econs 2; eauto.
    - do 2 eexists. econs 3; eauto.
    - exploit types_of_context1; eauto. intros [tys [A B]].
      inv WTTGT. ss. exploit (WTYE (Tstruct id a0)).
      eapply B. ss. auto. i. inv H1. des_ifs.
      do 2 eexists. econs 4; eauto; ss.
      erewrite field_offset_same; eauto. exploit EXTENDS; eauto. i. Eq. eauto.
      unfold linkorder_program. split; eauto.
      exploit link_list_linkorder; eauto. i. rr in H1. rewrite Forall_forall in H1.
      exploit H1; eauto. i. clear - H2. unfold linkorder_program in *. ss.
      unfold linkorder_program in H2. ss. des; eauto.
      hexploit (prog_comp_env_eq cp); et. intro X.
      exploit build_composite_env_consistent; et. intro Y.
      exploit co_consistent_complete; et.
    - exploit types_of_context1; eauto. intros [tys [A B]].
      inv WTTGT. ss. exploit (WTYE (Tunion id a0)).
      eapply B. ss. auto. i. inv H0. des_ifs.
      do 2 eexists. econs 5; eauto.
  Qed.

  Lemma match_focus_state_bsim
        cst_src0 cst_tgt0 cst_tgt1 k0 cp tr
        (ST: match_focus_state cst_src0 cst_tgt0 k0)
        (ISFOC: is_focus cp)
        (WTSRC: wt_state cp_link (geof cp_link) cst_src0)
        (WTTGT: wt_state cp (geof cp) cst_tgt0)
        (STEP: Csem.step skenv_link (geof cp) cst_tgt0 tr cst_tgt1)
        tl_tgt
        (SUM: sum_cont tl_tgt k0):
      <<STEP: Csem.step skenv_link (geof cp_link) cst_src0 tr (matched_state_source cst_tgt1 k0)>>.
  Proof.
    assert (FOC: linkorder cp cp_link).
    { exploit link_list_linkorder; eauto. i. rr in H.
      rewrite Forall_forall in H. exploit H; eauto. }
    pose cst_tgt1 as XXX.
    assert(EXTENDS: forall id cmp (IN: (prog_comp_env cp) ! id = Some cmp),
              <<IN: (prog_comp_env cp_link) ! id = Some cmp>>).
    { Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.
      unfold linkorder_program in FOC. inv FOC. eauto. }
    unfold NW in *.
    rr in STEP. des.
    - inv STEP; inv ST.
      (* lred *)
      + left; econs; eauto.
        inv H; try (by econs; ss; eauto).
        * econs 2; eauto. ss.
          unfold Genv.find_symbol in *. ss. rewrite MapsC.PTree_filter_key_spec in *.
          des_ifs. inv FOC. inv H. ss. des.
          rewrite CSk.of_program_defs in *.
          assert (defs cp x) by auto. rewrite <- defs_prog_defmap in *. des.
          exploit H6; eauto. i. des.
          assert (defs cp_link x).
          { rewrite <- defs_prog_defmap. exists gd2. eauto. } clarify.
        * econs; ss; eauto.
          hexploit (prog_comp_env_eq cp); et. intro X.
          exploit build_composite_env_consistent; et. intro Y.
          exploit co_consistent_complete; et. intro Z.
          erewrite <- field_offset_same; eauto.
      (* rred *)
      + left. econs; eauto.
        rename C into CC.
        inversion WTTGT; subst; ss. exploit types_of_context1; eauto. intros [tys [A B]].
        inv H; try (econs; ss; eauto); ss.
        * destruct op; ss.
          { erewrite <- sem_add_same; eauto. }
          { erewrite <- sem_sub_same; eauto. }
        * rpapply red_sizeof; eauto. ss.
          erewrite wt_type_sizeof_stable; eauto.
          clear - H0 WTTGT WTYE B.
          exploit (WTYE ty1); eauto.
          eapply B. ss. auto.
        * rpapply red_alignof; eauto. ss.
          erewrite wt_type_alignof_stable; eauto.
          clear - H0 WTTGT WTYE B.
          exploit (WTYE ty1); eauto.
          eapply B. ss. auto.
        * inv H2; try (by econs; eauto).
          econs 3; ss; eauto.
          { erewrite <- alignof_blockcopy_wt_stable; eauto.
            exploit (WTYE); try eapply B; ss; auto; i; ss. }
          { erewrite <- alignof_blockcopy_wt_stable; eauto.
            exploit (WTYE); try eapply B; ss; auto; i; ss. }
          { erewrite <- wt_type_sizeof_stable; eauto.
            inv WTTGT; ss. exploit (WTYE ty1); eauto. eapply B. ss. auto. }
          { erewrite <- wt_type_sizeof_stable; eauto.
            inv WTTGT; ss. exploit (WTYE ty1); eauto. eapply B. ss. auto. }
      + left. econs; eauto.
      + left. econs; eauto. ii. eapply H0.
        inv H1.
        * econs 1; eauto.
        * econs 2; eauto.
        (* lred progress *)
        * exploit context_compose. eapply H. eauto. i.
          exploit lred_progress; eauto; ss; eauto. i. des.
          econs 3; eauto.
        * inv H2; try (by (econs 4; eauto; econs; eauto)).
          { econs 4; eauto. econs 4; eauto. ss. unfold sem_binary_operation in *. des_ifs; eauto.
            - exploit context_compose. eapply H. eapply H3. i.
              erewrite sem_add_same; eauto. ss. eauto.
            - exploit context_compose. eapply H. eapply H3. i.
              erewrite sem_sub_same; try eapply H2. eauto. eapply WTSRC. eapply WTTGT. eauto. }
          { exploit context_compose. eapply H. eauto. i.
            inversion WTTGT; subst; ss. exploit types_of_context1; eauto. intros [tys [A B]].
            inv H4; econs 4; eauto; econs; eauto.
            - econs 1; eauto.
            - econs 2; eauto.
            - econs 3; eauto; ss.
              + erewrite alignof_blockcopy_wt_stable; eauto.
                exploit (WTYE); try eapply B; ss; auto; i; ss.
              + erewrite alignof_blockcopy_wt_stable; eauto.
                exploit (WTYE); try eapply B; ss; auto; i; ss.
              + erewrite wt_type_sizeof_stable; eauto.
                exploit (WTYE ty1); eauto. eapply B. ss. auto.
              + erewrite wt_type_sizeof_stable; eauto.
                exploit (WTYE ty1); eauto. eapply B. ss. auto. }
        * econs 5; eauto.
    - right.
      inv STEP; inv ST; try (by econs; eauto).
      + ss. rpapply step_return_0; eauto.
        * inv WTTGT; ss.
          exploit free_list_same; eauto.
        * erewrite call_cont_app_cont; et.
      + ss. rpapply step_return_2; eauto.
        * inv WTTGT; ss.
          exploit free_list_same; eauto.
        * erewrite call_cont_app_cont; et.
      + ss. eapply step_skip_call; eauto.
        * exploit Cstrategy.is_call_cont_call_cont; et. intro T.
          clear - H T SUM. unfold is_call_cont in H. des_ifs. ss. inv SUM; ss. des; clarify.
        * inv WTTGT; ss.
          exploit free_list_same; eauto.
      + ss. eapply step_goto; et.
        clear -H SUM.
        erewrite <- call_cont_app_cont; et.
        remember (fn_body f) as s. clear Heqs.
        remember (call_cont k) as k1. clear Heqk1.
        exploit find_label_same; eauto.
      + inversion WTTGT; subst; ss.
        exploit WTLOCAL; eauto. intros WT.
        eapply step_internal_function; et.
        * ss. unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          exploit prog_find_defs_same_rev; eauto.
        * exploit alloc_variables_same; eauto.
        * exploit bind_parameters_same; eauto.
      + destruct (classic (is_external_ef ef)) eqn:EXT.
        * unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          exploit CSkEnv.project_revive_no_external; eauto.
          eapply SkEnv.load_skenv_wf; eauto.
          { eapply link_sk_preserves_wf_sk; eauto. }
          clarify.
        * eapply step_external_function; eauto.
          { instantiate (1:=cc). instantiate (1 := tres). instantiate (1 := targs).
            unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            exploit prog_find_defs_same_rev2; eauto. ss.
            destruct ef; ss. }
          { ss. }
        Unshelve. all: auto.
  Qed.

  Lemma match_focus_state_progress
        cst_src0 cst_tgt0 cst_src1 k0 cp tr
        (NCALLTGT : ~ exists args, at_external skenv_link cp cst_tgt0 args)
        (NCALLSRC : ~ exists args, at_external skenv_link cp_link cst_src0 args)
        (NRETTGT : ~ ModSem.is_return (modsem skenv_link cp) cst_tgt0)
        (NRETSRC : ~ ModSem.is_return (modsem skenv_link cp_link) cst_src0)
        (ST: match_focus_state cst_src0 cst_tgt0 k0)
        (ISFOC: is_focus cp)
        (WTSRC: wt_state cp_link (geof cp_link) cst_src0)
        (WTTGT: wt_state cp (geof cp) cst_tgt0)
        (STEP: Csem.step skenv_link (geof cp_link) cst_src0 tr cst_src1)
        tl_tgt
        (SUM: sum_cont tl_tgt k0):
      (<<STEP: exists cst_tgt1, Csem.step skenv_link (geof cp) cst_tgt0 tr cst_tgt1>>).
  Proof.
    assert (FOC: linkorder cp cp_link).
    { exploit link_list_linkorder; eauto. i. rr in H.
      rewrite Forall_forall in H. exploit H; eauto. }
    pose cst_src1 as XXX.
    assert(EXTENDS: forall id cmp (IN: (prog_comp_env cp) ! id = Some cmp),
              <<IN: (prog_comp_env cp_link) ! id = Some cmp>>).
    { Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.
      unfold linkorder_program in FOC. inv FOC. eauto. }
    unfold NW in *.
    rr in STEP. des.
    - inv STEP; inv ST.
      (* lred *)
      + exploit lred_progress; eauto. i. des.
        eexists. left. econs; eauto.
      (* rred *)
      + rename C into CC.
        inversion WTTGT; subst; ss. exploit types_of_context1; eauto. intros [tys [A B]].
        inv H; try by (eexists; econs; econs 2; eauto; econs; eauto).
        * eexists; econs; econs 2; eauto; econs; eauto.
          destruct op; ss; eauto.
          { erewrite sem_add_same; eauto. }
          { erewrite sem_sub_same; eauto. }
        * eexists. econs. econs 2; eauto. econs; eauto.
          inv H2; try (by econs; eauto).
          econs 3; ss; eauto.
          { erewrite alignof_blockcopy_wt_stable; eauto.
            exploit (WTYE); try eapply B; ss; auto; i; ss. }
          { erewrite alignof_blockcopy_wt_stable; eauto.
            exploit (WTYE); try eapply B; ss; auto; i; ss. }
          { erewrite wt_type_sizeof_stable; eauto.
            inv WTTGT; ss. exploit (WTYE ty1); eauto. eapply B. ss. auto. }
          { erewrite  wt_type_sizeof_stable; eauto.
            inv WTTGT; ss. exploit (WTYE ty1); eauto. eapply B. ss. auto. }
      + eexists. econs. econs 3; eauto.
      + eexists. econs. econs 4; eauto. ii. eapply H0. inv H1.
        * econs 1; eauto.
        * econs 2; eauto.
        * inv H2.
          { econs 3; eauto.
            instantiate (1:= m'). instantiate (1:=(Eloc b Ptrofs.zero ty)). econs; eauto. }
          { ss. econs 3; eauto. econs 2; eauto. ss.
            instantiate (1 := b).
            unfold Genv.find_symbol in *. ss.
            rewrite PTree_filter_key_spec in *. des_ifs.
            rewrite CSk.of_program_defs in *.
            assert (defs cp x) by ss.
            assert (~ defs cp_link x) by (ii; clarify).
            rewrite <- defs_prog_defmap in *. des.
            exfalso. eapply H5.
            destruct gd.
            - exploit prog_defmap_exists_rev; eauto. i. des.
              exists (Gfun func'). eauto.
            - exploit prog_defmap_gvar_exists_rev; eauto. i. des.
              exists (Gvar var'). eauto. }
          { econs 3; eauto. ss. econs 3; eauto. }
          { exploit context_compose. eapply H. eauto. i.
            exploit types_of_context1; eauto. intros [tys [A B]].
            inv WTTGT. ss. exploit (WTYE (Tstruct id a)).
            eapply B. ss. auto. i. inv H5. des_ifs.
            econs 3; eauto. ss. econs 4; eauto; ss.
            erewrite <- field_offset_same; eauto. exploit EXTENDS; eauto. i. Eq. eauto.
            hexploit (prog_comp_env_eq cp); et. intro X.
            exploit build_composite_env_consistent; et. intro Y.
            exploit co_consistent_complete; et. }
          { exploit context_compose. eapply H. eauto. i.
            exploit types_of_context1; eauto. intros [tys [A B]].
            inv WTTGT. ss. exploit (WTYE (Tunion id a)).
            eapply B. ss. auto. i. inv H4. des_ifs.
            econs 3; eauto. ss. econs 5; eauto. }
        * inv H2; try (by (econs 4; eauto; econs; eauto)).
          { econs 4; eauto. econs 4; eauto. ss. unfold sem_binary_operation in *. des_ifs; eauto.
            - exploit context_compose. eapply H. eapply H3. i.
              erewrite <- sem_add_same; eauto. ss. eauto.
            - exploit context_compose. eapply H. eapply H3. i.
              erewrite <- sem_sub_same; try eapply H2. eauto. eapply WTSRC. eapply WTTGT. eauto. }
          { exploit context_compose. eapply H. eauto. i.
            inversion WTTGT; subst; ss. exploit types_of_context1; eauto. intros [tys [A B]].
            inv H4; econs 4; eauto; econs; eauto.
            - econs 1; eauto.
            - econs 2; eauto.
            - econs 3; eauto; ss.
              + erewrite <- alignof_blockcopy_wt_stable; eauto.
                exploit (WTYE); try eapply B; ss; auto; i; ss.
              + erewrite <- alignof_blockcopy_wt_stable; eauto.
                exploit (WTYE); try eapply B; ss; auto; i; ss.
              + erewrite <- wt_type_sizeof_stable; eauto.
                exploit (WTYE ty1); eauto. eapply B. ss. auto.
              + erewrite <- wt_type_sizeof_stable; eauto.
                exploit (WTYE ty1); eauto. eapply B. ss. auto. }
        * econs 5; eauto.
    - ss. inversion STEP; subst; inv ST; ss; try (by eexists; right; econs; eauto);
            (try by (destruct k3; destruct k0; ss; clarify; try (by  eexists; right; econs; eauto);
                 inv SUM; unfold is_call_cont_strong in CALL; des_ifs)).
      + eexists. right.
        ss. rpapply step_return_0; eauto.
        inv WTTGT. exploit free_list_exists; eauto.
      + destruct k3; destruct k0; ss; clarify; eauto;
          inv SUM; unfold is_call_cont_strong in *; des_ifs.
        * eexists. right.
          ss. rpapply step_return_2; eauto.
          inv WTTGT. exploit free_list_exists; eauto.
        * eexists. right.
          ss. rpapply step_return_2; eauto.
          inv WTTGT. exploit free_list_exists; eauto.
      + eexists. right. ss. eapply step_skip_call; eauto.
        * exploit Cstrategy.is_call_cont_call_cont; et. intro T.
          clear - H T SUM. unfold is_call_cont in H. des_ifs. ss.
          destruct k3; destruct k0; ss.
          inv SUM; ss. des; clarify.
          destruct k3; ss.
          destruct k3; ss.
        * inv WTTGT; ss.
          exploit free_list_exists; eauto.
      + clear -H SUM.
        erewrite <- call_cont_app_cont in H; et.
        exploit find_label_exists; eauto. i. des.
        eexists. right. ss. eapply step_goto; et.
      + eexists. right.
        destruct (lift_option (Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) fptr)) as [[gd TG] | TG].
        { assert (gd = Internal f).
          { unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            unfold Genv.find_def in *. ss.
            do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *. des_ifs.
            destruct (Genv.invert_symbol skenv_link b) eqn:SKENV; ss. unfold o_bind in Heq, Heq1. ss. des_ifs.
            destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:LINKSYMB; ss.
            destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:PROGSYMB; ss.
            unfold o_bind in FPTR, TG. ss.
            assert (i = i0).
            { destruct ((prog_defmap cp_link) ! i0) eqn:DMAP; ss; clarify.
              assert (defs cp_link i0) by (rewrite <- defs_prog_defmap; eauto).
              exploit invert_symbol_lemma2. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
            assert (i = i1).
            { destruct ((prog_defmap cp) ! i1) eqn:DMAP; ss; clarify.
              assert (defs cp i1) by (rewrite <- defs_prog_defmap; eauto).
              exploit invert_symbol_lemma1. eauto. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
            subst. destruct ((prog_defmap cp_link) ! i1) eqn:DMAP; ss.
            destruct ((prog_defmap cp) ! i1) eqn:DMAP0; ss. clarify.
            rewrite CSk.of_program_internals in *.
            unfold internals in Heq2. rewrite DMAP0 in Heq2. ss.
            exploit prog_defmap_func_same_rev; eauto. i. Eq. auto. }
          subst. inv WTTGT; ss.
          eapply step_internal_function; eauto.
          exploit preservation_alloc; eauto.
          exploit preservation_bind_param; eauto. }
        (* not call *)
        { exfalso. eapply NCALLTGT.
          eexists. econs; eauto.
          - assert (Genv.find_funct skenv_link fptr = Some (AST.Internal (signature_of_function f))).
            { assert (SkEnv.wf skenv_link).
              { eapply SkEnv.load_skenv_wf.
                eapply link_sk_preserves_wf_sk; eauto. }
              dup FPTR.
              unfold Genv.find_funct in FPTR. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
              unfold Genv.find_def in FPTR. ss.
              do 2 rewrite PTree_filter_map_spec, o_bind_ignore in *.
              des_ifs. rewrite Genv.find_funct_ptr_iff in *.
              unfold Genv.find_def. ss.
              exploit SkEnv.project_impl_spec. eapply INCL_LINKED. i. inv H3.
              destruct (Genv.invert_symbol skenv_link b) eqn:SKENV; ss.
              unfold o_bind in Heq. ss. des_ifs.
              assert (Genv.find_def (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b = Some (Gfun (AST.Internal (signature_of_function f)))).
              { unfold Genv.find_def. ss. rewrite PTree_filter_map_spec, o_bind_ignore. des_ifs.
                rewrite SKENV. unfold o_bind. ss. des_ifs.
                destruct ((prog_defmap (CSk.of_program signature_of_function cp_link)) ! i) eqn:DMAP; ss. clarify.
                destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:CPLINKSYMB; ss.
                unfold o_bind in FPTR. ss.
                destruct ((prog_defmap cp_link) ! i0) eqn:DMAP0; ss. clarify.
                assert (i = i0).
                { assert (defs cp_link i0) by (rewrite <- defs_prog_defmap; eauto).
                  exploit invert_symbol_lemma2. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
                subst. clear - DMAP DMAP0.
                unfold prog_defmap in DMAP. ss.
                unfold prog_defmap in DMAP0. ss.
                unfold skdefs_of_gdefs in DMAP. ss.
                do 2 rewrite prog_defmap_update_snd in DMAP.
                rewrite DMAP0 in *. ss. }
              exploit DEFKEPT; eauto. i. des.
              inv LO. inv H6.  eauto. }
              esplits; eauto. ss.
              unfold signature_of_function. unfold signature_of_type. ss.
              f_equal. remember (fn_params f) as l. clear Heql. clear.
              induction l. ss. ss. destruct a. ss. clarify. rewrite H0. ss.
          - inv WTTGT. ss. inv WTK; ss.
            exploit WTKS.
            { ii. unfold fundef in *. Eq. }
            i. des. clarify. }
      + eexists. right.
        destruct (lift_option (Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) fptr)) as [[gd TG] | TG].
        { assert (gd = (External ef targs tres cc)).
          { unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            unfold Genv.find_def in *. ss.
            do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *. des_ifs.
            destruct (Genv.invert_symbol skenv_link b) eqn:SKENV; ss. unfold o_bind in Heq, Heq1. ss. des_ifs.
            destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:LINKSYMB; ss.
            destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:PROGSYMB; ss.
            unfold o_bind in FPTR, TG. ss.
            assert (i = i0).
            { destruct ((prog_defmap cp_link) ! i0) eqn:DMAP; ss; clarify.
              assert (defs cp_link i0) by (rewrite <- defs_prog_defmap; eauto).
              exploit invert_symbol_lemma2. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
            assert (i = i1).
            { destruct ((prog_defmap cp) ! i1) eqn:DMAP; ss; clarify.
              assert (defs cp i1) by (rewrite <- defs_prog_defmap; eauto).
              exploit invert_symbol_lemma1. eauto. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
            subst.
            destruct ((prog_defmap cp_link) ! i1) eqn:DMAP; ss.
            destruct ((prog_defmap cp) ! i1) eqn:DMAP0; ss. clarify.
            rewrite CSk.of_program_internals in *.
            unfold internals in Heq2. rewrite DMAP0 in Heq2. ss.
            exploit prog_defmap_func_same_rev; eauto. i. Eq. auto. }
          subst. eapply step_external_function; eauto. }
        (* not call *)
        { exfalso. eapply NCALLTGT.
          eexists. dup FPTR.
          unfold Genv.find_funct in FPTR. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          unfold Genv.find_def in FPTR. ss.
          do 2 rewrite PTree_filter_map_spec, o_bind_ignore in *. des_ifs.
          rewrite Genv.find_funct_ptr_iff in *.
          destruct (Genv.invert_symbol skenv_link b) eqn:SKENV; ss.
          unfold o_bind in Heq. ss. des_ifs.
          destruct ((prog_defmap (CSk.of_program signature_of_function cp_link)) ! i) eqn:DMAP; ss. clarify.
          destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:CPLINKSYMB; ss.
          unfold o_bind in FPTR. ss.
          destruct ((prog_defmap cp_link) ! i0) eqn:DMAP0; ss. clarify.
          assert (i = i0).
          { assert (defs cp_link i0) by (rewrite <- defs_prog_defmap; eauto).
            exploit invert_symbol_lemma2. eauto. erewrite CSk.of_program_defs. eauto. eauto. eauto. }
          subst.
          econs; eauto.
          - assert (Genv.find_funct skenv_link (Vptr b Ptrofs.zero) = Some (AST.External ef)).
            { assert (SkEnv.wf skenv_link).
              { eapply SkEnv.load_skenv_wf.
                eapply link_sk_preserves_wf_sk; eauto. }
              unfold Genv.find_def. ss.
              exploit SkEnv.project_impl_spec. eapply INCL_LINKED. i.
              inv H1.
              assert (Genv.find_def (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b = Some (Gfun (AST.External ef))).
              { unfold Genv.find_def. ss. rewrite PTree_filter_map_spec, o_bind_ignore. des_ifs.
                rewrite SKENV. unfold o_bind. ss. des_ifs.
                clear - DMAP DMAP0. rewrite DMAP. ss.
                unfold prog_defmap in DMAP. ss.
                unfold prog_defmap in DMAP0. ss.
                unfold skdefs_of_gdefs in DMAP. ss.
                do 2 rewrite prog_defmap_update_snd in DMAP.
                rewrite DMAP0 in *. ss. }
              exploit DEFKEPT; eauto. i. des.
              inv LO. inv H4; des_ifs; rewrite Genv.find_funct_ptr_iff; eauto. }
            esplits; eauto.
            inv WTPROGLINK.
            unfold prog_defmap in DMAP0. ss. eapply PTree_Properties.in_of_list in DMAP0.
            exploit H2; eauto. i. exploit CSTYLE_EXTERN_LINK; eauto. i. des_ifs. congruence.
          - inv WTTGT. ss.
            inv WTK; ss.
            exploit WTKS.
            { ii. unfold fundef in *. Eq. }
            i. des. clarify. }
      + destruct k3; destruct k0; ss; clarify; try (by eexists; right; econs; eauto).
        inv SUM. unfold is_call_cont_strong in CALL. des_ifs.
        ss. exfalso. eapply NRETTGT. ss. econs. unfold ModSem.final_frame. ss.
        esplits; eauto. econs; eauto.
        Unshelve. all: ss.
  Qed.

End SIM.
