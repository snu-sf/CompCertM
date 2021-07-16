Require Import CoqlibC.
Require Export GlobalenvsC.
Require Import Memory.
Require Export ASTC.
Require Import MapsC.
Require Import Values.
Require Import Linking.
Require Import Conventions1.
Require Conventions.
Require Import Integers.

Set Implicit Arguments.

Generalizable Variables F.



Definition skdef_of_gdef {F V} (get_sg: F -> signature)
           (gdef: globdef (AST.fundef F) V): globdef (AST.fundef signature) unit :=
  match gdef with
  | Gfun (Internal f) => Gfun (Internal f.(get_sg))
  | Gfun (External ef) => Gfun (External ef)
  | Gvar v => Gvar (mkglobvar tt v.(gvar_init) v.(gvar_readonly) v.(gvar_volatile))
  end.

Lemma skdef_of_gdef_is_external_gd
      F V get_sg
      (gdef: globdef (AST.fundef F) V):
    is_external_gd (skdef_of_gdef get_sg gdef) = is_external_gd gdef.
Proof. u. des_ifs. ss. clarify. Qed.

Definition skdefs_of_gdefs {F V} (get_sg: F -> signature)
           (gdefs: list (ident * globdef (AST.fundef F) V)):
  list (ident * globdef (AST.fundef signature) unit) :=
  map (update_snd (skdef_of_gdef get_sg)) gdefs.

(* Skeleton *)
Module Sk.

  Definition t := AST.program (AST.fundef signature) unit.

  Definition load_skenv: t -> Genv.t (AST.fundef signature) unit := @Genv.globalenv (AST.fundef signature) unit.
  (* No coercion! *)

  Definition load_mem: t -> option mem := @Genv.init_mem (AST.fundef signature) unit.
  (* No coercion! *)

  Definition of_program {F V} (get_sg: F -> signature) (prog: AST.program (AST.fundef F) V): t :=
    mkprogram (skdefs_of_gdefs get_sg prog.(prog_defs)) prog.(prog_public) prog.(prog_main).

  Definition wf_match_fundef CTX F1 F2 (match_fundef: CTX -> fundef F1 -> fundef F2 -> Prop)
             (fn_sig1: F1 -> signature) (fn_sig2: F2 -> signature): Prop := forall
      ctx f1 f2
      (MATCH: match_fundef ctx f1 f2),
      (<<EXT: exists ef, f1 = External ef /\ f2 = External ef>>)
      \/ (<<INT: exists fd1 fd2, f1 = Internal fd1 /\ f2 = Internal fd2 /\ <<SIG: fn_sig1 fd1 = fn_sig2 fd2>> >>).

  Definition is_external_weak F (f: AST.fundef F): bool :=
    match f with
    | Internal _ => false
    | External _ => true
    end.

  Lemma match_program_eq
        F1 V1 F2 V2 fn_sig1 fn_sig2
        `{Linker (fundef F1)} `{Linker V1}
        match_fundef match_varinfo
        (p1: AST.program (fundef F1) V1)
        (p2: AST.program (fundef F2) V2)
        (MATCH: match_program match_fundef match_varinfo p1 p2)
        (WF: wf_match_fundef match_fundef fn_sig1 fn_sig2):
      <<EQ: Sk.of_program fn_sig1 p1 = Sk.of_program fn_sig2 p2>>.
  Proof.
    rr in MATCH. des. unfold of_program. r. f_equal; ss.
    revert MATCH. generalize p1 at 1 as CTX. i. destruct p1, p2; ss. clear - MATCH WF.
    ginduction prog_defs; ii; ss; inv MATCH; ss.
    erewrite IHprog_defs; eauto. f_equal; eauto. inv H3. destruct a, b1; ss. clarify. inv H2; ss.
    - unfold update_snd. exploit WF; eauto. i; des; clarify; ss.
      + repeat f_equal. exploit WF; et.
    - inv H1. ss.
  Qed.

  Let match_fundef F0 F1 (get_sig: F0 -> F1) (_: unit): AST.fundef F0 -> AST.fundef F1 -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | Internal func1, Internal func2 => get_sig func1 = func2
      | External ef0, External ef1 => external_function_eq ef0 ef1
      | _, _ => false
      end.

  Lemma of_program_prog_defmap
        F V (p: AST.program (AST.fundef F) V) get_sg:
      <<SIM: forall id, option_rel (@Linking.match_globdef unit _ _ _ _ _
                                                           (@match_fundef _ _ get_sg) top2 tt)
                                   ((prog_defmap p) ! id) ((prog_defmap (of_program get_sg p)) ! id)>>.
  Proof.
    ii. unfold prog_defmap, of_program, skdefs_of_gdefs. ss. rewrite prog_defmap_update_snd.
    destruct ((PTree_Properties.of_list (prog_defs p)) ! id) eqn:T; ss.
    - econs; et. unfold skdef_of_gdef. des_ifs.
      + econs; et; try refl.
      + econs; et; try refl. r. des_sumbool. refl.
      + econs; et. destruct v; ss.
    - econs; et.
  Unshelve.
    all: ss.
  Qed.

  Lemma of_program_defs_names
        F V get_sg (p: AST.program (AST.fundef F) V):
      (prog_defs_names (of_program get_sg p)) = (prog_defs_names p).
  Proof.
    destruct p; ss.
    Local Opaque in_dec.
    u; ss.
    Local Transparent in_dec.
    rewrite map_map. ss.
  Qed.

  Lemma of_program_defs
        F V get_sg (p: AST.program (AST.fundef F) V):
    (defs (of_program get_sg p)) = (defs p).
  Proof.
    unfold defs. rewrite of_program_defs_names; ss.
  Qed.

  Local Opaque prog_defmap.
  Lemma of_program_internals
        F V get_sg (p: AST.program (AST.fundef F) V):
      (internals (of_program get_sg p)) = (internals p).
  Proof.
    unfold internals. destruct p; ss.
    apply Axioms.functional_extensionality. intro id; ss.
    u. exploit (of_program_prog_defmap). i. inv H.
    - rewrite <- H2. rewrite <- H1. ss.
    - des_ifs_safe. inv H2; ss. unfold match_fundef in *. des_ifs. des_sumbool. clarify.
  Qed.
  Local Transparent prog_defmap.

  Lemma of_program_internals'
        F V get_sg (p: AST.program (AST.fundef F) V):
      (internals' (of_program get_sg p)) = (internals' p).
  Proof.
    destruct p; ss. unfold internals', of_program. ss.
    apply Axioms.functional_extensionality. intro id; ss.
    unfold skdefs_of_gdefs. rewrite find_map. unfold compose. ss. unfold ident.
    replace (fun (x: positive * globdef (fundef F) V) =>
               ident_eq id (fst x) && is_external_gd (skdef_of_gdef get_sg (snd x))) with
        (fun (x: positive * globdef (fundef F) V) => ident_eq id (fst x) && is_external (snd x)).
    - u. des_ifs.
    - apply Axioms.functional_extensionality. i; ss. rewrite skdef_of_gdef_is_external_gd. ss.
  Qed.

  Lemma of_program_prog_defmap_eq
        F V get_sg (p tp : AST.program (AST.fundef F) V) id
        (EQ: (prog_defmap p) ! id = (prog_defmap tp) ! id):
      <<EQ: (prog_defmap (Sk.of_program get_sg p)) ! id = (prog_defmap (Sk.of_program get_sg tp)) ! id>>.
  Proof.
    unfold Sk.of_program. unfold prog_defmap in *. ss. unfold skdefs_of_gdefs.
    rewrite ! prog_defmap_update_snd. rewrite EQ. ss.
  Qed.

  Definition empty: t := (mkprogram [] [] 1%positive).

  Definition get_csig (skdef: (AST.fundef signature)): option signature :=
    match skdef with
    | Internal sg0 =>
      if sg0.(sig_cstyle) then Some sg0 else None
    | External ef =>
      if (ef_sig ef).(sig_cstyle) then Some (ef_sig ef) else None
    end
  .

  Definition get_sig (skdef: (AST.fundef signature)): signature :=
    match skdef with
    | Internal sg0 => sg0
    | External ef => (ef_sig ef)
    end.

  Inductive wf (sk: t): Prop :=
  | wf_intro
      (NODUP: NoDup (prog_defs_names sk)) (* list_norepet *)
      (WFPTR: forall id_fr gv id_to _ofs
          (IN: In (id_fr, (Gvar gv)) sk.(prog_defs))
          (* (IN: sk.(prog_defmap) ! id_fr = Some (Gvar gv)) *)
          (INDAT: In (Init_addrof id_to _ofs) gv.(gvar_init)),
          <<IN: In id_to (prog_defs_names sk)>>)
      (PUBINCL: incl sk.(prog_public) (prog_defs_names sk))
      (* The sum of the sizes of the function parameters must be less than INT_MAX. *)
      (WFPARAM: forall id skd
          (IN: In (id, (Gfun skd)) sk.(prog_defs)),
          4 * Conventions.size_arguments (get_sig skd) <= Ptrofs.max_unsigned).

End Sk.

Hint Unfold skdef_of_gdef skdefs_of_gdefs Sk.load_skenv Sk.load_mem Sk.empty.

(* Skeleton Genv *)
Module SkEnv.

  Definition t := Genv.t (AST.fundef signature) unit.

  Inductive wf (skenv: t): Prop :=
  | wf_intro
    (SYMBDEF: forall id blk
        (SYMB: (Genv.find_symbol skenv) id = Some blk),
       <<DEF: exists skd, (Genv.find_def skenv) blk = Some skd>>)
    (DEFSYMB: forall blk skd
        (DEF: (Genv.find_def skenv) blk = Some skd),
       <<SYMB: exists id, (Genv.find_symbol skenv) id = Some blk>>)
    (WFPARAM: forall blk skd
        (DEF: (Genv.find_def skenv) blk = Some (Gfun skd)),
        <<SIZE: 4 * Conventions.size_arguments (Sk.get_sig skd) <= Ptrofs.max_unsigned>>).

  Inductive wf_mem (skenv: t) (sk: Sk.t) (m0: mem): Prop :=
  | wf_mem_intro
      (WFPTR: forall blk_fr _ofs_fr blk_to _ofs_to id_fr _q _n gv
          (SYMB: (Genv.find_symbol skenv) id_fr = Some blk_fr)
          (* (IN: In id_fr sk.(prog_defs_names)) *)
          (IN: In (id_fr, (Gvar gv)) sk.(prog_defs))
          (NONVOL: gv.(gvar_volatile) = false)
          (DEFINITIVE: classify_init gv.(gvar_init) = Init_definitive gv.(gvar_init))
          (* (IN: sk.(prog_defmap) ! id_fr = Some (Gvar gv)) *)
          (LOAD: Mem.loadbytes m0 blk_fr _ofs_fr 1 = Some [Fragment (Vptr blk_to _ofs_to) _q _n]),
          exists id_to, (<<SYMB: (Genv.invert_symbol skenv) blk_to = Some id_to>>)
                   /\ (<<IN: In id_to (prog_defs_names sk)>>)).

  Lemma load_skenv_wf
        sk (WF: Sk.wf sk):
      <<WF: SkEnv.wf (Sk.load_skenv sk)>>.
  Proof.
    unfold Sk.load_skenv. u. econs; try r.
    - unfold Genv.globalenv, Genv.find_symbol, Genv.find_def. eapply Genv.add_globals_preserves; i; ss.
      + destruct (peq id0 id).
        { subst id0. rewrite PTree.gss in SYMB. inv SYMB. exists g. eapply PTree.gss. }
        { rewrite PTree.gso in SYMB; eauto. exploit H; eauto. i. inv H1.
          exists x. rewrite PTree.gso; eauto. exploit Genv.genv_symb_range; eauto. i. extlia. }
      + rewrite PTree.gempty in SYMB. inv SYMB.
    - intros blk skd.
      set (P := fun ge => Genv.find_def ge blk = Some skd -> exists id, Genv.find_symbol ge id = Some blk).
      assert(REC: forall l ge, P ge -> NoDup (map fst l) ->
                          (forall id, In id (map fst l) -> Genv.find_symbol ge id = None) ->
                          P (Genv.add_globals ge l)).
      { induction l as [| [id1 g1] l]; auto. i. eapply IHl.
        - unfold P, Genv.add_global, Genv.find_def, Genv.find_symbol in *. ss. i.
          destruct (peq (Genv.genv_next ge) blk).
          + subst blk. exists id1. eapply PTree.gss.
          + rewrite PTree.gso in H2; eauto. exploit H; eauto. i. des.
            exists id. rewrite PTree.gso; eauto.
            ii. subst. exploit H1; eauto. i. congruence.
        - inv H0. eauto.
        - i. unfold Genv.add_global, Genv.find_symbol. ss. rewrite PTree.gso.
          + eapply H1. right. eauto.
          + ii. subst. inv H0; eauto.
      }
      eapply REC.
      { unfold P, Genv.find_def. i. ss. rewrite PTree.gempty in H. inv H. }
      { inv WF. eauto. }
      { i. unfold Genv.find_symbol. ss. eapply PTree.gempty. }
    - inv WF. i. eapply Genv.find_def_inversion in DEF. des. eapply WFPARAM in DEF. eauto.
  Qed.

  (* Note:
       1) It is more natural to define this predicate in `Genv` namespace, not `AST` namespace. (because of dependency)
       2) Natural ordering of parameters is __name__: Genv.t -> program -> Prop. (`ge.(__name__) prog`)

       Note: why not just name it `incl`?
       It is confusing as `List.incl` has an opposite direction.
       I think `List.incl` is abbreviation of `List.is_included`.
       le a b        === a.(le) b        === a <= b
       List.incl a b === a.(List.incl) b === a <= b
       includes a b  === a.(includes) b  === a >= b
   *)

  Inductive includes (skenv: SkEnv.t) (sk: AST.program (AST.fundef signature) unit): Prop :=
  | includes_intro
      (DEFS: forall id gd0
          (DEF: (prog_defmap sk) ! id = Some gd0),
          exists blk gd1, (<<SYMB: (Genv.find_symbol skenv) id = Some blk>>) /\
                          (<<DEF: (Genv.find_def skenv) blk = Some gd1>>) /\
                          (<<MATCH: linkorder gd0 gd1>>))
      (PUBS: incl sk.(prog_public) skenv.(Genv.genv_public)).

  Inductive project_spec (skenv: t) (prog: Sk.t) (skenv_proj: t): Prop :=
  | project_spec_intro
      (NEXT: skenv.(Genv.genv_next) = skenv_proj.(Genv.genv_next))
      (SYMBKEEP: forall id
          (KEEP: (defs prog) id),
          (<<KEEP: (Genv.find_symbol skenv_proj) id = (Genv.find_symbol skenv) id>>))
      (SYMBDROP: forall id
          (DROP: ~ (defs prog) id),
          <<NONE: (Genv.find_symbol skenv_proj) id = None>>)
      (DEFKEEP: forall id blk gd_big
          (INV: (Genv.invert_symbol skenv) blk = Some id)
          (KEEP: (internals prog) id)
          (BIG: (Genv.find_def skenv) blk = Some gd_big),
          exists gd_small, <<DEFSMALL: (Genv.find_def skenv_proj) blk = Some gd_small>>
                                    /\ <<INTERNAL: ~is_external gd_small>>
                                    /\ <<LO: linkorder gd_small gd_big>>
                                    /\ <<PROG: (prog_defmap prog) ! id = Some gd_small>>)
      (DEFKEPT: forall id blk gd_small
          (INV: (Genv.invert_symbol skenv) blk = Some id)
          (SMALL: (Genv.find_def skenv_proj) blk = Some gd_small),
          <<KEEP: (internals prog) id>> /\ <<INTERNAL: ~is_external gd_small>>
                                        /\ <<PROG: (prog_defmap prog) ! id = Some gd_small>> /\
          exists gd_big, <<DEFBIG: (Genv.find_def skenv) blk = Some gd_big>> /\ <<LO: linkorder gd_small gd_big>>)
      (DEFORPHAN: forall (* TODO: is it needed? *)
          blk
          (INV: (Genv.invert_symbol skenv) blk = None),
          <<SMALL: (Genv.find_def skenv_proj) blk = None>>)
      (PUBLIC: prog.(prog_public) = skenv_proj.(Genv.genv_public)).

  (* NOTE: it is total function! This is helpful because we don't need to state bsim of this, like
"(PROGRESS: project src succed -> project tgt succeed) /\ (BSIM: project tgt ~ projet src)".
I think "sim_skenv_monotone" should be sufficient.
   *)
  Definition project (skenv: t) (prog: Sk.t): t :=
    (Genv_map_defs
       ((Genv_filter_symb (Genv_update_publics skenv prog.(prog_public))) (fun id => (defs prog) id))
       (fun blk gd => (do id <- (Genv.invert_symbol skenv) blk;
                                       assertion((internals prog) id);
                                       (* assertion(prog.(defs) id); *)
                                       (* assertion(negb (is_external gd)); *) (* <--------- this is wrong *)
                                       do gd <- (prog_defmap prog) ! id;
                                       Some gd))).

  Lemma match_globdef_is_external_gd
        (gd1 gd2: globdef (AST.fundef signature) unit)
        (MATCH: match_globdef (@Sk.match_fundef _ _ id) top2 tt gd1 gd2):
      is_external_gd gd1 = is_external_gd gd2.
  Proof.
    inv MATCH; ss. rr in H0. des_ifs. ss. des_sumbool. clarify.
  Qed.

  Lemma project_impl_spec
        skenv (prog: Sk.t)
        (INCL: SkEnv.includes skenv prog):
      <<PROJ: project_spec skenv prog (project skenv prog)>>.
  Proof.
    u. unfold project in *. ss.
    econs; eauto; unfold Genv.find_symbol, Genv.find_def, Genv_map_defs in *; ss; ii;
      try (by rewrite PTree_filter_key_spec; des_ifs).
    - rewrite PTree_filter_map_spec. des_ifs. inv INCL.
      assert(exists gd_big, (prog_defmap prog) ! id = Some gd_big).
      { u in KEEP. des_ifs; et. }
      des. exploit DEFS; et. i; des. u. des_ifs_safe.
      assert(blk = blk0).
      { apply Genv.invert_find_symbol in Heq0. clarify. }
      clarify. uge. clarify. esplits; et. i. des_ifs. unfold internals in *. des_ifs. ss. bsimpl. clarify.
    - rewrite PTree_filter_map_spec in *. u in *. des_ifs_safe.
      assert(LO: linkorder gd_small g).
      { inv INCL. exploit DEFS; et. intro T; des.
        apply_all_once Genv.invert_find_symbol. clarify. uge. clarify.
      }
      esplits; et. des_ifs_safe. bsimpl. i; clarify.
    - rewrite PTree_filter_map_spec. des_ifs. u. des_ifs.
  Qed.

  Inductive wf_proj (skenv: t): Prop :=
  | wf_proj_intro
    (DEFSYMB: forall blk skd
        (DEF: (Genv.find_def skenv) blk = Some skd),
       <<SYMB: exists id, (Genv.find_symbol skenv) id = Some blk>> /\ <<INTERNAL: ~is_external skd>>).

  Lemma project_spec_preserves_wf
        skenv
        (WF: wf skenv)
        (prog: Sk.t) skenv_proj
        (PROJ: project_spec skenv prog skenv_proj):
      <<WF: wf_proj skenv_proj>>.
  Proof.
    inv WF. inv PROJ. econs; eauto. ii.
    destruct (Genv.invert_symbol skenv blk) eqn:T; cycle 1.
    { exploit DEFORPHAN; eauto. i; des. clarify. }
    rename i into id.
    exploit Genv.invert_find_symbol; eauto. intro TT.
    exploit DEFKEPT; eauto. i; des.
    u in H. des_ifs_safe. esplits; eauto.
    { erewrite SYMBKEEP; eauto. u. des_sumbool. eapply prog_defmap_image; et. }
  Qed.

  Definition internals (skenv: t): list block :=
    List.map fst (PTree.elements (skenv.(Genv.genv_defs))).

  (* We will not need this for now. Fix it when we need it (dynamic linking/incremental compilation) *)
  Definition filter_symbols (skenv: t) (symbols: list ident): t :=
    (Genv_filter_symb skenv) (fun id => List.in_dec ident_eq id symbols).

  (* Note: We only remove definitions. One can still get the address of external identifier. *)
  Definition revive `{HasExternal F} {V} (skenv: SkEnv.t) (prog: AST.program F V): Genv.t F V :=
    (Genv_map_defs (skenv)
             (fun blk gd => (do id <- (Genv.invert_symbol skenv) blk;
                               do gd <- (prog_defmap prog) ! id;
                               (* assertion (negb (is_external gd)); *)
                               Some gd))).

  Inductive genv_precise `{HasExternal F} {V} (ge: Genv.t F V) (p: program F V): Prop :=
  | genv_compat_intro
      (P2GE: forall id g
          (PROG: (prog_defmap p) ! id = Some g),
          (exists b, <<SYMB: Genv.find_symbol ge id = Some b>> /\
                     <<DEF: Genv.find_def ge b = if negb (is_external g) then Some g else None>>))
      (GE2P: forall b g
          (DEF: Genv.find_def ge b = Some g),
          exists id, <<SYMB: Genv.find_symbol ge id = Some b>> /\ <<PROG: (prog_defmap p) ! id = Some g>>
                                                                          /\ <<INTERNAL: ~ (is_external g)>>)
      (SYMB2P: forall id blk
          (SYMB: Genv.find_symbol ge id = Some blk),
          <<IN: (defs p) id>>).

  Lemma project_revive_precise
        F V
        skenv (prog: AST.program (fundef F) V)
        (* (DEFS0: forall id, In id prog.(prog_defs_names) -> is_some (skenv.(Genv.find_symbol) id)) *)
        (* (WF: wf skenv) *)
        skenv_link
        (* (PROJ: skenv = SkEnv.project skenv_link prog) *)
        get_sg
        (PROJ: SkEnv.project_spec skenv_link (Sk.of_program get_sg prog) skenv)
        (* (WF: SkEnv.wf skenv_link) *)
        (INCL: SkEnv.includes skenv_link (Sk.of_program get_sg prog))
    (* (PRECISE: SkEnv.genv_precise (SkEnv.revive skenv prog) prog *)
    :
      <<PRECISE: SkEnv.genv_precise (SkEnv.revive skenv prog) prog>>
  .
  Proof.
    assert(H: DUMMY_PROP) by ss.
    assert(DEFS: (defs prog) <1= fun id => is_some (Genv.find_symbol (skenv) id)).
    { ii; ss. u. des_ifs. exfalso.
      bar. inv PROJ. bar. inv INCL. bar.
      exploit SYMBKEEP; et.
      { rewrite Sk.of_program_defs. eauto. }
      intro EQ. des. rewrite Heq in *. symmetry in EQ.
      u in PR. des_sumbool. apply prog_defmap_spec in PR. des.
      hexploit (Sk.of_program_prog_defmap prog get_sg x0). intro REL. rewrite PR in *. inv REL. symmetry in H1.
      exploit DEFS; et. i; des. clarify.
    }
    econs; eauto; i; ss; swap 1 2.
    - des. unfold SkEnv.revive in *. apply_all_once Genv_map_defs_def. des; ss.
      uo. des_ifs. esplits; et.
      + rewrite Genv_map_defs_symb. eapply Genv.invert_find_symbol; et.
      + inv PROJ. rewrite Sk.of_program_defs in *. rewrite Sk.of_program_internals in *.
        assert(DEF: defs prog i).
        { u. des_sumbool. eapply prog_defmap_spec; et. }
        exploit DEFKEPT; et.
        { eapply Genv.find_invert_symbol; et. rewrite <- SYMBKEEP; et. eapply Genv.invert_find_symbol; et. }
        intro T; des. ss. rename g into gg. rename gd1 into gg1. bsimpl.
        unfold ASTC.internals in T. des_ifs. ss. unfold NW in *. bsimpl. congruence.
    - dup H. u in DEFS. unfold ident in *. spc DEFS.
      exploit DEFS; clear DEFS.
      { unfold proj_sumbool. des_ifs; ss. exfalso. apply n. eapply prog_defmap_spec; eauto. }
      i; des. des_ifs_safe. esplits; eauto.
      unfold SkEnv.revive. u. unfold Genv.find_def, Genv_map_defs. cbn. rewrite PTree_filter_map_spec. clear_tac.
      rewrite o_bind_ignore. exploit Genv.find_invert_symbol; et. intro INV.
      bar. inv PROJ. inv INCL. bar.
      assert(defs (Sk.of_program get_sg prog) id).
      { apply NNPP. ii. exploit SYMBDROP; et. i; des. clarify. }
      exploit SYMBKEEP; et. intro SYMBLINK; des. rewrite Heq in *. symmetry in SYMBLINK.
      exploit Genv.find_invert_symbol; et. intro INVLINK.
      hexploit (Sk.of_program_prog_defmap prog get_sg id); et. intro REL.
      rewrite PROG in *. inv REL.
      rename H2 into MATCHGD. rename H1 into PROG1.
      exploit DEFS; et. i; des. clarify. des_ifs_safe.
      inv MATCHGD; cycle 1.
      { des_ifs. inv MATCH. exploit DEFKEEP; et.
        { rewrite Sk.of_program_internals. u. des_ifs. }
        i; des. uge. clarify.
      }
      { inv MATCH. destruct (is_external_fd f1) eqn:T.
        - etrans; cycle 1.
          { instantiate (1:= None). des_ifs. ss. des_ifs. }
          assert(is_external f2).
          { rr in H1. des_ifs; ss. des_sumbool. clarify. }
          rename fd2 into fd_big.
          rename f2 into fd_small. rename f1 into fd_small2.
          (* if (Genv.genv_defs skenv) is some, then it should be fd_big *)
          (* fd_big *)
          bar. des_ifs. uge. exploit DEFKEPT; et. i; des. clarify.
          rewrite Sk.of_program_internals in *. u in H4. des_ifs. bsimpl. ss. clarify.
        - etrans; cycle 1.
          { instantiate (1:= Some (Gfun f1)). des_ifs. ss. des_ifs. }
          des_ifs. exfalso. exploit DEFKEEP; et.
          { rewrite Sk.of_program_internals in *. u. des_ifs. ss. bsimpl. ss. }
          intro GD; des. uge. clarify.
      }
    - unfold revive in *. erewrite Genv_map_defs_symb in SYMB. inv PROJ.
      apply NNPP; ii. exploit SYMBDROP; eauto.
      { rewrite Sk.of_program_defs. eauto. }
      i; des. clarify.
  Qed.

  Lemma project_revive_no_external
        F V (prog: AST.program (AST.fundef F) V) skenv_link get_sg blk gd
        (DEF: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program get_sg prog)) prog) blk = Some gd)
        (EXTERNAL: is_external gd)
        (INCL: SkEnv.includes skenv_link (Sk.of_program get_sg prog))
        (WF: SkEnv.wf skenv_link):
      False.
  Proof.
    assert(H: DUMMY_PROP) by ss.
    hexploit (@project_impl_spec skenv_link (Sk.of_program get_sg prog)); et. intro PROJ. des.
    exploit project_revive_precise; et. intro GEP; des.
    exploit project_spec_preserves_wf; et. intro WF0; des.
    inv WF0. dup DEF.
    unfold revive in DEF. apply Genv_map_defs_def in DEF. des.
    exploit DEFSYMB; et. i; des.
    inv GEP. exploit GE2P.
    { esplits; et. }
    i; des.
    assert(id0 = id).
    { unfold revive in SYMB0. rewrite Genv_map_defs_symb in *. apply_all_once Genv.find_invert_symbol. ss. }
    clarify.
  Qed.

  Definition privs (skenv: SkEnv.t): ident -> bool :=
    fun id =>
      match (Genv.find_symbol skenv) id with
      | Some _ => negb (proj_sumbool (in_dec ident_eq id skenv.(Genv.genv_public)))
      | None => false
      end.

  Definition empty: t := @Genv.empty_genv _ _ [].

  Lemma senv_genv_compat
        F V (skenv_link: t) fn_sig (prog: program (AST.fundef F) V)
        (INCL: includes skenv_link (Sk.of_program fn_sig prog)):
      senv_genv_compat skenv_link (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog).
  Proof.
    exploit SkEnv.project_revive_precise; eauto.
    { eapply SkEnv.project_impl_spec; eauto. }
    intro PREC. econs; eauto. i. ss.
    ss. uge. unfold SkEnv.revive in *. ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs.
  Qed.

  Lemma revive_incl_skenv
        F V (skenv:t) fn_sig (prog: program (AST.fundef F) V) fptr fd
        (INCL : includes skenv (Sk.of_program fn_sig prog))
        (WF : wf skenv)
        (FINDF : Genv.find_funct (SkEnv.revive (SkEnv.project skenv (Sk.of_program fn_sig prog)) prog) fptr =
                 Some (Internal fd)):
      exists blk, Genv.find_def skenv blk = Some (Gfun (Internal (fn_sig fd))).
  Proof.
    exploit SkEnv.project_revive_precise.
    eapply SkEnv.project_impl_spec. eauto. eauto. i. inv H. ss.
    unfold Genv.find_funct in FINDF. des_ifs.
    rewrite Genv.find_funct_ptr_iff in FINDF. eapply GE2P in FINDF. des.
    inv INCL. ss. exploit (Sk.of_program_prog_defmap prog fn_sig).
    instantiate (1 := id). i. inv H; rewrite PROG in *; clarify.
    inv H2. ss. des_ifs. symmetry in H1. eapply DEFS in H1. des. inv MATCH. inv H1. eauto.
  Qed.

End SkEnv.

Hint Unfold SkEnv.empty.
