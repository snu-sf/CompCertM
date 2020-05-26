Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC EventsC GlobalenvsC Smallstep.
Require Import Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib SemProps.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.
Require Import BehaviorsC.
Require Import CtypingC.
Require Import Any SemTyping.

Set Implicit Arguments.

Local Opaque Z.mul.

Definition is_external (ge: genv) (s:Csem.state) : Prop :=
  match s with
  | Csem.Callstate fptr ty args k m  =>
    match Genv.find_funct ge fptr with
    | Some f =>
      match f with
      | External ef targs tres cconv => is_external_ef ef = true
      | _ => False
      end
    | None => False
    end
  | _ => False
  end.

Definition internal_function_state (ge: genv) (s: Csem.state) : Prop :=
  match s with
  | Csem.Callstate fptr ty args k m  =>
    match Genv.find_funct ge fptr with
    | Some f =>
      match f with
      | Internal func => type_of_fundef f = Tfunction Tnil type_int32s cc_default
      | _ => False
      end
    | None => False
    end
  | _ => False
  end.

Section PRESERVATION.

  Inductive my_eq {A: Type} (x: A): A -> Prop :=
  | my_eq_refl: my_eq x x.

  Notation "a m= b" := (my_eq a b) (at level 10).

  Ltac Eq :=
    match goal with
    | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Eq
    | [ H1: ?a m= ?b, H2: ?a m= ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Eq
    | _ => idtac
    end.

  Section PLANB0.
(** ********************* linking *********************************)

  Variable prog: Csyntax.program.
  Let tprog : Syntax.program := List.map CsemC.module [prog].

(** ********************* genv *********************************)

  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  Let skenv_link := Sk.load_skenv sk_tgt.
  Hypothesis WTSK: Sk.wf sk_tgt.
  Let SKEWF: SkEnv.wf skenv_link.
  Proof.
    eapply SkEnv.load_skenv_wf; et.
  Qed.

  Let ge := globalenv prog.
  Let tge_ce : composite_env := prog_comp_env prog.
  Let tge := load_genv tprog skenv_link.

  Hypothesis MAIN_INTERNAL: forall st_src, Csem.initial_state prog st_src -> internal_function_state ge st_src.

  Hypothesis WTPROG: wt_program prog.

  Hypothesis WT_EXTERNAL:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) prog.(prog_defs) ->
      external_call ef skenv_link vargs m t vres m' ->
      wt_retval vres res.

  Hypothesis CSTYLE_EXTERN:
    forall id ef tyargs ty cc,
      In (id, (Gfun (Ctypes.External ef tyargs ty cc))) prog.(prog_defs) ->
      (ef_sig ef).(sig_cstyle).

  Definition local_genv (p : Csyntax.program) :=
    (SkEnv.revive ((SkEnv.project skenv_link) (CSk.of_program signature_of_function p))) p.

  Inductive match_states : Csem.state -> Sem.state -> nat -> Prop :=
  | match_states_intro
      fr (st: Csem.state) ohs
      (FRAME: fr = Frame.mk (CsemC.modsem skenv_link prog) st):
      match_states st (Sem.State [fr] ohs) 1
  | match_states_call
      fptr tyf vargs k m args fr (st: Csem.state) cconv tres targs n
      ohs
      (STATE: st = (Csem.Callstate fptr tyf vargs k m))
      (FRAME: fr = Frame.mk (CsemC.modsem skenv_link prog) st)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd
                        /\ Some (signature_of_type targs tres cconv) = Sk.get_csig skd)
      (FPTR: (Args.fptr args) = fptr)
      (ARGS: (Args.vs args) = vargs)
      (MEM: (Args.m args) = m)
      (NOTPROG: Genv.find_funct (local_genv prog) (Args.fptr args) = None)
      (ORD: n = 0%nat):
      match_states (Csem.Callstate fptr tyf vargs k m) (Callstate args [fr] ohs) n
  | match_states_init
      st_src st_tgt
      (INITSRC: Csem.initial_state prog st_src)
      (INITTGT: initial_state tprog tge st_tgt):
      match_states st_src st_tgt 0.

  Let INCL: SkEnv.includes (Sk.load_skenv (CSk.of_program signature_of_function prog)) (CSk.of_program signature_of_function prog).
  Proof. eapply includes_refl. Qed.

  (** ********************* init_memory *********************************)

  Variable m_init : mem.
  Hypothesis INIT_MEM: (Sk.load_mem sk_tgt) = Some m_init.

  Definition m_src_init := m_init.

  Lemma prog_sk_tgt:
    CSk.of_program signature_of_function prog = sk_tgt.
  Proof.
    unfold skenv_link, link_sk, link_list in LINK_SK_TGT; inversion LINK_SK_TGT. auto.
  Qed.

  Lemma SRC_INIT_MEM: Genv.init_mem prog = Some m_src_init.
  Proof.
    Local Transparent Linker_prog.
    unfold Sk.load_mem in *.
    eapply Genv.init_mem_match
      with (ctx := tt) (match_fundef := top3) (match_varinfo := top2);
      [| eapply INIT_MEM]. econs.
    - rewrite <- prog_sk_tgt. ss.
      remember (prog_defs prog) as l. clear Heql.
      ginduction l; ss; ii; econs.
      + destruct a; ss; econs; eauto.
        destruct g; ss; des_ifs; try (by (econs; eauto; econs)).
        { econs. ss. destruct v. ss. }
      + exploit IHl; eauto.
    - split.
      + subst tprog; ss.
        unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
      + subst tprog.
        unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
        Unshelve. all: econs.
  Qed.

  Lemma skenv_link_wf:
    SkEnv.wf skenv_link.
  Proof.
    clear INIT_MEM. (unfold skenv_link; eapply SkEnv.load_skenv_wf). ss.
  Qed.

  Lemma proj_wf:
    SkEnv.project_spec skenv_link (CSk.of_program signature_of_function prog) (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)).
  Proof.
    eapply SkEnv.project_impl_spec.
    unfold skenv_link.
    rpapply link_includes; et.
    { unfold tprog. rewrite in_map_iff. esplits; et. ss. left; et. }
    ss.
  Qed.

  Lemma match_ge_skenv_link :
    Genv.match_genvs (fun fdef skdef => skdef_of_gdef signature_of_function ((globdef_of_globdef (V:=type)) fdef) = skdef) ge skenv_link.
  Proof.
    unfold ge, skenv_link. rewrite <- prog_sk_tgt. unfold Sk.load_skenv, Genv.globalenv. ss.
    eapply Genv.add_globals_match; cycle 1.
    { econs; ss.
      i. do 2 rewrite PTree.gempty. econs. }
    ss. clear.
    remember (prog_defs prog) as l.
    clear Heql.
    ginduction l; ss.
    - econs.
    - ii. destruct a. ss. econs; ss.
      eapply IHl; eauto.
  Qed.

  Lemma symb_preserved id:
      Senv.public_symbol (symbolenv (sem tprog)) id =
      Senv.public_symbol (symbolenv (semantics prog)) id.
  Proof.
    destruct match_ge_skenv_link. ss.
    unfold symbolenv. ss.
    unfold Genv.public_symbol, proj_sumbool.
    unfold Sk.load_skenv in *. ss.
    unfold Genv.find_symbol in *. ss.
    rewrite <- mge_symb. unfold skenv_link.
    rewrite <- prog_sk_tgt. ss.
    des_ifs.
    unfold Genv.globalenv in *. ss. erewrite Genv.genv_public_add_globals in *. ss.
    unfold Genv.globalenv in *. ss. erewrite Genv.genv_public_add_globals in *. ss.
  Qed.

  Lemma transf_initial_states:
    forall st1, Csem.initial_state prog st1 ->
           exists st2, Sem.initial_state tprog tge st2 /\ match_states st1 st2 0.
  Proof.
    destruct match_ge_skenv_link. destruct skenv_link_wf.
    i. inversion H; subst.
    assert (ge = ge0).
    { unfold ge, ge0. auto. }
    subst ge0.
    unfold tge, skenv_link, link_sk, link_list in *; inversion LINK_SK_TGT.
    assert (Genv.find_funct (Sk.load_skenv sk_tgt) (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero) =
            Some (AST.Internal signature_main)).
    { dup H.
      eapply MAIN_INTERNAL in H.
      ss. des_ifs.
      unfold Genv.symbol_address.
      unfold Genv.find_symbol in *.
      unfold fundef in *. ss.
      des_ifs; cycle 1.
      { rewrite <- mge_symb in H1.
        unfold skenv_link in H1.
        rewrite H1 in Heq0. clarify. }
      ss. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
      unfold Genv.find_def in *.
      rewrite mge_symb in Heq0.
      assert (b = b0).
      { Eq. auto. } subst.
      specialize (mge_defs b0). inv mge_defs.
      { rewrite Heq in H7. clarify. }
      Eq. rewrite Heq in H6. inv H6. ss.
      destruct f0; ss. unfold type_of_function in H. ss. inv H. destruct fn_params; ss.
      destruct p. inv H8. }
    esplits; eauto.
    { econs; et.
      - i. ss. des; ss. clarify.
      - ss. rr. ss. econs; et.
    }
    { econs; et. econs; et.
      - i. ss. des; ss. clarify.
      - ss. rr. ss. econs; et.
    }
  Qed.

(** ********************* transf step  *********************************)

  Inductive valid_owner fptr (p: Csyntax.program) : Prop :=
  | valid_owner_intro
      fd
      (MSFIND: tge.(Ge.find_fptr_owner) fptr (CsemC.modsem skenv_link p))
      (FINDF: Genv.find_funct (local_genv p) fptr = Some (Internal fd)).

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner tge fptr ms0)
        (FIND1: Ge.find_fptr_owner tge fptr ms1):
      ms0 = ms1.
  Proof.
    eapply SemProps.find_fptr_owner_determ; ss;
      try rewrite LINK_SK_TGT; eauto.
    { ii. ss. des; ss. clarify. ss. unfold link_sk, link_list in *. ss. clarify. }
  Qed.

  Lemma alloc_variables_determ
        g e m
        vars e2 m2
        e2' m2'
        (ALLOCV1: alloc_variables g e m vars e2 m2)
        (ALLOCV2: alloc_variables g e m vars e2' m2'):
      e2' = e2 /\ m2' = m2.
  Proof.
    generalize dependent g.
    generalize dependent e2'.
    generalize dependent m2'.
    induction 1; i; inv ALLOCV2; auto.
    rewrite H in H7. inv H7. eapply IHALLOCV1 in H8. auto.
  Qed.

  Notation "'assign_loc'" := (assign_loc skenv_link) (only parsing).
  Notation "'bind_parameters'" := (bind_parameters skenv_link) (only parsing).
  Notation "'rred'" := (rred skenv_link) (only parsing).
  Notation "'estep'" := (estep skenv_link) (only parsing).

  Lemma assign_loc_determ
        g ty m b
        ofs v tr m1 m1'
        (ASSIGN1: assign_loc g ty m b ofs v tr m1)
        (ASSIGN2: assign_loc g ty m b ofs v tr m1'):
      m1 = m1'.
  Proof.
    generalize dependent g.
    generalize dependent m1'.
    induction 1; i; inv ASSIGN2; f_equal; Eq; auto.
    inv H1; inv H4. inv H5; inv H15; try congruence. Eq. auto.
  Qed.

  Lemma bind_parameters_determ
        g env m l vl m1 m1'
        (BIND1: bind_parameters g env m l vl m1)
        (BIND2: bind_parameters g env m l vl m1'):
      m1 = m1'.
  Proof.
    generalize dependent g.
    generalize dependent m1'.
    induction 1; i; inv BIND2; f_equal; Eq; auto.
    determ_tac assign_loc_determ.
    eapply IHBIND1; eauto.
  Qed.

  (** ********************* aux lemmas  *********************************)

  Lemma senv_equiv_ge_link:
    Senv.equiv (Genv.globalenv prog) skenv_link.
  Proof.
    destruct match_ge_skenv_link.
    econs; ss; splits.
    - unfold skenv_link in *. unfold Genv.public_symbol in *. des_ifs; ss.
      rewrite <- prog_sk_tgt in *.
      i. des_ifs; ss; unfold Genv.find_symbol in *;
           rewrite <- mge_symb in *; rewrite Heq0 in Heq; clarify.
      unfold Genv.public_symbol in *. des_ifs; ss.
      repeat rewrite Genv.globalenv_public in *. ss.
    - unfold Genv.block_is_volatile in *. i.
      des_ifs.
      + rewrite Genv.find_var_info_iff in *.
        unfold skenv_link in *. rewrite <- prog_sk_tgt in *. ss.
        unfold Genv.find_def in *;
          specialize (mge_defs b); inv mge_defs; symmetry in H, H0; Eq; ss.
        inv H2. destruct g0; ss.
      + unfold Genv.find_var_info in *.
        des_ifs;
          unfold Genv.find_def in *;
          destruct (mge_defs b); clarify; des_ifs.
      + unfold Genv.find_var_info in *.
        des_ifs;
          unfold Genv.find_def in *;
          destruct (mge_defs b); clarify; des_ifs.
  Qed.

  Lemma id_in_prog id:
      defs prog id <-> In id (prog_defs_names prog).
  Proof.
    split; i; unfold defs, in_dec, ident_eq in *; destruct (prog_defs_names prog); ss; des_ifs; eauto.
    inv H; clarify.
  Qed.

  Lemma id_not_in_prog id:
      ~ defs prog id <-> ~ In id (prog_defs_names prog).
  Proof.
    split; i; unfold not; i.
    - rewrite <- id_in_prog in H0. clarify.
    - rewrite id_in_prog in H0. clarify.
  Qed.

  Lemma not_prog_defmap_spec F V p id:
      ~ In id (prog_defs_names p) <-> ~ (exists g : globdef F V, (prog_defmap p) ! id = Some g).
  Proof.
    split; i; unfold not; i.
    - des. eapply H. rewrite prog_defmap_spec. eauto.
    - eapply H. rewrite prog_defmap_spec in H0. des. eauto.
  Qed.

  Lemma var_info_same
        blk g
        (VAR: Genv.find_var_info (Genv.globalenv prog) blk = Some g):
      Genv.find_var_info (local_genv prog) blk = Some g
  .
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    rewrite Genv.find_var_info_iff in *.
    unfold Genv.find_def in *. ss.
    repeat rewrite MapsC.PTree_filter_map_spec.
    rewrite o_bind_ignore.
    specialize (mge_defs blk). inv mge_defs.
    { rewrite VAR in H0. inv H0. }
    symmetry in H0.
    eapply DEFSYMB in H0. des. des_ifs.
    - destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) blk) eqn:SYMINV; ss; cycle 1.
      + assert ((prog_defmap prog) ! id = Some x).
        { rewrite Genv.find_def_symbol. exists blk. splits.
          unfold Genv.find_symbol in *. rewrite <- mge_symb. ss.
          unfold Genv.find_def. ss. }
        exploit SYMBKEEP; eauto.
        { instantiate (1 := id). rewrite CSk.of_program_defs.
          rewrite id_in_prog. rewrite prog_defmap_spec. eauto. }
        i. rewrite <- H2 in H0.
        eapply Genv.find_invert_symbol in H0. clarify.
      + unfold o_bind; ss.
        assert ((prog_defmap prog) ! id = Some x).
        { rewrite Genv.find_def_symbol. exists blk. splits.
          unfold Genv.find_symbol in *. rewrite <- mge_symb. ss.
          unfold Genv.find_def. ss. }
        exploit SYMBKEEP; eauto.
        { instantiate (1 := id).
          rewrite CSk.of_program_defs.
          rewrite id_in_prog. rewrite prog_defmap_spec. eauto. } i. des.
        rewrite <- H2 in H0.
        exploit Genv.find_invert_symbol; eauto. i. rewrite H3 in SYMINV. inv SYMINV.
        rewrite H1. ss. rewrite VAR in H. inv H. ss.
    - unfold o_bind in Heq; ss.
      exploit Genv.find_invert_symbol; eauto. i. rewrite H1 in Heq. ss.
      rewrite VAR in *. clarify. des_ifs.
      { uo. unfold internals in *. des_ifs. }
      unfold Genv.find_symbol in *. rewrite mge_symb in H0.
      assert ((prog_defmap prog) ! id = Some (Gvar g)).
      { rewrite Genv.find_def_symbol. exists blk. splits; eauto. }
      assert (In id (prog_defs_names prog)).
      { rewrite prog_defmap_spec. exists (Gvar g). auto. }
      rewrite <- id_in_prog in H2. rewrite CSk.of_program_internals in *. unfold internals in Heq0. des_ifs.
  Qed.

  Lemma var_info_same'
        blk g
        (VAR: Genv.find_var_info (local_genv prog) blk = Some g):
      Genv.find_var_info (Genv.globalenv prog) blk = Some g.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    rewrite Genv.find_var_info_iff in *. dup VAR.
    unfold Genv.find_def in VAR. ss.
    repeat rewrite MapsC.PTree_filter_map_spec in VAR.
    rewrite o_bind_ignore in VAR. des_ifs.
    destruct ((Genv.genv_defs skenv_link) ! blk) eqn:LINKDEF; cycle 1.
    { unfold o_bind in *; ss. }
    unfold o_bind in Heq; ss.
    destruct (Genv.invert_symbol skenv_link blk) eqn:LINKINV; cycle 1; ss. des_ifs.
    exploit Genv.invert_find_symbol; eauto. i.
    exploit SYMBKEEP; eauto. { eapply internals_defs; et. } i. rewrite <- H0 in H.
    exploit Genv.find_invert_symbol; eauto. i.
    rewrite H1 in VAR. unfold o_bind in VAR; ss.
    assert (defs prog i).
    { eapply internals_defs; et. erewrite <- CSk.of_program_internals; et. }
    rewrite id_in_prog in H2. rewrite prog_defmap_spec in H2. des.
    rewrite H2 in VAR. ss. des_ifs. ss.
    exploit DEFKEEP; eauto. i. rewrite Genv.find_def_symbol in H2. des.
    rewrite H in H0. unfold Genv.find_symbol in *. rewrite mge_symb in H0. rewrite <- H0 in H2. inv H2.
    clarify.
  Qed.

  Lemma volatile_block_same
        blk b
        (VOLATILE: Genv.block_is_volatile (local_genv prog) blk = b):
      Genv.block_is_volatile (Genv.globalenv prog) blk = b.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    ss. unfold Genv.block_is_volatile in *. des_ifs; try (by (exploit var_info_same; eauto; i; clarify)).
    exploit var_info_same'; eauto. i. rewrite H in Heq. clarify.
  Qed.

  Lemma volatile_block_same'
        blk b
        (VOLATILE: Genv.block_is_volatile (Genv.globalenv prog) blk = b):
      Genv.block_is_volatile (local_genv prog) blk = b.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    unfold Genv.block_is_volatile in *.
    des_ifs.
    - exploit var_info_same; eauto. i. Eq. clarify.
    - exploit var_info_same'; eauto. i. rewrite Heq0 in H. clarify.
    - exploit var_info_same; eauto. i. rewrite H in Heq. clarify.
  Qed.

  Lemma symbol_same id:
      Genv.find_symbol (local_genv prog) id =  Genv.find_symbol (Genv.globalenv prog) id.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    unfold Genv.find_symbol; ss.
    rewrite MapsC.PTree_filter_key_spec. des_ifs; ss.
    destruct ((Genv.genv_symb (Genv.globalenv prog)) ! id) eqn:SYMB; ss.
    exploit mge_symb. i. rewrite SYMB in H.
    exploit SYMBDEF; eauto. i. des.
    specialize (mge_defs b). inv mge_defs.
    { unfold Genv.find_def in H0. rewrite H0 in H3. clarify. }
    assert (~ defs prog id).
    { rewrite CSk.of_program_defs in *. unfold not. i. inv H. clarify. }
    exfalso. apply H3.
    rewrite id_in_prog. rewrite prog_defmap_spec. exists x.
    rewrite Genv.find_def_symbol. exists b. split; eauto.
  Qed.

  Lemma public_same id:
      Genv.public_symbol {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} id =
      Genv.public_symbol (Genv.globalenv prog) id.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    unfold Genv.public_symbol in *. des_ifs; ss.
    - rewrite Genv.globalenv_public. ss.
    - rewrite symbol_same in Heq. rewrite Heq in Heq0. clarify.
    - rewrite symbol_same in Heq. rewrite Heq in Heq0. clarify.
  Qed.

  Lemma Senv_equiv1:
    Senv.equiv (Genv.globalenv prog) {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}.
  Proof.
    econs; splits.
    - eapply symbol_same.
    - eapply public_same.
    - i. destruct (Senv.block_is_volatile (Genv.globalenv prog) b) eqn:VOLA;
           eapply volatile_block_same'; eauto.
  Qed.

  Lemma Senv_equiv2:
    Senv.equiv {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} (Genv.globalenv prog).
  Proof.
    econs; splits; symmetry.
    - eapply symbol_same.
    - eapply public_same.
    - i. destruct (Senv.block_is_volatile (Genv.globalenv prog) b) eqn:VOLA;
           eapply volatile_block_same'; eauto.
  Qed.

  Lemma volatile_load_same chunk m' b ofs tr v:
      volatile_load {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} chunk
                    m' b ofs tr v
      <-> volatile_load (globalenv prog) chunk m' b ofs tr v.
  Proof.
    split; i;
      exploit volatile_load_preserved; eauto. eapply Senv_equiv2. eapply Senv_equiv1.
  Qed.

  Lemma deref_loc_same ty m' b ofs tr v:
    deref_loc {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} ty m' b ofs tr v
    <-> deref_loc (globalenv prog) ty m' b ofs tr v.
  Proof.
    destruct match_ge_skenv_link.
    split; intro DEREF;
      inv DEREF; try (by econs; eauto);
        econs 2; eauto.
    - rewrite <- volatile_load_same; eauto.
    - rewrite volatile_load_same; eauto.
  Qed.

  Lemma volatile_store_same chunk m b ofs v tr m':
        volatile_store
          {| genv_genv := (local_genv prog);
             genv_cenv := prog_comp_env prog |} chunk m b ofs v tr m'
        <-> volatile_store (globalenv prog) chunk m b ofs v tr m'.
  Proof.
    split; i;
      exploit volatile_store_preserved; eauto. eapply Senv_equiv2. eapply Senv_equiv1.
  Qed.

  Lemma assign_loc_same ty m b ofs v tr m':
      assign_loc
        {| genv_genv := (local_genv prog);
           genv_cenv := prog_comp_env prog |} ty m b ofs v tr m'
      <-> assign_loc (globalenv prog) ty m b ofs v tr m'.
  Proof.
    destruct match_ge_skenv_link.
    split; intro ASSIGN;
      inv ASSIGN; try (by econs; eauto);
        econs 2; eauto.
  Qed.

  Lemma bind_parameters_same e m1 params vl m2:
      bind_parameters {| genv_genv := local_genv prog;
                         genv_cenv := prog_comp_env prog |} e m1 params vl m2
      <-> bind_parameters (globalenv prog) e m1 params vl m2.
  Proof.
    destruct match_ge_skenv_link.
    split; intro BPARAM.
    - induction BPARAM; try econs; eauto.
      rewrite assign_loc_same in H0. eauto.
    - induction BPARAM; try econs; eauto.
      rewrite <- assign_loc_same in H0. eauto.
  Qed.

  Lemma lred_same e a m a' m':
        lred {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} e a m a' m'
        <-> lred (globalenv prog) e a m a' m'.
  Proof.
    destruct match_ge_skenv_link.
    split; intro LRED;
      inv LRED; try (by econs; eauto); econs 2; eauto.
    - rewrite <- symbol_same; auto.
    - rewrite symbol_same; auto.
  Qed.

  Lemma rred_same
        a m tr a' m'
    :
        rred {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |} a m tr a' m'
        <-> rred (globalenv prog) a m tr a' m'.
  Proof.
    destruct match_ge_skenv_link.
    split; intro RRED.
    - inv RRED; try (by econs); ss
      ; try (by (econs; eauto; rewrite <- deref_loc_same; eauto)).
      + econs; eauto. rewrite <- assign_loc_same; eauto.
    - inv RRED; try (by econs); ss
      ; try (by (econs; eauto; rewrite deref_loc_same; eauto)).
      + econs; eauto. rewrite assign_loc_same; eauto.
  Qed.

  Lemma estep_same
        st_src tr st0
        (ESTEP: estep
                  {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}
                  st_src tr st0):
      estep (globalenv prog) st_src tr st0.
  Proof.
    destruct match_ge_skenv_link.
    inv ESTEP; ss; try (by econs; eauto).
    - econs; eauto.
      rewrite <- lred_same; eauto.
    - econs 2; eauto.
      rewrite <- rred_same; eauto.
    - econs; eauto.
      unfold not in *. i. eapply H0.
      inv H1; try (by econs); ss.
      + econs; eauto.
        rewrite lred_same; eauto.
      + econs 4; eauto.
        rewrite rred_same; eauto.
      + econs 5; eauto.
  Qed.

  Ltac o_bind_b :=
    match goal with
    | [ H : (do id <- ?stmt; ?next) = Some ?f |- _ ] => destruct stmt eqn:SYMB; clarify; unfold o_bind in *; ss
    end.

  Lemma def_same
        b f
        (DEF: Genv.find_def
                {| genv_genv := (local_genv prog);
                   genv_cenv := prog_comp_env prog |} b = Some f):
      Genv.find_def ge b = Some f.
  Proof.
    destruct match_ge_skenv_link.
    destruct proj_wf. destruct skenv_link_wf.
    ss. unfold Genv.find_def in DEF. ss.
    repeat rewrite MapsC.PTree_filter_map_spec in DEF.
    rewrite o_bind_ignore in DEF.
    des_ifs. o_bind_b.
    destruct ((prog_defmap prog)! i) eqn:PROGDEF; ss. des_ifs. ss.
    exploit (SYMBKEEP i).
    rewrite CSk.of_program_defs.
    rewrite id_in_prog. rewrite prog_defmap_spec.
    eauto. i.
    exploit Genv.invert_find_symbol; eauto; i. Eq.
    rewrite H in H0. exploit SYMBDEF; eauto. i. des.
    rewrite Genv.find_def_symbol in PROGDEF. des.
    unfold Genv.find_symbol in *. rewrite mge_symb in H0. Eq.
    auto.
  Qed.

  Lemma function_find_same
        fptr f
        (FUNC: Genv.find_funct (local_genv prog) fptr = Some f):
      Genv.find_funct ge fptr = Some f.
  Proof.
    unfold Genv.find_funct in FUNC. des_ifs.
    rewrite Genv.find_funct_ptr_iff in FUNC.
    exploit def_same; eauto. i. ss. des_ifs.
    rewrite Genv.find_funct_ptr_iff. auto.
  Qed.

  Definition is_external_fd :=
  fun (F : Type) (f : fundef) =>
    match f with
    | Internal _ => false
    | External ef _ _ _ => is_external_ef ef
    end.

  Lemma not_external_function_find_same
        f fptr
        (INTERN : is_external_fd function f = false)
        (FUNC : Genv.find_funct (Genv.globalenv prog) fptr = Some f):
      Genv.find_funct (local_genv prog) fptr = Some f.
  Proof.
    destruct match_ge_skenv_link.
    destruct proj_wf. destruct skenv_link_wf.
    ss. unfold Genv.find_funct. des_ifs; cycle 1.
    { ss. des_ifs. }
    ss. des_ifs.
    rewrite Genv.find_funct_ptr_iff in *.
    unfold Genv.find_def in *. ss.
    specialize (mge_defs b). inv mge_defs.
    { rewrite FUNC in H0. clarify. }
    repeat rewrite MapsC.PTree_filter_map_spec.
    rewrite o_bind_ignore. des_ifs; cycle 1.
    { rewrite FUNC in H. inv H. rewrite <- H0 in Heq.
      unfold o_bind in Heq; ss.
      destruct (Genv.invert_symbol skenv_link b) eqn:SYMB; ss.
      - assert (~ defs prog i).
        { des_ifs_safe; ss. ii. rewrite CSk.of_program_internals in *. unfold internals, defs in *. des_sumbool.
          apply prog_defmap_spec in H. des. des_ifs_safe. ss.
          destruct (is_external_gd g) eqn:ISEXT; ss; cycle 1.
          { uo. generalize (CSk.of_program_prog_defmap prog signature_of_function i). intro REL.
            inv REL; ss; try congruence. des_ifs. }
          apply Genv.find_def_symbol in Heq0. des. uge. clarify.
          apply Genv.invert_find_symbol in SYMB. uge.
          assert(b0 = b).
          { rewrite mge_symb in *. clarify. }
          clarify.
          clear - INTERN ISEXT. bsimpl. ss. destruct f; ss. clarify. }
        exploit Genv.invert_find_symbol; eauto. i.
        unfold Genv.find_symbol in *. rewrite mge_symb in H1.
        assert ((prog_defmap prog) ! i = Some (Gfun f)).
        { rewrite Genv.find_def_symbol. exists b.
          splits. unfold Genv.find_symbol in *. auto.
          auto. }
        rewrite id_not_in_prog in H. rewrite not_prog_defmap_spec in H.
        exfalso. apply H. exists (Gfun f). auto.
      - exploit DEFSYMB; eauto. i. des.
        exploit Genv.find_invert_symbol; eauto. i. Eq. }
    rewrite <- H0 in Heq. unfold o_bind in Heq. ss.
    dup H.
    rewrite FUNC in H. inv H.
    exploit DEFSYMB; eauto. i. des.
    exploit Genv.find_invert_symbol; eauto. i. rewrite H2 in Heq. ss.
    assert (defs prog id).
    { rewrite CSk.of_program_internals in *. des_ifs_safe. eapply internals_defs; et. }
    exploit (SYMBKEEP id); ss. { rewrite CSk.of_program_defs; ss. } i.
    dup H. rewrite <- H4 in H.
    exploit Genv.find_invert_symbol. eapply H. i. rewrite H6.
    unfold o_bind. ss. rewrite id_in_prog in H3. rewrite prog_defmap_spec in H3. des.
    rewrite H3. ss.
    assert ((prog_defmap prog) ! id = Some (Gfun f)).
    { rewrite Genv.find_def_symbol. exists b.
      splits. unfold Genv.find_symbol in *. rewrite <- mge_symb. auto.
      auto. }
    Eq. ss.
  Qed.

  Notation "'sstep'" := (sstep skenv_link) (only parsing).

  Lemma sstep_same
        st_src tr st0
        (SSTEP: sstep
                  {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}
                  st_src tr st0):
      sstep (globalenv prog) st_src tr st0.
  Proof.
    inv SSTEP; ss; try (by econs; eauto).
    - (* internal call *)
      econs; eauto.
      + exploit function_find_same; eauto.
      + instantiate (1 := m1).
        clear -H0. induction H0; try (by econs).
        econs; eauto.
      + induction H1; try (by econs).
        econs; eauto.
        rewrite assign_loc_same in H2. eauto.
        rewrite bind_parameters_same in H3. eauto.
    - (* external call *)
      econs; eauto; ss.
      exploit function_find_same; eauto.
  Qed.

  Lemma cstep_same
        st_src tr st0
        (STEP: Csem.step skenv_link
                 {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}
                 st_src tr st0):
      Csem.step skenv_link (globalenv prog) st_src tr st0.
  Proof.
    inv STEP.
    - econs. exploit estep_same; eauto.
    - econs 2. exploit sstep_same; eauto.
  Qed.

  Lemma system_internal
        ptr fn_sig f
        (SYSCALL: Genv.find_funct (System.skenv skenv_link) ptr = Some (AST.Internal fn_sig))
        (INTERNAL: Genv.find_funct ge ptr = Some (Internal f)):
      False.
  Proof.
    destruct match_ge_skenv_link.
    unfold System.skenv in SYSCALL. ss. unfold skenv_link in *.
    unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
    unfold Genv.find_def in *. ss. rewrite MapsC.PTree_filter_map_spec in SYSCALL.
    specialize (mge_defs b). inv mge_defs; unfold fundef in *.
    { rewrite INTERNAL in H0. clarify. }
    rewrite INTERNAL in H. inv H. ss. rewrite <- H0 in SYSCALL. ss.
  Qed.

  Lemma estep_progress
        st_src tr st0
        (ESTEP: estep (globalenv prog) st_src tr st0):
      estep
        {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}
        st_src tr st0.
  Proof.
    destruct match_ge_skenv_link.
    inv ESTEP; try (by econs; eauto).
    - econs; eauto.
      rewrite lred_same; eauto.
    - econs 2; eauto.
      rewrite rred_same; eauto.
    - econs; eauto.
      unfold not in *. i. eapply H0.
      inv H1; try (by econs); ss.
      + econs; eauto.
        rewrite <- lred_same; eauto.
      + econs 4; eauto.
        rewrite <- rred_same; eauto.
      + econs 5; eauto.
  Qed.

  Lemma sstep_progress
        st_src tr st0
        (INTERN: ~ is_external ge st_src)
        (SSTEP: sstep (globalenv prog) st_src tr st0):
      sstep
        {| genv_genv := (local_genv prog); genv_cenv := prog_comp_env prog |}
        st_src tr st0.
  Proof.
    destruct match_ge_skenv_link.
    inv SSTEP; try (by econs; eauto).
    - eapply step_internal_function; eauto.
      + exploit not_external_function_find_same; eauto. ss.
      + instantiate (1 := m1).
        clear -H0. induction H0; try (by econs).
        econs; eauto.
      + induction H1; try (by econs).
        exploit bind_parameters_same. i.
        rewrite H4. ss. econs; eauto.
    - econs; eauto; ss.
      + des_ifs.
        exploit not_external_function_find_same; eauto.
        ss. destruct ef; ss.
        Unshelve. all: auto.
  Qed.

  Lemma senv_same : ((Genv.globalenv prog): Senv.t) = (skenv_link: Senv.t).
  Proof.
    generalize match_ge_skenv_link; intro MGE.
    clear - skenv_link LINK_SK_TGT MGE.
    subst skenv_link. ss. unfold Sk.load_skenv in *. subst tprog. unfold link_sk in *. ss.
    unfold link_list in *. ss. clarify.
    inv MGE. apply senv_eta; ss.
    - uge. apply func_ext1. i. ss.
    - unfold Genv.public_symbol. uge. apply func_ext1. i. specialize (mge_symb x0). rewrite mge_symb. des_ifs.
      rewrite mge_pubs. ss.
    - apply func_ext1. i.
      destruct (Genv.invert_symbol (Genv.globalenv prog) x0) eqn:T.
      + apply Genv.invert_find_symbol in T. symmetry. apply Genv.find_invert_symbol. uge. rewrite mge_symb. ss.
      + destruct (Genv.invert_symbol (Genv.globalenv (CSk.of_program signature_of_function prog)) x0) eqn:U; ss.
        apply Genv.invert_find_symbol in U. specialize (mge_symb i). uge. rewrite mge_symb in *.
        apply Genv.find_invert_symbol in U. congruence.
    - unfold Genv.block_is_volatile, Genv.find_var_info. apply func_ext1. i.
      specialize (mge_defs x0). uge. inv mge_defs; ss.
      destruct x; ss. des_ifs.
  Qed.

  Lemma progress_step
        st_src frs ohs n t st_src'
        (INTERN: ~ is_external ge st_src)
        (MTCHST : match_states st_src (State frs ohs) n)
        (STEP: Step (semantics prog) st_src t st_src'):
      exists (tr : trace) (st_tgt1 : Smallstep.state (sem tprog)), Step (sem tprog) (State frs ohs) tr st_tgt1.
  Proof.
    inv MTCHST; inv STEP; ss; exists t.
    - esplits. econs; ss.  econs 1. exploit estep_progress; eauto. rewrite <- senv_same. eauto.
    - esplits. econs; ss. econs 2. exploit sstep_progress; eauto. rewrite <- senv_same. eauto.
    - inv INITSRC; inv INITTGT; inv H.
    - inv INITSRC; inv INITTGT; inv H.
  Qed.

  Lemma init_case st args frs ohs fptr tr st_src st_src'
        (STATE: st = Callstate args frs ohs)
        (FPTR: fptr = (Args.fptr args))
        (MTCHST: match_states st_src st 0)
        (SAFESRC: Step (semantics prog) st_src tr st_src'):
      (<<CMOD: valid_owner fptr prog>>) \/
      (<<SYSMOD: tge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link)>>).
  Proof.
    subst.
    destruct (classic (valid_owner (Args.fptr args) prog)); eauto.
    right. inv MTCHST.
    (* syscall *)
    - inv SAFESRC; inv H0.
      + ss. exploit not_external_function_find_same; eauto. ss.
        i. unfold local_genv in *. Eq.
      + econs.
        * unfold tge. ss. left. eauto.
        * destruct match_ge_skenv_link.
          ss. des.
          unfold local_genv in NOTPROG.
          unfold System.skenv.
          unfold Genv.find_funct in *. des_ifs.
          rewrite Genv.find_funct_ptr_iff in *.
          specialize (mge_defs b).
          inv mge_defs; unfold Genv.find_def in *; unfold fundef in *.
          { rewrite FPTR in H1. clarify. }
          rewrite FPTR in H0. inv H0. ss. rewrite SIG in H1. inv H1.
          rewrite MapsC.PTree_filter_map_spec. rewrite SIG.
          unfold o_bind. ss.
    (* initial state *)
    - inv INITTGT; ss.
      assert (SAME: sk_link = sk_tgt).
      { rewrite LINK_SK_TGT in INITSK. clarify. }
      clear INITSK.
      destruct proj_wf. destruct match_ge_skenv_link.
      exploit MAIN_INTERNAL; eauto. intros MAIN_INTERN.
      inv INITSRC; inv SAFESRC; inv H4.
      + exploit not_external_function_find_same; eauto. ss. i.
        ss. des_ifs. exfalso. eapply H.
        unfold Genv.symbol_address in *.
        repeat (ss; des_ifs).
        assert (b = b0).
        { unfold Genv.find_symbol in *. unfold skenv_link in *.
          rewrite <- mge_symb in H1. rewrite <- prog_sk_tgt in *. ss.
          rewrite Heq0 in H1. inversion H1. auto. } subst b0.
        assert (Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f)
                <-> Genv.find_funct (SkEnv.project skenv_link (CSk.of_program signature_of_function prog))
                                   (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero)
                   = Some (AST.Internal signature_main)).
        { i. ss. des_ifs.
          unfold Genv.symbol_address in *.
          des_ifs.
          unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          unfold Genv.find_symbol in *. unfold skenv_link in *.
          assert (PROGDEF: defs prog (prog_main prog)).
          { rewrite id_in_prog. rewrite prog_defmap_spec. ss.
            eexists. erewrite Genv.find_def_symbol. esplits; eauto. }
          exploit DEFKEEP; eauto.
          { exploit Genv.find_invert_symbol. unfold Genv.find_symbol. eapply Heq1.
            rewrite <- prog_sk_tgt in *. ss. eauto. }
          { rewrite CSk.of_program_internals. unfold internals. rename b into bb.
            hexploit (Genv.find_def_symbol prog (prog_main prog) (Gfun (Internal f))); et. intro T; des.
            exploit T0; et. i. des_ifs. }
          i. unfold Genv.find_funct_ptr. des. rewrite DEFSMALL. inv LO; ss. inv H7; ss.
        }
        econs; i; eauto.
        econs; i; ss; eauto. des_ifs.
        unfold Genv.symbol_address in *.
        des_ifs. erewrite <- H5. eauto.
      + set (if_sig := (mksignature (typlist_of_typelist targs) (Some (typ_of_type tres)) cc true)).
        econs; ss; auto.
        instantiate (1:= if_sig). des_ifs.
  Qed.

  Lemma prog_precise:
      SkEnv.genv_precise (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog) prog.
  Proof.
    eapply CSkEnv.project_revive_precise; eauto.
    exploit SkEnv.project_impl_spec. eauto. ii. red in H. unfold skenv_link. rewrite <- prog_sk_tgt. eauto.
  Qed.


  Lemma preservation_prog
        st0 tr st1
        (WT: wt_state prog ge st0)
        (STEP: Csem.step skenv_link ge st0 tr st1):
      <<WT: wt_state prog ge st1>>.
  Proof.
    eapply Ctyping.preservation; try apply STEP; try refl; eauto; et; destruct prog_precise.
    - ii. eapply Genv.find_def_symbol. esplits; eauto.
    - i. rewrite Genv.find_def_symbol in MAP. des; eauto.
    - i.
      destruct match_ge_skenv_link.
      specialize (mge_defs blk). inv mge_defs; unfold Genv.find_def in *.
      + unfold ge in DEF. unfold fundef in *.
        symmetry in H0. unfold fundef, genv_genv in *. ss. Eq.
      + unfold ge in DEF. unfold fundef in *.
        symmetry in H. unfold fundef, genv_genv in *. ss.
        Eq. symmetry in H0.
        destruct SKEWF.
        exploit DEFSYMB; eauto. i. des.
        unfold Genv.find_symbol in *. rewrite mge_symb in H. eauto.
  Qed.

  Lemma match_state_xsim:
      forall st_src st_tgt n (MTCHST: match_states st_src st_tgt n),
        xsim (Csem.semantics prog) (Sem.sem tprog) lt (wt_state prog ge) (sound_state tprog) n%nat st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold.
    destruct match_ge_skenv_link.
    destruct st_tgt.
    (* call state *)
    - inversion MTCHST; subst.
      (* syscall *)
      + left. right. econs; i. econs; i; cycle 1.
        * inv FINALSRC.
        * econs; i.
          (* step *)
          -- exploit init_case; eauto. i. des.
             { inv CMOD. clarify. }
             assert (CSTYLEARGS: exists fptr vs m, args = Args.Cstyle fptr vs m).
             { inv SYSMOD; ss. destruct args; ss. eauto. }
             des; subst args; econs; i.
             esplits.
             ++ left. split; cycle 1. {
          (* receptive *)
          -- econs.
             ++ i. inv H; inv H1; ss; clarify.
                { inv H0. eexists. econs 2.
                  eapply step_internal_function; eauto. }
                { exploit external_call_receptive; eauto. i. des.
                  eexists. econs 2.
                  eapply step_external_function; eauto. }
             ++ red. i.
                inv H; inv H0; ss; clarify; auto.
                exploit external_call_trace_length; eauto. }
                eapply plus_left'.
                (* step init *)
                ** econs; i.
                   (* determ *)
                   --- econs; i.
                       { inv H; inv H0.
                         split. econs. i. ss.
                         dup LINK_SK_TGT.
                         unfold tge, skenv_link, link_sk, link_list in LINK_SK_TGT0, SYSMOD; inversion LINK_SK_TGT0.
                         rewrite -> H1 in *.
                         unfold Args.get_fptr in *. des_ifs.
                         determ_tac find_fptr_owner_determ.
                         subst ms0. exploit find_fptr_owner_determ.
                         unfold tge, skenv_link, link_sk, link_list. rewrite <- H1 in *. eapply MSFIND.
                         unfold tge, skenv_link, link_sk, link_list. rewrite <- H1 in *. eapply MSFIND0.
                         i. subst ms. rewrite H1. auto.
                         inversion INIT0; inversion INIT. rewrite CSTYLE in *. clarify.
                         rewrite H5. rewrite H6. rewrite H7. eauto. }
                       { inv FINAL. }
                       { red. i. inv H. auto. }
                   --- eapply step_init; ss.
                       { unfold Args.get_fptr. des_ifs.
                         unfold tge, skenv_link, link_sk, link_list in *; inversion LINK_SK_TGT.
                         rewrite H0. eauto. }
                       { ss. instantiate (1:= tt).
                         exploit SSTGT; et. { apply star_refl. } intro T; des. rr in T. des.
                         exploit (WTY); ss; et.
                       }
                       { ss. }
                ** inv STEPSRC; inv H.
                   { ss. exploit not_external_function_find_same; eauto; ss.
                     i. unfold local_genv in *. Eq. }
                   eapply plus_left'.
                   (* step internal *)
                   --- econs; i.
                       (* determ *)
                       +++ econs; i.
                           { inv H; inv H0; try (by ss); try (by inv FINAL).
                             inv STEP; inv STEP0; ss.
                             rewrite FPTR1 in FPTR0. inv FPTR0.
                             exploit external_call_determ. eapply EXTCALL.
                             eapply EXTCALL0. i. des.
                             splits; eauto.
                             { eapply match_traces_le; eauto. ii.
                               destruct senv_equiv_ge_link. des. rewrite symb_preserved.
                               rewrite <- H2. auto. }
                             { i. subst.
                               exploit H0; eauto. i. des. rewrite H1. rewrite H2. eauto. } }
                           { inv FINAL. }
                           { red. i. inv H; auto.
                             inv STEP.
                             exploit external_call_trace_length; eauto. }
                       (* step *)
                       +++ instantiate (2 := tr).
                           eapply step_internal. ss.
                           instantiate (1 := (System.Returnstate vres m')).
                           econs; ss.
                           { instantiate (1 := ef). unfold System.globalenv.
                             unfold Genv.find_funct in *. des_ifs.
                             rewrite Genv.find_funct_ptr_iff in *.
                             specialize (mge_defs b). inv mge_defs; unfold Genv.find_def in *; unfold fundef.
                             { rewrite SIG in H. inv H. }
                             unfold fundef in *. rewrite FPTR in H. inv H; ss. }
                           unfold System.globalenv.
                           exploit external_call_symbols_preserved; eauto.
                           eapply senv_equiv_ge_link.
                   (* step_return *)
                   --- eapply plus_one.
                       instantiate (2:=E0).
                       econs; i.
                       (* determ *)
                       +++ econs; i.
                           { inv H; inv H0; try (by ss); try (by inv FINAL; inv AFTER; inv STEP).
                             - inv STEP; inv STEP0.
                             - inv FINAL; inv FINAL0. inv AFTER; inv AFTER0.
                               split; eauto.
                               { econs. }
                               { ii; ss. repeat f_equal. des.
                                 determ_tac typify_c_dtm. } }
                           { inv FINAL. }
                           { red. i. inv H; auto. inv STEP. }
                       (* step *)
                       +++ ss. eapply step_return.
                           { instantiate (1 := (Retv.mk vres m')). econs. }
                           { ss.
                           assert (after_external (Csem.Callstate fptr (Tfunction targs0 tres0 cc) vs k m)
                                                  (Retv.mk vres m') (Returnstate vres k m')).
                           { econs. ss. econs. ss.
                             unfold Genv.find_funct in FPTR. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
                             exploit Genv.find_def_inversion; eauto. i. des. exploit WT_EXTERNAL. eauto.
                             exploit external_call_symbols_preserved. eapply senv_equiv_ge_link. eauto. i. eauto. i. eauto. }
                           eauto.
                           }
                           { ss. }
                           { ss. }
                   --- traceEq.
                ** traceEq.
             ++ right. eapply CIH.
                { econs. ss. }
      (* initial state *)
      + inversion INITSRC; subst; ss.
        left. right. econs; i. econs; i; cycle 1.
        (* FINAL *)
        * inv FINALSRC.
        * econs; i; cycle 1.
          (* step *)
          -- exploit init_case; eauto. i. des.
             (* main is C internal function *)
             ++ inv CMOD; ss.
                inversion STEPSRC; inv H3; cycle 1.
                (* external *)
                ** exploit MAIN_INTERNAL; eauto. intro INTERN.
                   inv MSFIND; ss. des_ifs.
                (* internal *)
                ** esplits.
                   --- left. split; cycle 1. {
          (* receptive at *)
          -- econs; i.
             ++ inv H3; inv H5.
                { inv H4. eexists. econs 2.
                  eapply step_internal_function; eauto. }
                { exploit external_call_receptive; eauto. i. des.
                  eexists. econs 2.
                  eapply step_external_function; eauto. }
             ++ red. i.
                inv H3; inv H4; auto.
                exploit external_call_trace_length; eauto.
                       }
                       eapply plus_two.
                       econs; i.
                       (* determ *)
                       +++ econs; i.
                           { inv H3; inv H4.
                             split. econs. i. ss.
                             dup LINK_SK_TGT.
                             unfold tge, skenv_link, link_sk, link_list in LINK_SK_TGT0; inversion LINK_SK_TGT0.
                             rewrite -> H5 in *.
                             dup LINK_SK_TGT. unfold Args.get_fptr in *. destruct args; ss.
                             exploit find_fptr_owner_determ.
                             unfold tge. eauto.
                             eapply MSFIND. i.
                             generalize dependent st_init0. subst ms0.
                             exploit find_fptr_owner_determ.
                             unfold tge. eapply MSFIND0. eauto. i. des. subst ms.
                             ss. inversion INIT0; inversion INIT. auto.
                             rewrite FINDF0 in FINDF1. inversion FINDF1. subst fd0.
                             rewrite TYPE0 in TYPE1.
                             rewrite TYPE1 in *. auto. }
                           { inv FINAL. }
                           { red. i. inv H3. auto. }
                       +++ ss. eapply step_init.
                           { instantiate (1 := modsem skenv_link prog). ss.
                             unfold tge in MSFIND.
                             unfold tge, skenv_link, link_sk, link_list in *.
                             des_ifs. inversion Heq. rewrite <- H4 in MSFIND. unfold Args.get_fptr. des_ifs. }
                           { instantiate (1:= tt). ss.
                             clear - SSTGT.
                             exploit SSTGT; eauto. { eapply star_refl. } intro T; des_safe.
                             rr in T. des_safe. ss.
                             exploit (WTY); ss; et. intro U; des. clear - U. ss.
                             abstr (ohs None) x. destruct x; ss. clarify. des_u. refl.
                           }
                           ss. des_ifs.
                           instantiate (1 := (Csem.Callstate (Vptr b Ptrofs.zero) (Tfunction Tnil type_int32s cc_default) [] Kstop m0)).
                           assert  (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero = (Vptr b Ptrofs.zero)).
                           { destruct match_ge_skenv_link. specialize (mge_symb (prog_main prog)).
                             destruct senv_equiv_ge_link; ss.
                             unfold Genv.symbol_address. des_ifs.
                             - unfold fundef in *. rewrite H3 in Heq. rewrite <- prog_sk_tgt in *; ss.
                               rewrite H0 in Heq. clarify.
                             - unfold fundef in *. rewrite H3 in Heq. rewrite <- prog_sk_tgt in *; ss.
                               rewrite H0 in Heq. clarify. }
                           assert (Genv.init_mem prog = Some m_init).
                           { eapply SRC_INIT_MEM. }
                           unfold Sk.load_mem in *. Eq. clarify.
                           inv INITTGT; ss; unfold Sk.load_mem in *.
                           rewrite LINK_SK_TGT in INITSK. inversion INITSK. rewrite <- H5 in *.
                           rewrite INIT_MEM in INITMEM. inversion INITMEM. rewrite <- H6 in *.
                           rewrite H3. econs; ss; des_ifs; eauto.
                           { unfold fundef in *.
                             exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero)); eauto. }
                           { unfold type_of_function in *. clarify.
                             destruct (fn_params f) eqn:T; ss; des_ifs.
                             econs; ss. }
                       (* step_internal *)
                       +++ econs; i.
                           (* determ *)
                           *** econs; i.
                               { inv H3; inv H4; ss; try (by ss); try (by inv FINAL).
                                 - inv AT; inv AT0. ss.
                                 - inv AT. ss.
                                 - inv AT. ss.
                                 - inv STEP; inv STEP0; inv H3; inv H4; ss; des_ifs.
                                   + des_ifs.
                                     exploit alloc_variables_determ. eapply H16. eauto. i. des. subst.
                                     exploit bind_parameters_determ. eapply H17. eapply H19. i. subst.
                                     split; [ apply match_traces_E0 | i; auto].
                                   + unfold fundef in *.
                                     exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero)); eauto.
                                     i. ss. des_ifs. unfold local_genv in *. des_ifs. }
                               { inv STEP; inv FINAL; inv FINAL0. }
                               { red. i. inv H3; auto.
                                 inv STEP; inv H3; auto.
                                 exploit external_call_trace_length; eauto. }
                           (* step *)
                           *** instantiate (2:=E0).
                               eapply step_internal. ss. econs 2.
                               inv STEPSRC; inv H3. des_ifs.
                               instantiate (1 := (Csem.State f (fn_body f) Kstop e m2)).
                               eapply step_internal_function; ss; eauto.
                               { des_ifs. unfold fundef in *.
                                 exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero)); eauto. }
                               { instantiate (1 := m3).
                                 clear -INIT_MEM m_init ge LINK_SK_TGT tprog H17.
                                 induction H17; try (by econs).
                                 econs; eauto. }
                               { clear - INCL WT_EXTERNAL WTPROG MAIN_INTERNAL SKEWF WTSK INIT_MEM m_init ge LINK_SK_TGT tprog H18.
                                 induction H18; try (by econs). econs; eauto.
                                 unfold fundef in *. rewrite senv_same in H0.
                                 rewrite <- assign_loc_same in H0. eauto. }
                       +++ traceEq.
                   (* match state *)
                   --- right. eapply CIH.
                       { ss. instantiate (1:= 1%nat). inv INITTGT.
                         eapply match_states_intro. ss. }
             (* main is syscall *)
             ++ inv SYSMOD. inv INITTGT. ss.
                assert (SAME: sk_tgt = sk_link) by (Eq; auto). clear INITSK.
                exploit MAIN_INTERNAL; eauto. i. unfold internal_function_state in H3.
                assert  (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero = (Vptr b Ptrofs.zero)).
                { des_ifs. destruct match_ge_skenv_link. specialize (mge_symb (prog_main prog)).
                  unfold Genv.find_symbol, skenv_link, Genv.symbol_address in *.
                  rewrite <- prog_sk_tgt in *. unfold Genv.find_symbol in *.
                  des_ifs; ss; unfold fundef in *; rewrite mge_symb in Heq0; Eq; auto. }
                destruct (Genv.find_funct ge (Vptr b Ptrofs.zero)) eqn:HFUNC; ss.
                destruct f. ss.
                exploit system_internal; eauto; clarify. des_ifs.
                rewrite SAME in *. rewrite H4 in *. unfold fundef in *. eauto. i.
                clarify.
    (* state *)
    - right. econs; i; ss.
      + econs; i.
        (* step *)
        * inv MTCHST; cycle 1.
          { inv INITTGT. }
          inv STEPTGT; ss.
          (* step_call *)
          -- inv AT; ss. des.
             esplits.
             ++ right.
                splits; auto. eapply star_refl.
             ++ right. eapply CIH.
                { econs; eauto. }
          (* step_internal *)
          -- assert(STEPSRC: Csem.step skenv_link (globalenv prog) st_src tr st0).
             { exploit cstep_same; eauto. }
             esplits.
             ++ left. eapply plus_one. unfold fundef in *. rewrite senv_same. eauto.
             ++ right. eapply CIH.
                { econs; eauto. }
        (* progress *)
        * specialize (SAFESRC _ (star_refl _ _ _ _)). des.
          (* final *)
          -- inv SAFESRC; inv MTCHST; cycle 1.
             { inv INITTGT. }
             left. exists r0. econs; ss.
          (* step *)
          -- destruct (classic (is_external ge st_src)).
             (* external *)
             ++ right. inv SAFESRC; inv H0; ss; des_ifs.
              inv MTCHST; cycle 1.
              { inv INITTGT. }
              set ef as XX.
              exists E0. esplits. eapply step_call; ss. econs.
              { unfold Genv.find_funct. des_ifs.
                unfold Genv.find_funct_ptr. des_ifs.
                eapply CSkEnv.project_revive_no_external in Heq0; clarify; cycle 1.
                { rpapply link_includes; et.
                  { ss. left. et. }
                  ss. }
                ss. des_ifs. rewrite Genv.find_funct_ptr_iff in Heq.
                exploit def_same; eauto. i. unfold ge in H0.
                ss. Eq. ss. }
              { exists (External ef targs tres cc); ss.
                splits.
                { unfold Genv.find_funct in *. des_ifs.
                  rewrite Genv.find_funct_ptr_iff in *.
                  destruct match_ge_skenv_link.
                  specialize (mge_defs b). inv mge_defs; unfold Genv.find_def in *; ss.
                  - unfold fundef in *. rewrite <- H2 in Heq. clarify.
                  - assert (x = (Gfun (External ef targs tres cc))).
                    { unfold fundef in *. rewrite <- H0 in Heq. clarify. }
                    subst. ss. }
                exploit Genv.find_funct_inversion; eauto. i; des. f_equal.
                inv WTPROG. exploit CSTYLE_EXTERN; eauto. i. des_ifs. f_equal. eapply H3; eauto. }
              { specialize (SSSRC _ _ (star_refl _ _ _ _)). inv SSSRC; ss. exploit WTKS; eauto. { ii. clarify. } esplits; ss; eauto. rr. des. des_ifs. }
             (* internal *)
             ++ exploit progress_step; eauto.
        * inv MTCHST.
          { inv FINALTGT. inv FINAL. ss. subst.
            esplits.
            { eapply star_refl. }
            econs. }
          { inv INITTGT. }
    Unshelve.
      all: ss.
  Qed.

  Hypothesis INITSAFE: forall st (INIT: Smallstep.initial_state (semantics prog) st),
      <<SAFE: safe (semantics prog) st>>.

  Lemma transf_xsim_properties:
      xsim_properties (Csem.semantics prog) (Sem.sem tprog) nat lt.
  Proof.
    econstructor 1 with (xsim_ss_src := wt_state prog ge) (xsim_ss_tgt := sound_state tprog);
      ss; [| |apply lt_wf| |i; apply symb_preserved].
    { clear - MAIN_INTERNAL tprog WTPROG SKEWF LINK_SK_TGT INITSAFE WTSK WT_EXTERNAL INCL.
      econs.
      - ii. hexploit INITSAFE; eauto. intro SAFE. inv INIT.
        destruct (classic (exists fd, Genv.find_funct (globalenv prog) (Vptr b Ptrofs.zero) = Some (Internal fd))).
        + eapply wt_initial_state; ss; eauto.
          { i. rr. rewrite Genv.find_def_symbol. esplits; eauto. }
          { des. ii.
            destruct SKEWF.
            destruct match_ge_skenv_link.
            specialize (mge_defs blk). inv mge_defs.
            { ss. unfold Genv.find_def in DEF. unfold fundef, genv_genv in *. ss.
              symmetry in H5. Eq. }
            ss. unfold Genv.find_def in DEF. unfold fundef, genv_genv in *. ss.
            symmetry in H4. Eq.
            symmetry in H5. exploit DEFSYMB; eauto. i. des.
            unfold Genv.find_symbol in *. rewrite mge_symb in H4. eauto. }
        + ss. des_ifs.
          specialize (SAFE _ (star_refl _ _ _ _)). des; inv SAFE; ss.
          { inv H4. }
          { contradict H3. inv H4; ss; des_ifs; rewrite FPTR in *; eauto.
            exploit MAIN_INTERNAL; eauto.
            { econs; eauto. }
            i; des. ss. des_ifs.
          }
      - ii. eapply preservation_prog; eauto. rewrite <- senv_same; et.
    }
    { eapply preservation; et. }
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - ss. rp; try eapply H; eauto. unfold tge. unfold skenv_link. rewrite prog_sk_tgt. ss.
    - i. inv INIT0. inv INIT1. clarify.
    - apply match_state_xsim; eauto.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Csem.semantics prog) (Sem.sem tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.

  End PLANB0.

End PRESERVATION.


Theorem upperbound_b_correct
        builtins
        (cprog: Csyntax.program)
        (MAIN: exists main_f,
            (<<INTERNAL: (prog_defmap cprog) ! (cprog.(prog_main)) = Some (Gfun (Internal main_f))>>)
            /\
            (<<SIG: type_of_function main_f = Tfunction Tnil type_int32s cc_default>>))
        (TYPED: typechecked builtins cprog):
    (<<REFINE: improves (Csem.semantics cprog) (Sem.sem (map CsemC.module [cprog]))>>).
Proof.
  destruct (link_sk (map CsemC.module [cprog])) eqn:T; cycle 1.
  { ii. ss. }
  destruct (Sk.load_mem t) eqn:T2; cycle 1.
  { ii. exists beh2. ss. inv BEH.
    + ss. esplits; cycle 1.
      { apply behavior_improves_refl. }
      inv H. rewrite T in INITSK. clarify.
    + ss. esplits; cycle 1.
      { apply behavior_improves_refl. }
      econs 2. ii. inv H0.
      Local Transparent Linker_prog.
      unfold Sk.load_mem in *.
      assert (Genv.init_mem t = Some m0).
      { eapply Genv.init_mem_match
          with (ctx := tt) (match_fundef := top3) (match_varinfo := top2);
          [| eapply H1]. econs.
        - unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
          ss.
          remember (prog_defs cprog) as l. clear Heql.
          ginduction l; ss; ii; econs.
          + destruct a; ss; econs; eauto.
            destruct g; ss; des_ifs; try (by (econs; eauto; econs)).
            { econs. ss. destruct v. ss. }
          + exploit IHl; eauto.
        - split; unfold link_sk, link_list in *; ss; unfold link_prog in *; des_ifs. }
      rewrite T2 in H0. clarify. }
  eapply improves_free_theorem; i.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  inv TYPED.
  eapply transf_program_correct; eauto.
  { ss. unfold link_sk, link_list in *. ss. clarify. }
  { ii. rr. inv H. ss. des_ifs_safe.
    des.
    apply Genv.find_def_symbol in INTERNAL. des. unfold fundef in *.
    rewrite INTERNAL in *. clarify.
    unfold Genv.find_funct_ptr. des_ifs. }
  { eapply typecheck_program_sound; eauto. }
  Unshelve. all: econs.
Qed.
