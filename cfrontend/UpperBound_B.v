Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib SemProps.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.
Require Import BehaviorsC.
Require Import CtypingC.

Set Implicit Arguments.

Local Opaque Z.mul.

Section PRESERVATION.

  Existing Instance Val.mi_final.

(** PLAN B-0*)

(*
B-0
* : Physical
+ : Logical 
c0 * empty
>=
c0 + empty
*)

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

  (* TODO: prog always exists *)

(** ********************* genv *********************************)

  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link := Sk.load_skenv sk_tgt.

  Let ge := globalenv prog.
  Let tge_ce : composite_env := prog_comp_env prog.
  Let tge := load_genv tprog skenv_link.

  Hypothesis MAIN_INTERNAL: forall st_src, Csem.initial_state prog st_src -> internal_function_state ge st_src.

  Hypothesis WTPROG: wt_program prog.

  Hypothesis WT_EXTERNAL:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) prog.(prog_defs) ->
      external_call ef ge vargs m t vres m' ->
      wt_val vres res.

  Definition local_genv (p : Csyntax.program) :=
    (skenv_link.(SkEnv.project) p.(defs)).(SkEnv.revive) p.

  Inductive match_states : Csem.state -> Sem.state -> nat -> Prop :=
  | match_states_intro
      fr (st: Csem.state)
      (FRAME: fr = Frame.mk (CsemC.modsem skenv_link prog) st)
    :
      match_states st (Sem.State [fr]) 1
  | match_states_call
      fptr tyf vargs k m args fr (st: Csem.state) cconv tres targs n
      (STATE: st = (Csem.Callstate fptr tyf vargs k m))
      (FRAME: fr = Frame.mk (CsemC.modsem skenv_link prog) st)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd
                        /\ signature_of_type targs tres cconv = SkEnv.get_sig skd)
                   (* /\ (SkEnv.get_sig skd = sg_arg *)
                   (*    -> tyf = Tfunction targs tres cconv *)
                   (*    -> signature_of_type targs tres cconv = sg_arg)) *)
      (FPTR: args.(Args.fptr) = fptr)
      (ARGS: args.(Args.vs) = vargs)
      (MEM: args.(Args.m) = m)
      (NOTPROG: Genv.find_funct (local_genv prog) (Args.fptr args) = None)
      (ORD: n = 0%nat)
    :
      match_states (Csem.Callstate fptr tyf vargs k m) (Callstate args [fr]) n
  | match_states_init
      st_src st_tgt
      (INITSRC: Csem.initial_state prog st_src)
      (INITTGT: initial_state tprog st_tgt)
    :
      match_states st_src st_tgt 0
  .

  Lemma symb_preserved id
    :
      Senv.public_symbol (symbolenv (sem tprog)) id =
      Senv.public_symbol (symbolenv (semantics prog)) id.
  Proof.
    ss.
    admit "this should hold. fill in `symbolenv` of `Sem.v`".
  Qed.

  (** ********************* init_memory *********************************)

  Variable m_init : mem.
  Hypothesis INIT_MEM: sk_tgt.(Sk.load_mem) = Some m_init.
  (* TODO: m_init exist *)

  Definition m_src_init := m_init.

  Lemma SRC_INIT_MEM: Genv.init_mem prog = Some m_src_init.
  Proof.
    Local Transparent Linker_prog.
    unfold Sk.load_mem in *.
    eapply Genv.init_mem_match
      with (ctx := tt) (match_fundef := top3) (match_varinfo := top2);
      [| eapply INIT_MEM]. econs.
    - admit "list_forall2 (match_ident_globdef top3 top2 ()) (prog_defs sk_tgt) (prog_defs tprog)".
    - split.
      + subst tprog; ss.
        unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
      + subst tprog.
        unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
  Qed.

  Lemma skenv_link_wf:
    SkEnv.wf skenv_link.
  Proof. (unfold skenv_link; eapply Sk.load_skenv_wf). Qed.

  Lemma proj_wf:
    SkEnv.project_spec skenv_link (fun x : ident => (defs prog) x) (SkEnv.project skenv_link (defs prog)).
  Proof.
    exploit SkEnv.project_impl_spec. instantiate (1 := (defs prog)). instantiate (1 := skenv_link). auto.
  Qed.

  Lemma prog_sk_tgt:
    CSk.of_program signature_of_function prog = sk_tgt.
  Proof.
    unfold skenv_link, link_sk, link_list in LINK_SK_TGT; inversion LINK_SK_TGT. auto.
  Qed.

  Lemma match_ge_skenv_link :
    Genv.match_genvs (fun fdef skdef => skdef_of_gdef signature_of_function ((globdef_of_globdef (V:=type)) fdef) = skdef) ge skenv_link.
  Proof.
    admit "prove it".
  Qed.

  Lemma transf_initial_states:
    forall st1, Csem.initial_state prog st1 ->
           exists st2, Sem.initial_state tprog st2 /\ match_states st1 st2 0.
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
    esplits; repeat (econs; eauto).
  Qed.

(** ********************* transf step  *********************************)

  Inductive valid_owner fptr (p: Csyntax.program) : Prop :=
  | valid_owner_intro
      fd
      (MSFIND: tge.(Ge.find_fptr_owner) fptr (CsemC.modsem skenv_link p))
      (FINDF: Genv.find_funct (local_genv p) fptr = Some (Internal fd))
  .

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner tge fptr ms0)
        (FIND1: Ge.find_fptr_owner tge fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    eapply SemProps.find_fptr_owner_determ; ss;
      rewrite LINK_SK_TGT; eauto.
  Qed.

  Lemma alloc_variables_determ
        g e m
        vars e2 m2
        e2' m2'
        (ALLOCV1: alloc_variables g e m vars e2 m2)
        (ALLOCV2: alloc_variables g e m vars e2' m2')
    :
      e2' = e2 /\ m2' = m2.
  Proof.
    generalize dependent g.
    generalize dependent e2'.
    generalize dependent m2'.
    induction 1; i; inv ALLOCV2; auto.
    rewrite H in H7. inv H7. eapply IHALLOCV1 in H8. auto.
  Qed.

  Lemma assign_loc_determ
        g ty m b
        ofs v tr m1 m1'
        (ASSIGN1: assign_loc g ty m b ofs v tr m1)
        (ASSIGN2: assign_loc g ty m b ofs v tr m1')
    :
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
        (BIND2: bind_parameters g env m l vl m1')
    :
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

  Lemma id_in_prog
        id
    :
      defs prog id <-> In id (prog_defs_names prog).
  Proof.
    split; i; unfold defs, in_dec, ident_eq in *; destruct (prog_defs_names prog); ss; des_ifs; eauto.
    inv H; clarify.
  Qed.

  Lemma id_not_in_prog
        id
    :
      ~ defs prog id <-> ~ In id (prog_defs_names prog).
  Proof.
    split; i; unfold not; i.
    - rewrite <- id_in_prog in H0. clarify.
    - rewrite id_in_prog in H0. clarify.
  Qed.

  Lemma not_prog_defmap_spec
        F V p id
    :
      ~ In id (prog_defs_names p) <-> ~ (exists g : globdef F V, (prog_defmap p) ! id = Some g).
  Proof.
    split; i; unfold not; i.
    - des. eapply H. rewrite prog_defmap_spec. eauto.
    - eapply H. rewrite prog_defmap_spec in H0. des. eauto.
  Qed.

  Lemma var_info_same
        blk g
        (VAR: Genv.find_var_info (Genv.globalenv prog) blk = Some g)
    :
      Genv.find_var_info (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) blk = Some g
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
    eapply DEFSYMB in H0. des.
    des_ifs.
    - destruct (Genv.invert_symbol (SkEnv.project skenv_link (defs prog)) blk) eqn:SYMINV; ss; cycle 1.
      + assert ((prog_defmap prog) ! id = Some x).
        { rewrite Genv.find_def_symbol. exists blk. splits.
          unfold Genv.find_symbol in *. rewrite <- mge_symb. ss.
          unfold Genv.find_def. ss. }
        exploit SYMBKEEP; eauto.
        { instantiate (1 := id).
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
          rewrite id_in_prog. rewrite prog_defmap_spec. eauto. } i. des.
        rewrite <- H2 in H0.
        exploit Genv.find_invert_symbol; eauto. i. rewrite H3 in SYMINV. inv SYMINV.
        rewrite H1. ss. rewrite VAR in H. inv H. ss.
    - unfold o_bind in Heq; ss.
      exploit Genv.find_invert_symbol; eauto. i. rewrite H1 in Heq. ss.
      des_ifs.
      unfold Genv.find_symbol in *. rewrite mge_symb in H0.
      assert ((prog_defmap prog) ! id = Some (Gvar g)).
      { rewrite Genv.find_def_symbol. exists blk. splits; eauto. }
      assert (In id (prog_defs_names prog)).
      { rewrite prog_defmap_spec. exists (Gvar g). auto. }
      rewrite <- id_in_prog in H3. inv H3. clarify.
  Qed.

  Lemma var_info_same'
        blk g
        (VAR: Genv.find_var_info (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) blk = Some g)
    :
      Genv.find_var_info (Genv.globalenv prog) blk = Some g.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    rewrite Genv.find_var_info_iff in *.
    dup VAR.
    unfold Genv.find_def in VAR. ss.
    repeat rewrite MapsC.PTree_filter_map_spec in VAR.
    rewrite o_bind_ignore in VAR.
    des_ifs.
    destruct ((Genv.genv_defs skenv_link) ! blk) eqn:LINKDEF; cycle 1.
    { unfold o_bind in *; ss. }
    unfold o_bind in Heq; ss.
    destruct (Genv.invert_symbol skenv_link blk) eqn:LINKINV; cycle 1; ss.
    des_ifs.
    exploit Genv.invert_find_symbol; eauto. i.
    exploit SYMBKEEP; eauto. i. rewrite <- H0 in H.
    exploit Genv.find_invert_symbol; eauto. i.
    rewrite H1 in VAR. unfold o_bind in VAR; ss.
    assert (defs prog i) by ss.
    rewrite id_in_prog in H2. rewrite prog_defmap_spec in H2. des.
    rewrite H2 in VAR. ss. des_ifs. ss.
    exploit DEFKEEP; eauto. i. rewrite Genv.find_def_symbol in H2. des.
    rewrite H in H0. unfold Genv.find_symbol in *. rewrite mge_symb in H0. rewrite <- H0 in H2. inv H2.
    clarify.
  Qed.

  Lemma volatile_block_same
        blk b
        (VOLATILE: Genv.block_is_volatile (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) blk = b)
    :
      Genv.block_is_volatile (Genv.globalenv prog) blk = b.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    ss. unfold Genv.block_is_volatile in *. des_ifs; try (by (exploit var_info_same; eauto; i; clarify)).
    exploit var_info_same'; eauto. i. rewrite H in Heq. clarify.
  Qed.

  Lemma volatile_block_same'
        blk b
        (VOLATILE: Genv.block_is_volatile (Genv.globalenv prog) blk = b)
    :
      Genv.block_is_volatile (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) blk = b.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    unfold Genv.block_is_volatile in *.
    des_ifs.
    - exploit var_info_same; eauto. i. Eq. clarify.
    - exploit var_info_same'; eauto. i. rewrite Heq0 in H. clarify.
    - exploit var_info_same; eauto. i. rewrite H in Heq. clarify.
  Qed.

  Lemma symbol_same
        id
    :
      Genv.find_symbol (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) id =  Genv.find_symbol (Genv.globalenv prog) id.
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
    { unfold not. i. inv H. clarify. }
    exfalso. apply H3.
    rewrite id_in_prog. rewrite prog_defmap_spec. exists x.
    rewrite Genv.find_def_symbol. exists b. split; eauto.
  Qed.

  Lemma public_same
        id
    :
      Genv.public_symbol {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} id =
      Genv.public_symbol (Genv.globalenv prog) id.
  Proof.
    destruct match_ge_skenv_link.
    destruct skenv_link_wf. destruct proj_wf.
    unfold Genv.public_symbol in *. des_ifs; ss.
    - unfold tprog, skenv_link, link_sk, link_list in LINK_SK_TGT. des_ifs; ss. inv Heq1.
      unfold skenv_link, Sk.load_skenv in *. repeat rewrite Genv.globalenv_public in *. ss.
    - rewrite symbol_same in Heq. rewrite Heq in Heq0. clarify.
    - rewrite symbol_same in Heq. rewrite Heq in Heq0. clarify.
  Qed.

  Lemma Senv_equiv1:
    Senv.equiv (Genv.globalenv prog) {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}.
  Proof.
    econs; splits.
    - eapply symbol_same.
    - eapply public_same.
    - i. destruct (Senv.block_is_volatile (Genv.globalenv prog) b) eqn:VOLA;
           eapply volatile_block_same'; eauto.
  Qed.

  Lemma Senv_equiv2:
    Senv.equiv {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} (Genv.globalenv prog).
  Proof.
    econs; splits; symmetry.
    - eapply symbol_same.
    - eapply public_same.
    - i. destruct (Senv.block_is_volatile (Genv.globalenv prog) b) eqn:VOLA;
           eapply volatile_block_same'; eauto.
  Qed.

  Lemma volatile_load_same
        chunk m' b ofs tr v
    :
      volatile_load {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} chunk
                    m' b ofs tr v <->
      volatile_load (globalenv prog) chunk m' b ofs tr v.
  Proof.
    split; i;
      exploit volatile_load_preserved; eauto. eapply Senv_equiv2. eapply Senv_equiv1.
  Qed.

  Lemma deref_loc_same
        ty m' b ofs tr v
    :
      deref_loc {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} ty m' b ofs tr v <-> deref_loc (globalenv prog) ty m' b ofs tr v.
  Proof.
    destruct match_ge_skenv_link.
    split; intro DEREF;
      inv DEREF; try (by econs; eauto);
        econs 2; eauto.
    - rewrite <- volatile_load_same; eauto.
    - rewrite volatile_load_same; eauto.
  Qed.

  Lemma volatile_store_same
        chunk m b ofs v tr m'
    :
        volatile_store
          {|
            genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog;
            genv_cenv := prog_comp_env prog |} chunk m b ofs v tr m'
        <-> volatile_store (globalenv prog) chunk m b ofs v tr m'.
  Proof.
    split; i;
      exploit volatile_store_preserved; eauto. eapply Senv_equiv2. eapply Senv_equiv1.
  Qed.

  Lemma assign_loc_same
        ty m b ofs v tr m'
    :
      assign_loc
        {|
          genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog;
          genv_cenv := prog_comp_env prog |} ty m b ofs v tr m'
        <-> assign_loc (globalenv prog) ty m b ofs v tr m'.
  Proof.
    destruct match_ge_skenv_link.
    split; intro ASSIGN;
      inv ASSIGN; try (by econs; eauto);
        econs 2; eauto.
    - rewrite <- volatile_store_same; eauto.
    - rewrite volatile_store_same; eauto.
  Qed.

  Lemma lred_same
        e a m a' m'
    :
        lred {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} e a m a' m'
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
        rred {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |} a m tr a' m'
        <-> rred (globalenv prog) a m tr a' m'.
  Proof.
    destruct match_ge_skenv_link.
    split; intro RRED.
    - inv RRED; try (by econs); ss
      ; try (by (econs; eauto; rewrite <- deref_loc_same; eauto)).
      + econs; eauto. rewrite <- assign_loc_same; eauto.
      + econs; eauto. exploit external_call_symbols_preserved; eauto. eapply Senv_equiv2.
    - inv RRED; try (by econs); ss
      ; try (by (econs; eauto; rewrite deref_loc_same; eauto)).
      + econs; eauto. rewrite assign_loc_same; eauto.
      + econs; eauto. exploit external_call_symbols_preserved; eauto. eapply Senv_equiv1.
  Qed.

  Lemma estep_same
        st_src tr st0
        (ESTEP: estep
                  {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}
                  st_src tr st0)
    :
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
                {|
                  genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog;
                  genv_cenv := prog_comp_env prog |} b = Some f)
    :
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
        (FUNC: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) fptr = Some f)
    :
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
        (FUNC : Genv.find_funct (Genv.globalenv prog) fptr = Some f)
        (* (External ef targs tres cc) *)
    :
      Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog) fptr =
      Some f.
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
        { des_ifs; ss. }
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
    { destruct (defs prog id) eqn:DEFS; ss. }
    exploit (SYMBKEEP id); ss. i.
    dup H. rewrite <- H4 in H.
    exploit Genv.find_invert_symbol. eapply H. i. rewrite H6.
    unfold o_bind. ss. rewrite id_in_prog in H3. rewrite prog_defmap_spec in H3. des.
    rewrite H3. ss.
    assert ((prog_defmap prog) ! id = Some (Gfun f)).
    { rewrite Genv.find_def_symbol. exists b.
      splits. unfold Genv.find_symbol in *. rewrite <- mge_symb. auto.
      auto. }
    Eq. ss. des_ifs; subst. ss. rewrite negb_false_iff in Heq0.
    unfold is_external_fd in *. des_ifs. inv Heq. Eq.
  Qed.

  Lemma sstep_same
        st_src tr st0
        (SSTEP: sstep
                  {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}
                  st_src tr st0)
    :
      sstep (globalenv prog) st_src tr st0.
  Proof.
    inv SSTEP; ss; try (by econs; eauto).
    - (* internal call *)
      econs; eauto.
      + exploit function_find_same; eauto.
      + instantiate (1 := m1).
        clear -H0. induction H0; try (by econs).
        econs; eauto.
      + clear -INIT_MEM m_init ge LINK_SK_TGT tprog H1.
        induction H1; try (by econs).
        econs; eauto.
        rewrite assign_loc_same in H0. eauto.
    - (* external call *)
      econs; eauto; ss.
      + exploit function_find_same; eauto.
      + exploit external_call_symbols_preserved; eauto. eapply Senv_equiv2.
  Qed.

  Lemma cstep_same
        st_src tr st0
        (STEP: Csem.step
                 {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}
                 st_src tr st0)
    :
      Csem.step (globalenv prog) st_src tr st0.
  Proof.
    inv STEP.
    - econs. exploit estep_same; eauto.
    - econs 2. exploit sstep_same; eauto.
  Qed.

  Lemma system_internal
        ptr fn_sig f
        (SYSCALL: Genv.find_funct (System.skenv skenv_link) ptr = Some (AST.Internal fn_sig))
        (INTERNAL: Genv.find_funct ge ptr = Some (Internal f))
    :
      False
  .
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
        (INTERN: ~ is_external ge st_src)
        (ESTEP: estep (globalenv prog) st_src tr st0)
    :
      estep
        {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}
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
        (SSTEP: sstep (globalenv prog) st_src tr st0)
    :
      sstep
        {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs prog)) prog; genv_cenv := prog_comp_env prog |}
        st_src tr st0.
  Proof.
    destruct match_ge_skenv_link.
    inv SSTEP; try (by econs; eauto).
    - eapply step_internal_function; eauto.
      + exploit not_external_function_find_same; eauto. ss.
      + instantiate (1 := m1).
        clear -H0. induction H0; try (by econs).
        econs; eauto.
      + clear -INIT_MEM m_init ge LINK_SK_TGT tprog H1.
        induction H1; try (by econs).
        econs; eauto.
        rewrite <- assign_loc_same in H0. eauto.
    - econs; eauto; ss.
      + des_ifs.
        exploit not_external_function_find_same; eauto.
        ss. destruct ef; ss.
      + exploit external_call_symbols_preserved; eauto. eapply Senv_equiv1.
  Qed.

  Lemma progress_step
        st_src frs n t st_src'
        (INTERN: ~ is_external ge st_src)
        (MTCHST : match_states st_src (State frs) n)
        (STEP: Step (semantics prog) st_src t st_src')
    :
      exists (tr : trace) (st_tgt1 : Smallstep.state (sem tprog)), Step (sem tprog) (State frs) tr st_tgt1.
  Proof.
    inv MTCHST; inv STEP; ss; exists t.
    - esplits. econs; ss. econs 1. exploit estep_progress; eauto.
    - esplits. econs; ss. econs 2. exploit sstep_progress; eauto.
    - inv INITSRC; inv INITTGT; inv H.
    - inv INITSRC; inv INITTGT; inv H.
  Qed.

  Lemma init_case st args frs fptr tr st_src st_src'
        (STATE: st = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
        (MTCHST: match_states st_src st 0)
        (SAFESRC: Step (semantics prog) st_src tr st_src')
    :
      (<<CMOD: valid_owner fptr prog>>) \/
      (<<SYSMOD: tge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link)>>).
  Proof.
    subst.
    destruct (classic (valid_owner args.(Args.fptr) prog)); eauto.
    right. inv MTCHST.
    - (* syscall *)
      inv SAFESRC; inv H0.
      + ss. exploit not_external_function_find_same; eauto. ss.
        i. unfold local_genv in NOTPROG. Eq.
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
    - (* initial state *)
      inv INITTGT; ss.
      assert (SAME: sk_link = sk_tgt).
      { rewrite LINK_SK_TGT in INITSK. clarify. }
      clear INITSK.
      destruct proj_wf. destruct match_ge_skenv_link.
      exploit MAIN_INTERNAL; eauto. intros MAIN_INTERN.
      inv INITSRC; inv SAFESRC; inv H4.
      + ss. des_ifs. exfalso. eapply H.
        unfold Genv.symbol_address in *.
        repeat (ss; des_ifs).
        assert (b = b0).
        {  unfold Genv.find_symbol in *. unfold skenv_link in *.
           rewrite <- mge_symb in H1. rewrite <- prog_sk_tgt in *. ss.
           rewrite Heq0 in H1. inversion H1. auto. } subst b0.
        assert (Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f)
                <-> Genv.find_funct (SkEnv.project skenv_link (defs prog)) (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero) = Some (AST.Internal signature_main)).
        { exploit not_external_function_find_same; eauto; ss.
          { instantiate (1:=(Internal f)); ss. }
          { instantiate (1:=Vptr b Ptrofs.zero true). ss. }
          i. ss. des_ifs.
          unfold Genv.symbol_address in *.
          des_ifs.
          unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          unfold Genv.find_symbol in *. unfold skenv_link in *.
          assert (PROGDEF: defs prog (prog_main prog)).
          { rewrite id_in_prog. rewrite prog_defmap_spec. ss.
            eexists. erewrite Genv.find_def_symbol. esplits; eauto. }
          exploit DEFKEEP; eauto. exploit Genv.find_invert_symbol. unfold Genv.find_symbol. eapply Heq1.
          rewrite <- prog_sk_tgt in *. ss. eauto.
          i. unfold Genv.find_funct_ptr. rewrite H5. rewrite SIG. ss. }
        econs; i.
        * econs; i; ss; eauto. des_ifs.
          unfold Genv.symbol_address in *.
          des_ifs. erewrite <- H4. eauto.
        * instantiate (1:=f).
          exploit not_external_function_find_same; eauto; ss.
      + set (if_sig := (mksignature (typlist_of_typelist targs) (Some (typ_of_type tres)) cc)).
        econs; ss; auto.
        instantiate (1:=if_sig). des_ifs.
  Qed.

  Lemma preservation_prog
        st0 tr st1
        (WT: wt_state ge st0)
        (STEP: Csem.step ge st0 tr st1)
    :
      <<WT: wt_state ge st1>>
  .
  Proof.
    eapply preservation; try refl; eauto.
    - ii. eapply Genv.find_def_symbol. esplits; eauto.
    - i. admit "ez".
  Qed.

  Lemma match_state_xsim
    :
      forall st_src st_tgt n (MTCHST: match_states st_src st_tgt n) (WTST: wt_state ge st_src),
        xsim (Csem.semantics prog) (Sem.sem tprog) lt n%nat st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold.
    destruct match_ge_skenv_link.
    destruct st_tgt.
    - (* call state *)
      inversion MTCHST; subst.
      + (* syscall *)
        left. econs; i.
        * inv FINALSRC.
        * econs; i; cycle 1.
          -- (* receptive *)
            econs.
            ++ i. inv H; inv H1; ss; clarify.
             { inv H0. eexists. econs 2.
               eapply step_internal_function; eauto. }
             { exploit external_call_receptive; eauto. i. des.
               eexists. econs 2.
               eapply step_external_function; eauto. }
            ++ red. i.
               inv H; inv H0; ss; clarify; auto.
               exploit external_call_trace_length; eauto.
          -- (* step *)
            econs; i.
            exploit init_case; eauto. i. des.
            { inv CMOD. clarify. }
            esplits.
            ++ left.
               eapply plus_left'.
               ** (* step init *)
                 econs; i.
                 --- (* determ *)
                   econs; i.
                   { inv H; inv H0.
                     split. econs.
                     i. ss.
                     dup LINK_SK_TGT.
                     unfold tge, skenv_link, link_sk, link_list in LINK_SK_TGT0, SYSMOD; inversion LINK_SK_TGT0.
                     rewrite -> H1 in *.
                     determ_tac find_fptr_owner_determ.
                     generalize dependent st_init0.
                     subst ms0.
                     exploit find_fptr_owner_determ.
                     unfold tge, skenv_link, link_sk, link_list. rewrite <- H1 in *. eapply MSFIND.
                     unfold tge, skenv_link, link_sk, link_list. rewrite <- H1 in *. eapply MSFIND0.
                     i. subst ms.
                     rewrite H1. auto.
                     inversion INIT0; inversion INIT. auto.
                   }
                   { inv FINAL. }
                   { red. i. inv H. auto. }
                 --- eapply step_init; ss.
                     { unfold tge, skenv_link, link_sk, link_list in *; inversion LINK_SK_TGT.
                       rewrite H0. eauto. }
                     { ss. }
               ** inv STEPSRC; inv H.
                  { ss. exploit not_external_function_find_same; eauto; ss.
                    i. unfold local_genv in NOTPROG. Eq. }
                  eapply plus_left'.
                  --- (* step internal *)
                    econs; i.
                    +++ (* determ *)
                      econs; i.
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
                          exploit H0; eauto. i. des.
                          assert (retv = retv0).
                          { destruct retv; destruct retv0; ss; subst. auto. }
                          subst. auto. }
                      }
                      { inv FINAL. }
                      { red. i. inv H; auto.
                        inv STEP.
                        exploit external_call_trace_length; eauto. }
                    +++ (* step *)
                      instantiate (2 := tr).
                      eapply step_internal. ss.
                      instantiate (1 := (System.Returnstate (Retv.mk vres m'))).
                      econs; ss.
                      { instantiate (1 := ef).
                        unfold System.globalenv.
                        (* make lemma *)
                        unfold Genv.find_funct in *. des_ifs.
                        rewrite Genv.find_funct_ptr_iff in *.
                        specialize (mge_defs b). inv mge_defs; unfold Genv.find_def in *; unfold fundef.
                        { rewrite SIG in H. inv H. }
                        unfold fundef in *. rewrite FPTR in H. inv H; ss. }
                      unfold System.globalenv.
                      exploit external_call_symbols_preserved; eauto.
                      eapply senv_equiv_ge_link.
                  --- (* step_return *)
                    eapply plus_one.
                    instantiate (2:=E0).
                    econs; i.
                    +++ (* determ *)
                      econs; i.
                      { inv H; inv H0; try (by ss); try (by inv FINAL; inv AFTER; inv STEP).
                        - inv STEP; inv STEP0.
                        - inv FINAL; inv FINAL0. inv AFTER; inv AFTER0.
                          split; eauto.
                          { econs. }
                          { ii; ss. repeat f_equal. des.
                            determ_tac typify_c_dtm.
                          }
                      }
                      { inv FINAL. }
                      { red. i. inv H; auto. inv STEP. }
                    +++ (* step *)
                      ss. eapply step_return; ss.
                      admit "remove this".
                  --- traceEq.
               ** traceEq.
            ++ right. eapply CIH.
               { econs. ss. }
               { ss. eapply preservation_prog; eauto. }
      + (* initial state *)
        inversion INITSRC; subst; ss.
        left. econs; i.
        * (* FINAL *)
          inv FINALSRC.
        * econs; i; cycle 1.
          -- (* receptive at *)
            econs; i.
            ++ inv H3; inv H5.
               { inv H4. eexists. econs 2.
                 eapply step_internal_function; eauto.
               }
               { exploit external_call_receptive; eauto. i. des.
                 eexists. econs 2.
                 eapply step_external_function; eauto. }
            ++ red. i.
               inv H3; inv H4; auto.
               exploit external_call_trace_length; eauto.
          -- (* step *)
            econs; i.
            exploit init_case; eauto. i. des.
            ++ (* main is C internal function *)
              inv CMOD; ss.
              inversion STEPSRC; inv H3; cycle 1.
              ** (* external *)
                exploit MAIN_INTERNAL; eauto. intro INTERN.
                inv MSFIND; ss. des_ifs.
              ** (* internal *)
                esplits.
                --- left. eapply plus_two.
                    econs; i.
                    +++ (* determ *)
                      econs; i.
                      { inv H3; inv H4.
                        split. econs.
                        i. ss.
                        dup LINK_SK_TGT.
                        unfold tge, skenv_link, link_sk, link_list in LINK_SK_TGT0; inversion LINK_SK_TGT0.
                        rewrite -> H5 in *.
                        dup LINK_SK_TGT.
                        exploit find_fptr_owner_determ.
                        unfold tge. eauto.
                        eapply MSFIND. i.
                        generalize dependent st_init0.
                        subst ms0.
                        exploit find_fptr_owner_determ.
                        unfold tge. eapply MSFIND0. eauto. i. des. subst ms.
                        ss. inversion INIT0; inversion INIT. auto.
                        rewrite FINDF0 in FINDF1. inversion FINDF1. subst fd0.
                        rewrite TYPE0 in TYPE1.
                        rewrite TYPE1 in *. auto.
                        (* repeat f_equal. *)
                        (* inversion TYP. inversion TYP0. congruence. *)
                      }
                      { inv FINAL. }
                      { red. i. inv H3. auto. }
                    +++ ss.
                        eapply step_init.
                        { instantiate (1 := modsem skenv_link prog). ss.
                          unfold tge in MSFIND.
                          unfold tge, skenv_link, link_sk, link_list in *.
                          des_ifs.
                          inversion Heq. rewrite <- H4 in MSFIND.
                          eauto.
                        }
                         ss. des_ifs.
                        instantiate (1 := (Csem.Callstate (Vptr b Ptrofs.zero true) (Tfunction Tnil type_int32s cc_default) [] Kstop m0)).
                        assert  (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero = (Vptr b Ptrofs.zero true)).
                        { destruct match_ge_skenv_link. specialize (mge_symb (prog_main prog)).
                          destruct senv_equiv_ge_link; ss.
                          unfold Genv.symbol_address. des_ifs.
                          - unfold fundef in *. rewrite H3 in Heq. rewrite <- prog_sk_tgt in *; ss.
                            rewrite H0 in Heq. clarify.
                          - unfold fundef in *. rewrite H3 in Heq. rewrite <- prog_sk_tgt in *; ss.
                            rewrite H0 in Heq. clarify. (* refact plz *)
                        }
                        assert (Genv.init_mem prog = Some m_init).
                        { eapply SRC_INIT_MEM. }
                        unfold Sk.load_mem in *. Eq. clarify.
                        inv INITTGT; ss; unfold Sk.load_mem in *.
                        rewrite LINK_SK_TGT in INITSK. inversion INITSK. rewrite <- H5 in *.
                        rewrite INIT_MEM in INITMEM. inversion INITMEM. rewrite <- H6 in *.
                        rewrite H3. econs; ss; des_ifs; eauto.
                        { unfold fundef in *.
                          exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero true)); eauto. }
                        { unfold type_of_function in *. clarify.
                          destruct (fn_params f) eqn:T; ss; des_ifs.
                          econs; ss.
                        }
                    +++ (* step_internal *)
                      econs; i.
                      *** (* determ *)
                        econs; i.
                        {
                          inv H3; inv H4; ss; try (by ss); try (by inv FINAL).
                          - inv AT; inv AT0. ss.
                          - inv AT. ss.
                          - inv AT. ss.
                          - inv STEP; inv STEP0; inv H3; inv H4; ss; des_ifs.
                            + des_ifs.
                              exploit alloc_variables_determ. eapply H16. eauto. i. des. subst.
                              exploit bind_parameters_determ. eapply H17. eapply H19. i. subst.
                              split; [ apply match_traces_E0 | i; auto].
                            + unfold fundef in *.
                              exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero true)); eauto.
                              i. ss. des_ifs.
                        }
                        { inv STEP; inv FINAL; inv FINAL0. }
                        { red. i. inv H3; auto.
                          inv STEP; inv H3; auto.
                          exploit external_call_trace_length; eauto. }
                      *** (* step *)
                        instantiate (2:=E0).
                        eapply step_internal. ss.
                        econs 2.
                        inv STEPSRC; inv H3. des_ifs.
                        instantiate (1 := (Csem.State f (fn_body f) Kstop e m2)).
                        eapply step_internal_function; ss; eauto.
                        { des_ifs.
                          unfold fundef in *.
                          exploit (@not_external_function_find_same (Internal f) (Vptr b Ptrofs.zero true)); eauto. }
                        { instantiate (1 := m3).
                          clear -INIT_MEM m_init ge LINK_SK_TGT tprog H17.
                          induction H17; try (by econs).
                          econs; eauto. }
                        { clear -INIT_MEM m_init ge LINK_SK_TGT tprog H18.
                          induction H18; try (by econs).
                          econs; eauto.
                          rewrite <- assign_loc_same in H0. eauto. }
                    +++ traceEq.
                --- (* match state *)
                  right. eapply CIH.
                  { ss. instantiate (1:= 1%nat). inv INITTGT.
                    eapply match_states_intro. ss. }
                  { ss. eapply preservation_prog; eauto. }
            ++ (* main is syscall *)
              inv SYSMOD. inv INITTGT. ss.
              assert (SAME: sk_tgt = sk_link) by (Eq; auto). clear INITSK.
              exploit MAIN_INTERNAL; eauto. i. unfold internal_function_state in H3. des_ifs.
              assert  (Genv.symbol_address (Sk.load_skenv sk_tgt) (AST.prog_main sk_tgt) Ptrofs.zero = (Vptr b Ptrofs.zero true)).
              { destruct match_ge_skenv_link. specialize (mge_symb (prog_main prog)).
                unfold Genv.find_symbol, skenv_link, Genv.symbol_address in *.
                rewrite <- prog_sk_tgt in *.
                unfold Genv.find_symbol in *.
                des_ifs; ss; unfold fundef in *; rewrite mge_symb in Heq0; Eq; auto. }
              rewrite SAME in *. rewrite H4 in *.
              exploit system_internal; eauto. clarify.
    - (* state *)
      right. econs; i; ss.
      + inv MTCHST.
        * inv FINALTGT. inv FINAL. ss. subst.
          esplits.
          { eapply star_refl. }
          econs.
        * inv INITTGT.
      + econs; i.
        * (* step *)
          inv MTCHST; cycle 1.
          { inv INITTGT. }
          inv STEPTGT; ss.
          -- (* step_call *)
            inv AT; ss. des.
            esplits.
            ++ right.
               splits; auto. eapply star_refl.
            ++ right. eapply CIH.
               { econs; eauto. }
               { ss. }
          -- (* step_internal *)
            assert(STEPSRC: Csem.step (globalenv prog) st_src tr st0).
            { exploit cstep_same; eauto. }
            esplits.
            ++ left. eapply plus_one. eauto.
            ++ right. eapply CIH.
               { econs; eauto. }
               { ss. eapply preservation_prog; eauto. }
        * (* progress *)
          specialize (SAFESRC _ (star_refl _ _ _)). des.
          -- (* final *)
            inv SAFESRC; inv MTCHST; cycle 1.
            { inv INITTGT. }
            left. exists r0. econs; ss.
          -- (* step *)
            destruct (classic (is_external ge st_src)).
            ++ (* external *)
              right. inv SAFESRC; inv H0; ss; des_ifs.
              inv MTCHST; cycle 1.
              { inv INITTGT. }
              set ef as XX.
              (* unfold is_external_ef in *. des_ifs. *)
              exists E0. esplits. eapply step_call; ss. econs.
              { unfold Genv.find_funct. des_ifs.
                unfold Genv.find_funct_ptr. des_ifs.
                eapply SkEnv.revive_no_external in Heq0; clarify.
                ss. des_ifs. rewrite Genv.find_funct_ptr_iff in Heq.
                exploit def_same; eauto. i. unfold ge in H0.
                ss. Eq. ss. }
              {
                exists (External ef targs tres cc); ss.
                splits.
                { unfold Genv.find_funct in *. des_ifs.
                  rewrite Genv.find_funct_ptr_iff in *.
                  destruct match_ge_skenv_link.
                  specialize (mge_defs b). inv mge_defs; unfold Genv.find_def in *; ss.
                  - unfold fundef in *. rewrite <- H2 in Heq. clarify.
                  - assert (x = (Gfun (External ef targs tres cc))).
                    { unfold fundef in *. rewrite <- H0 in Heq. clarify. }
                    subst. ss. }
                exploit Genv.find_funct_inversion; eauto. i; des.
                inv WTPROG. eauto.
              }
              { inv WTST; ss. exploit WTKS; eauto. { ii. clarify. } esplits; ss; eauto. rr. des. des_ifs. }
            ++ (* internal *)
              exploit progress_step; eauto.
              Unshelve.
  Qed.

  Lemma transf_xsim_properties
    :
      xsim_properties (Csem.semantics prog) (Sem.sem tprog) nat lt.
  Proof.
    econs; [apply lt_wf| |apply symb_preserved].
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - i. inv INIT0. inv INIT1. clarify.
    - ss. inv INITSRC.
      destruct (classic (exists fd, Genv.find_funct (globalenv prog) (Vptr b Ptrofs.zero true) = Some (Internal fd))).
      + apply match_state_xsim; eauto.
        eapply wt_initial_state; eauto.
        econs; eauto.
      + assert(NOSTEP: Nostep (semantics prog) (Csem.Callstate (Vptr b Ptrofs.zero true)
                                                               (Tfunction Tnil type_int32s cc_default) [] Kstop m0)).
        { ii. rr in H6. des; inv H6; ss; des_ifs.
           - contradict H5; eauto.
           - exploit MAIN_INTERNAL; eauto.
             { econs; eauto. }
             i; des. ss. des_ifs.
        }
        assert(UB: ~safe (semantics prog) (Csem.Callstate (Vptr b Ptrofs.zero true)
                                                          (Tfunction Tnil type_int32s cc_default) [] Kstop m0)).
        { ii; ss. specialize (H6 _ (star_refl _ _ _)). des; ss.
          - inv H6; ss.
          - rr in NOSTEP. contradict NOSTEP; eauto.
        }
        pfold. right. econs; ii; ss.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Csem.semantics prog) (Sem.sem tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.

  End PLANB0.

End PRESERVATION.


Theorem upperbound_b_correct
        (_cprog: Csyntax.program) cprog
        (MAIN: exists main_f,
            (<<INTERNAL: cprog.(prog_defmap) ! (cprog.(prog_main)) = Some (Gfun (Internal main_f))>>)
            /\
            (<<SIG: type_of_function main_f = Tfunction Tnil type_int32s cc_default>>))
        (TYPED: typecheck_program _cprog = Errors.OK cprog)
        (WT_EXTERNAL: forall id ef args res cc vargs m t vres m',
            In (id, Gfun (External ef args res cc)) cprog.(prog_defs) ->
            external_call ef cprog.(globalenv) vargs m t vres m' ->
            wt_val vres res)
  :
    (<<REFINE: improves (Csem.semantics cprog) (Sem.sem (map CsemC.module [cprog]))>>)
.
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  eapply transf_program_correct; eauto.
  { ss. }
  { ii. rr. inv H. ss. des_ifs_safe.
    des.
    apply Genv.find_def_symbol in INTERNAL. des. unfold fundef in *.
    rewrite INTERNAL in *. clarify.
    unfold Genv.find_funct_ptr. des_ifs.
  }
  { eapply typecheck_program_sound; eauto. }
  { admit "remove this". }
Unshelve.
  { admit "remove this". }
Qed.

