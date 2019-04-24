Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program SemProps.
Require Import Equality.
Require Import CtypingC LinkingC2.

Set Implicit Arguments.


Ltac Eq :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
    rewrite H1 in H2; inv H2; Eq
  | [ H1: ?a m= ?b, H2: ?a m= ?c |- _ ] =>
    rewrite H1 in H2; inv H2; Eq
  | _ => idtac
  end.

(* put k1 inside k0 (k1 is executed later) *)
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
  end
.

(* Definition get_cont (st0: Csem.state): option cont := *)
(*   match st0 with *)
(*   | Csem.State _ _ k0 _ _ => Some k0 *)
(*   | Csem.ExprState _ _ k0 _ _ => Some k0 *)
(*   | Csem.Callstate _ _ _ k0 _ => Some k0 *)
(*   | Csem.Returnstate _ k0 _ => Some k0 *)
(*   | _ => None *)
(*   end *)
(* . *)

Lemma app_cont_stop_right
      k0
  :
    <<EQ: app_cont k0 Kstop = k0>>
.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_stop_left
      k0
  :
    <<EQ: app_cont Kstop k0 = k0>>
.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_kstop_inv
      k0 k1
      (APP: app_cont k0 k1 = Kstop)
  :
    k0 = Kstop /\ k1 = Kstop
.
Proof.
  destruct k0; ss.
Qed.

Section PRESERVATION.

  Variable cp_link cp0 cp1: Csyntax.program.
  Variable ctx: Syntax.program.
  Hypothesis FOCUS: link cp0 cp1 = Some cp_link.
  (* Let prog_src := cp_link.(CsemC.module) :: ctx. *)
  (* Let prog_tgt := cp1.(CsemC.module) :: cp2.(CsemC.module) :: ctx. *)
  Let prog_src := ctx ++ [cp_link.(CsemC.module)].
  Let prog_tgt := ctx ++ [cp0.(CsemC.module) ; cp1.(CsemC.module)].
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk prog_src = Some sk_link).
  Notation " 'geof' cp" := (Build_genv (SkEnv.revive (SkEnv.project skenv_link cp.(CSk.of_program signature_of_function)) cp) cp.(prog_comp_env))
                           (at level 50, no associativity, only parsing).
  Let ge_cp_link: genv := geof cp_link.
  Let ge_cp0: genv := geof cp0.
  Let ge_cp1: genv := geof cp1.

  Hypothesis WTPROGLINK: wt_program cp_link.
  Hypothesis WTSKLINK: Sk.wf cp_link.(CsemC.module).
  Hypothesis WTPROG0: wt_program cp0.
  Hypothesis WTSK0: Sk.wf cp0.(CsemC.module).
  Hypothesis WTPROG1: wt_program cp1.
  Hypothesis WTSK1: Sk.wf cp1.(CsemC.module).

  Hypothesis WT_EXTERNALLINK:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp_link.(prog_defs) ->
      external_call ef skenv_link vargs m t vres m' ->
      wt_retval vres res.
  Hypothesis WT_EXTERNAL0:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp0.(prog_defs) ->
      external_call ef skenv_link vargs m t vres m' ->
      wt_retval vres res.
  Hypothesis WT_EXTERNAL1:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp1.(prog_defs) ->
      external_call ef skenv_link vargs m t vres m' ->
      wt_retval vres res.

  Lemma link_sk_match
    :
      <<EQ: link_sk prog_src = link_sk prog_tgt>>
  .
  Proof.
    subst_locals.
    unfold link_sk.
    rewrite ! map_app. ss.
    symmetry.
    eapply link_list_snoc_commut; eauto.
    admit "this should hold - it should be proven somewhere else too. ask @minki".
  Qed.

  Let LINKTGT: link_sk prog_tgt = Some sk_link.
  Proof.
    rewrite link_sk_match in *. ss.
  Qed.

  (* Definition match_prog (p: Csyntax.program) (tp: Sk.t) := *)
  (*   match_program (fun ctx f tf => fundef_of_fundef f = tf) eq p tp. *)

  (* Lemma match_genvs_le A B V W R1 R2 (ge1: Genv.t A V) (ge2: Genv.t B W) *)
  (*       (MATCHGE: Genv.match_genvs R1 ge1 ge2) *)
  (*       (LE: R1 <2= R2) *)
  (*   : *)
  (*     Genv.match_genvs R2 ge1 ge2. *)
  (* Proof. *)
  (*   inv MATCHGE. econs; i; ss; eauto. *)
  (*   cinv (mge_defs b). *)
  (*   - econs 1. *)
  (*   - econs 2. eapply LE; eauto. *)
  (* Qed. *)

  Definition is_focus (cp: Csyntax.program): Prop := cp = cp0 \/ cp = cp1.

  Let INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function cp_link).
  Proof.
    exploit link_includes. eapply LINKSRC.
    subst prog_src. instantiate (1 := (module cp_link)).
    apply in_or_app. ss. auto. ss. Qed.

  Let INCL_FOCUS: forall pgm, is_focus pgm -> SkEnv.includes skenv_link (CSk.of_program signature_of_function pgm).
  Proof.
    i. exploit link_includes. eapply LINKTGT.
    { subst prog_tgt. instantiate (1 := (module pgm)).
      rewrite in_app_iff in *. des; ss. unfold is_focus in H. inv H; subst; auto. }
    inv H; eauto. Qed.

  Inductive sum_cont: list Frame.t -> cont -> Prop :=
  | sum_cont_nil
    :
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
      (K0: exists _f _e _C _k, k0 = (Kcall _f _e _C _tres _k))
      (* (WTTGT: exists ge_cp, wt_state ge_cp (Csem.Callstate _fptr (Tfunction _targs _tres _cconv) _vs k0 _m)) *)
      (WTTGT: wt_state (geof cp) (Csem.Callstate _fptr (Tfunction _targs _tres _cconv) _vs k0 _m))
    :
      sum_cont ((Frame.mk (CsemC.modsem skenv_link cp)
                          (Csem.Callstate _fptr (Tfunction _targs _tres _cconv) _vs k0 _m)) :: tl) k2
  .

  Lemma sum_cont_kstop_inv
        frs
        (SUM: sum_cont frs Kstop)
    :
      frs = []
  .
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
      (* tyargs tyres cconv *)
      (* (TYF: classify_fun tyf = fun_case_f tyargs tyres cconv) *)
      (* (WTVALS: Forall2 val_casted vargs tyargs.(typelist_to_listtype)) *)
    : match_focus_state (Csem.Callstate fptr tyf vargs k m) (Csem.Callstate fptr tyf vargs k1 m) k0
  | return_sate_similar
      vres k k0 k1 m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.Returnstate vres k m) (Csem.Returnstate vres k1 m) k0
  .

  Inductive match_focus: Frame.t -> list Frame.t -> Prop :=
  | match_focus_cons_right
      cst_src cst_tgt
      tl_tgt k_tl_tgt
      (SUM: sum_cont tl_tgt k_tl_tgt)
      (ST: match_focus_state cst_src cst_tgt k_tl_tgt)
      cp
      (FOCUS: is_focus cp)
      (WTSRC: wt_state ge_cp_link cst_src)
      (WTTGT: wt_state (geof cp) cst_tgt)
    :
      match_focus (Frame.mk (CsemC.modsem skenv_link cp_link) cst_src)
                  ((Frame.mk (CsemC.modsem skenv_link cp) cst_tgt) :: tl_tgt)
  .

  Lemma match_focus_nonnil
        fr frs
        (FC: match_focus fr frs)
    :
      <<NONNIL: frs <> []>>
  .
  Proof.
    inv FC; ss.
  Qed.

  Inductive match_stacks: list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_nil
    :
      match_stacks [] []
  | match_stacks_cons_ctx
      tail_src tail_tgt
      (TAIL: match_stacks tail_src tail_tgt)
      hd
    :
      match_stacks (hd :: tail_src) (hd :: tail_tgt)
  | match_stacks_focus
      tail_src tail_tgt
      (TAIL: match_stacks tail_src tail_tgt)
      hd_src hds_tgt
      (HD: match_focus hd_src hds_tgt)
    :
      match_stacks (hd_src :: tail_src) (hds_tgt ++ tail_tgt)
  .

  Lemma match_stacks_right_nil
        frs
        (STK: match_stacks frs [])
    :
      <<NIL: frs = []>>
  .
  Proof.
    (* ginduction frs; ii; ss. *)
    inv STK; ss. destruct hds_tgt, tail_tgt; ss.
    exploit match_focus_nonnil; et. i; ss.
  Qed.

  Inductive match_states : Sem.state -> Sem.state -> Prop :=
  | match_states_normal
      frs_src frs_tgt
      (STK: match_stacks frs_src frs_tgt)
    :
      match_states (State frs_src) (State frs_tgt)
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks frs_src frs_tgt)
    :
      match_states (Callstate args frs_src) (Callstate args frs_tgt)
  .

  Lemma init_fsim
        st_init_src
        (INIT: initial_state prog_src st_init_src)
    :
      exists (i0: unit) st_init_tgt,
        (<<INIT: Dinitial_state (sem prog_tgt) st_init_tgt>>) /\
        (<<MATCH: match_states st_init_src st_init_tgt>>)
  .
  Proof.
    exists tt, st_init_src.
    esplits; eauto.
    { inv INIT. econs; ss; eauto.
      - (* init *)
        econs; ss; eauto. rewrite <- link_sk_match; eauto.
        unfold prog_src in WF. unfold prog_tgt. i. rewrite in_app_iff in IN. des.
        { eapply WF; et. rewrite in_app_iff. et. }
        { ss. des; ss; clarify. }
      - (* dtm *)
        ii. inv INIT0; inv INIT1; ss. f_equal.
        generalize link_sk_match; i. des. rewrite H in *. clarify.
    }
    { inv INIT.
      econs; ss; eauto. econs; ss; eauto.
    }
  Qed.

  Lemma final_bsim
        retv
        frs_src frs_tgt
        (MATCH: match_states (State frs_src) (State frs_tgt))
        (FINAL: final_state (State frs_tgt) retv)
        (SAFESRC: safe (sem prog_src) (State frs_src))
    :
      <<FINAL: final_state (State frs_src) retv>>
  .
  Proof.
    ss.
    inv FINAL. inv MATCH; ss. inv STK; ss.
    - (* ctx *)
      exploit match_stacks_right_nil; eauto. i; des; clarify.
      econs; eauto.
    - (* focus *)
      exploit app_length; try rewrite H1; eauto. intro LEN; ss.
      hexploit match_focus_nonnil; et. i; des.
      destruct hds_tgt; ss. destruct tail_tgt; ss; try xomega. destruct hds_tgt; ss. clarify. clear_tac.
      exploit match_stacks_right_nil; et. i; des; clarify.
      econs; et.
      inv HD. ss. inv SUM.
      inv FINAL0; ss.
      inv ST; ss.
  Qed.

  Lemma final_fsim
        retv
        frs_src frs_tgt
        (MATCH: match_states (State frs_src) (State frs_tgt))
        (FINAL: final_state (State frs_src) retv)
    :
      <<DFINAL: Dfinal_state (sem prog_tgt) (State frs_tgt) retv>>
  .
  Proof.
    rr. econs; ss; et.
    {
      inv FINAL. inv MATCH; ss. inv STK; ss.
      - (* ctx *)
        inv TAIL. econs; et.
      - (* focus *)
        inv TAIL. rewrite app_nil_r in *. inv HD. ss. inv FINAL0; ss. inv ST; ss.
        hexpl app_cont_kstop_inv. clarify.
        hexpl sum_cont_kstop_inv. clarify.
        econs; ss; et.
    }
    { ii; ss. inv FINAL0; inv FINAL1; ss. determ_tac ModSem.final_frame_dtm. rewrite INT in *. clarify. }
    { ii. ss. des_ifs; ss.
      inv FINAL. inv MATCH; ss. inv STK; ss.
      - (* ctx *)
        inv TAIL. inv H; ModSem.tac.
      - (* focus *)
        inv TAIL. rewrite app_nil_r in *. inv FINAL0; ss. inv H; ss; ModSem.tac.
    }
  Qed.

  Section WTMODULE.

  Hypothesis WFSRC: forall md : Mod.t, In md prog_src -> Sk.wf md.
  Hypothesis WFTGT: forall md : Mod.t, In md prog_tgt -> Sk.wf md.

  Lemma id_in_prog
        (prog:Csyntax.program) id
    :
      defs prog id <-> In id (prog_defs_names prog).
  Proof.
    split; i; unfold defs, in_dec, ident_eq in *; destruct (prog_defs_names prog); ss; des_ifs; eauto.
    inv H; clarify.
  Qed.

  Lemma id_not_in_prog
        (prog:Csyntax.program) id
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

  Lemma cp_link_precise
    :
      SkEnv.genv_precise (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) cp_link.
  Proof.
    eapply CSkEnv.project_revive_precise; eauto.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

  Lemma is_focus_precise
        pgm
        (FOCUS1: is_focus pgm)
    :
      SkEnv.genv_precise (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function pgm)) pgm) pgm.
  Proof.
    eapply CSkEnv.project_revive_precise; eauto.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

  Lemma defmap_with_signature
        (cp:Csyntax.program) i g
        (DMAP: (prog_defmap cp) ! i = Some g)
    :
      exists gd, (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some gd.
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H. rewrite DMAP in *. clarify. eauto.
  Qed.

  Lemma defmap_with_signature_internal
        (cp:Csyntax.program) i if_sig
        (DMAP: (prog_defmap cp) ! i = Some (Gfun (Internal if_sig)))
    :
      exists if_sig0, (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some (Gfun (AST.Internal if_sig0)).
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H; rewrite DMAP in *; clarify.
    inv H2. unfold CtypesC.CSk.match_fundef in H3. destruct f2; ss.
    rewrite <- H1. eauto.
  Qed.

  Lemma prog_defmap_exists_gvar
        id func
        (DEFMAP: (prog_defmap cp_link) ! id = Some (Gvar func))
    :
      exists pgm func', is_focus pgm /\ (prog_defmap pgm) ! id = Some (Gvar func').
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    hexploit (link_prog_inv _ _ _ Heq). intro LINKSPEC; des.

    assert(MAIN: AST.prog_main p = AST.prog_main cp0 /\ AST.prog_main p = AST.prog_main cp1).
    { clarify; ss. }
    assert(PUBLIC: AST.prog_public p = AST.prog_public cp0 ++ AST.prog_public cp1).
    { clarify; ss. }
    assert(DEFS: AST.prog_defs p = PTree.elements (PTree.combine link_prog_merge (prog_defmap cp0) (prog_defmap cp1))).
    { clarify; ss. }

    assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
    {
      ii.
      clarify.
      unfold prog_defmap; ss.
      rewrite PTree_Properties.of_list_elements.
      rewrite PTree.gcombine; ss.
    }
    unfold prog_defmap in *. ss.
    rewrite DEFREL in *.
    unfold link_prog_merge in DEFMAP. des_ifs; ss.
    - exploit LINKSPEC0; eauto. i. des.
      clarify.
      Local Transparent Linker_def. ss.
      unfold link_def in H1. des_ifs.
      Local Transparent Linker_fundef. ss.
      unfold link_fundef in Heq4. des_ifs.
      { exists cp0. esplits; eauto. econs; eauto. }
    - clarify. exists cp0. esplits; eauto.
      unfold is_focus. auto.
    - clarify. exists cp1. esplits; eauto.
      unfold is_focus. auto.
  Qed.

  Lemma prog_defmap_same_rev
        pgm id func
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gfun (Internal func))) (* (Internal func))) *)
    :
      (prog_defmap cp_link) ! id = Some (Gfun (Internal func)). (* (Internal func')). *)
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    hexploit (link_prog_inv _ _ _ Heq). intro LINKSPEC; des.

    assert(MAIN: AST.prog_main p = AST.prog_main cp0 /\ AST.prog_main p = AST.prog_main cp1).
    { clarify; ss. }
    assert(PUBLIC: AST.prog_public p = AST.prog_public cp0 ++ AST.prog_public cp1).
    { clarify; ss. }
    assert(DEFS: AST.prog_defs p = PTree.elements (PTree.combine link_prog_merge (prog_defmap cp0) (prog_defmap cp1))).
    { clarify; ss. }

    assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
    {
      ii.
      clarify.
      unfold prog_defmap; ss.
      rewrite PTree_Properties.of_list_elements.
      rewrite PTree.gcombine; ss.
    }
    unfold prog_defmap in *. ss.
    rewrite DEFREL in *.
    unfold link_prog_merge. des_ifs; ss.

    - unfold is_focus in FOC. inv FOC.
      + exploit LINKSPEC0. eapply Heq2. eapply Heq3. i. des_safe. destruct g0. ss; des_ifs; eauto.
        unfold link_def in H1. inv H1.
      + exploit LINKSPEC0. eapply Heq2. eapply Heq3. i. des_safe. destruct g. ss; des_ifs; eauto.
        ss. unfold link_fundef in Heq4. des_ifs. ss.
    - unfold is_focus in FOC. inv FOC.
      + rewrite DMAP in *. clarify.
      + rewrite DMAP in *. clarify.
    - unfold is_focus in FOC. inv FOC.
      + rewrite DMAP in *. clarify.
      + rewrite DMAP in *. clarify.
  Qed.


  Lemma prog_defmap_exists_rev
        pgm id func
        (FOC: is_focus pgm)
        (DMAP: (prog_defmap pgm) ! id = Some (Gfun func)) (* (Internal func))) *)
    :
      exists func', (prog_defmap cp_link) ! id = Some (Gfun func'). (* (Internal func')). *)
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    hexploit (link_prog_inv _ _ _ Heq). intro LINKSPEC; des.

    assert(MAIN: AST.prog_main p = AST.prog_main cp0 /\ AST.prog_main p = AST.prog_main cp1).
    { clarify; ss. }
    assert(PUBLIC: AST.prog_public p = AST.prog_public cp0 ++ AST.prog_public cp1).
    { clarify; ss. }
    assert(DEFS: AST.prog_defs p = PTree.elements (PTree.combine link_prog_merge (prog_defmap cp0) (prog_defmap cp1))).
    { clarify; ss. }

    assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
    {
      ii.
      clarify.
      unfold prog_defmap; ss.
      rewrite PTree_Properties.of_list_elements.
      rewrite PTree.gcombine; ss.
    }
    unfold prog_defmap in *. ss.
    rewrite DEFREL in *.
    unfold link_prog_merge. des_ifs; ss.

    - unfold is_focus in FOC. inv FOC.
      + exploit LINKSPEC0. eapply Heq2. eapply Heq3. i. des_safe. destruct g0. ss; des_ifs; eauto.
        unfold link_def in H1. inv H1.
      + exploit LINKSPEC0. eapply Heq2. eapply Heq3. i. des_safe. destruct g. ss; des_ifs; eauto.
        ss.
    - unfold is_focus in FOC. inv FOC.
      + rewrite DMAP in *. clarify. eauto.
      + rewrite DMAP in *. clarify.
    - unfold is_focus in FOC. inv FOC.
      + rewrite DMAP in *. clarify.
      + rewrite DMAP in *. clarify. eauto.
  Qed.

  Lemma defmap_with_signature_rev
        cp gd i
        (DMAP: (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some gd)
    :
      exists g, (prog_defmap cp) ! i = Some g.
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H. rewrite DMAP in *. clarify. eauto.
  Qed.

  Lemma defmap_with_signature_rev_internal
        cp if_sig i
        (DMAP: (prog_defmap (CSk.of_program signature_of_function cp)) ! i = Some (Gfun (AST.Internal if_sig)))
    :
      exists if_sig0, (prog_defmap cp) ! i = Some (Gfun (Internal if_sig0)).
  Proof.
    exploit (CSk.of_program_prog_defmap cp signature_of_function).
    i. inv H; rewrite DMAP in *. clarify.
    clarify. inv H2. unfold CtypesC.CSk.match_fundef in H4. destruct f1; clarify.
    rewrite <- H0. eauto.
  Qed.

  Lemma invert_symbol_lemma1
        b i0 i cp
        (FOC: is_focus cp)
        (SYMBSKENV : Genv.invert_symbol skenv_link b = Some i0)
        (DEFS: defs (CSk.of_program signature_of_function cp) i)
        (SYMB : Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b = Some i)
    :
      i = i0.
  Proof.
    exploit Genv.invert_find_symbol. eauto. i. exploit Genv.invert_find_symbol. eapply SYMBSKENV. i.
    exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H1.
    exploit SYMBKEEP; eauto. i.
    (* rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i. *)
    rewrite H1 in H.
    exploit Genv.find_invert_symbol. eapply H. i. exploit Genv.find_invert_symbol. eapply H0. i.
    rewrite H2 in H3. clarify.
  Qed.

  Lemma internals_linking
        cp i
        (FOC: is_focus cp)
        (INTERNALS : internals (CSk.of_program signature_of_function cp) i = true)
    :
      internals (CSk.of_program signature_of_function cp_link) i = true.
  Proof.
    rewrite CSk.of_program_internals in *.
    unfold internals in INTERNALS.
    destruct ((prog_defmap cp) ! i) eqn:DMAP; ss.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    hexploit (link_prog_inv _ _ _ Heq). intro LINKSPEC; des.

    assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
    {
      ii.
      clarify.
      unfold prog_defmap; ss.
      rewrite PTree_Properties.of_list_elements.
      rewrite PTree.gcombine; ss.
    }
    Local Transparent Linker_def. ss.
    unfold internals. ss.
    des_ifs; cycle 1.
    { unfold prog_defmap in *. ss.
      rewrite DEFREL in *. unfold link_prog_merge in Heq2. des_ifs.
      exploit LINKSPEC0. eapply Heq3. eapply Heq4. i. des_safe; ss.
      rewrite Heq2 in *; clarify.
      unfold is_focus in *. des; subst; rewrite DMAP in *; clarify. }
    unfold prog_defmap in *. ss.
    rewrite DEFREL in *. unfold link_prog_merge in Heq2.
    des_ifs; ss; unfold is_focus in *; des; subst; rewrite DMAP in *; clarify;
      ss; unfold link_def in *; des_ifs; ss; destruct f; ss; des_ifs; ss.
    do 2 rewrite <- andb_assoc in *. exploit andb_prop; eauto. i. des.
    destruct e1; destruct e2; clarify.
  Qed.

  Lemma prog_def_exists_rev
        cp fptr if_sig
        (FOC: is_focus cp)
        (INTERNAL : Genv.find_funct
                      (SkEnv.project skenv_link (CSk.of_program signature_of_function cp))
                      fptr = Some (AST.Internal if_sig))
    :
      exists if_sig0, Genv.find_funct
                   (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) fptr =
                 Some (AST.Internal if_sig0).
  Proof.
    unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *. unfold Genv.find_def in *. ss.
    rewrite MapsC.PTree_filter_map_spec in INTERNAL. unfold o_bind in *.
    destruct ((Genv.genv_defs skenv_link) ! b) eqn:Hdefs; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. des_ifs.
    destruct ((prog_defmap (CSk.of_program signature_of_function cp)) ! i) eqn:Hdefmap; ss; clarify.
    exploit defmap_with_signature_rev_internal; eauto. i. des.
    assert (exists g', (prog_defmap cp_link) ! i = Some g').
    { exploit prog_defmap_exists_rev; eauto. i. des. eauto. } des.
    assert (exists if_sig0, (prog_defmap cp_link) ! i = Some (Gfun (Internal if_sig0))).
    { Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.

      hexploit (link_prog_inv _ _ _ Heq0). intro LINKSPEC; des.

      assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
      {
        ii.
        clarify.
        unfold prog_defmap; ss.
        rewrite PTree_Properties.of_list_elements.
        rewrite PTree.gcombine; ss.
      }
      unfold prog_defmap in *. ss.
      rewrite DEFREL in *.
      unfold link_prog_merge in H0.
      unfold is_focus in *. inv FOC; subst.

      rewrite H in H0. des_ifs.
      Local Transparent link. ss. des_ifs.

      unfold link_prog_merge.
      rewrite H. ss. eauto.
      unfold link_prog_merge.
      rewrite H. ss. eauto.

      rewrite H in H0. des_ifs.
      Local Transparent link. ss. des_ifs.

      rewrite H0. destruct g0; ss. des_ifs. destruct f; ss. des_ifs. eauto.
      ss. eauto. }

    des. exploit defmap_with_signature_internal; eauto. i. des.
    exists if_sig2.
    rewrite Genv.find_funct_ptr_iff. unfold Genv.find_def. ss.
    rewrite MapsC.PTree_filter_map_spec. rewrite o_bind_ignore. rewrite Hdefs. rewrite Hsymb.
    unfold o_bind. ss. exploit internals_linking; eauto. i. rewrite H3.
    rewrite H2. ss.
  Qed.

  Lemma prog_find_defs_same_rev
        cp b if_sig
        (FOC: is_focus cp)
        (FIND: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) b = Some (Gfun (Internal if_sig)))
    :
      Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) b = Some (Gfun (Internal if_sig)).
  Proof.
    unfold Genv.find_def in FIND. ss. rewrite MapsC.PTree_filter_map_spec in FIND. rewrite o_bind_ignore in FIND. des_ifs.
    destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:SYMB; ss.
    unfold o_bind in FIND. ss. destruct ((prog_defmap cp) ! i) eqn:DMAP; ss. clarify.
    rewrite MapsC.PTree_filter_map_spec in Heq. rewrite o_bind_ignore in Heq. destruct ((Genv.genv_defs skenv_link) ! b) eqn:GENVDEF; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:SYMBSKENV; ss. unfold o_bind in Heq. ss. des_ifs.
    exploit invert_symbol_lemma1; eauto. rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i. subst.
    unfold Genv.find_def. ss. do 2 rewrite MapsC.PTree_filter_map_spec.
    do 2 rewrite o_bind_ignore. rewrite GENVDEF. rewrite SYMBSKENV. unfold o_bind. ss.
    exploit prog_defmap_same_rev; eauto. i. des_safe.
    des_ifs; cycle 1.
    - exploit defmap_with_signature; eauto. i. des_safe. rewrite H0 in Heq1. ss.
    - exploit internals_linking; eauto. i. rewrite H0 in *; clarify.
    - exploit SkEnv.project_impl_spec. eapply INCL. i. inv H0.
      exploit SYMBKEEP. rewrite <- defs_prog_defmap. exploit defmap_with_signature. eapply H. i. eauto. i.
      exploit Genv.invert_find_symbol. eapply SYMBSKENV. i. rewrite <- H0 in H1.
      exploit Genv.find_invert_symbol. eauto. i. rewrite H2. ss. rewrite H. eauto.
  Qed.

  Lemma prog_find_defs_revive_rev
        cp b func
        (FOC: is_focus cp)
        (FIND: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) b = Some (Gfun func))
    :
      exists func', Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) b = Some (Gfun func').
  Proof.
    unfold Genv.find_def in FIND. ss. rewrite MapsC.PTree_filter_map_spec in FIND. rewrite o_bind_ignore in FIND. des_ifs.
    destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:SYMB; ss.
    unfold o_bind in FIND. ss. destruct ((prog_defmap cp) ! i) eqn:DMAP; ss. clarify.
    rewrite MapsC.PTree_filter_map_spec in Heq. rewrite o_bind_ignore in Heq. destruct ((Genv.genv_defs skenv_link) ! b) eqn:GENVDEF; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:SYMBSKENV; ss. unfold o_bind in Heq. ss. des_ifs.
    exploit invert_symbol_lemma1; eauto. rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i. subst.
    unfold Genv.find_def. ss. do 2 rewrite MapsC.PTree_filter_map_spec.
    do 2 rewrite o_bind_ignore. rewrite GENVDEF. rewrite SYMBSKENV. unfold o_bind. ss.
    exploit prog_defmap_exists_rev; eauto. i. des_safe.
    exists func'. des_ifs; cycle 1.
    - exploit defmap_with_signature; eauto. i. des_safe. rewrite H0 in Heq1. ss.
    - exploit internals_linking; eauto. i. rewrite H0 in *; clarify.
    - exploit SkEnv.project_impl_spec. eapply INCL. i. inv H0.
      exploit SYMBKEEP. rewrite <- defs_prog_defmap. exploit defmap_with_signature. eapply H. i. eauto. i.
      exploit Genv.invert_find_symbol. eapply SYMBSKENV. i. rewrite <- H0 in H1.
      exploit Genv.find_invert_symbol. eauto. i. rewrite H2. ss. rewrite H. eauto.
  Qed.

  Lemma prog_defmap_exists
        id func
        (DEFMAP: (prog_defmap cp_link) ! id = Some (Gfun (Internal func)))
    :
      exists pgm, is_focus pgm /\ (prog_defmap pgm) ! id = Some (Gfun (Internal func)).
    (* /\ linkorder func' func)).  *)
  Proof.
    Local Transparent Linker_program. ss.
    unfold link_program in *. des_ifs.
    Local Transparent Linker_prog. ss.

    hexploit (link_prog_inv _ _ _ Heq). intro LINKSPEC; des.

    assert(MAIN: AST.prog_main p = AST.prog_main cp0 /\ AST.prog_main p = AST.prog_main cp1).
    { clarify; ss. }
    assert(PUBLIC: AST.prog_public p = AST.prog_public cp0 ++ AST.prog_public cp1).
    { clarify; ss. }
    assert(DEFS: AST.prog_defs p = PTree.elements (PTree.combine link_prog_merge (prog_defmap cp0) (prog_defmap cp1))).
    { clarify; ss. }

    assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge (prog_defmap cp0) ! id (prog_defmap cp1) ! id).
    {
      ii.
      clarify.
      unfold prog_defmap; ss.
      rewrite PTree_Properties.of_list_elements.
      rewrite PTree.gcombine; ss.
    }
    unfold prog_defmap in *. ss.
    rewrite DEFREL in *.
    unfold link_prog_merge in DEFMAP. des_ifs; ss.
    - exploit LINKSPEC0; eauto. i. des.
      clarify.
      Local Transparent Linker_def. ss.
      unfold link_def in H1. des_ifs.
      Local Transparent Linker_fundef. ss.
      unfold link_fundef in Heq4. des_ifs.
      { exists cp0. esplits; eauto. econs; eauto. }
      { exists cp1. esplits; eauto. econs 2; eauto. }
    - clarify. exists cp0. esplits; eauto.
      unfold is_focus. auto.
    - clarify. exists cp1. esplits; eauto.
      unfold is_focus. auto.
  Qed.

  Lemma prog_def_same
        b if_sig
        (FIND: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) cp_link) b = Some (Gfun (Internal if_sig)))
    :
      exists cp, is_focus cp /\ Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) cp) b = Some (Gfun (Internal if_sig)).
  Proof.
    unfold Genv.find_def in *. ss.
    rewrite MapsC.PTree_filter_map_spec in *. rewrite o_bind_ignore in *. des_ifs.
    destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:SYMB; ss.
    unfold o_bind in FIND. ss.
    destruct ((prog_defmap cp_link) ! i) eqn:DMAP; ss. clarify.
    exploit prog_defmap_exists; eauto. i. des.
    exists pgm. split; eauto.
    rewrite MapsC.PTree_filter_map_spec in *. rewrite o_bind_ignore in *.
    des_ifs. destruct (Genv.invert_symbol skenv_link b) eqn:SYMBSKENV; ss.
    unfold o_bind in *. ss.
    assert (i = i0).
    { exploit SkEnv.project_impl_spec. eapply INCL; eauto. i. inv H1.
      exploit SYMBKEEP. rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i.
      exploit Genv.invert_find_symbol. eapply SYMB. i. des. rewrite H2 in H1. symmetry in H1.
      exploit Genv.find_invert_symbol. eapply H1. i. rewrite H3 in SYMBSKENV. clarify. }

    des_ifs.
    assert (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function pgm)) b = Some i0).
    { exploit SkEnv.project_impl_spec. eapply INCL_FOCUS; eauto. i. inv H1.
      exploit SYMBKEEP. rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i.
      exploit Genv.invert_find_symbol. eapply SYMBSKENV. i. des. rewrite H2 in H1.
      eapply Genv.find_invert_symbol; eauto. }
    rewrite H1. ss. rewrite H0. ss.

    { (* contradiction *)
      destruct (Genv.invert_symbol skenv_link b) eqn:SYMBSKENV; ss.
      rewrite MapsC.PTree_filter_map_spec in *. rewrite o_bind_ignore in *.
      des_ifs.
      assert (i = i0).
      { exploit SkEnv.project_impl_spec. eapply INCL; eauto. i. inv H1.
        exploit SYMBKEEP. rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i.
        exploit Genv.invert_find_symbol. eapply SYMB. i. des. rewrite H2 in H1. symmetry in H1.
        exploit Genv.find_invert_symbol. eapply H1. i. rewrite H3 in SYMBSKENV. clarify. } subst.
      rewrite SYMBSKENV in *. unfold o_bind in *. ss. des_ifs.
      exploit defmap_with_signature. eauto. i. des.
      rewrite H1 in Heq0. ss. rewrite CSk.of_program_internals in Heq1.
      unfold internals in Heq1. des_ifs. }
  Qed.

  Lemma prog_def_exists
        if_sig fptr
        (INTERNAL : Genv.find_funct (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) fptr =
                    Some (AST.Internal if_sig))
    :
      exists pgm, is_focus pgm /\ exists sig, Genv.find_funct (ModSem.skenv (modsem skenv_link pgm)) fptr = Some (AST.Internal sig).
  Proof.
    unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *. unfold Genv.find_def in *. ss.
    rewrite MapsC.PTree_filter_map_spec in INTERNAL. unfold o_bind in *.
    destruct ((Genv.genv_defs skenv_link) ! b) eqn:Hdefs; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. des_ifs.
    rewrite CSk.of_program_internals in Heq. unfold internals in Heq. des_ifs.
    destruct ((prog_defmap (CSk.of_program signature_of_function cp_link)) ! i) eqn:Hdefmap; ss; clarify.
    exploit CSk.of_program_prog_defmap. instantiate (1:=cp_link). instantiate (1:=signature_of_function). instantiate (1:= i).
    intros MAPREL.
    destruct g0; ss; cycle 1.
    { inv MAPREL.
      - rewrite Heq0 in H0. clarify.
      - rewrite Heq0 in H. rewrite Hdefmap in H0. clarify. inv H1. }
    destruct f; ss; cycle 1.
    { inv MAPREL.
      - rewrite Heq0 in H0. clarify.
      - rewrite Heq0 in H. rewrite Hdefmap in H0. clarify. inv H1. inv H3. }
    exploit prog_defmap_exists; eauto. i. des.
    exists pgm. splits; eauto.
    exploit is_focus_precise; eauto. i. inv H1.

    exploit P2GE; eauto. i. des; ss.
    assert (b0 = b).
    { exploit Genv.invert_find_symbol. eauto. i.
      clear -SYMB H1. unfold Genv.find_symbol in *.
      ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs. }
    subst.

    subst. unfold Genv.find_def in DEF. ss. rewrite MapsC.PTree_filter_map_spec in DEF.
    rewrite o_bind_ignore in DEF. des_ifs. rewrite MapsC.PTree_filter_map_spec in Heq1.
    rewrite o_bind_ignore in Heq1. rewrite Hdefs in Heq1. rewrite Hsymb in Heq1. ss.

    unfold o_bind in Heq1. ss. des_ifs. ss.
    unfold internals in Heq2. des_ifs.
    exploit CSk.of_program_prog_defmap. instantiate (1:=pgm). instantiate (1:=signature_of_function). instantiate (1:= i).
    intros MAPREL1.
    destruct g1; ss; cycle 1.
    { inv MAPREL1.
      - rewrite Heq3 in H3. clarify.
      - rewrite H0 in H1. rewrite Heq3 in H2. clarify. inv H3. }
    destruct f0; ss; cycle 1.
    { inv MAPREL1.
      - rewrite Heq3 in H3. clarify.
      - rewrite H0 in H1. rewrite Heq3 in H2. clarify. inv H3. inv H5. }
    exists s. rewrite Genv.find_funct_ptr_iff.
    unfold Genv.find_def. ss. rewrite MapsC.PTree_filter_map_spec. rewrite o_bind_ignore. rewrite Hdefs. rewrite Hsymb.
    unfold o_bind. ss. unfold internals. rewrite Heq3. simpl. ss.
  Qed.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms0)
        (FIND1: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    eapply SemProps.find_fptr_owner_determ; ss;
      try rewrite LINKTGT; eauto.
  Qed.

  Lemma same_prog
        cp2 cp_top blk if_sig1 if_sig2
        (FOC1 : is_focus cp2)
        (FOC2: is_focus cp_top)
        (INTERNAL1: Genv.find_def (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) blk =
                    Some (Gfun (AST.Internal if_sig1)))
        (INTERNAL2: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp2)) cp2) blk =
                    Some (Gfun (Internal if_sig2)))
    :
      cp2 = cp_top.
  Proof.
    unfold is_focus in *. inv FOC1; inv FOC2; subst; auto.
    (* H0 && INTERNAL contradiction *)
    - unfold Genv.find_def in *. ss. rewrite MapsC.PTree_filter_map_spec in *.
      rewrite o_bind_ignore in *. des_ifs.
      destruct (Genv.invert_symbol skenv_link blk) eqn:SYMBSKENV; ss.
      destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp0)) blk) eqn:SYMB; ss.
      unfold o_bind in INTERNAL1, INTERNAL2. ss.
      destruct ((prog_defmap cp0) ! i0) eqn:DMAP; ss.
      exploit invert_symbol_lemma1; eauto. unfold is_focus. auto.
      rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i. subst.
      destruct (internals (CSk.of_program signature_of_function cp1) i) eqn:INTERNALS; ss.
      destruct ((prog_defmap (CSk.of_program signature_of_function cp1)) ! i) eqn:DMAP0; ss. clarify.
      exploit (CSk.of_program_prog_defmap cp1 signature_of_function).
      instantiate (1 := i). i. inv H; rewrite DMAP0 in *; clarify.
      inv H2. unfold CtypesC.CSk.match_fundef in H4. destruct f1; clarify.

      Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.

      hexploit (link_prog_inv _ _ _ Heq1). intro LINKSPEC; des_safe.

      symmetry in H0.
      exploit LINKSPEC0. eauto. eapply H0. i. des_safe. destruct H3.

      Local Transparent link. ss.
    - unfold Genv.find_def in *. ss. rewrite MapsC.PTree_filter_map_spec in *.
      rewrite o_bind_ignore in *. des_ifs.
      destruct (Genv.invert_symbol skenv_link blk) eqn:SYMBSKENV; ss.
      destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp1)) blk) eqn:SYMB; ss.
      unfold o_bind in INTERNAL1, INTERNAL2; ss.
      destruct ((prog_defmap cp1) ! i0) eqn:DMAP; ss.
      exploit invert_symbol_lemma1; eauto. unfold is_focus. auto.
      rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i. subst.
      destruct (internals (CSk.of_program signature_of_function cp0) i) eqn:INTERNALS; ss.
      destruct ((prog_defmap (CSk.of_program signature_of_function cp0)) ! i) eqn:DMAP0; ss. clarify.
      exploit (CSk.of_program_prog_defmap cp0 signature_of_function).
      instantiate (1 := i). i. inv H; rewrite DMAP0 in *; clarify.
      inv H2. unfold CtypesC.CSk.match_fundef in H4. destruct f1; clarify.

      Local Transparent Linker_program. ss.
      unfold link_program in *. des_ifs.
      Local Transparent Linker_prog. ss.

      hexploit (link_prog_inv _ _ _ Heq1). intro LINKSPEC; des_safe.

      symmetry in H0.
      exploit LINKSPEC0. eapply H0. eauto. i. des_safe. destruct H3.

      Local Transparent link. ss.
  Qed.

  Lemma msfind_fsim
        fptr ms
        (MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms)
    :
      (<<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms>>) \/
      (exists cp, (<<ISFOCSRC: ms = CsemC.modsem skenv_link cp_link>>)
                  /\ (<<ISFOCTGT: is_focus cp>>)
                  /\ (<<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr (CsemC.modsem skenv_link cp)>>))
  .
  Proof.
    unfold load_genv in *. ss. inv MSFIND. ss. des.
    { clarify. left. econs; et. ss. left; ss. }
    unfold load_modsems in *.
    rewrite in_map_iff in *. des; ss. clarify. unfold prog_src in MODSEM0.
    rewrite in_app_iff in *. des; ss.
    { left. econs; et. ss. right. rewrite in_map_iff. esplits; et. unfold prog_tgt. rewrite in_app_iff. left; ss. }
    des; ss. clarify.
    right. ss.
    {
      unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *. unfold Genv.find_def in *. ss.
      rewrite MapsC.PTree_filter_map_spec in INTERNAL. unfold o_bind in *.
      destruct ((Genv.genv_defs skenv_link) ! b) eqn:Hdefs; ss.
      destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. des_ifs.
      rewrite CSk.of_program_internals in Heq. unfold internals in Heq. des_ifs.
      destruct ((prog_defmap (CSk.of_program signature_of_function cp_link)) ! i) eqn:Hdefmap; ss; clarify.
      exploit CSk.of_program_prog_defmap. instantiate (1:=cp_link). instantiate (1:=signature_of_function). instantiate (1:= i).
      intros MAPREL.
      destruct g0; ss; cycle 1.
      { inv MAPREL.
        - rewrite Heq0 in H0. clarify.
        - rewrite Heq0 in H. rewrite Hdefmap in H0. clarify. inv H1. }
      destruct f; ss; cycle 1.
      { inv MAPREL.
        - rewrite Heq0 in H0. clarify.
        - rewrite Heq0 in H. rewrite Hdefmap in H0. clarify. inv H1. inv H3. }
      exploit prog_defmap_exists; eauto. i. des.
      exists pgm. splits; eauto.
      exploit is_focus_precise; eauto. i. inv H1.

      exploit P2GE; eauto. i. des; ss.
      assert (b0 = b).
      { exploit Genv.invert_find_symbol. eauto. i.
        clear -SYMB H1. unfold Genv.find_symbol in *.
        ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs. }
      subst.

      subst. unfold Genv.find_def in DEF. ss. rewrite MapsC.PTree_filter_map_spec in DEF.
      rewrite o_bind_ignore in DEF. des_ifs. rewrite MapsC.PTree_filter_map_spec in Heq1.
      rewrite o_bind_ignore in Heq1. rewrite Hdefs in Heq1. rewrite Hsymb in Heq1. ss.

      unfold o_bind in Heq1. ss. des_ifs. ss.
      unfold internals in Heq2. des_ifs.
      exploit CSk.of_program_prog_defmap. instantiate (1:=pgm). instantiate (1:=signature_of_function). instantiate (1:= i).
      intros MAPREL1.
      destruct g1; ss; cycle 1.
      { inv MAPREL1.
        - rewrite Heq3 in H3. clarify.
        - rewrite H0 in H1. rewrite Heq3 in H2. clarify. inv H3. }
      destruct f0; ss; cycle 1.
      { inv MAPREL1.
        - rewrite Heq3 in H3. clarify.
        - rewrite H0 in H1. rewrite Heq3 in H2. clarify. inv H3. inv H5. }
      econs; eauto; ss.
      - right. subst prog_tgt.
        rewrite in_map_iff. exists (module pgm); ss.
        split; unfold flip; ss.
        rewrite in_app_iff; right. inv H.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. }
      - des_ifs.
        rewrite Genv.find_funct_ptr_iff.
        unfold Genv.find_def. ss. rewrite MapsC.PTree_filter_map_spec. rewrite o_bind_ignore. rewrite Hdefs. rewrite Hsymb.
        unfold o_bind. ss. unfold internals. rewrite Heq3. ss. }
  Qed.

  Lemma msfind_bsim
        fptr ms
        (MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms)
    :
      (<<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms>>) \/
      ((<<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr (CsemC.modsem skenv_link cp_link)>>)
       /\ exists cp, (<<ISFOCSRC: ms = CsemC.modsem skenv_link cp>>)
                     /\ (<<ISFOCTGT: is_focus cp>>))
  .
  Proof.
    unfold load_genv in *. ss. inv MSFIND. ss. des.
    { clarify. left. econs; et. ss. left; ss. }
    unfold load_modsems in *.
    rewrite in_map_iff in *. des; ss. clarify. unfold prog_tgt in MODSEM0.
    rewrite in_app_iff in *. des; ss.
    { left. econs; et. ss. right. rewrite in_map_iff. esplits; et. unfold prog_src. rewrite in_app_iff. left; ss. }
    des; ss.
    - clarify.
      right.
      unfold flip. ss.
      esplits; et; rr; et.
      exploit prog_def_exists_rev; eauto. unfold is_focus. auto. i. des.
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
    - clarify.
      right.
      unfold flip. ss.
      esplits; et; rr; et.
      exploit prog_def_exists_rev; eauto. unfold is_focus. auto. i. des.
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
  Qed.

  Lemma app_cont_call_cont_strong
        k0 k1
        (APP: is_call_cont_strong (app_cont k0 k1))
    :
      <<CONT: is_call_cont_strong k0>>
  .
  Proof.
    r in APP. rr. des_ifs. exploit app_cont_stop_left; et. i.
  Abort.

  Lemma preservation_cp_link
        st0 tr st1
        (WT: wt_state ge_cp_link st0)
        (* (INTERNAL: ~ Ctyping.is_external ge_cp_link st0) *)
        (STEP: Csem.step skenv_link ge_cp_link st0 tr st1)
    :
      <<WT: wt_state ge_cp_link st1>>
  .
  Proof.
    (* eapply preservation_internal; try refl; et. *)
    eapply preservation; try apply STEP; try refl; et; destruct cp_link_precise.
    - ii. red. unfold ge_cp_link in *. ss.
      exploit GE2P; eauto. i. des.
      eapply Genv.find_invert_symbol in SYMB. eapply Genv.find_invert_symbol in SYMB0.
      unfold Genv.invert_symbol in *. ss. rewrite SYMB in *. clarify.
    - ii. exploit GE2P; eauto. i. des. unfold ge_cp_link. ss. exists id. eauto.
  Qed.

  Lemma preservation_cp_focus
        cp st0 tr st1
        (FOC: is_focus cp)
        (WT: wt_state (geof cp) st0)
        (* (INTERNAL: ~ Ctyping.is_external (geof cp) st0) *)
        (STEP: Csem.step skenv_link (geof cp) st0 tr st1)
    :
      <<WT: wt_state (geof cp) st1>>
  .
  Proof.
    exploit is_focus_precise; eauto. i. inv H.
    rr in FOC. des; clarify.
    - eapply preservation; try apply STEP; try refl; et.
      + ii. ss. exploit GE2P; eauto. i. des.
        eapply Genv.find_invert_symbol in SYMB. eapply Genv.find_invert_symbol in SYMB0.
        unfold Genv.invert_symbol in *. ss. rewrite SYMB in *. clarify.
      + i. exploit GE2P; eauto. i. des. eauto.
    - eapply preservation; try refl; et.
      + ii. ss. exploit GE2P; eauto. i. des.
        eapply Genv.find_invert_symbol in SYMB. eapply Genv.find_invert_symbol in SYMB0.
        unfold Genv.invert_symbol in *. ss. rewrite SYMB in *. clarify.
      + i. exploit GE2P; eauto. i. des. eauto.
  Qed.

  Lemma preservation_alloc
        cp_top m1 e l m0
        (FOCUS1 : is_focus cp_top)
        (ALLOC : alloc_variables ge_cp_link empty_env m0
                   l e m1)
        (COMP : Forall (fun t : type => complete_type (prog_comp_env cp_top) t)
                       (map snd l))
    :
      alloc_variables
       {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) cp_top;
          genv_cenv := prog_comp_env cp_top |} empty_env m0 l
        e m1.
  Proof.
    induction ALLOC.
    - econs.
    - ss. inv COMP.
      assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
      { i. unfold link_program in *. des_ifs. ss. des_safe.
        rr in FOCUS1. des; subst.
        exploit a0; eauto. exploit a1; eauto. }
      exploit sizeof_stable; eauto.
      i. eapply IHALLOC in H3. des.
      econs; eauto. simpl. rewrite <- H1. eauto.
  Qed.

  Lemma preservation_bind_param
        cp_top m1 e l l' m2 vs_arg
        (FOCUS1 : is_focus cp_top)
        (PARAM : bind_parameters skenv_link ge_cp_link e m1 l vs_arg m2)
        (COMP : Forall (fun t : type => complete_type (prog_comp_env cp_top) t) (map snd (l ++ l')))
    :
      bind_parameters skenv_link
                      {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) cp_top;
                         genv_cenv := prog_comp_env cp_top |} e m1
                      l vs_arg m2.
  Proof.
    induction PARAM.
    - econs.
    - ss. inv COMP.
      exploit IHPARAM; eauto. i. econs; eauto.
      inv H0.
      * econs; eauto.
      * econs 2; eauto.
      * assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
        { i. unfold link_program in *. des_ifs. ss. des_safe.
          rr in FOCUS1. clear H7. des; subst.
          exploit a0; eauto. exploit a1; eauto. }
        des; econs 3; eauto; ss;
          destruct ty; ss; des_ifs; exploit H0; eauto; i; rewrite Heq0 in H10; inv H10; eauto.
  Qed.

  Lemma alloc_variable_dtm
        genv e m0 l e1 m3 e2 m5
        (ALLOC1: alloc_variables genv e m0 l e1 m3)
        (ALLOC2: alloc_variables genv e m0 l e2 m5)
    :
      e1 = e2 /\ m3 = m5.
  Proof.
    clear -ALLOC1 ALLOC2.
    revert ALLOC1. revert ALLOC2. revert m5. revert e2. revert m3. revert e1.
    revert m0. revert e.
    induction l.
    i. inv ALLOC1; inv ALLOC2. split; auto.
    i. inv ALLOC1; inv ALLOC2.
    rewrite H3 in H8. inv H8.
    exploit IHl. eapply H6. eapply H9. i. des. subst. split; eauto.
  Qed.

  Lemma assign_loc_dtm:
        forall senv genv ty m3 b ofs v1 tr m1,
        assign_loc senv genv ty m3 b ofs v1 tr m1 ->
        forall m0, assign_loc senv genv ty m3 b ofs v1 tr m0 -> m1 = m0.
  Proof.
    induction 1; intros m0 EV; inv EV; f_equal; Eq; clarify.
    clear -H1 H4.
    revert H4. revert m0.
    induction H1; intros m0 EV; inv EV; f_equal; Eq; clarify.
  Qed.

  Lemma bind_param_dtm
        senv genv e1 m3 l vs_arg m4 m6
        (BPARAM1: bind_parameters senv genv e1 m3
                                  l vs_arg m4)
        (BPARAM2: bind_parameters senv genv e1 m3
                                  l vs_arg m6)
    :
      m4 = m6.
  Proof.
    clear -BPARAM1 BPARAM2.
    revert BPARAM1. revert BPARAM2. revert m4. revert m6. revert vs_arg. revert m3. revert e1.
    induction l.
    i. inv BPARAM1. inv BPARAM2. auto.
    i. inv BPARAM1. inv BPARAM2. auto.
    Eq.
    exploit assign_loc_dtm. eapply H3. eapply H10. i. subst.
    exploit IHl. eapply H6. eapply H11. i. eauto. Qed.

  Lemma match_xsim
        st_src0 st_tgt0
        (MATCH: match_states st_src0 st_tgt0)
    :
      <<XSIM: xsim (sem prog_src) (sem prog_tgt) bot2 tt st_src0 st_tgt0>>
  .
  Proof.
    revert_until LINKTGT.
    pcofix CIH. i. pfold.
    dup LINKSRC. sguard in LINKSRC.

    inv MATCH.
    - (* normal state *)
      ss.
      destruct frs_src; ss.
      { inv STK. left. right.
        econs 1; eauto.
        - i. ss. econs. eauto. i. ss. inv FINAL0; inv FINAL1.
          i. inv FINAL.
        - econs 1; eauto. i. inv STEPSRC. }
      rename t into fr_src.
      destruct frs_tgt; ss.
      { exploit match_stacks_right_nil; et. i; des. clarify. }
      rename t into fr_tgt.
      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
      { (* tgt call *)

        (* fsim *)
        left. right. econs; et.
        { i. eapply final_fsim; et. econs; et. }

        destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
        - (* src call *)
          econs; ss; cycle 1.
          i. unsguard LINKSRC. rewrite LINKSRC in STEPSRC.
          inv STEPSRC; ss; ModSem.tac.
          esplits; eauto.
          { left. split; cycle 1.
            {
              (* receptiveness *)
              econs. ii. inv H1; ModSem.tac.
              inv H2. eexists. eapply step_call. instantiate (1:=args). eauto.
              ii. inv H1; ModSem.tac. ss. omega. }
            eapply plus_one. econs; et.
            { (* determ *)
              econs.
              - ii. ss. des_ifs.
                clear H0.
                inv H1; inv H2; ModSem.tac.
                + split. econs. i. exploit ModSem.at_external_dtm. eapply AT0. eauto. i. subst. auto.
                + assert (ModSem.is_step (Frame.ms fr_tgt) (Frame.st fr_tgt)).
                  { unfold ModSem.is_step. ss. eauto. }
                  exfalso; eapply ModSem.call_step_disjoint. split. eapply H. eauto.
                + exfalso; eapply ModSem.call_return_disjoint. split. eauto. eauto.
              - i. ss. inv FINAL.
                eapply ModSem.call_return_disjoint. split. eapply H. eauto.
              - ii. inv H1; ss; try omega.
                exfalso; eapply ModSem.call_step_disjoint. split. eapply H. eauto. }
            econs; eauto.
            instantiate (1:= args).
            sguard in LINKSRC.
            inv STK; ss. inv HD; ss. des. clarify. ss.
            inv AT; ss.
            inv ST; ss.
            econs; ss; et.
            - destruct cp_link_precise.
              unfold Genv.find_funct in EXTERNAL. destruct fptr_arg; ss. destruct b0; ss. destruct (Ptrofs.eq_dec i Ptrofs.zero); ss.
              unfold Genv.find_funct_ptr in EXTERNAL. des_ifs.
              + (* None or Gvar *)
                unfold Genv.find_funct. des_ifs. unfold Genv.find_funct_ptr. des_ifs.
                unfold Genv.find_def in Heq, Heq0. ss. rewrite MapsC.PTree_filter_map_spec in *. rewrite o_bind_ignore in *.
                des_ifs.
                destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) b) eqn:SYMB; ss.
                destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp)) b) eqn:SYMB0; ss.
                unfold o_bind in Heq, Heq0. ss.
                destruct ((prog_defmap cp_link) ! i) eqn:DMAP; ss; clarify.
                destruct ((prog_defmap cp) ! i0) eqn:DMAP0; ss; clarify.
                assert (i = i0).
                { exploit Genv.invert_find_symbol. eauto. i. exploit Genv.invert_find_symbol. eapply SYMB. i.
                  exploit SkEnv.project_impl_spec. eauto. i. inv H3.
                  exploit SYMBKEEP; eauto. rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i.
                  rewrite H3 in H2.
                  exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H4.
                  exploit SYMBKEEP0; eauto. rewrite <- defs_prog_defmap. eapply defmap_with_signature; eauto. i.
                  rewrite H4 in H1.
                  exploit Genv.find_invert_symbol. eauto. i. exploit Genv.find_invert_symbol. eapply H1. i.
                  rewrite H5 in H6. clarify. }
                subst. exploit prog_defmap_exists_rev. eauto. eauto. i. inv H1. rewrite DMAP in *. clarify.
              + unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs.
                exploit prog_find_defs_revive_rev; eauto. i. des.
                unfold fundef in *. rewrite Heq in H1. clarify.
            - rr in H. des. inv H. ss.
          }
          {
            right. eapply CIH; et.
            econs; et.
          }
        - (* src step *)
          inv STK; ss.
          econs; ss; cycle 1.
          i. unsguard LINKSRC. rewrite LINKSRC in STEPSRC.
          (* i; des_ifs. *)

          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. contradict H0. rr. eauto. }
          { exfalso.
            inv HD; ss. clarify.
            clear - FINAL ST H.
            rr in H. des. ss. inv H; inv FINAL; inv ST.
          }
          dup H. rename H1 into ISCALLTGT.
          rr in H. des.
          sguard in LINKSRC.
          inv HD; ss. clarify. ss. inv H. ss. clarify.
          inv ST.
          rr in STEP. des; try (by inv STEP; ss).
          folder.
          inv STEP; ss; cycle 1.
          { destruct (classic(is_external_ef ef)).
            - exfalso.
              unfold Genv.find_funct in FPTR. des_ifs.
              rewrite Genv.find_funct_ptr_iff in FPTR. exploit CSkEnv.project_revive_no_external; eauto.
              unfold skenv_link. eapply SkEnv.load_skenv_wf. eapply link_list_preserves_wf_sk; eauto.
            - admit "Contradiction. by FPTR, H, ISCALLTGT". }
          assert(TGTFIND: exists cp_top,
                    <<FINDMS: Ge.find_fptr_owner (load_genv prog_tgt skenv_link)
                                                 fptr_arg (CsemC.modsem skenv_link cp_top)>>
                              /\ <<FOCUS: is_focus cp_top>>).
          (* actually it is counterpart of current cp *)
          { unfold Genv.find_funct in FPTR. des_ifs.
            rewrite Genv.find_funct_ptr_iff in FPTR.
            unsguard LINKSRC. destruct cp_link_precise.
            exploit GE2P. eauto. i.
            sguard in LINKSRC. des_safe.
            exploit prog_defmap_exists. eauto. i. des_safe. exists pgm. split; auto.
            exploit (CSk.of_program_prog_defmap pgm signature_of_function).
            i. inv H2. rewrite H1 in *. clarify.
            assert (exists func, (prog_defmap (CSk.of_program signature_of_function pgm)) ! id = Some (Gfun (AST.Internal func))).
            { rewrite H1 in *. clarify. inv H5. unfold CtypesC.CSk.match_fundef in H6. destruct f2; clarify.
              exists s. rewrite H4. auto. } des.

            red. econs. ss. right. unfold prog_tgt.
            unfold load_modsems in *. rewrite list_append_map. rewrite in_app_iff. right.
            unfold is_focus in H. inv H; subst; ss; auto.
            rewrite <- CsemC.module_obligation_1.
            ss. des_ifs. rewrite Genv.find_funct_ptr_iff.
            assert (Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) id = Some b).
            { unfold Genv.find_symbol in SYMB. ss. }
            exploit SkEnv.project_impl_spec. eauto. i. inv H10.
            exploit (CSk.of_program_prog_defmap cp_link signature_of_function).
            i. inv H10. rewrite PROG in *. clarify. eauto. i.
            exploit SYMBKEEP. rewrite <- defs_prog_defmap. eauto. i. rewrite H10 in *.
            unfold Genv.find_def. ss. rewrite MapsC.PTree_filter_map_spec. rewrite o_bind_ignore.
            rewrite Genv.find_funct_ptr_iff in SIG.
            unfold Genv.find_def in SIG. rewrite SIG.
            exploit Genv.find_invert_symbol. eapply H6. i. rewrite H14. unfold o_bind. ss.
            unfold internals. rewrite H2. ss. }
          des.

          unfold Genv.find_funct, Genv.find_funct_ptr in SIG, FPTR. des_ifs. rename b into blk.
          assert(SYMB: exists id, Genv.find_symbol (geof cp_top) id = Some blk).
          { inv FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            unfold Genv.find_def in INTERNAL. ss.
            rewrite MapsC.PTree_filter_map_spec in *. rewrite o_bind_ignore in *.
            des_ifs. destruct (Genv.invert_symbol skenv_link blk) eqn:SYMBSKENV; ss.
            unfold o_bind in INTERNAL. ss. des_ifs.
            destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! i) eqn:DMAP; ss. clarify.
            exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eapply FOCUS1. i.
            inv H. exploit SYMBKEEP. rewrite <- defs_prog_defmap. eauto. i.
            exploit Genv.invert_find_symbol. eapply SYMBSKENV. i. rewrite H1 in H.
            exists i. unfold SkEnv.revive. ss. } des.
          inversion FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in INTERNAL.
          unfold Genv.find_def in INTERNAL. ss. rewrite MapsC.PTree_filter_map_spec in INTERNAL.
          rewrite o_bind_ignore in INTERNAL. des_ifs.
          destruct (Genv.invert_symbol skenv_link blk) eqn:SYMBSKENV; ss.
          eapply Genv.invert_find_symbol in SYMBSKENV. clear INTERNAL.

          esplits; eauto.
          { left. split; cycle 1.
            { ss. eapply lift_receptive_at. ss. des_ifs.
              econs. ii.
              - inv H; clarify.
                inv H2. inv H2.
                { inv H1. eexists. econs 2. econs; eauto. }
                { exfalso. ss. des_ifs.
                  rewrite Genv.find_funct_ptr_iff in *. rewrite Heq in FPTR. clarify. }
              - ii. inv H; inv H1; ss; try omega.
                eapply external_call_trace_length; eauto. }
            eapply plus_left with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { eapply lift_determinate_at. ss. des_ifs.
                econs. ii.
                - inv H; inv H1; inv H2; inv H; clarify.
                  split. econs. i. unsguard LINKSRC.
                  exploit alloc_variable_dtm. eapply H13. eapply H15. i. des_safe; subst.
                  exploit bind_param_dtm. eapply H14. eapply H16. i. subst. eauto.
                  exploit external_call_match_traces. eapply H12. eapply H11. i. split; auto. i.
                  subst. exploit external_call_deterministic. eapply H12. eapply H11. i. des; subst. auto. auto.
                - i. ss.
                - ii. inv H; inv H1; ss; try omega.
                  exploit external_call_trace_length; eauto. }
              econs 1; ss; et.
              econs; ss; et.
              esplits; eauto. unfold Genv.find_funct_ptr. des_ifs.
            }
            eapply star_two with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { econs.
                - ii.
                  ss. rewrite LINKTGT in *. inv H; inv H1; clarify. ss.
                  split. econs. i. ss.
                  exploit find_fptr_owner_determ. eapply FINDMS. eauto. i.
                  exploit find_fptr_owner_determ. eapply MSFIND. eauto. i. subst ms. subst ms0.
                  ss. inv INIT; inv INIT0. ss. des_ifs.
                - i. ss. des_ifs. inv FINAL.
                - ii. inv H. ss. omega.
              }
              econs 2; ss; et.
              { des_ifs. folder. eauto. }
              ss. econs; ss; et.
              - instantiate (1:= f). des_ifs.
                inv FINDMS. ss. des_ifs.  rewrite Genv.find_funct_ptr_iff in *.
                exploit prog_def_same; eauto. i. des_safe.
                exploit same_prog; try eapply INTERNAL; eauto. i. subst. auto.
              - inv WTSRC. ss. clarify.
                econs; ss; et.
                + inv WTTGT. ss. unfold type_of_function in *. clarify.
                + inv WTTGT. ss. unfold type_of_function in *. clarify.
                + admit "add size_arguments in typechecking".
            }
            { ss.
              assert(WTPROG: wt_program cp_top).
              { rr in FOCUS1. des; clarify. }
              bar.
              (* inv WTST. ss. *)
              inv WTPROG. specialize (H id f).
              assert (Hi: i = id).
              { assert (Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) id = Some blk).
                { unfold SkEnv.revive in SYMB. ss. }
                exploit Genv.find_invert_symbol. eapply H2. i.
                exploit Genv.find_invert_symbol. eapply SYMBSKENV. i.
                (* exploit invert_symbol_lemma1; eauto. *)
                exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H5.
                exploit SYMBKEEP.
                inv FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in INTERNAL. unfold Genv.find_def in INTERNAL. ss.
                rewrite MapsC.PTree_filter_map_spec in INTERNAL. rewrite o_bind_ignore in INTERNAL. des_ifs.
                rewrite H4 in INTERNAL. unfold o_bind in INTERNAL. ss. des_ifs.
                destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! i) eqn:DMAP; ss. clarify.
                rewrite <- defs_prog_defmap. eauto. i. rewrite SYMBSKENV in H5.
                exploit Genv.find_invert_symbol. eauto. i. rewrite H6 in H3. clarify. } subst.

              assert (Haux: In (id, Gfun (Internal f)) (prog_defs cp_top)).
              { inv FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in INTERNAL. ss.
                unfold Genv.find_def in Heq. ss. rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in Heq. des_ifs.
                rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in Heq2. des_ifs.
                exploit Genv.find_invert_symbol. eauto. i. rewrite H2 in Heq2. unfold o_bind in Heq2. ss. des_ifs.
                destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) blk) eqn:SYMBLINK; ss.
                unfold o_bind in Heq. ss.
                assert (i = id).
                { destruct ((prog_defmap cp_link) ! i) eqn:DMAP; ss; clarify.
                  exploit SkEnv.project_impl_spec. eapply INCL. i. inv H3.
                  exploit SYMBKEEP. rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i.
                  exploit Genv.invert_find_symbol. eapply SYMBLINK. i. rewrite H4 in H3. inv H3. symmetry in H6.
                  exploit Genv.find_invert_symbol. eapply SYMBSKENV. i.
                  exploit Genv.find_invert_symbol. eapply H6. i. Eq. auto. } subst.
                destruct ((prog_defmap cp_link) ! id) eqn:DMAP; ss. clarify.
                unfold Genv.find_def in INTERNAL. ss. rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in INTERNAL. des_ifs.
                rewrite H2 in INTERNAL. unfold o_bind in INTERNAL. ss. des_ifs.
                destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! id) eqn:DMAP0; ss. clarify.

                exploit (CSk.of_program_prog_defmap cp_top signature_of_function).
                instantiate (1 := id). i. inv H3; rewrite DMAP0 in *; clarify.
                inv H6. unfold CtypesC.CSk.match_fundef in H11. des_ifs; clarify. symmetry in H4.

                exploit prog_defmap_same_rev. eauto. eauto. i. Eq.
                unfold prog_defmap in H4. ss. eapply PTree_Properties.in_of_list. eauto. }

              specialize (H Haux).
              inv H.
              econs; ss; et.
              { eapply lift_determinate_at.
                - ss. des_ifs.
                - econs.
                  + ii. inv H; inv H3; inv H; inv H4; clarify.
                    split. econs. i. unsguard LINKSRC.
                    exploit alloc_variable_dtm. eapply H15. eapply H17. i. des_safe; subst.
                    exploit bind_param_dtm. eapply H16. eapply H18. i. subst. eauto.
                    exploit external_call_match_traces. eapply H13. eapply H14. i. split; auto. i.
                    subst. exploit external_call_deterministic. eapply H13. eapply H14. i. des; subst. auto. auto.
                  + i. inv FINAL.
                  + ii. inv H; inv H3. ss; omega.
                    eapply external_call_trace_length; eauto. }
              (* des_ifs. *) rewrite LINKTGT in *.
              rpapply step_internal; ss; et.
              rr. right.
              (* ZmFkZDJkODhmOGM1YWI0NDI1YjEzMDFi *)
              econs; ss; et.
              - inv FINDMS. ss. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); ss.
                rewrite Genv.find_funct_ptr_iff in *. exploit prog_def_same. eauto. i. des_safe.
                assert (cp2 = cp_top).
                { exploit same_prog. eauto. eapply FOCUS1. eapply INTERNAL. eauto. i. auto. } subst. eauto.
              - unguardH LINKSRC. eapply preservation_alloc; eauto.
              - unguardH LINKSRC. eapply preservation_bind_param; eauto.
            }
          }
          {
            right. eapply CIH; et.
            ss.
            econs; ss; et.
            unfold Frame.update_st. ss.
            rewrite ! app_comm_cons.
            econs 3; et.
            econs; et.
            { econs; et. inv WTTGT.
              des_ifs.
              exploit WTKS; et.
              { ii. ss. des_ifs. }
              i; des_safe. clarify. inv CLASSIFY. esplits; et.
            }
            { econs; et. }
            { des_ifs. eapply preservation_cp_link; et.
              right. econs; ss; et. des_ifs. unfold Genv.find_funct_ptr. des_ifs.
            }
            {
              assert(WTPROG: wt_program cp_top).
              { rr in FOCUS1. des; clarify. }
              bar.
              (* inv WTST. ss. *)
              inv WTPROG. specialize (H id f).

              assert (Hi: i = id).
              { assert (Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) id = Some blk).
                { unfold SkEnv.revive in SYMB. ss. }
                exploit Genv.find_invert_symbol. eapply H2. i.
                exploit Genv.find_invert_symbol. eapply SYMBSKENV. i.
                (* exploit invert_symbol_lemma1; eauto. *)
                exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H5.
                exploit SYMBKEEP.
                inv FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in INTERNAL. unfold Genv.find_def in INTERNAL. ss.
                rewrite MapsC.PTree_filter_map_spec in INTERNAL. rewrite o_bind_ignore in INTERNAL. des_ifs.
                rewrite H4 in INTERNAL. unfold o_bind in INTERNAL. ss. des_ifs.
                destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! i) eqn:DMAP; ss. clarify.
                rewrite <- defs_prog_defmap. eauto. i. rewrite SYMBSKENV in H5.
                exploit Genv.find_invert_symbol. eauto. i. rewrite H6 in H3. clarify. } subst.

              assert (Haux: In (id, Gfun (Internal f)) (prog_defs cp_top)).
              { inv FINDMS. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in INTERNAL. ss.
                unfold Genv.find_def in Heq. ss. rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in Heq. des_ifs.
                rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in Heq2. des_ifs.
                exploit Genv.find_invert_symbol. eauto. i. rewrite H2 in Heq2. unfold o_bind in Heq2. ss. des_ifs.
                destruct (Genv.invert_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_link)) blk) eqn:SYMBLINK; ss.
                unfold o_bind in Heq. ss.
                assert (i = id).
                { destruct ((prog_defmap cp_link) ! i) eqn:DMAP; ss; clarify.
                  exploit SkEnv.project_impl_spec. eapply INCL. i. inv H3.
                  exploit SYMBKEEP. rewrite CSk.of_program_defs. rewrite <- defs_prog_defmap. eauto. i.
                  exploit Genv.invert_find_symbol. eapply SYMBLINK. i. rewrite H4 in H3. inv H3. symmetry in H6.
                  exploit Genv.find_invert_symbol. eapply SYMBSKENV. i.
                  exploit Genv.find_invert_symbol. eapply H6. i. Eq. auto. } subst.
                destruct ((prog_defmap cp_link) ! id) eqn:DMAP; ss. clarify.
                unfold Genv.find_def in INTERNAL. ss. rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in INTERNAL. des_ifs.
                rewrite H2 in INTERNAL. unfold o_bind in INTERNAL. ss. des_ifs.
                destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! id) eqn:DMAP0; ss. clarify.

                exploit (CSk.of_program_prog_defmap cp_top signature_of_function).
                instantiate (1 := id). i. inv H3; rewrite DMAP0 in *; clarify.
                inv H6. unfold CtypesC.CSk.match_fundef in H11. des_ifs; clarify. symmetry in H4.

                exploit prog_defmap_same_rev. eauto. eauto. i. Eq.
                unfold prog_defmap in H4. ss. eapply PTree_Properties.in_of_list. eauto. }

              specialize (H Haux).
              inv H.
              des_ifs. inv FINDMS. ss. (* des_ifs. *) destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); ss.
              eapply preservation_cp_focus; et; revgoals.
              { right. eapply step_internal_function; ss; et.
                - unfold Genv.find_funct. instantiate (1:= Vptr blk Ptrofs.zero true). ss. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); ss.
                  rewrite Genv.find_funct_ptr_iff in *. exploit prog_def_same. eauto. i. des_safe.
                  assert (cp2 = cp_top).
                  { exploit same_prog. eauto. eapply FOCUS1. eapply INTERNAL. eauto. i. auto. } subst. eauto.
                  (* ditto(ZmFkZDJkODhmOGM1YWI0NDI1YjEzMDFi) *)
                - eapply preservation_alloc; eauto.
                - eapply preservation_bind_param; eauto. }
              econs.
              - econs; et.
              - econs; et.
              - i. ss. des_ifs. exfalso. eapply EXT; ss; et.
                assert (exists f, Genv.find_funct_ptr (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) cp_top) blk = Some (Internal f)).
                { unfold Genv.find_funct_ptr in INTERNAL. des_ifs.
                  assert (exists f, Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) cp_top) blk = Some (Gfun(Internal f))).
                  { unfold Genv.find_def in Heq2. ss. rewrite MapsC.PTree_filter_map_spec in Heq2. rewrite o_bind_ignore in Heq2. des_ifs.
                    exploit Genv.find_invert_symbol. eapply SYMBSKENV. intros INVSKENV. rewrite INVSKENV in Heq2.
                    unfold o_bind in Heq2. ss. des_ifs. ss.
                    destruct ((prog_defmap (CSk.of_program signature_of_function cp_top)) ! id) eqn:DMAP; ss. clarify.

                    (* exploit INCL_FOCUS. eapply FOCUS1. i. exploit SkEnv.project_impl_spec. eauto. i. inv H3. *)
                    (* inv H2. *)
                    exploit (CSk.of_program_prog_defmap cp_top signature_of_function).
                    i. inv H. rewrite DMAP in *. clarify.
                    assert (exists if_sig, (prog_defmap cp_top) ! id = Some (Gfun (Internal if_sig))).
                    { rewrite DMAP in *. inv H5. unfold CtypesC.CSk.match_fundef in H6. destruct f1; destruct f2; eauto; clarify. inv H4. } des_safe.
                    destruct (is_focus_precise FOCUS1). exploit P2GE; eauto. i. des_safe. des_ifs.
                    assert (b = blk).
                    {
                      assert (Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function cp_top)) id = Some b).
                      { unfold SkEnv.revive in *; ss. }
                      exploit SkEnv.project_impl_spec. eapply INCL_FOCUS. eauto. i. inv H10.
                      exploit SYMBKEEP. rewrite <- defs_prog_defmap. eauto. i. exploit Genv.invert_find_symbol. eauto. i. rewrite <- H10 in H11.
                      rewrite H6 in H11. clarify. }
                    subst. eauto. }
                  des_safe. exists f0. rewrite Genv.find_funct_ptr_iff. eauto. }
                des_safe. specialize (EXT f0). exfalso. eapply EXT. eauto.
              - (* instantiate (1:= vs_arg). *)
                inv WTTGT; ss. clarify. unfold type_of_function in *. clarify.
              - inv WTTGT; ss. clarify. unfold type_of_function in *. clarify.
            }
          }
      }


      assert(CALLLE: forall
                (CALLSRC: ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src))
              ,
                <<CALLTGT: ModSem.is_call (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
      { admit "this should hold". }
      rename H into NCALLTGT.
      assert(NCALLSRC: ~ ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src)).
      { tauto. }


      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_return) fr_tgt.(Frame.st))).
      { (* tgt return *)
        left. right. econs; et.
        { i. eapply final_fsim; et. econs; et. }
        econs; et; cycle 1.
        i. ss. rewrite LINKSRC in *.

        (* inv STK; ss. *)
        (* { inv STEPSRC; ss; ModSem.tac. *)
        (*   assert(frs_tgt <> []). *)
        (*   { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". } *)
        (*   destruct frs_tgt as [|fr_snd frs_tgt]; ss. *)
        (*   esplits; et. *)
        (*   - left. split. apply plus_one. econs; ss; et. *)
        (*     { admit "determinate". } *)
        (*     des_ifs. *)
        (*     rpapply step_return; et. inv TAIL; eauto. *)

        assert(RECEP: receptive_at (sem prog_src) (State (fr_src :: frs_src))).
        { (* is it receptive? *)
          econs.
          - ii. inv H0.
            + admit "".
            + ss. rewrite LINKSRC in *.
              rr in H. des. ss.
              inv STK.
              admit "".
              ss. inv HD. ss. clarify. ss. inv H. inv ST. ss. inv STEP; inv H. inv H1.
              eexists. ss. econs 3. ss. econs 2. econs; eauto.
            + admit "".
          - admit "".
        }

        inv STEPSRC; ss.
        { contradict NCALLSRC. rr. et. }
        - (* src step *)
          inv STK; ss.
          { ModSem.tac. }
          inv HD; ss. clarify; ss.
          rr in H. des. ss. inv H.
          inv ST. ss.
          rr in STEP. des; inv STEP; ss.
          inv SUM; ss.
          rr in CALL. destruct k0; ss. (* des_ifs. destruct k0. *) ss. clarify.
          hexploit (typify_c_ex v_ret _tres). i; des.
          esplits; eauto.
          + left. split; ss.
            eapply plus_two with (t1 := E0) (t2 := E0); ss.
            * econs; et.
              { eapply lift_determinate_at.
                ss. des_ifs.
                econs.
                - i. inv H; inv H0; inv H; inv H1.
                - i. ss.
                - ii. inv H; inv H0. }
              ss. des_ifs.
              econs 4; ss; et.
              econs; ss; et.
            * econs; et.
              { eapply lift_determinate_at.
                ss. des_ifs.
                econs.
                - i. ss. inv H; inv H0; inv H; inv H1.
                  split. econs. i. auto.
                - i. ss.
                - ii. inv H; inv H0. ss. nia. }
              ss. des_ifs.
              unfold Frame.update_st. s.
              rpapply step_internal; ss; et.
              right.
              econs; ss; et.
          + right. ss. eapply CIH; eauto.
            econs; ss; et.
            unfold Frame.update_st. ss.
            rewrite app_comm_cons.
            econs 3; ss; et.
            econs; ss; et.
            {
              assert(v_ret = tv).
              { inv WTSRC. inv TYP; ss. clarify.
                inv WTK. ss.
              }
              clarify.
              econs; ss; et.
            }
            { eapply preservation_cp_link; et.
              right. econs; ss; et.
            }
            {
              (* MmEyZjBiNDFkYzlkNGY3YWVkNTlhMWE2 *)
              des_ifs.
              assert(WTTGT1: wt_state (geof cp2)
                                      (Returnstate tv (Kcall _f _e _C _tres _k) (m_ret))).
              { econs; ss; et; cycle 1.
                { eapply typify_c_spec; et. }
                inv WTTGT0. ss. clarify.
              }
              eapply preservation_cp_focus; et; cycle 1.
              right. econs; ss; et.
            }
        - (* src return *)
          inv STK; ss; cycle 1.
          { (* top is focus *)
            inv HD; ss. clarify; ss.
            inv FINAL. inv ST. exploit app_cont_kstop_inv; et. i; des. clarify. ss. clear_tac.
            exploit sum_cont_kstop_inv; et. i; des. clarify. ss.
            inv SUM.
            assert(tail_tgt <> []).
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des.
              destruct hds_tgt; ss. }
            destruct tail_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. split; ss.
                apply plus_one.
                econs; et.
                { eapply lift_determinate_at.
                  ss. des_ifs.
                  econs.
                  - ii. ss. inv H1; inv H2; inv H1; inv H3.
                  - ss.
                  - ii. inv H1; inv H2. }
                econs 4; ss; et.
              + right. eapply CIH; eauto. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. split; ss.
                apply plus_one.
                econs; et.
                { eapply lift_determinate_at.
                  ss. des_ifs.
                  econs.
                  - ii. ss. inv H2; inv H3; inv H4; inv H2.
                  - i. ss.
                  - ii. inv H2; inv H3. }
                ss. des_ifs.
                econs 4; ss; et.
                econs; ss; et.
              + right. eapply CIH; eauto. unfold Frame.update_st. econs; ss; et.
                rewrite app_comm_cons.
                econs 3; ss; et.
                econs; ss; et.
                { econs; ss; et. }
                { inv WTSRC0.
                  econs; ss; et. clarify.
                  eapply typify_c_spec; et.
                }
                {
                  (* copied from: MmEyZjBiNDFkYzlkNGY3YWVkNTlhMWE2 *)
                  assert(WTTGT1: wt_state (geof cp2)
                                          (Returnstate tv k2 m_ret)).
                  { econs; ss; et; cycle 1.
                    { eapply typify_c_spec; et. }
                    inv WTTGT0. ss. clarify.
                  }
                  ss.
                }
          }
          { (* top is ctx *)
            assert(frs_tgt <> []).
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des.
              destruct hds_tgt; ss. }
            destruct frs_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. split; ss.
                apply plus_one.
                econs; et.
                { econs. ii. ss. des_ifs.
                  - inv H1; inv H2; ModSem.tac.
                    split. econs. i. ss.
                    exploit ModSem.final_frame_dtm. eapply FINAL1. eapply FINAL0. i. subst.
                    exploit ModSem.after_external_dtm. eapply AFTER0. eapply AFTER1. i. subst.
                    auto.
                  - i. inv FINAL0.
                  - ii. inv H1; ModSem.tac; ss; try nia. }
                econs 4; ss; et.
              + right. eapply CIH; eauto. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. split; ss.
                apply plus_one.
                econs; et.
                { econs. ii. ss. des_ifs.
                  - inv H3; inv H2; ModSem.tac.
                    split. econs. i.
                    exploit ModSem.final_frame_dtm. eapply FINAL1. eapply FINAL0. i. subst.
                    exploit ModSem.after_external_dtm. eapply AFTER. eapply AFTER0. i. subst.
                    auto.
                  - i. inv FINAL0.
                  - ii. inv H2; ModSem.tac; ss; try nia. }
                ss. des_ifs.
                econs 4; ss; et.
                econs; ss; et.
              + right. eapply CIH; eauto. unfold Frame.update_st. econs; ss; et.
                rewrite app_comm_cons.
                econs 3; ss; et.
                econs; ss; et.
                { econs; ss; et. }
                {
                  (* copied from: MmEyZjBiNDFkYzlkNGY3YWVkNTlhMWE2 *)
                  assert(WTSRC0: wt_state ge_cp_link
                                          (Returnstate tv (app_cont k2 k_tl_tgt) (Retv.m retv))).
                  { econs; ss; et; cycle 1.
                    { eapply typify_c_spec; et. }
                    inv WTSRC. ss. clarify.
                  }
                  ss.
                }
                {
                  (* copied from: MmEyZjBiNDFkYzlkNGY3YWVkNTlhMWE2 *)
                  assert(WTTGT0: wt_state (geof cp)
                                          (Returnstate tv k2 (Retv.m retv))).
                  { econs; ss; et; cycle 1.
                    { eapply typify_c_spec; et. }
                    inv WTTGT. ss. clarify.
                  }
                  ss.
                }
          }
      }


      assert(RETLE: forall
                (RETSRC: ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src))
              ,
                <<RETTGT: ModSem.is_return (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
      { admit "this should hold". }
      rename H into NRETTGT.
      assert(NRETSRC: ~ ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src)).
      { tauto. }




      (* src internal && tgt internal *)
      right. econs; et.
      { i. exploit final_bsim; et. { econs; et. } i; des. esplits; et. apply star_refl. }
      i.
      inv STK.
      {
        (* ctx *)
        clear_tac.
        econs; cycle 1.
        - (* progress *)
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
          { inv SAFESRC. contradict NRETTGT. rr. et. }
          des_ifs.
          inv SAFESRC; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          esplits; et.
          econs 3; et.
        - (* bsim *)
          i. ss. des_ifs. clear_tac.
          (* specialize (SAFESRC _ (star_refl _ _ _)). des; ss. *)
          (* { inv SAFESRC. contradict NRETTGT. rr. et. } *)
          (* des_ifs. *)
          inv STEPTGT; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          esplits; et.
          { left. apply plus_one. econs 3; et. }
          right. eapply CIH; eauto. econs; et. econs; et.
      }
      {
        (* focus *)
        inv HD; ss. clarify; ss.
        econs; cycle 1.
        - (* progress *)
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
          { inv SAFESRC. contradict NRETSRC. rr. et. }
          des_ifs.
          inv SAFESRC; swap 2 3.
          { contradict NCALLSRC. rr. et. }
          { contradict NRETSRC. rr. et. }
          ss.
          esplits; et.
          econs 3; et. ss.
          admit "match_focus_state - progress".
        - (* bsim *)
          i. ss. des_ifs. clear_tac.
          (* specialize (SAFESRC _ (star_refl _ _ _)). des; ss. *)
          (* { inv SAFESRC. contradict NRETTGT. rr. et. } *)
          (* des_ifs. *)
          inv STEPTGT; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          ss.
          esplits; et.
          { left. apply plus_one. econs 3; et. ss.
            admit "match_focus_state - bsim".
          }
          right. eapply CIH; eauto. econs; et. unfold Frame.update_st. ss. admit "match_focus_state - bsim".
      }
    - (* call state *)
      right.
      econs; ss; et.
      { i. inv FINALTGT. }
      econs; cycle 1.
      { i. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
        { inv SAFESRC. }
        rewrite LINKSRC in SAFESRC; ss.
        (* des_ifs. *) inv SAFESRC.
        right. exploit msfind_fsim; eauto. i; des.
        - rewrite LINKTGT. esplits; eauto. econs; eauto.
        - rewrite LINKTGT. clarify. ss. inv INIT. ss.  esplits; eauto. econs; eauto. ss. econs; et. ss.
          unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          exploit prog_def_same; eauto. i. des.
          assert (cp = cp2).
          { inv MSFIND0. ss. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            exploit same_prog. eapply H. eapply ISFOCTGT. eauto. eauto. eauto. } subst. eauto.
      }
      i. inv STEPTGT. ss.
      exploit msfind_bsim; et.
      { des_ifs. eauto. } i; des.
      + des_ifs. esplits; eauto.
        { left. apply plus_one. econs; et. }
        right. eapply CIH; eauto. econs; et. econs; et.
      + rewrite LINKSRC in *. rewrite LINKTGT in *.
        (* des_ifs. *) clarify. ss. inv INIT.
        esplits; eauto.
        { left. apply plus_one. econs; et.
          ss. econs; et. ss.
          unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
          eapply prog_find_defs_same_rev; eauto. }
        right. eapply CIH; eauto. econs; et.
        rewrite cons_app with (xtl := frs_tgt).
        econs 3; ss; et.
        econs; ss; et.
        { econs; ss; et. }
        { econs; ss; et. }
        { inv TYP. eapply wt_initial_frame; ss; et.
          - esplits; et. instantiate (1:= fd).
            unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
            eapply prog_find_defs_same_rev; eauto.
        }
       { inv TYP. eapply wt_initial_frame; ss; et. }
  Unshelve.
    all: ss.
  Qed.

  End WTMODULE.

  Theorem upperbound_a_xsim
    :
      <<XSIM: mixed_simulation (Sem.sem prog_src) (Sem.sem prog_tgt)>>
  .
  Proof.
    econs; ss; eauto. econs; ss; eauto.
    { eapply unit_ord_wf. }
    { econs 1.
      ii. inversion INITSRC. exploit init_fsim; eauto. i; des. esplits; eauto.
      rewrite H.
      eapply match_xsim; et.
      inv INIT. ss. inv INIT0. eauto.
    }
    i; des. des_ifs.
  Qed.

End PRESERVATION.

Require Import BehaviorsC.

Let geof := fun skenv_link (cp: Csyntax.program) =>
              (Build_genv (SkEnv.revive (SkEnv.project skenv_link cp.(CSk.of_program signature_of_function)) cp) cp.(prog_comp_env)).

Theorem upperbound_a_correct
        (cp0 cp1 cp_link: Csyntax.program) ctx
        (TYPED0: typechecked cp0)
        (TYPED1: typechecked cp1)
        (TYPEDLINK: typechecked cp_link)
        (LINK: link cp0 cp1 = Some cp_link)
  :
    (<<REFINE: improves (Sem.sem (ctx ++ [cp_link.(CsemC.module)]))
                        (Sem.sem (ctx ++ [cp0.(CsemC.module) ; cp1.(CsemC.module)]))
                        >>)
.
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  destruct (link_sk (ctx ++ [module cp_link])) eqn:LINKSK; cycle 1.
  { econs; et.
    econs; et.
    { eapply unit_ord_wf. }
    { econs; et. i. ss. inv INITSRC. clarify. }
    i; des. ss. des_ifs.
    hexploit (link_sk_match cp_link cp0 cp1 ctx); eauto. i; des. congruence.
  }
  rename t into link_sk.
  des.
  inv TYPED0. inv TYPED1. inv TYPEDLINK.
  eapply upperbound_a_xsim; eauto.
  { eapply typecheck_program_sound; et. }
  { eapply typecheck_program_sound; et. }
  { eapply typecheck_program_sound; et. }
Qed.
