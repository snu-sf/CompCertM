Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.
Require Import Equality.
Require Import CtypingC.

Set Implicit Arguments.








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
  Notation " 'geof' cp" := (Build_genv (SkEnv.revive (SkEnv.project skenv_link (defs cp)) cp) cp.(prog_comp_env))
                           (at level 50, no associativity, only parsing).
  Let ge_cp_link: genv := geof cp_link.
  Let ge_cp0: genv := geof cp0.
  Let ge_cp1: genv := geof cp1.

  Hypothesis WTPROGLINK: wt_program cp_link.
  Hypothesis WTPROG0: wt_program cp0.
  Hypothesis WTPROG1: wt_program cp1.


  Hypothesis WT_EXTERNALLINK:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp_link.(prog_defs) ->
      external_call ef ge_cp_link vargs m t vres m' ->
      wt_retval vres res.
  Hypothesis WT_EXTERNAL0:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp0.(prog_defs) ->
      external_call ef ge_cp0 vargs m t vres m' ->
      wt_retval vres res.
  Hypothesis WT_EXTERNAL1:
    forall id ef args res cc vargs m t vres m',
      In (id, Gfun (External ef args res cc)) cp1.(prog_defs) ->
      external_call ef ge_cp1 vargs m t vres m' ->
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




  Definition is_focus (cp: Csyntax.program): Prop := cp = cp0 \/ cp = cp1.

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

  Lemma genv_find_funct
        fptr if_sig
        (FIND: Genv.find_funct (SkEnv.project skenv_link (defs cp_link)) fptr = Some (AST.Internal if_sig))
    :
      exists pgm, is_focus pgm /\
             Genv.find_funct  (SkEnv.project skenv_link (defs pgm)) fptr = Some (AST.Internal if_sig).
  Proof.
    unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *. unfold Genv.find_def in *. ss.
    rewrite MapsC.PTree_filter_map_spec in FIND. unfold o_bind in *.
    destruct ((Genv.genv_defs skenv_link) ! b) eqn:Hdefs; ss.
    destruct (Genv.invert_symbol skenv_link b) eqn:Hsymb; ss. des_ifs.
    exploit Genv.invert_find_symbol; eauto. i. unfold skenv_link in *. ss. unfold link_sk in *. subst prog_src prog_tgt. ss.
    unfold link_list in *. des_ifs. 
    
    admit "i think it must be true".
  Qed.

  Lemma genv_find_funct_rev
        pgm fptr if_sig
        (FOCUS1: is_focus pgm)
        (FIND: Genv.find_funct (SkEnv.project skenv_link (defs pgm)) fptr = Some (AST.Internal if_sig))
    :
      Genv.find_funct (SkEnv.project skenv_link (defs cp_link)) fptr = Some (AST.Internal if_sig).
  Proof.
    admit "i think it must be true".
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
    right.
    exploit genv_find_funct; eauto. i. des. exists pgm. esplits; eauto.
    econs; eauto. ss. right. subst prog_tgt. ss. unfold flip. ss.
    rewrite map_app. eapply in_or_app. right. ss. inv H; eauto.
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
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
      + instantiate (1:= if_sig). exploit genv_find_funct_rev; eauto. unfold is_focus. auto.
    - clarify.
      right.
      unfold flip. ss.
      esplits; et; rr; et.
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
      + instantiate (1:= if_sig). exploit genv_find_funct_rev; eauto. unfold is_focus. auto.
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
        (STEP: Csem.step ge_cp_link st0 tr st1)
    :
      <<WT: wt_state ge_cp_link st1>>
  .
  Proof.
    (* eapply preservation_internal; try refl; et. *)
    eapply preservation; try refl; et.
    - admit "ez".
    - admit "ez".
  Qed.

  Lemma preservation_cp_focus
        cp st0 tr st1
        (FOC: is_focus cp)
        (WT: wt_state (geof cp) st0)
        (* (INTERNAL: ~ Ctyping.is_external (geof cp) st0) *)
        (STEP: Csem.step (geof cp) st0 tr st1)
    :
      <<WT: wt_state (geof cp) st1>>
  .
  Proof.
    rr in FOC. des; clarify.
    - eapply preservation; try refl; et.
      + admit "ez".
      + admit "ez".
    - eapply preservation; try refl; et.
      + admit "ez".
      + admit "ez".
  Qed.

  Lemma preservation_alloc
        cp_top m1 e l m0
        (FOCUS1 : is_focus cp_top)
        (ALLOC : alloc_variables
                   {|
                     genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs cp_link))
                                               cp_link;
                     genv_cenv := prog_comp_env cp_link |} empty_env m0
                   l e m1)
        (COMP : Forall (fun t : type => complete_type (prog_comp_env cp_top) t)
                       (map snd l))
    :
      alloc_variables
        {|
          genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs cp_top)) cp_top;
          genv_cenv := prog_comp_env cp_top |} empty_env m0 l
        e m1.
  Proof.
    induction ALLOC.
    - econs.
    - ss. inv COMP.
      assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
      { i.  admit "ez". }
      exploit sizeof_stable; eauto.
      i. eapply IHALLOC in H3. des.
      econs; eauto. simpl. rewrite <- H1. eauto.
  Qed.

  Lemma preservation_bind_param
        cp_top m1 e l l' m2 vs_arg
        (FOCUS1 : is_focus cp_top)
        (PARAM : bind_parameters ge_cp_link e m1 l vs_arg m2)
        (COMP : Forall (fun t : type => complete_type (prog_comp_env cp_top) t) (map snd (l ++ l')))
    :
      bind_parameters
        {| genv_genv := SkEnv.revive (SkEnv.project skenv_link (defs cp_top)) cp_top; genv_cenv := prog_comp_env cp_top |} e m1
        l vs_arg m2.
  Proof.
    induction PARAM.
    - econs.
    - ss. inv COMP.
      exploit IHPARAM; eauto. i. econs; eauto.
      inv H0.
      * econs; eauto.
      * econs 2; eauto.
        inv H6.
        econs; eauto. ss.
        unfold Genv.block_is_volatile in *. des_ifs.
        admit "if def exists in cp_top -> same def exists in linked pg".
        admit "if def exists in cp_top -> same def exists in linked pg".
      * assert (forall id co, (prog_comp_env cp_top) ! id = Some co -> (prog_comp_env cp_link) ! id = Some co).
        { i.  admit "ez". }
        (* TODO:must simplify *)
        des.
        { econs 3; eauto; ss.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto. }
        { econs 3; eauto; ss.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto. }
        { econs 3; eauto; ss.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto. }
        { econs 3; eauto; ss.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - destruct ty; ss; des_ifs.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10. eauto.
            + exploit H0; eauto. i. rewrite Heq0 in H10. inv H10.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto.
          - exploit sizeof_stable; eauto. i. rewrite <- H10. eauto. }
  Qed.

  Lemma match_xsim
        st_src0 st_tgt0
        (MATCH: match_states st_src0 st_tgt0)
    :
      <<XSIM: xsim (sem prog_src) (sem prog_tgt) bot2 tt st_src0 st_tgt0>>
  .
  Proof.
    revert_until LINKTGT.
    pcofix CIH. i. pfold.
    inv MATCH.
    - (* normal state *)
      ss.
      destruct frs_src; ss.
      { inv STK. admit "spurious case". }
      rename t into fr_src.
      destruct frs_tgt; ss.
      { exploit match_stacks_right_nil; et. i; des. clarify. }
      rename t into fr_tgt.
      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
      { (* tgt call *)

        (* fsim *)
        left. econs; et.
        { i. eapply final_fsim; et. econs; et. }

        destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
        - (* src call *)
          econs; ss; cycle 1.
          { admit "receptive - SemProps.v". }
          i; des_ifs.
          inv STEPSRC; ss; ModSem.tac.
          esplits; eauto.
          { left. eapply plus_one. econs; et.
            { admit "determinate - SemProps.v". }
            econs; eauto.
            instantiate (1:= args).
            inv STK; ss. inv HD; ss. des. clarify. ss.
            inv AT; ss.
            inv ST; ss.
            econs; ss; et.
            - admit "ez".
            - rr in H. des. inv H. ss.
          }
          {
            right. eapply CIH; et.
            econs; et.
          }
        - (* src step *)
          inv STK; ss.
          econs; ss; cycle 1.
          { admit "receptive - SemProps.v". }
          i; des_ifs.

          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. contradict H0. rr. eauto. }
          { exfalso.
            inv HD; ss. clarify.
            clear - FINAL ST H.
            rr in H. des. ss. inv H; inv FINAL; inv ST.
          }

          rr in H. des.
          inv HD; ss. clarify. ss. inv H. ss. clarify.
          inv ST.
          rr in STEP. des; try (by inv STEP; ss).
          folder.
          inv STEP; ss; cycle 1.
          { exfalso. admit "project only internals". }

          assert(TGTFIND: exists cp_top,
                    <<FINDMS: Ge.find_fptr_owner (load_genv prog_tgt skenv_link)
                                                 fptr_arg (CsemC.modsem skenv_link cp_top)>>
                              /\ <<FOCUS: is_focus cp_top>>).
          (* actually it is counterpart of current cp *)
          { admit "this should hold". }
          des.
          
          unfold Genv.find_funct, Genv.find_funct_ptr in SIG, FPTR. des_ifs. rename b into blk.
          assert(SYMB: exists id blk, Genv.find_symbol cp_top.(globalenv) id = Some blk).
          { admit "1) use SkEnv.wf or 2) change definition of wt_program". }
          des.

          esplits; eauto.
          { left.
            eapply plus_left with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { admit "determinate - SemProps.v". }
              econs 1; ss; et.
              econs; ss; et.
              esplits; eauto. unfold Genv.find_funct_ptr. des_ifs.
            }
            eapply star_two with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { admit "determinate - SemProps.v". }
              econs 2; ss; et.
              { des_ifs. folder. eauto. }
              ss. econs; ss; et.
              - instantiate (1:= f). des_ifs.
                admit "this should hold".
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
              inv WTPROG. specialize (H id f). specialize (H (admit "ez")).
              inv H.
              econs; ss; et.
              { admit "determinate - SemProps.v". }
              des_ifs.
              econs 3; ss; et.
              rr. right.
              (* ZmFkZDJkODhmOGM1YWI0NDI1YjEzMDFi *)
              econs; ss; et.
              - inv FINDMS. ss. admit "ez".
              - eapply preservation_alloc; eauto.
              - eapply preservation_bind_param; eauto.
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
              i; des. clarify. inv CLASSIFY. esplits; et.
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
              inv WTPROG. specialize (H id f). specialize (H (admit "ez")).
              inv H.
              des_ifs. inv FINDMS. ss. des_ifs.
              eapply preservation_cp_focus; et; revgoals.
              { right. eapply step_internal_function; ss; et.
                - unfold Genv.find_funct. instantiate (1:= Vptr blk Ptrofs.zero true). ss. des_ifs.
                  admit "ditto(ZmFkZDJkODhmOGM1YWI0NDI1YjEzMDFi) - ez".
                - eapply preservation_alloc; eauto.
                - eapply preservation_bind_param; eauto.
              econs.
              - econs; et.
              - econs; et.
              - i. ss. des_ifs. exfalso. eapply EXT; ss; et. admit "ditto - ez".
              - instantiate (1:= vs_arg).
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
        left. econs; et.
        { i. eapply final_fsim; et. econs; et. }
        econs; et; cycle 1.
        { admit "receptive". }
        i. ss. des_ifs.


        (* inv STK; ss. *)
        (* { inv STEPSRC; ss; ModSem.tac. *)
        (*   assert(frs_tgt <> []). *)
        (*   { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". } *)
        (*   destruct frs_tgt as [|fr_snd frs_tgt]; ss. *)
        (*   esplits; et. *)
        (*   - left. apply plus_one. econs; ss; et. *)
        (*     { admit "determinate". } *)
        (*     des_ifs. *)
        (*     rpapply step_return; et. *)



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
          rr in CALL. des_ifs. ss. clarify.
          hexploit (typify_c_ex v_ret _tres). i; des.
          esplits; eauto.
          + left. eapply plus_two with (t1 := E0) (t2 := E0); ss.
            * econs; et.
              { admit "determinate". }
              ss. des_ifs.
              econs 4; ss; et.
              econs; ss; et.
            * econs; et.
              { admit "determinate". }
              ss. des_ifs.
              unfold Frame.update_st. s.
              econs 3; ss; et.
              right.
              econs; ss; et.
          + right. ss. eapply CIH.
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
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". }
            destruct tail_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                ss. des_ifs.
                econs 4; ss; et.
                econs; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et.
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
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". }
            destruct frs_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                ss. des_ifs.
                econs 4; ss; et.
                econs; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et.
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
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
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
          right. eapply CIH. econs; et. econs; et.
      }
      {
        (* focus *)
        inv HD; ss. clarify; ss.
        econs; cycle 1.
        - (* progress *)
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
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
          right. eapply CIH. econs; et. unfold Frame.update_st. ss. admit "match_focus_state - bsim".
      }
    - (* call state *)
      right.
      econs; ss; et.
      { i. inv FINALTGT. }
      econs; cycle 1.
      { i. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
        { inv SAFESRC. }
        des_ifs. inv SAFESRC.
        right. exploit msfind_fsim; eauto. i; des.
        - esplits; eauto. econs; eauto.
        - clarify. ss. inv INIT. ss. esplits; eauto. econs; eauto. ss. econs; et. ss. admit "ez".
      }
      i. inv STEPTGT. ss. des_ifs.
      exploit msfind_bsim; et. i; des.
      + esplits; eauto.
        { left. apply plus_one. econs; et. }
        right. eapply CIH. econs; et. econs; et.
      + clarify. ss. inv INIT.
        esplits; eauto.
        { left. apply plus_one. econs; et.
          ss. econs; et. ss. admit "this should hold".
        }
        right. eapply CIH. econs; et.
        rewrite cons_app with (xtl := frs_tgt).
        econs 3; ss; et.
        econs; ss; et.
        { econs; ss; et. }
        { econs; ss; et. }
        { inv TYP. eapply wt_initial_frame; ss; et.
          - esplits; et. instantiate (1:= fd). admit "ez".
        }
        { inv TYP. eapply wt_initial_frame; ss; et. }
  Unshelve.
    all: ss.
  Qed.

  Theorem upperbound_a_xsim
    :
      <<XSIM: mixed_simulation (Sem.sem prog_src) (Sem.sem prog_tgt)>>
  .
  Proof.
    econs; ss; eauto. econs; ss; eauto.
    { eapply unit_ord_wf. }
    econs 1.
    ii. exploit init_fsim; eauto. i; des. esplits; eauto.
    eapply match_xsim; et.
  Qed.

End PRESERVATION.

Require Import BehaviorsC.

Let geof := fun skenv_link (cp: Csyntax.program) =>
              (Build_genv (SkEnv.revive (SkEnv.project skenv_link (defs cp)) cp) cp.(prog_comp_env)).

Theorem upperbound_a_correct
        (_cp0 _cp1 _cp_link: Csyntax.program) cp0 cp1 cp_link ctx
        (LINK: link cp0 cp1 = Some _cp_link)

        (TYPED0: typecheck_program _cp0 = Errors.OK cp0)
        (TYPED1: typecheck_program _cp1 = Errors.OK cp1)
        (TYPEDLINK: typecheck_program _cp_link = Errors.OK cp_link)

        (WT_EXTERNAL0: forall id ef args res cc vargs m t vres m'
                              sk_link skenv_link
                              (SK: link_sk (ctx ++ [cp_link.(CsemC.module)]) = Some sk_link)
                              (SKE: skenv_link = sk_link.(Sk.load_skenv))
          ,
            In (id, Gfun (External ef args res cc)) cp0.(prog_defs) ->
            external_call ef (geof skenv_link cp0) vargs m t vres m' ->
            wt_retval vres res)
        (WT_EXTERNAL1: forall id ef args res cc vargs m t vres m'
                              sk_link skenv_link
                              (SK: link_sk (ctx ++ [cp_link.(CsemC.module)]) = Some sk_link)
                              (SKE: skenv_link = sk_link.(Sk.load_skenv))
          ,
            In (id, Gfun (External ef args res cc)) cp1.(prog_defs) ->
            external_call ef (geof skenv_link cp1) vargs m t vres m' ->
            wt_retval vres res)
        (WT_EXTERNALLINK: forall id ef args res cc vargs m t vres m'
                                 sk_link skenv_link
                                 (SK: link_sk (ctx ++ [cp_link.(CsemC.module)]) = Some sk_link)
                                 (SKE: skenv_link = sk_link.(Sk.load_skenv))
          ,
            In (id, Gfun (External ef args res cc)) cp_link.(prog_defs) ->
            external_call ef (geof skenv_link cp_link) vargs m t vres m' ->
            wt_retval vres res)
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
    econs; et. i. ss. inv INITSRC. clarify.
  }
  rename t into link_sk.
  eapply upperbound_a_xsim; eauto.
  { eapply typecheck_program_sound; et. }
  { eapply typecheck_program_sound; et. }
  { eapply typecheck_program_sound; et. }
Qed.
