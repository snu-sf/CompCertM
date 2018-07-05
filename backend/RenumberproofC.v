Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC Renumber.
Require Import sflib.
(** newly added **)
Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimSymbId SimMem SimMemId AsmregsC MatchSimModSem.

Set Implicit Arguments.







Section RNMBREXTRA.

  Variables prog tprog: program.
  Hypothesis TRANSL: match_prog prog tprog.
  (* Let ge := Genv.globalenv prog. *)
  (* Let tge := Genv.globalenv tprog. *)
  Variable ge tge: genv.

  Lemma step_simulation
        (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge)
    :
  forall S1 t S2 (NOTEXT: ~ RTLC.is_external ge S1), Step (semantics_with_ge prog ge) S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', DStep (semantics_with_ge tprog tge) S1' t S2' /\ match_states S2 S2'.
  Proof.
    admit "".
  Qed.

End RNMBREXTRA.



Section MATCHEXTRA.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
  Variable match_fundef: C -> AST.fundef F1 -> AST.fundef F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Hypothesis MATCH_FUNDEF_EXTERNAL: forall
      ctx f_src f_tgt
      (MATCH: match_fundef ctx f_src f_tgt)
    ,
      is_external_fd f_src = is_external_fd f_tgt
  .

  Variables (ctx: C) (p_src: AST.program (AST.fundef F1) V1) (p_tgt: AST.program (AST.fundef F2) V2).

  Lemma match_program_gen_defs
        (MATCH: match_program_gen match_fundef match_varinfo ctx p_src p_tgt)
    :
      <<EQ: p_src.(defs) = p_tgt.(defs)>>
  .
  Proof.
    apply Axioms.functional_extensionality. ii; ss. u.
    (* hexploit (match_program_defmap _ _ ctx p_src p_tgt MATCH x). intro REL. *)
    inv MATCH. des.
    assert((prog_defs_names p_src) = (prog_defs_names p_tgt)).
    { unfold prog_defs_names.
      clear - H.
      ginduction H; ii; ss.
      inv H; ss. f_equal; ss.
    }
    rewrite H2; ss.
  Qed.

  Lemma match_program_gen_preserves_sim_skenv
        skenv_link_src skenv_link_tgt
        (SIMSKENV: SimSymbId.sim_skenv skenv_link_src skenv_link_tgt)
        (MATCH: match_program_gen match_fundef match_varinfo ctx p_src p_tgt)
        proj_src proj_tgt
        (PROJSRC: SkEnv.project_spec skenv_link_src p_src.(defs) proj_src)
        (PROJTGT: SkEnv.project_spec skenv_link_tgt p_tgt.(defs) proj_tgt)
    :
      <<SIMSKENV: SimSymbId.sim_skenv proj_src proj_tgt>>
  .
  Proof.
    clarify. inv SIMSKENV. inv PROJSRC. inv PROJTGT.
    econs; eauto.
    - eq_closure_tac.
    - ii; ss.
      destruct (defs p_src x0) eqn:T.
      + erewrite SYMBKEEP; eauto.
        erewrite SYMBKEEP0; eauto.
        erewrite <- match_program_gen_defs; eauto.
      + erewrite SYMBDROP; eauto.
        erewrite SYMBDROP0; eauto.
        erewrite <- match_program_gen_defs; eauto.
        congruence.
        congruence.
    - intro blk.
      destruct (Genv.invert_symbol skenv_link_src blk) eqn:T0; cycle 1.
      + rewrite DEFORPHAN; ss.
        destruct (Genv.invert_symbol skenv_link_tgt blk) eqn:T1; cycle 1.
        * rewrite DEFORPHAN0; ss.
        * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
          rewrite <- SYMB in *.
          repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
          clarify.
      + destruct (Genv.invert_symbol skenv_link_tgt blk) eqn:T1; cycle 1.
        * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
          rewrite SYMB in *.
          repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
          clarify.
        * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
          assert(i = i0).
          { eapply Genv.genv_vars_inj; eauto. unfold Genv.find_symbol in *. rewrite SYMB. ss. }
          clarify.
          repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
          destruct (classic (defs p_src i0)).
          { erewrite DEFKEEP; eauto. erewrite DEFKEEP0; eauto. erewrite <- match_program_gen_defs; eauto. }
          { erewrite DEFDROP; eauto. erewrite DEFDROP0; eauto. erewrite <- match_program_gen_defs; eauto. }
  Admitted. (* COQ BUG!!!!!!!!!!!!!!!! HOW TO FIX THIS?????????? *)

  Lemma o_bind_assertion
        X Y
        (x: option X) (y: option Y)
    :
      (do _ <- x ; y) = assertion(x) ; y
  .
  Proof. u. des_ifs. Qed.

  Lemma match_globdef_external
        x y
        (MATCH: match_globdef match_fundef match_varinfo ctx x y)
    :
      <<EQ: is_external x = is_external y>>
  .
  Proof. inv MATCH; ss. eapply MATCH_FUNDEF_EXTERNAL; eauto. Qed.

  Lemma match_program_gen_revive_match_genvs
        skenv_link_src skenv_link_tgt
        (SIMSKENV: SimSymbId.sim_skenv skenv_link_src skenv_link_tgt)
        (MATCH: match_program_gen match_fundef match_varinfo ctx p_src p_tgt)
        proj_src proj_tgt
        (PROJSRC: SkEnv.project_spec skenv_link_src p_src.(defs) proj_src)
        (PROJTGT: SkEnv.project_spec skenv_link_tgt p_tgt.(defs) proj_tgt)
        ge_src ge_tgt
        (REVIVESRC: ge_src = SkEnv.revive proj_src p_src)
        (REVIVETGT: ge_tgt = SkEnv.revive proj_tgt p_tgt)
    :
      <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>>
  .
  Proof.
    exploit match_program_gen_preserves_sim_skenv; eauto. intro SIMSKENVPROJ; des. inv SIMSKENVPROJ.
    econs; eauto.
    intro blk; ss.
    inv PROJSRC. inv PROJTGT. rewrite ! MapsC.PTree_filter_map_spec in *.
    {
      rewrite ! o_bind_assertion.
      destruct (Genv.invert_symbol proj_src blk) eqn:T0; cbn; cycle 1.
      - destruct (Genv.invert_symbol proj_tgt blk) eqn:T1; cbn; cycle 1.
        + u. des_ifs; econs; eauto.
        + repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
          erewrite <- SYMB in *.
          repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
          clarify.
      - repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
        dup T0.
        rewrite SYMB in T1.
        repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
        rewrite T1. cbn.
        rename i into id.
        specialize (DEFS blk).
        unfold Genv.find_def in *.
        des_ifs; clarify; cycle 1.
        { econs; eauto. }
        apply match_program_defmap with (id0 := id) in MATCH.
        inv MATCH; cbn.
        { econs; eauto. }
        erewrite match_globdef_external; eauto.
        des_ifs; econs; eauto.
    }
  Admitted. (* COQ BUG!!!!!!!!!!!!!!!! HOW TO FIX THIS?????????? *)

  Lemma match_program_gen_revive_match_genvs_deprecated
        skenv_link_src skenv_link_tgt
        (SIMSKENV: SimSymbId.sim_skenv skenv_link_src skenv_link_tgt)
        (MATCH: match_program_gen match_fundef match_varinfo ctx p_src p_tgt)
        ge_src ge_tgt
        (REVIVESRC: ge_src = SkEnv.revive (SkEnv.project skenv_link_src (defs p_src)) p_src)
        (REVIVETGT: ge_tgt = SkEnv.revive (SkEnv.project skenv_link_tgt (defs p_tgt)) p_tgt)
    :
      <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>>
  .
  Proof.
    clarify. dup MATCH. inv MATCH. des; ss. inv SIMSKENV. ss.
    hexploit (@SkEnv.project_impl_spec skenv_link_src p_src.(defs)). intro SPECSRC.
    hexploit (@SkEnv.project_impl_spec skenv_link_tgt p_tgt.(defs)). intro SPECTGT.
    abstr ((SkEnv.project skenv_link_src (defs p_src))) proj_src.
    abstr ((SkEnv.project skenv_link_tgt (defs p_tgt))) proj_tgt.
    (* set ((SkEnv.project skenv_link_src (defs p_src))) as proj_src in *. *)
    (* set ((SkEnv.project skenv_link_tgt (defs p_tgt))) as proj_tgt in *. *)
    inv SPECSRC. inv SPECTGT.
    {
      econs; eauto.
      - unfold SkEnv.revive. unfold Genv_map_defs. simpl. eq_closure_tac.
      - i. u. ss.
        unfold Genv.find_symbol in *.
        destruct (defs p_src id) eqn:T.
        + erewrite SYMBKEEP; eauto.
          erewrite SYMBKEEP0; eauto.
          erewrite <- match_program_gen_defs; eauto.
        + erewrite SYMBDROP; eauto.
          erewrite SYMBDROP0; eauto.
          erewrite <- match_program_gen_defs; eauto.
          congruence.
          congruence.
      - ii.
  Abort.

End MATCHEXTRA.







Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).

Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem skenv_link_src prog) (RTLC.modsem skenv_link_tgt tprog) tt
.

Inductive match_states (rs_init_src rs_init_tgt: regset)
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt)
    (MATCHST: Renumberproof.match_states st_src0 st_tgt0)
    (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0)
.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states); eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - destruct sm_arg; ss. clarify.
    unfold SimMem.sim_regset in *. ss. apply Axioms.functional_extensionality in SIMRS. clarify.
    inv INITSRC.
    esplits; eauto.
    + econs; eauto.
      * inv SIMSKENV. ss.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        admit "simskenv".
    + instantiate (1:= SimMemId.mk _ _). econs; ss; eauto.
    + u. econs; ss; eauto. econs; ss; eauto. econs; ss; eauto.
  - inv CALLSRC. des. inv MATCH. ss. destruct sm0; ss.
    inv MATCHST; inv H; ss; clarify.
    inv MCOMPAT. ss. fold_all ge. u in *. clarify.
    esplits; eauto.
    econs; eauto.
    fold_all tge.
    admit "simskenv".
  - inv CALLTGT. inv MATCH; ss. u in *. destruct sm0; ss. inv MCOMPAT; ss. u in *. clarify.
    do 2 eexists. eexists (SimMemId.mk _ _).
    esplits; ss; eauto. inv MATCHST; ss.
    econs; eauto.
    admit "simskenv".
  - apply Axioms.functional_extensionality in SIMRSRET. clarify.
    apply Axioms.functional_extensionality in SIMRSARG. clarify.
    inv AFTERSRC. inv MATCH; ss. inv MCOMPAT. u in *. clarify.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    inv MATCHST; ss. des_ifs. clear_tac. destruct sm0; ss. clarify.
    destruct sm_ret; ss. clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      econs; eauto.
  - inv FINALSRC. inv MATCH; ss. inv MATCHST; ss. inv MCOMPAT0; ss. u in *. destruct sm0; ss. des_ifs.
    inv STACKS; ss. inv MCOMPAT; ss. u in *. des_ifs. clear_tac.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    esplits; eauto.
    + econs; eauto.
      admit "simskenv".
    + ii; ss.
  - esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    ii. hexploit (@step_simulation prog tprog ge tge); eauto.
    { unfold match_prog, match_program in *.
      eapply match_program_gen_revive_match_genvs; [| |unshelve eapply TRANSL; eauto|..].
      { ii; ss. clarify. u. des_ifs. }
      admit "".
      admit "".
      apply TRANSL.
      admit "WE SHOULD ADDRESS THIS". }
    { apply not_external. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
    + econs; ss; eauto.
Unshelve.
  all: try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - econs; eauto. admit "easy".
  - ii. eapply sim_modsem; eauto.
Qed.

End SIMMOD.

