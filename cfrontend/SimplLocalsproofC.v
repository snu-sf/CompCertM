Require Import FSets.
Require Import CoqlibC Errors Ordered Maps IntegersC Floats.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import CtypesC CopC ClightC SimplLocals.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export SimplLocalsproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.



Lemma val_casted_list_spec: forall vs tys,
    Forall2 val_casted vs (typelist_to_listtype tys) <-> val_casted_list vs tys.
Proof.
  split; i.
  all: ginduction vs; destruct tys; ii; ss; inv H; clarify; econs; eauto.
Qed.

Lemma typecheck_inject
      j vs0 vs1 tys
      (TYS: typecheck vs0 tys)
      (INJ: Val.inject_list j vs0 vs1):
    <<TYS: typecheck vs1 tys>>.
Proof.
  inv TYS. econs; eauto. rewrite <- forall2_eq in *.
  eapply forall2_val_casted_inject; eauto.
Qed.

Lemma typecheck_typecheck
      vs fd
      (CTYS: typecheck vs (type_of_params (fn_params fd))):
    <<TYS: ValuesC.typecheck vs (signature_of_function fd) vs>>.
Proof.
  inv CTYS. econs; eauto.
  - exploit Forall2_length; eauto. i. ss. etrans; eauto. rewrite typelist_to_listtype_length; ss.
  - ss. eapply has_type_list_typify; eauto.
    rpapply val_casted_has_type_list; eauto.
    rewrite typlist_of_typelist_eq; ss.
Qed.

Lemma transf_function_type
      f_src f_tgt
      (TRANSL: transf_function f_src = OK f_tgt):
    (* <<TY: f_src.(type_of_function) = f_tgt.(type_of_function)>> *)
    (<<PRMS: (fn_params f_src) = (fn_params f_tgt)>>) /\
    (<<RET: (fn_return f_src) = (fn_return f_tgt)>>) /\
    (<<CCONV: (fn_callconv f_src) = (fn_callconv f_tgt)>>).
Proof. unfold transf_function, bind in *. des_ifs. Qed.




Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog tprog: Clight.program.
Let md_src: Mod.t := (ClightC.module1 prog).
Let md_tgt: Mod.t := (ClightC.module2 tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog) prog.(prog_comp_env).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) tprog) tprog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: Clight.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: SimplLocalsproof.match_states skenv_link skenv_link ge st_src0 st_tgt0 sm0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src)) (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef (fun (ctx: AST.program fundef type) f tf => transf_fundef f = OK tf) eq prog) ge tge
  /\ prog_comp_env prog = prog_comp_env tprog.
Proof.
  subst_locals. ss. rr in TRANSL. destruct TRANSL. r in H. esplits.
  - eapply SimSymbId.sim_skenv_revive; eauto.
  - hexploit (prog_comp_env_eq prog); eauto. i.
    hexploit (prog_comp_env_eq tprog); eauto. i.
    ss. congruence.
Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply CSkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply CSkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    destruct args_src, args_tgt; try (by inv INITTGT; des; inv SAFESRC; ss).
    inv SIMARGS; ss. clarify. inv INITTGT.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. exists sm_arg. esplits; eauto; try refl.
    + econs; eauto; ss; cycle 1.
      * inv TYP. inv SAFESRC. folder. ss.
        exploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. intro FINDFTGT; des. ss.
        assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link)).
        { inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
          econs; eauto.
          + ii. ss. eapply Plt_Ple_trans. { genext. } ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans. { genext. } ss. refl.
        }
        hexploit fsim_external_inject_eq; try apply FINDF0; et. i; clarify.
        exploit typecheck_inject; eauto. intro TYPTGT0; des.
        exploit typecheck_typecheck; eauto. intro TYPTGT1; des.
        rpapply match_call_state; ss; eauto.
        { i. inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss.
          econs; eauto.
          - eapply SimMemInjC.sim_skenv_symbols_inject; et.
          - etrans; try apply MWF. ss. etrans; try apply MWF. rewrite NBSRC. extlia.
          - etrans; try apply MWF. ss. etrans; try apply MWF. rewrite NBTGT. extlia.
        }
        { econs; et. }
        { apply MWF. }
        { inv TYP. eapply val_casted_list_spec; eauto. }
        f_equal.
        { unfold transf_function in *. unfold bind in *. des_ifs. }
        { inv TYPTGT1. rewrite <- TYP0 at 2. f_equal. ss.
          unfold transf_function in *. unfold bind in *. des_ifs. }
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR.
    (* unfold transf_function, bind in *. des_ifs. *)
    unfold bind in *. des_ifs. esplits; eauto. econs; eauto.
    + eapply typecheck_typecheck; et. exploit transf_function_type; eauto. i; des.
      eapply typecheck_inject; et. congruence.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss. folder. inv MCOMPAT; ss. clear_tac.
    exploit (fsim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT.
    esplits; eauto; try refl; econs; eauto.
    + des. clarify. esplits; eauto.
      (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *)

      (* Arguments sim_internal_funct_inject [_]. *)
      (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *)
      (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *)
      (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *)
      (* { inv SIMSKENV. ss. } *)

      (***************** TODO: Add as a lemma in GlobalenvsC. *******************)
      inv SIMSKENV.
      assert(fptr_arg = tv).
      { inv VAL; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
        inv SIMSKE. ss. inv INJECT; ss.
        exploit (DOMAIN b1); eauto.
        { eapply Genv.genv_defs_range; et. }
        i; clarify.
      }
      clarify.
  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv AFTERSRC. inv SIMRET; ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. inv HISTORY. ss. clear_tac.
    esplits; eauto; try refl; econs; eauto.
    + destruct args_src, args_tgt; try (by inv CALLSRC; inv CALLTGT; ss). ss. clarify.
      inv MLE0; ss. inv MCOMPAT. clear_tac.
      rpapply match_return_state; ss; eauto; ss.
      { ss. ii.
        eapply match_cont_incr_bounds; eauto; revgoals.
        { eauto with mem. }
        { eauto with mem. }
        eapply match_cont_extcall with (ge := ge) (tge := tge); eauto; try refl.
        { eapply Mem.unchanged_on_implies; try eassumption. ii. rr. esplits; eauto. }
        { eapply SimMemInj.inject_separated_frozen; et. }
      }
      { eapply MWFAFTR. }
      { eapply typify_inject; et. }
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    specialize (MCONT VSet.empty). inv MCONT. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto; try refl. econs; eauto.
  - left; i.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH. esplits; eauto.
    { apply modsem1_receptive. }
    ii. hexploit (@step_simulation prog skenv_link skenv_link); eauto; ss. i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem2_determinate; eauto.
    + econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.

Section SIMMOD.

Variable prog tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := SimSymbId.mk_mp (ClightC.module1 prog) (ClightC.module2 tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. inv TRANSL. eapply CSk.match_program_eq; et.
    ii. destruct f1; ss.
    + clarify. right. inv MATCH. monadInv H2. esplits; eauto. unfold transf_function in *. des_ifs. monadInv EQ. ss.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. inv SIMSKENV. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
