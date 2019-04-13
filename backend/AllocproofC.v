Require Import FunInd.
Require Import FSets.
Require Import CoqlibC Ordered Maps Errors IntegersC Floats.
Require Import AST Linking Lattice Kildall.
Require Import ValuesC MemoryC Globalenvs Events Smallstep.
Require Archi.
Require Import Op Registers RTLC LocationsC Conventions RTLtypingC LTLC.
Require Import Allocation.
Require Import sflib.
(** newly added **)
Require Export Allocproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require Import ModSemProps.
Require SimMemExt.
Require SoundTop.
Require Import LiftDummy.

Set Implicit Arguments.




Definition strong_wf_tgt (st_tgt0: LTL.state): Prop :=
  exists sg_init ls_init, last_option st_tgt0.(LTLC.get_stack) = Some (LTL.dummy_stack sg_init ls_init)
.

Lemma agree_callee_save_after
      tstks ls sg tv
      (NOTNIL: tstks <> [])
      (AG: agree_callee_save (parent_locset tstks) ls)
  :
    <<AG: agree_callee_save (parent_locset (stackframes_after_external tstks))
                            (Locmap.setpair (loc_result sg) tv (undef_caller_save_regs ls))>>
.
Proof.
  hexploit (loc_result_one sg); et. intro ONE.
  unfold agree_callee_save in *. ii. exploit AG; et. intro T.
  destruct tstks; ss. des_ifs. ss.
  rewrite locmap_get_set_loc_result; ss; cycle 1.
  { des_ifs. }
  unfold undef_outgoing_slots, callee_save_loc in *. des_ifs; ss. des_ifs.
Qed.

Lemma match_stackframes_after
      tse tge stks tstks sg
      (STACKS: match_stackframes tse tge stks tstks sg)
  :
    <<STACKS: match_stackframes tse tge stks tstks.(stackframes_after_external) sg>>
.
Proof.
  inv STACKS; econs; et.
  i. exploit STEPS; et. clear - H1.
  unfold agree_callee_save in *.
  ii. exploit H1; et. intro T. unfold undef_outgoing_slots in *. des_ifs.
Qed.



Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: RTL.program.
Variable tprog: LTL.program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (LTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: LTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Allocproof.match_states skenv_link tge st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(RTLC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(LTLC.get_mem) = sm0.(SimMem.tgt))
    (DUMMYTGT: strong_wf_tgt st_tgt0)
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := fun _ _ => wt_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply wt_state_local_preservation; et.
    ii. exploit wt_prog; eauto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit lessdef_list_length; et. intro LEN; des.
    exploit (bsim_internal_funct_id SIMGE); et. i; des.
    exploit (sig_function_translated); eauto. intro SGEQ. ss.
    eexists. eexists (SimMemExt.mk _ _).
    esplits; cycle 2.
    + econs; eauto; ss.
      * inv TYP. eapply match_states_call; eauto.
        { econs; et. econs. }
        { rewrite <- TYP0. eapply lessdef_list_typify_list; try apply VALS; et. xomega. }
        { ii. ss. }
        { eapply typify_has_type_list; et. xomega. }
      * rr. ss. esplits; et.
    + inv SAFESRC. folder. hexploit (find_funct_lessdef ge FINDF0 FPTR); et. intro FEQ. rewrite <- FEQ in *. clarify.
      rpapply RTLC.initial_frame_intro; et. f_equal; ss.
      inv TYP0; ss. congruence.
    + ss.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    inv FPTR; cycle 1.
    { rewrite <- H0 in *. ss. }
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des.
    exploit (sig_function_translated); eauto. intro SGEQ. ss.
    ss. unfold bind in *. folder. des_ifs. ss.

    exploit (fill_arguments_progress (Locmap.init Vundef)
                                     (typify_list (Args.vs args_tgt) (sig_args (fn_sig f)))
                                     (loc_arguments f.(fn_sig))); eauto.
    { rewrite <- sig_args_length. rewrite SGEQ. rewrite <- LEN. admit "ez". }
    i; des.
    rename ls1 into ls_init.
    exploit fill_arguments_spec; et. i; des.

    esplits; eauto. econs; eauto.
    + folder. rewrite <- H1. eauto.
    + econs; eauto.
      * erewrite <- lessdef_list_length; eauto. congruence.
      * inv TYP; ss. congruence.
    + ii. rewrite OUT in H0; ss.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder.
    esplits; eauto.
    + econs; eauto.
      * folder. des.
        r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE.
        apply (fsim_external_funct_id GE); ss.
        folder.
        inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemExt.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC.
    inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify. econs; eauto.
      * eapply match_stackframes_after; et.
      * hexploit (loc_result_one sg_arg); et. intro ONE. destruct (loc_result sg_arg) eqn:T; ss.
        rewrite Locmap.gss. eapply lessdef_typify; et.
      * eapply agree_callee_save_after; et.
        admit "ez - we can just use 'inv STACKS; ss.' but make lemma".
      * eapply typify_has_type; et.
      * rr. rr in DUMMYTGT. des. ss. destruct ts; ss. des_ifs_safe; ss. destruct ts; ss; et.
        unfold undef_outgoing_slots. unfold dummy_stack in *. clarify. esplits; et.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS; ss. { inv MAINARGS. } destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
    econs; et; ss.
    rpapply RES.
    admit "ez - make lemma: below proof works
    do 2 f_equal.
    clear - SAMERES.
    unfold loc_result. des_ifs. unfold loc_result_64. des_ifs.
".
  - left; i.
    esplits; eauto.
    { apply RTLC.modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@step_simulation prog _ skenv_link skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    { ss. des. ss. }
    i; des.
    exploit (lift_plus LTL.step (fun st => get_stack st <> []) strong_wf_tgt); et.
    { intros st X Y. rr in X. des. rewrite Y in *. ss. }
    { i. folder. unfold strong_wf_tgt in *. des. inv HSTEP; ss; eauto.
      - des_ifs; ss; eauto.
      - des_ifs; ss; eauto. right. ii. inv HSTEP0; ss. }
    { ii. unfold strong_wf_tgt in *; des. inv HSTEP; try inv STACKS; ss; clarify; et; des_ifs; et. }
    { intro T. inv H0; ss; clarify; try inv STACKS; ss; try inv MAINARGS; ss. }
    i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
    + instantiate (1:= (SimMemExt.mk _ _)). econs; ss.
Unshelve.
  all: ss.
  all: econs; et.
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (RTLC.module prog) (LTLC.module tprog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy - see DeadcodeproofC".
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
