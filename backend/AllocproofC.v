Require Import FunInd.
Require Import FSets.
Require Import CoqlibC IntegersC.
From compcertr Require Import
     Ordered Maps Errors Floats
     AST Linking Lattice Kildall
     Globalenvs Events Smallstep
     Op Registers Conventions
     sflib.
Require Import ValuesC MemoryC.
From compcertr Require Archi.
Require Import RTLC LocationsC RTLtypingC LTLC.
From compcertr Require Import Allocation.
(** newly added **)
From compcertr Require Export Allocproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require Import ModSemProps.
Require SimMemExt.
Require SoundTop.
Require Import LiftDummy.

Set Implicit Arguments.




Definition strong_wf_tgt (st_tgt0: LTL.state): Prop :=
  exists sg_init ls_init, last_option (LTLC.get_stack st_tgt0) = Some (LTL.dummy_stack sg_init ls_init).

Lemma agree_callee_save_after
      tstks ls sg tv
      (NOTNIL: tstks <> [])
      (AG: agree_callee_save (parent_locset tstks) ls):
    <<AG: agree_callee_save (parent_locset (stackframes_after_external tstks))
                            (Locmap.setpair (loc_result sg) tv (undef_caller_save_regs ls))>>.
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
      (STACKS: match_stackframes tse tge stks tstks sg):
    <<STACKS: match_stackframes tse tge stks (stackframes_after_external tstks) sg>>.
Proof.
  inv STACKS; econs; et.
  i. exploit STEPS; et. clear - H1.
  unfold agree_callee_save in *.
  ii. exploit H1; et. intro T. unfold undef_outgoing_slots in *. des_ifs.
Qed.

Lemma match_stackframes_not_nil
      skenv_link tge stack ts sg_arg
      (MATCH: match_stackframes skenv_link tge stack ts sg_arg):
  ts <> [].
Proof. inv MATCH; ss. Qed.

Lemma getpair_equal
      sg_init sg ls
      (SAMERES : sig_res sg_init = sig_res sg):
  Locmap.getpair (map_rpair R (loc_result sg_init)) ls = Locmap.getpair (map_rpair R (loc_result sg)) ls.
Proof. do 2 f_equal. unfold loc_result. des_ifs. unfold loc_result_64. unfold proj_sig_res. rewrite SAMERES. ss. Qed.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: RTL.program.
Variable tprog: LTL.program.
Let md_src: Mod.t := (RTLC.module2 prog).
Let md_tgt: Mod.t := (LTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: RTL.state) (st_tgt0: LTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Allocproof.match_states skenv_link tge st_src0 st_tgt0)
    (MCOMPATSRC: (RTL.get_mem st_src0) = (SimMem.src sm0))
    (MCOMPATTGT: (LTLC.get_mem st_tgt0) = (SimMem.tgt sm0))
    (DUMMYTGT: strong_wf_tgt st_tgt0).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link (Mod.sk md_src))
                      (SkEnv.project skenv_link (Mod.sk md_tgt)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := fun _ _ => wt_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply wt_state_local_preservation; et.
    ii. exploit wt_prog; eauto.
  - (* init bsim *)
    destruct sm_arg; ss. clarify. inv INITTGT. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit lessdef_list_length; et. intro LEN; des.
    exploit (bsim_internal_funct_id SIMGE); et. i; des.
    exploit (sig_function_translated); eauto. intro SGEQ. ss.
    eexists. eexists (SimMemExt.mk _ _). esplits; cycle 2.
    + econs; eauto; ss.
      * inv TYP. eapply match_states_call; eauto; ss.
        { econs; et. }
        { rewrite <- TYP0. eapply lessdef_list_typify_list; try apply VALS; et. extlia. }
        { eapply JunkBlock.assign_junk_block_extends; eauto. }
        { eapply typify_has_type_list; et. extlia. }
      * rr. ss. esplits; et.
    + inv SAFESRC. folder. hexploit (find_funct_lessdef ge FINDF0 FPTR); et. intro FEQ. rewrite <- FEQ in *. clarify.
      rpapply RTLC.initial_frame2_intro; et. f_equal; ss.
      inv TYP0; ss. congruence.
    + ss.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. inv FPTR; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des.
    exploit (sig_function_translated); eauto. intro SGEQ. ss.
    ss. unfold bind in *. folder. des_ifs. ss.

    exploit (fill_arguments_progress (Locmap.init Vundef)
                                     (typify_list vs_tgt (sig_args (fn_sig f)))
                                     (loc_arguments f.(fn_sig))); eauto.
    { rewrite <- sig_args_length. rewrite SGEQ.
      unfold typify_list. rewrite zip_length. rewrite <- LEN.
      erewrite <- lessdef_list_length; et. eapply Min.min_idempotent.
    }
    i; des. rename ls1 into ls_init.
    exploit fill_arguments_spec; et. i; des.

    esplits; eauto. econs; eauto.
    + rewrite SGEQ. ss.
    + econs; eauto.
      erewrite <- lessdef_list_length; eauto. congruence.
    + ii. rewrite OUT; ss.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
        folder. inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
    + econs; ss; eauto.
      * instantiate (1:= SimMemExt.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. econs; eauto.
      * eapply match_stackframes_after; et.
      * hexploit (loc_result_one sg_arg); et. i. des. rewrite ONE. ss.
        rewrite Locmap.gss. eapply lessdef_rettypify; et.
      * eapply agree_callee_save_after; et. eapply match_stackframes_not_nil; et.
      * eapply Val.has_proj_rettype. eapply rettypify_has_rettype; et.
      * rr. rr in DUMMYTGT. des. ss. destruct ts; ss. des_ifs_safe; ss. destruct ts; ss; et.
        unfold undef_outgoing_slots. unfold dummy_stack in *. clarify. esplits; et.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS; ss. destruct sm0; ss. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
    econs; et; ss. rpapply RES. eapply getpair_equal; et.
  - left; i. esplits; eauto.
    { apply RTLC.modsem2_receptive; et. }
    inv MATCH. ii. hexploit (@step_simulation prog _ skenv_link skenv_link); eauto.
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
  all: ss. apply msp.
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := SimSymbId.mk_mp (RTLC.module2 prog) (LTLC.module tprog).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. exploit sig_function_translated; et. i. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. des_ifs. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
