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
Require Import Program.

Set Implicit Arguments.




(** exactly copied from Linearizeproof *)
Section WFTGT.

Definition wf_tgt (st_tgt0: LTL.state): Prop :=
  exists sg_init ls_init, last_option st_tgt0.(LTLC.get_stack) = Some (LTLC.dummy_stack sg_init ls_init)
.

Lemma lift_starN
      cnt tse tge st_tgt0 tr st_tgt1
      (STAR: starN LTL.step tse tge cnt st_tgt0 tr st_tgt1)
      (DUMMYTGT: wf_tgt st_tgt0)
      (STKAFTER: get_stack st_tgt1 <> [])
  :
    <<STAR: starN step tse tge cnt st_tgt0 tr st_tgt1>>
.
Proof.
  unfold wf_tgt in *.
  induction STAR; ii; ss.
  { econs; et. }
  pose s as S1. pose s' as S2. pose s'' as S3.
  (* pose s1 as S1. pose s2 as S2. pose s3 as S3. *)
  econs; et.
  - econs; et.
    des. inv H; ss; destruct s0; ss. exfalso. clarify.
    clear - STAR STKAFTER.
    dependent induction STAR; ii; ss. inv H; ss.
  - des. exploit IHSTAR; et. inv H; ss; try (by esplits; et).
    + des_ifs. rewrite DUMMYTGT. esplits; et.
    + des_ifs.
      * ss. clarify.
        clear - STAR STKAFTER.
        dependent induction STAR; ii; ss. inv H; ss.
      * rewrite DUMMYTGT. esplits; et.
Qed.

Lemma lift_starN_stronger
      cnt tse tge st_tgt0 tr st_tgt1
      (STAR: starN LTL.step tse tge cnt st_tgt0 tr st_tgt1)
      (DUMMYTGT: wf_tgt st_tgt0)
      (STKAFTER: get_stack st_tgt1 <> [])
  :
    <<STAR: starN step tse tge cnt st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: wf_tgt st_tgt1>>
.
Proof.
  unfold wf_tgt in *.
  revert_until STAR.
  induction STAR; ii; ss.
  { split. - econs; et. - des. esplits; et. }
  assert(DUMMYTGT0: wf_tgt s'').
  { clarify.
    eapply IHSTAR; et. clear IHSTAR.
    des. inv H; ss; try (by esplits; et).
    - des_ifs. esplits; et.
    - des_ifs.
      + ss. clarify. inv STAR; ss. inv H; ss.
      + esplits; et.
  }
  split; ss.
  econs; et.
  - econs; et.
    des. inv H; ss; destruct s0; ss. exfalso. clarify. ss. clarify.
    clear - STAR STKAFTER.
    dependent induction STAR; ii; ss. inv H; ss.
  - des.
    exploit IHSTAR; et.
    { inv H; ss; try (by esplits; et).
      - des_ifs. esplits; et.
      - des_ifs.
        + ss. clarify. inv STAR; ss. inv H; ss.
        + esplits; et.
    }
    i; des.
    inv H; ss; try (by esplits; et).
Qed.

Lemma starN_plus_iff
      G ST (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se ge st0 tr st1
  :
    (exists n, starN step se ge n st0 tr st1 /\ (n > 0)%nat) <-> plus step se ge st0 tr st1
.
Proof.
  split; i; des.
  - destruct n; ss.
    { xomega. }
    ginduction H; ii; ss.
    { xomega. }
    clarify. inv H0.
    + eapply plus_star_trans; et.
      { apply plus_one; et. }
      { apply star_refl; et. }
    + eapply plus_trans; et.
      { apply plus_one; et. }
      eapply IHstarN; et. xomega.
  - inv H. apply star_starN in H1. des. exists (Datatypes.S n). esplits; et.
    { econs; et. }
    { xomega. }
Qed.

Lemma lift_plus
      tse tge st_tgt0 tr st_tgt1
      (PLUS: plus LTL.step tse tge st_tgt0 tr st_tgt1)
      (DUMMYTGT: wf_tgt st_tgt0)
      (STKAFTER: get_stack st_tgt1 <> [])
  :
    <<PLUS: plus step tse tge st_tgt0 tr st_tgt1>> /\ <<DUMMYTGT: wf_tgt st_tgt1>>
.
Proof.
  apply starN_plus_iff in PLUS. des. apply lift_starN_stronger in PLUS; et. des. esplits; et.
  apply starN_plus_iff; et.
Qed.

End WFTGT.



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
    (DUMMYTGT: wf_tgt st_tgt0)
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
    exploit lift_plus; et.
    { ii. inv H0; try inv STACKS; ss; clarify; et; try inv MAINARGS; inv H2; ss. (* TODO: notnil lemma *) }
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
