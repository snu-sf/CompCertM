Require Import CoqlibC Maps UnionFind.
Require Import AST Linking.
Require Import ValuesC Memory Events Globalenvs Smallstep.
Require Import Op LocationsC LTLC.
Require Import Tunneling.
(* newly added *)
Require Export Tunnelingproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require Import ConventionsC.
Require SimMemExt.
Require SoundTop.
Require Import LiftDummy.

Set Implicit Arguments.


Definition strong_wf_tgt (st_tgt0: LTL.state): Prop :=
  exists sg_init ls_init, last_option st_tgt0.(LTLC.get_stack) = Some (LTL.dummy_stack sg_init ls_init).

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog tprog: program.
Let md_src: Mod.t := (LTLC.module prog).
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
          (idx: nat) (st_src0: LTL.state) (st_tgt0: LTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Tunnelingproof.match_states st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (DUMMYTGT: strong_wf_tgt st_tgt0)
    (MEASURE: measure st_src0 = idx).

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun ctx f tf => tf = tunnel_fundef f) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4);
    eauto; ii; ss.
  - eapply lt_wf.
  - eapply SoundTop.sound_state_local_preservation; et.
  - (* init bsim *)
    inv INITTGT. destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv TYP.
    exploit (fill_arguments_progress ls_init (typify_list vs_src (sig_args (fn_sig fd)))
                                     (Conventions1.loc_arguments (fn_sig fd))); eauto.
    { apply (f_equal (@length _)) in TYP0. rewrite map_length in *. etrans; try apply TYP0; eauto.
      exploit lessdef_list_length; eauto. intro EQ.
      rewrite ! typify_list_length. exploit lessdef_list_length; eauto.
    }
    intro P; des.
    hexploit (@fill_arguments_spec); et. intro Q; des.
    assert(LOCMAP: locmap_lessdef ls1 ls_init).
    { ii. destruct (classic (In l (regs_of_rpairs (loc_arguments (fn_sig fd))))).
      - exploit in_regs_of_rpairs_inv; et. intro P; des.
        exploit loc_arguments_one; eauto. intro Q; des.
        destruct p; ss. des; clarify. clear - P FILL TYP0 VALS.
        abstr (loc_arguments (fn_sig fd)) locs. abstr (sig_args (fn_sig fd)) tys.
        clear_tac. ginduction locs; ii; ss.
        destruct vs_src, vs_tgt; ss. inv VALS. destruct tys; ss. des; clarify; ss.
        + unfold typify_list in *. ss. des_ifs.
          rewrite <- H1. rewrite <- H5. eapply lessdef_typify; et.
        + exploit (IHlocs vs_src ls_init vs_tgt); eauto.
          * unfold typify_list in *. ss. des_ifs; eauto.
          * unfold typify_list in *. ss. des_ifs; eauto.
      - erewrite OUT; ss.
    }
    eexists. eexists (SimMemExt.mk _ _). esplits; ss; cycle 1.
    + econs; eauto; ss.
      * rpapply match_states_call; eauto.
        { econs; eauto.
          - instantiate (1:= (dummy_stack (fn_sig fd) ls1)). unfold dummy_stack, dummy_function. econs; eauto. 
          - econs; eauto. }
        { eapply JunkBlock.assign_junk_block_extends; eauto. }
      * rr. ss. esplits; eauto.
    + bar. inv SAFESRC. inv TYP. bar.
      exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. folder. clarify.
      inv FPTR; ss.
      clarify. eapply initial_frame_intro; ss.
      * ii. rewrite OUT; ss. exploit PTRFREE; eauto. clear - MWF. unfold JunkBlock.is_junk_value.
        i. des_ifs. des. esplits; eauto.
        { rewrite Mem.valid_block_extends; eauto. }
        { rewrite Mem.valid_block_extends; eauto. eapply JunkBlock.assign_junk_block_extends; eauto. }
      * ii. rewrite OUT; ss. rewrite SLOT; ss.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. inv FPTR; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify.
    inv TYP.
    exploit (fill_arguments_progress (Locmap.init Vundef) (typify_list vs_tgt (sig_args (fn_sig fd)))
                                     (Conventions1.loc_arguments (fn_sig fd))); eauto.
    { apply (f_equal (@length _)) in TYP0. rewrite map_length in *. etrans; try apply TYP0; eauto.
      exploit lessdef_list_length; eauto. intro EQ.
      rewrite ! typify_list_length. exploit lessdef_list_length; eauto.
    }
    intro P; des.
    hexploit (fill_arguments_spec); eauto. intro Q; des.
    esplits; eauto. econs; ss.
    + folder. eauto.
    + econs; eauto. ss. erewrite <- lessdef_list_length; eauto.
    + i. rewrite OUT; ss.
    + i. rewrite OUT; ss.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify. u in CALLSRC. des. inv CALLSRC. inv MATCHST; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. inv MATCHST; ss.
    folder. esplits; eauto.
    + econs; eauto.
      * folder. des. r in TRANSL. r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
        folder. inv FPTR; ss.
      * des. esplits; eauto. eapply SimSymb.simskenv_func_fsim; eauto; ss.
    + econs; ss; eauto.
      * eapply locmap_getpairs_lessdef; eauto.
      * instantiate (1:= SimMemExt.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      * econs; eauto.
        { inv STK; ss.
          { econs; et. }
          des_ifs. econs; et. inv H; econs; et; ii; unfold undef_outgoing_slots; des_ifs; ss.
        }
        eapply locmap_setpair_lessdef; et.
        { eapply locmap_undef_caller_save_regs_lessdef; et. }
        { eapply lessdef_typify; et. }
      * clear - DUMMYTGT. unfold strong_wf_tgt in *. des. destruct ts; ss. unfold dummy_stack, dummy_function in *. des_ifs; ss; clarify; esplits; et.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STK; ss. inv H3; ss. destruct sm0; ss. clarify. rr in DUMMYTGT. ss. des. clarify.
    eexists (SimMemExt.mk _ _). eexists (Retv.mk _ _). esplits; ss; eauto.
    + econs; ss; eauto. assert(sg_init = sg_init0). { inv H1; ss. } clarify.
      eapply locmap_getpair_lessdef; et.
  - left; i. esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH. ii. rr in STEPSRC. des. hexploit (@tunnel_step_correct prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des_safe. des.
    + assert(WEAKWFTGT: get_stack st2' <> []).
      { intro T. inv H; ss; clarify; try inv H0; ss; try inv STACKS; ss; try inv STK; ss. }
      esplits; eauto.
      * left. apply plus_one. split; ss.
        { eapply modsem_determinate; eauto. }
        rr. esplits; et.
      * instantiate (1:= SimMemExt.mk _ _). econs; ss.
        { rr. rr in DUMMYTGT. des. exploit step_preserves_last_option; try apply DUMMYTGT; eauto. }
    + clarify. esplits; et.
      * right. esplits; et.
        { eapply star_refl. }
      * instantiate (1:= SimMemExt.mk _ _). econs; ss.
Unshelve.
  all: ss.
  all: try (by econs; ss).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t := ModPair.mk (LTLC.module prog) (LTLC.module tprog) tt.

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto. ii. destruct f1; ss.
    + clarify. right. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.