Require Import Axioms CoqlibC Maps Iteration (* Errors *).
Require Import Integers Floats AST Linking.
Require Import ValuesC Memory Events Globalenvs Smallstep.
Require Import Machregs LocationsC Conventions Op LinearC.
Require Import Debugvar.
(** newly added **)
Require Export Debugvarproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.
Require Import LiftDummy.

Set Implicit Arguments.



Definition strong_wf_tgt (st_tgt0: Linear.state): Prop :=
  exists sg_init ls_init, last_option st_tgt0.(LinearC.get_stack) = Some (Linear.dummy_stack sg_init ls_init)
.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog tprog: program.
Let md_src: Mod.t := (LinearC.module prog).
Let md_tgt: Mod.t := (LinearC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: Linear.state) (st_tgt0: Linear.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Debugvarproof.match_states st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (DUMMYTGT: strong_wf_tgt st_tgt0)
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = Errors.OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    inv TYP.
    exploit (fill_arguments_progress ls_init (typify_list (Args.vs args_src) (sig_args (fn_sig fd)))
                                     (Conventions1.loc_arguments (fn_sig fd))); eauto.
    { apply (f_equal (@length _)) in TYP0. rewrite map_length in *. etrans; try apply TYP0; eauto. congruence. }
    intro P; des.
    hexploit (@fill_arguments_spec); et. intro Q; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    destruct args_src, args_tgt; ss. clarify.
    eexists. eexists (SimMemId.mk _ _).
    esplits; ss; cycle 1.
    + econs; eauto; ss.
      * rpapply match_states_call.
        { econs; eauto.
          - instantiate (1:= (dummy_stack (fn_sig fd) ls_init)). unfold dummy_stack, dummy_function.
            rpapply match_stackframe_intro; eauto; swap 1 2.
            + econs; eauto.
            + econs; eauto. ss. econs; eauto. econs; eauto.
            + ss. f_equal; ss.
              * instantiate (1:= None). instantiate (1:= None). ss.
              * instantiate (1:= None). instantiate (1:= None). ss.
          - econs; et.
        }
      * rr. esplits; ss; eauto.
    + inv SAFESRC. folder.
      inv TYP.
      exploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. intro FINDFSRC; des; clarify.
      unfold transf_fundef; ss. unfold Errors.bind in *. des_ifs.
      econs; swap 1 2.
      { folder; ss. eauto. }
      all: ss.
      unfold transf_function in *. des_ifs.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP.
    destruct args_src, args_tgt; ss. clarify. unfold Errors.bind in *. des_ifs.
    destruct sm_arg; ss. clarify.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify.
    exploit (fill_arguments_progress (Locmap.init Vundef) (typify_list vs0 (sig_args (fn_sig fd)))
                                     (Conventions1.loc_arguments (fn_sig fd))); eauto.
    { apply (f_equal (@length _)) in TYP0. rewrite map_length in *. etrans; try apply TYP0; eauto. }
    intro P; des.
    hexploit (fill_arguments_spec); eauto. intro Q; des.
    assert(SGEQ: fn_sig fd = fn_sig f).
    { unfold transf_function in *; des_ifs. }
    esplits; eauto. econs; swap 1 2.
    { ss. folder. eauto. }
    all: ss; eauto with congruence.
    + econs; ss; eauto with congruence.
  - (* call wf *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
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
    + econs; ss; eauto.
      * instantiate (1:= SimMemId.mk _ _). ss.
      * ss.
    + ss.
  - (* after fsim *)
    inv AFTERSRC.
    inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify. econs; eauto.
      { inv H5; ss. - econs; eauto. - des_ifs. econs; eauto. inv H. econs; eauto. }
      { clear - DUMMYTGT. unfold strong_wf_tgt in *. des. destruct ts; ss. unfold dummy_stack, dummy_function in *. des_ifs; ss; clarify; esplits; et. }
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv H3; ss. inv H4; ss. rr in DUMMYTGT. des. ss. clarify. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto.
    econs; ss; eauto. inv H1; ss. inv H2; ss.
  - left; i.
    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH.
    ii. rr in STEPSRC. des. hexploit (@transf_step_correct prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des.
    exploit (lift_plus Linear.step (fun st => get_stack st <> []) strong_wf_tgt); ss; et.
    { intros st X Y. rr in X. des. rewrite Y in *. ss. }
    { i. folder. unfold strong_wf_tgt in *. des. inv HSTEP; ss; eauto.
      - des_ifs; ss; eauto.
      - des_ifs; ss; eauto. right. ii. inv HSTEP0; ss. }
    { ii. unfold strong_wf_tgt in *; des. inv HSTEP; try inv STACKS; ss; clarify; et; des_ifs; et. }
    { intro T. inv H0; ss; clarify; try inv STACKS; ss; try inv H1; ss. }
    intro TT; des.
    esplits; eauto.
    * left. eapply ModSemProps.spread_dplus; eauto.
      { eapply modsem_determinate; eauto. }
    * instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (LinearC.module prog) (LinearC.module tprog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold Errors.bind, transf_function in *. des_ifs. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.

