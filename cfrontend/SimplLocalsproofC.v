Require Import FSets.
Require Import CoqlibC Errors Ordered Maps Integers Floats.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import Ctypes Cop ClightC SimplLocals.
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




Lemma proj_sig_res_type
      targs0 tres0 cconv0
  :
    proj_sig_res (signature_of_type targs0 tres0 cconv0) = typ_of_type tres0
.
Proof.
  destruct tres0; ss.
Qed.


Local Existing Instance Val.mi_normal.

Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variable prog: Clight.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge: Clight.genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog)
                                  prog.(prog_comp_env).
Let tge: Clight.genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog)
                                   prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (ClightC.modsem1 skenv_link_src prog) (ClightC.modsem2 skenv_link_tgt tprog) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Clight.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: SimplLocalsproof.match_states ge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(ClightC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) ->
  Genv.match_genvs (match_globdef (fun (ctx: AST.program fundef type) f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof.
  subst_locals. ss.
  rr in TRANSL. destruct TRANSL. r in H.
  eapply SimSymbId.sim_skenv_revive; eauto.
  { ii. u. unfold transf_fundef, bind in MATCH. des_ifs; ss; clarify. }
Qed.

Goal forall v ty, wt_val v ty -> val_casted v ty.
Proof.
  i. inv H; try econs; et.
  - unfold cast_int_int. unfold wt_int in *. unfold Int.eq in *. des_ifs.
    admit "".
    admit "".
  - admit "abort!!!!!!!!".
  - admit "abort!!!!!!!!".
  - admit "abort!!!!!!!!".
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des.
    eexists. exists sm_arg.
    esplits; eauto.
    { refl. }
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.
        exploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. intro FINDFTGT; des. ss.
        assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link_src)).
        {
          inv SIMSKENV. ss. inv INJECT. ss. 
          econs; eauto.
          + ii. ss. unfold Genv.find_symbol in *. eapply Plt_Ple_trans.
            { eapply Genv.genv_symb_range; et. }
            ss. refl.
          + ii. ss. unfold Genv.find_funct_ptr, Genv.find_funct, Genv.find_def in *. des_ifs. eapply Plt_Ple_trans.
            { eapply Genv.genv_defs_range; et. }
            ss. refl.
          + ii. ss. unfold Genv.find_var_info, Genv.find_def in *. des_ifs. eapply Plt_Ple_trans.
            { eapply Genv.genv_defs_range; et. }
            ss. refl.
        }
        assert(fptr = fptr0).
        { inv FPTR; ss. des_ifs.
          inv MGE. exploit FUNCTIONS; eauto. i. exploit DOMAIN; eauto. i. clarify.
        } clarify.
        assert(TYPTGT: exists tvs0, typecheck vs0 (signature_of_function fd0) tvs0).
        { inv TYP. esplits; eauto. econs; eauto. etrans; eauto. ss.
          unfold transf_function in *. unfold bind in *. des_ifs.
        } des.
        rpapply match_call_state; ss; eauto.
        { clear - MWF. inv MWF. ii. apply SRCEXT in H. rr in H. des. ss. }
        { clear - MWF. inv MWF. ii. apply TGTEXT in H. rr in H. des. ss. }
        { i. inv SIMSKENV. ss. inv INJECT. ss. 
          econs; eauto.
          - etrans; try apply MWF. ss.
          - etrans; try apply MWF. ss.
        }
        { econs; et. }
        { apply MWF. }
        { instantiate (1:= tvs0). admit "ez". }
        { }
        inv TYP.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. intro FINDFSRC; des.
        rewrite <- FPTR in *. clarify.
        inv FINDFSRC0.
        (* assert(TYEQ: (ClightC.signature_of_function fd0) = fn_sig fd). *)
        (* { monadInv H1. ss. } *)
        monadInv H1; ss.
        f_equal; try congruence.
        { exploit (function_type_implies_sig fd0); et. unfold type_of_function. ss. }
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    exploit make_match_genvs; eauto. intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP.
    inv H0. ss.
    assert(TYEQ: (ClightC.signature_of_function fd) = fn_sig tf0).
    { monadInv H3. ss. }
    (* assert(TYEQ: (map typ_of_type (map snd (Clight.fn_params fd))) = sig_args (fn_sig tf0)). *)
    (* { monadInv H3. ss. } *)
    esplits; eauto. econs; eauto.
    + folder. rewrite <- FPTR. eauto.
    + rewrite <- VALS. econs; eauto with congruence. rewrite <- TYEQ. ss.
    + rewrite <- VALS. rewrite <- TYEQ. ss.
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
        r in TRANSL.
        exploit (SimSymbId.sim_skenv_revive TRANSL); eauto.
        { ii. inv MATCH; ss. }
        intro GE.
        apply (sim_external_id GE); ss.
      * des. clarify. esplits; eauto.
        eapply SimSymb.simskenv_func_fsim; eauto; ss. destruct SIMSKENVLINK. ss.
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
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      rpapply match_returnstate; eauto. repeat f_equal. rewrite proj_sig_res_type. ss.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv MK; ss. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto.
  - esplits; eauto.
    { apply modsem2_receptive. }
    inv MATCH.
    ii. hexploit (@transl_step prog ge tge); eauto.
    { apply make_match_genvs; eauto. }
    i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (ClightC.module2 prog) (CsharpminorC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy - see DeadcodeproofC".
  - ii. eapply sim_modsem; eauto.
Unshelve.
  ss.
Qed.

End SIMMOD.

