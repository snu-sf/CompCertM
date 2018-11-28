Require Import CoqlibC Errors Maps Integers Floats.
Require Import AST Linking.
Require Import ValuesC Events Memory Globalenvs Smallstep.
Require Import CtypesC Cop ClightC Cminor CsharpminorC.
Require Import Cshmgen.
Require Import sflib.
(** newly added **)
Require Export Cshmgenproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.
Require Import CtypingC.

Set Implicit Arguments.




Lemma proj_sig_res_type
      targs0 tres0 cconv0
  :
    proj_sig_res (signature_of_type targs0 tres0 cconv0) = typ_of_type tres0
.
Proof.
  destruct tres0; ss.
Qed.


Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge: Clight.genv := Build_genv (CSkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog)
                                  prog.(prog_comp_env).
Let tge: Csharpminor.genv := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (ClightC.modsem2 skenv_link_src prog) (CsharpminorC.modsem skenv_link_tgt tprog) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Clight.state) (st_tgt0: Csharpminor.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Cshmgenproof.match_states prog ge st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(ClightC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(CsharpminorC.get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) ->
  Genv.match_genvs (match_globdef match_fundef match_varinfo prog) ge tge.
Proof. subst_locals. ss. admit "". (* eapply SimSymbId.sim_skenv_revive; eauto. { ii. clarify. u. des_ifs. } *) Qed.

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
    exploit make_match_genvs; eauto. intro SIMGE. des.
    eexists. eexists (SimMemId.mk _ _).
    esplits; eauto.
    + econs; eauto; ss.
      * inv TYP.
        inv SAFESRC. folder.
        rpapply match_callstate; eauto.
        { econs; eauto. }
        { ss. }
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
        (* exploit (SimSymbId.sim_skenv_revive TRANSL); eauto. *)
        (* { ii. destruct f_src, f_tgt; ss; try unfold bind in *; des_ifs. } *)
        (* intro GE. *)
        (* apply (sim_external_id GE); ss. *)
        admit "".
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
    { admit"apply modsem_receptive.". }
    inv MATCH.
    ii. hexploit (@transl_step prog ge tge); eauto.
    { apply make_match_genvs; eauto. }
    i; des.
    esplits; eauto.
    + left. admit "plus -> DPlus".
    + instantiate (1:= SimMemId.mk _ _). econs; ss. eauto.
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

