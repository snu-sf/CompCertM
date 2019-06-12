Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import b bspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.

Set Implicit Arguments.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (bspec.module prog).
Let md_tgt: Mod.t := (ClightC.module2 prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog) prog.(prog_comp_env).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states_internal: bspec.state -> Clight.state -> Prop :=
| match_callstate
    i m_src m_tgt
    fptr ty 
  :
    match_states_internal (Callstate i m_src) (Clight.Callstate fptr ty [Vint i] Kstop m_tgt)
.

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: bspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ => eq) eq tt) ge tge.
Proof.
  subst_locals. ss. ii.
  eapply SimSymbId.sim_skenv_revive; eauto.
  admit "ez".
Qed.

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
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemInj.mk _ _ _ _ _ _ _).
    esplits; eauto.
    + econs; eauto with mem; ss.
      eapply SimMemInj.frozen_refl.
    + inv SAFESRC. destruct args_src, args_tgt; ss. clarify.
      econs; ss; eauto.
      inv VALS. inv H1. inv H3.
      assert(fd = f_f).
      {
        uge. des_ifs.
        unfold SkEnv.revive, SkEnv.project in Heq. ss.
        rewrite MapsC.PTree_filter_map_spec in *.
        unfold o_bind, o_join, o_map in Heq. des_ifs.
        clear - Heq2.
        unfold prog in *. unfold Clightdefs.mkprogram in *. ss.
        unfold prog_defmap in *. ss. unfold global_definitions in *.
        apply PTree_Properties.in_of_list in Heq2.
        ss. des; clarify.
      } clarify.
      assert(tvs = [Vint i]).
      {
        unfold signature_of_function in TYP. ss.
        inv TYP. ss. cbn. unfold typify. des_ifs; ss.
      } clarify.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    (* exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder. *)
    (* inv TYP. *)
    esplits; eauto. econs; eauto.
    + folder. rewrite <- FPTR. eauto.
    + rewrite <- VALS. ss.
    + ss. eauto with congruence.
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
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv STACKS; ss. destruct sm0; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto.
  - left; i.
    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@step_simulation prog skenv_link); eauto.
    { inv SIMSKENV. ss. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
