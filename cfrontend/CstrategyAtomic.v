Require Import Axioms.
Require Import Classical.
Require Import CoqlibC.
Require Import Errors.
Require Import MapsC.
Require Import IntegersC.
Require Import Floats.
Require Import ValuesC.
Require Import ASTC.
Require Import MemoryC.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import CsemC.
Require Import sflib.
(** newly added **)
Require Export Simulation Cstrategy CopC Ctypes Ctyping Csyntax Cexec.
Require Import Skeleton Mod ModSem.
Require Import CtypesC.
Require Import Conventions.
Require Import CtypingC.
Require Export CstrategyC.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.

Definition modsem (skenv_link: SkEnv.t) (p: program) := ModSem.Atomic.trans (CstrategyC.modsem skenv_link p).

Definition module (p: program) := Mod.Atomic.trans (CstrategyC.module p).







Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog: program.
Let md_src: Mod.t := (CstrategyC.module prog).
Let md_tgt: Mod.t := (module prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: Csem.state) (st_tgt0: (trace * Csem.state)) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: st_src0 = st_tgt0.(snd))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge.
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
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemId.mk _ _).
    esplits; eauto.
    + econs; eauto; ss.
      * inv TYP. rpapply match_callstates; eauto.
        { econs; eauto. }
        inv SAFESRC. folder.
        inv TYP.
        exploit (Genv.find_funct_transf_genv SIMGE); eauto. rewrite <- FPTR in *. intro FINDFSRC; clarify.
        ss. f_equal; try congruence.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    inv TYP.
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

Variables prog: program.
Definition mp: ModPair.t := ModPair.mk (CstrategyC.module prog) (module prog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  ii. inv SIMSKENVLINK. econs; eauto.
  { eapply SoundTop.sound_state_local_preservation; eauto. }
  i. ss. split.
Qed.

End SIMMOD.

