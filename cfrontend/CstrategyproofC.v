From compcertr Require Import
     Axioms
     Floats
     sflib.
Require Import Classical.
Require Import CoqlibC.
Require Import ErrorsC.
Require Import MapsC.
Require Import IntegersC.
Require Import ValuesC.
Require Import ASTC.
Require Import MemoryC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import SmallstepC.
Require Import CtypesC.
Require Import CopC.
From compcertr Require Import Csyntax.
Require Import CsemC.
Require Import CstrategyC.
From compcertr Require Import Cstrategyproof.
(** newly added *)
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.


Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog: program.
Let md_src: Mod.t := (CsemC.module prog).
Let md_tgt: Mod.t := (module prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge: genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_src)) prog) prog.(prog_comp_env).
Let tge: genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: Csem.state) (st_tgt0: Csem.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: st_src0 = st_tgt0)
    (MWF: SimMem.wf sm0).

Require Import Classes.Equivalence. Ltac inv H := inversion H; clear H; subst *.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv INITTGT. inv SIMARGS; ss. subst *.
    eexists. eexists (SimMemId.mk _ _). esplits; eauto; cycle 1.
    + econs; ss; eauto.
    + econs; eauto; ss.
  - (* init progress *)
    des. inv SAFESRC. inv SIMARGS; ss. subst *. inv TYP.
    esplits; eauto. econs; eauto. ss.
  - (* call wf *)
    inv MATCH; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify. inv CALLSRC. ss. des; ss. clarify.
    folder. eexists _, (SimMemId.mk _ _). esplits; ss; eauto.
    + econs; eauto.
    + econs; ss; eauto.
  - (* after fsim *)
    inv AFTERSRC. inv SIMRET; ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. des; ss. clarify. esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
  - (* final fsim *)
    inv MATCH. inv FINALSRC. ss. des; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto. econs; ss; eauto.
  - (* step *)
    right; i. inv MATCH; ss. splits.
    { ii. exploit Cstrategyproof.progress; eauto.
      { instantiate (1:= ModSem.is_call (CsemC.modsem skenv_link prog) \1/
                                        ModSem.is_return (CsemC.modsem skenv_link prog)).
        ss. intro T. des; inv T; inv H0; ss.
      }
      { ii. exploit H; eauto. i; des; eauto. }
      i; des; eauto.
      - inv H0. contradict NOTRET. rr. esplits. econs; eauto.
      - inv H0. contradict NOTCALL. rr. esplits. eauto.
      - inv H0. contradict NOTRET. rr. esplits. eauto.
    }
    i. folder.
    exploit Cstrategyproof.step_simulation; eauto. i. esplits; eauto.
    { econs; eauto. instantiate (1:= sm0). ss. }
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog: program.
Definition mp: ModPair.t := SimSymbId.mk_mp (CsemC.module prog) (Mod.Atomic.trans (module prog)).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK.
    eapply factor_simmodsem_target; eauto.
    { ii. eapply CsemC.single_events_at; eauto. ss. eauto. }
    { ii. ss. hexploit (@modsem_strongly_receptive skenv_link_tgt prog s); eauto. intro SR.
      inv SR. exploit ssr_traces_at; eauto.
    }
    eapply sim_modsem; eauto.
Qed.

End SIMMOD.
