Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import Skeleton SimModSem SimMemLift SimSymb.
Require Import Sound Preservation.
Require Import ModSemProps.
Require MatchSimModSemExcl.

Set Implicit Arguments.





Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Variable msp: ModSemPair.t.
  Let SMO := (ModSemPair.SMO msp).
  Context {SMOL: SimMemOhLift.class SMO}.
  Local Existing Instance SMO.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).
  Variable sound_state: Sound.t -> mem -> ms_src.(state) -> Prop.
  Hypothesis PRSV: local_preservation ms_src sound_state.

  Variable match_states: forall
      (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMemOh.t),
      Prop.

  Variable match_states_at: forall
      (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t),
      Prop.

  Inductive match_states_at_helper
            (idx_at: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t): Prop :=
  | match_states_at_intro
      (MATCH: match_states idx_at st_src0 st_tgt0 sm_at)
      oh_src oh_tgt args_src args_tgt
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 oh_src args_src)
      (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt)
      (SIMARGS: SimMemOh.sim_args oh_src oh_tgt args_src args_tgt sm_arg)
      (MLE: SimMemOh.le sm_at sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (MATCHARG: match_states_at st_src0 st_tgt0 sm_at sm_arg).

  Hypothesis MIDX: ms_src.(ModSem.midx) = ms_tgt.(ModSem.midx).

  Hypothesis INITBSIM: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt st_init_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (SIMARGS: SimMemOh.sim_args oh_src oh_tgt args_src args_tgt sm_arg)
      (INITTGT: ms_tgt.(ModSem.initial_frame) oh_tgt args_tgt st_init_tgt)
      (SAFESRC: exists _st_init_src, ms_src.(ModSem.initial_frame) oh_src args_src _st_init_src),
      exists st_init_src sm_init idx_init,
        (<<INITSRC: ms_src.(ModSem.initial_frame) oh_src args_src st_init_src>>) /\
        (<<MLE: SimMemOh.le sm_arg sm_init>>) /\
        (<<MATCH: match_states idx_init st_init_src st_init_tgt sm_init>>).

  Hypothesis INITPROGRESS: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (SIMARGS: SimMemOh.sim_args oh_src oh_tgt args_src args_tgt sm_arg)
      (SAFESRC: exists st_init_src, ms_src.(ModSem.initial_frame) oh_src args_src st_init_src),
      exists st_init_tgt, (<<INITTGT: ms_tgt.(ModSem.initial_frame) oh_tgt args_tgt st_init_tgt>>).

  Hypothesis ATMWF: forall idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.is_call) st_src0),
      <<MWF: SimMemOh.wf sm0>>.

  Hypothesis ATFSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) oh_src args_src
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 oh_src args_src)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0),
      exists oh_tgt args_tgt sm_arg,
        (<<CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt>>) /\
        (<<SIMARGS: SimMemOh.sim_args oh_src oh_tgt args_src args_tgt sm_arg>>) /\
        (<<MLE: SimMemOh.le sm0 sm_arg>>) /\
        (<<MWF: SimMemOh.wf sm_arg>>) /\
        (<<MATCHAT: match_states_at st_src0 st_tgt0 sm0 sm_arg>>).

  Hypothesis AFTERFSIM: forall
      idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) sm_arg sm_ret
      oh_src oh_tgt retv_src retv_tgt st_src1
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (MLE: SimMemOh.le sm0 sm_arg)
      (* (MWF: SimMemOh.wf sm_arg) *)
      (MLE: SimMemOh.le (SimMemOhLift.lift sm_arg) sm_ret)
      (MWF: SimMemOh.wf sm_ret)
      (SIMRET: SimMemOh.sim_retv oh_src oh_tgt retv_src retv_tgt sm_ret)
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 oh_src retv_src st_src1)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)

      (* history *)
      (HISTORY: match_states_at_helper idx0 st_src0 st_tgt0 sm0 sm_arg)

      (* just helpers *)
      (MWFAFTR: SimMemOh.wf (SimMemOhLift.unlift sm_arg sm_ret))
      (MLEAFTR: SimMemOh.le sm_arg (SimMemOhLift.unlift sm_arg sm_ret)),
      exists sm_after idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 oh_tgt retv_tgt st_tgt1>>) /\
        (<<MATCH: match_states idx1 st_src1 st_tgt1 sm_after>>) /\
        (<<MLE: SimMemOh.le (SimMemOhLift.unlift sm_arg sm_ret) sm_after>>).

  Hypothesis FINALFSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) oh_src retv_src
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (FINALSRC: ms_src.(ModSem.final_frame) st_src0 oh_src retv_src),
      exists sm_ret oh_tgt retv_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 oh_tgt retv_tgt>>) /\
        (<<SIMRET: SimMemOh.sim_retv oh_src oh_tgt retv_src retv_tgt sm_ret>>) /\
        (<<MLE: SimMemOh.le sm0 sm_ret>>) /\
        (<<MWF: SimMemOh.wf sm_ret>>).

  Let STEPFSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<RECEP: receptive_at ms_src st_src0>>) /\
      (<<STEPFSIM: forall tr st_src1
             (STEPSRC: Step ms_src st_src0 tr st_src1) ,
             exists idx1 st_tgt1 sm1,
               (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/
                           <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMemOh.le sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Let STEPBSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) /\
      (<<STEPBSIM: forall tr st_tgt1
             (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1) ,
             exists idx1 st_src1 sm1,
               (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/
                           <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMemOh.le sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Hypothesis STEPSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t)
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0),
      STEPFSIM idx0 st_src0 st_tgt0 sm0 \/ STEPBSIM idx0 st_src0 st_tgt0 sm0.

  Remark safe_modsem_is_smaller
         st_src0
         (NOTCALL: ~ ModSem.is_call ms_src st_src0)
         (NOTRET: ~ ModSem.is_return ms_src st_src0)
         (SAFE: safe_modsem ms_src st_src0):
      ModSem.is_step ms_src st_src0.
  Proof. rr. specialize (SAFE _ (star_refl _ _ _ _)). des; ss. eauto. Qed.

  Hypothesis BAR: bar_True.

  Theorem match_states_sim: <<SIM: msp.(ModSemPair.sim)>>.
  Proof.
    eapply MatchSimModSemExcl.match_states_sim with
        (has_footprint := top3) (mle_excl := fun _ _ => SimMemOh.le) (sidx := unit); eauto; ss.
    { ii. eapply PRSV. }
    { ii. r. etrans; eauto. }
    { ii. exploit ATFSIM; eauto. { eapply SOUND. ss. } i; des. esplits; eauto. }
    { i. exploit AFTERFSIM; et.
      { eapply SOUND. ss. }
      { inv HISTORY; econs; eauto. }
      i; des. esplits; eauto.
    }
    { ii. exploit STEPSIM; eauto. { eapply SOUND; ss. } i; des; r in H; des; eauto.
      left. esplits; eauto. i. exploit STEPFSIM0; eauto. i; des_safe. esplits; eauto. apply star_refl.
    }
  Qed.

End MATCHSIMFORWARD.
