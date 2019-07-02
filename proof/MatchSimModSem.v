Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import Skeleton SimModSem SimMem SimSymb.
Require Import Sound Preservation.
Require MatchSimModSemExcl.

Set Implicit Arguments.





Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Variable msp: ModSemPair.t.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).
  Variable sound_state: Sound.t -> mem -> ms_src.(state) -> Prop.
  Hypothesis PRSV: local_preservation ms_src sound_state.

  Variable match_states: forall
      (sm_arg: SimMem.t)
      (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMem.t)
    ,
      Prop
  .

  Variable match_states_at: forall
      (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMem.t)
    ,
      Prop
  .

  Inductive match_states_at_helper
            (sm_init: SimMem.t)
            (idx_at: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMem.t): Prop :=
  | match_states_at_intro
      (MATCH: match_states sm_init idx_at st_src0 st_tgt0 sm_at)
      args_src args_tgt
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 args_src)
      (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 args_tgt)
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      (MLE: SimMem.le sm_at sm_arg)
      (MWF: SimMem.wf sm_arg)
      (MATCHARG: match_states_at st_src0 st_tgt0 sm_at sm_arg)
  .

  Hypothesis INITBSIM: forall
      sm_arg
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      args_src args_tgt
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      st_init_tgt
      (INITTGT: ms_tgt.(ModSem.initial_frame) args_tgt st_init_tgt)
      (SAFESRC: exists _st_init_src, ms_src.(ModSem.initial_frame) args_src _st_init_src)
    ,
      exists st_init_src sm_init idx_init,
        (<<INITSRC: ms_src.(ModSem.initial_frame) args_src st_init_src>>)
        /\
        (<<MLE: SimMem.le sm_arg sm_init>>)
        /\
        (<<MATCH: match_states sm_arg
                               idx_init st_init_src st_init_tgt sm_init>>)
  .

  Hypothesis INITPROGRESS: forall
      sm_arg
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      args_src args_tgt
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      (SAFESRC: exists st_init_src, ms_src.(ModSem.initial_frame) args_src st_init_src)
    ,
      exists st_init_tgt,
        (<<INITTGT: ms_tgt.(ModSem.initial_frame) args_tgt st_init_tgt>>)
  .

  Hypothesis ATMWF: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.is_call) st_src0)
    ,
      <<MWF: SimMem.wf sm0>>
  .

  Hypothesis ATFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      args_src
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 args_src)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)
    ,
      exists args_tgt sm_arg,
        (<<CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 args_tgt>>)
        /\
        (<<SIMARGS: SimMem.sim_args args_src args_tgt sm_arg>>)
        /\
        (<<MLE: SimMem.le sm0 sm_arg>>)
        /\
        (<<MWF: SimMem.wf sm_arg>>)
        /\
        (<<MATCHAT: match_states_at st_src0 st_tgt0 sm0 sm_arg>>)
  .

  Hypothesis AFTERFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      sm_arg
      (MLE: SimMem.le sm0 sm_arg)
      (* (MWF: SimMem.wf sm_arg) *)
      sm_ret
      (* (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret) *)
      sm_arg_lift
      (MLE: SimMem.le sm_arg_lift sm_ret)
      (MWF: SimMem.wf sm_ret)
      retv_src retv_tgt
      (SIMRET: SimMem.sim_retv retv_src retv_tgt sm_ret)
      st_src1
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 retv_src st_src1)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)

      (* history *)
      (HISTORY: match_states_at_helper sm_init idx0 st_src0 st_tgt0 sm0 sm_arg)

      (* just helpers *)
      sm_unlift
      (MWFAFTR: SimMem.wf sm_unlift)
      (MLEAFTR: SimMem.le sm_arg sm_unlift)
      (* (MWFAFTR: SimMem.wf (SimMem.unlift sm_arg sm_ret)) *)
      (* (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret)) *)
    ,
      exists sm_after idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 retv_tgt st_tgt1>>)
        /\
        (<<MATCH: match_states sm_init idx1 st_src1 st_tgt1 sm_after>>)
        /\
        (<<MLE: SimMem.le sm_unlift sm_after>>)
  .

  Hypothesis FINALFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MFUTURE: SimMem.le sm_init sm0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      retv_src
      (FINALSRC: ms_src.(ModSem.final_frame) st_src0 retv_src)
    ,
      exists sm_ret retv_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 retv_tgt>>)
        /\
        (<<SIMRET: SimMem.sim_retv retv_src retv_tgt sm_ret>>)
        /\
        (<<MLE: SimMem.le sm0 sm_ret>>)
        /\
        (<<MWF: SimMem.wf sm_ret>>)
  .

  Let STEPFSIM := forall
      sm_init idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)
    ,
      (<<RECEP: receptive_at ms_src st_src0>>)
      /\
      (<<STEPFSIM: forall
             tr st_src1
             (STEPSRC: Step ms_src st_src0 tr st_src1)
           ,
             exists idx1 st_tgt1 sm1,
               (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/
                           <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states sm_init idx1 st_src1 st_tgt1 sm1>>)
                    >>)
  .

  Let STEPBSIM := forall
      sm_init idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)
    ,
      (* (<<PROGRESS: ModSem.is_step ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) *)
      (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>)
      /\
      (<<STEPBSIM: forall
             tr st_tgt1
             (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1)
           ,
             exists idx1 st_src1 sm1,
               (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/
                           <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states sm_init idx1 st_src1 st_tgt1 sm1>>)
                    >>)
  .

  Remark safe_modsem_is_smaller
         st_src0
         (NOTCALL: ~ ModSem.is_call ms_src st_src0)
         (NOTRET: ~ ModSem.is_return ms_src st_src0)
         (SAFE: safe_modsem ms_src st_src0)
    :
      ModSem.is_step ms_src st_src0
  .
  Proof. rr. specialize (SAFE _ (star_refl _ _ _ _)). des; ss. eauto. Qed.

  Hypothesis STEPSIM: STEPFSIM \/ STEPBSIM.

  Hypothesis BAR: bar_True.

  Theorem match_states_sim
    :
      <<SIM: msp.(ModSemPair.sim)>>
  .
  Proof.
    eapply MatchSimModSemExcl.match_states_sim with
        (has_footprint := top3) (mle_excl := fun _ _ => SimMem.le) (sidx := unit); eauto.
    { ss. }
    { ii. eapply PRSV. }
    { ii. r. etrans; eauto. }
    { i. eapply SimMem.pub_priv; et. }
    { ii. exploit ATFSIM; eauto. { eapply SOUND. ss. } i; des. esplits; eauto. }
    { i. exploit AFTERFSIM; try apply SIMRET; et.
      { eapply SOUND. ss. }
      { inv HISTORY; econs; eauto. }
      i; des. esplits; eauto.
    }
    { destruct STEPSIM.
      - left. subst STEPFSIM. ii. exploit H; eauto. { eapply SOUND; ss. }
      - right. subst STEPBSIM. ii. exploit H; eauto. { eapply SOUND; ss. }
    }
  Qed.

End MATCHSIMFORWARD.

