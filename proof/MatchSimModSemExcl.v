Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem GlobalenvsC MemoryC ASTC.
Require Import Skeleton SimModSemLift SimMem SimMemLift SimSymb.
Require Import Sound Preservation ModSemProps.
Require Import Any.

Set Implicit Arguments.





Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Variable msp: ModSemPair.t.
  Let SMO := (ModSemPair.SMO msp).
  Context {SML: SimMemLift.class SM}.
  Local Existing Instance SMO.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).
  Variable sidx: Type.
  Hypothesis INHAB: inhabited sidx.
  Variable sound_states: sidx -> Sound.t -> mem -> ms_src.(state) -> Prop.
  Hypothesis PRSV: forall si, local_preservation ms_src (sound_states si).

  Variable match_states: forall
      (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMemOh.t),
      Prop.

  Variable match_states_at: forall
      (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t),
      Prop.

  (* you maintain some kind of `ownership` here. *)
  (* normal ownership: if I alloced, I can free that *)
  (* here: if I freed, I can unfree that *)
  Variable has_footprint: forall
      (st_init_src: ms_src.(ModSem.state)) (st_init_tgt: ms_tgt.(ModSem.state)) (sm0: SimMemOh.t),
      Prop.

  Variable mle_excl: forall
      (st_init_src: ms_src.(ModSem.state)) (st_init_tgt: ms_tgt.(ModSem.state)) (sm0: SimMemOh.t) (sm1: SimMemOh.t),
      Prop.

  Hypothesis FOOTEXCL: forall st_at_src st_at_tgt sm0 sm1 sm2
        (MWF: SimMemOh.wf sm0)
        (FOOT: has_footprint st_at_src st_at_tgt sm0)
        (MLEEXCL: (mle_excl st_at_src st_at_tgt) sm1 sm2)
        (MLE: SimMemOh.le sm0 sm1),
        <<MLE: SimMemOh.le sm0 sm2>>.

  Hypothesis (EXCLPRIV: forall st_init_src st_init_tgt sm0 sm1
                 (MWF: SimMemOh.wf sm0)
                 (EXCL: mle_excl st_init_src st_init_tgt sm0 sm1),
                 <<LE: SimMemOh.lepriv sm0 sm1>>).

  Inductive match_states_at_helper
            (idx_at: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t): Prop :=
  | match_states_at_intro
      (MATCH: match_states idx_at st_src0 st_tgt0 sm_at)
      oh_src oh_tgt args_src args_tgt
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 oh_src args_src)
      (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt)
      (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg)
      (MLE: SimMemOh.le sm_at sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (MATCHARG: match_states_at st_src0 st_tgt0 sm_at sm_arg).
      (* (FOOT: has_footprint st_src0 st_tgt0 sm_at) *)

  Hypothesis MIDX: SimMemOh.midx = ms_src.(ModSem.midx).
  Hypothesis MIDX0: ms_src.(ModSem.midx) = ms_tgt.(ModSem.midx).

  Hypothesis INITBSIM: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt st_init_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg)
      (INITTGT: ms_tgt.(ModSem.initial_frame) oh_tgt args_tgt st_init_tgt)
      (SAFESRC: exists _st_init_src, ms_src.(ModSem.initial_frame) oh_src args_src _st_init_src),
      exists st_init_src sm_init idx_init,
        (<<INITSRC: ms_src.(ModSem.initial_frame) oh_src args_src st_init_src>>) /\
        (<<MLE: SimMemOh.le sm_arg sm_init>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm_arg sm_init>>) /\
        (<<MATCH: match_states idx_init st_init_src st_init_tgt sm_init>>).

  Hypothesis INITPROGRESS: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMemOh.wf sm_arg)
      (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg)
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
      (SOUND: forall si, exists su0 m_init, (sound_states si) su0 m_init st_src0),
      exists oh_tgt args_tgt sm_arg,
        (<<CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt>>) /\
        (<<SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg>>) /\
        (<<FOOT: has_footprint st_src0 st_tgt0 sm0>>) /\
        (<<MLE: SimMemOh.le sm0 sm_arg>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_arg>>) /\
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
      (SIMRET: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt sm_ret)
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 oh_src retv_src st_src1)
      (SOUND: forall si, exists su0 m_init, (sound_states si) su0 m_init st_src0)

      (* history *)
      (HISTORY: match_states_at_helper idx0 st_src0 st_tgt0 sm0 sm_arg)

      (* just helpers *)
      (MWFAFTR: SimMemOh.wf (SimMemOhLift.unlift sm_arg sm_ret))
      (MLEAFTR: SimMemOh.le sm_arg (SimMemOhLift.unlift sm_arg sm_ret)),
      exists sm_after idx1 st_tgt1,
        (<<MLE: mle_excl st_src0 st_tgt0 (SimMemOhLift.unlift sm_arg sm_ret) sm_after>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx (SimMemOhLift.unlift sm_arg sm_ret) sm_after>>) /\
        forall (MLE: SimMemOh.le sm0 sm_after) (* helper *),
          ((<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 oh_tgt retv_tgt st_tgt1>>) /\
           (<<MATCH: match_states idx1 st_src1 st_tgt1 sm_after>>)).

  Hypothesis FINALFSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) oh_src retv_src
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (FINALSRC: ms_src.(ModSem.final_frame) st_src0 oh_src retv_src),
      exists sm_ret oh_tgt retv_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 oh_tgt retv_tgt>>) /\
        (<<SIMRET: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt sm_ret>>) /\
        (<<MLE: SimMemOh.le sm0 sm_ret>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_ret>>) /\
        (<<MWF: SimMemOh.wf sm_ret>>).

  Let STEPFSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<RECEP: receptive_at ms_src st_src0>>) /\
      (<<STEPFSIM: forall tr st_src1
             (STEPSRC: Step ms_src st_src0 tr st_src1) ,
             exists st_src2 idx1 st_tgt1 sm1,
               (<<STARSRC: Star ms_src st_src1 nil st_src2>>) /\
               (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/
                           <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMemOh.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src2 st_tgt1 sm1>>)>>).

  Let STEPBSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) /\
      (<<STEPBSIM: forall tr st_tgt1
             (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1)
             (SAFESRC: safe_modsem ms_src st_src0),
             exists idx1 st_src1 sm1,
               (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/
                           <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMemOh.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Hypothesis STEPSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t)
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (SOUND: forall si, exists su0 m_init, (sound_states si) su0 m_init st_src0),
      STEPFSIM idx0 st_src0 st_tgt0 sm0 \/ STEPBSIM idx0 st_src0 st_tgt0 sm0.

  Hypothesis INITOH: forall
      sm
      (SIMSKENV: ModSemPair.sim_skenv msp sm)
      (WF: SimMem.wf sm)
    ,
      exists (smo: SimMemOh.t),
        (<<WF: SimMemOh.wf smo>>) /\
        (<<SMEQ: smo.(SimMemOh.sm) = sm>>) /\
        (<<OHSRC: smo.(SimMemOh.oh_src) = upcast msp.(ModSemPair.src).(ModSem.initial_owned_heap)>>) /\
        (<<OHTGT: smo.(SimMemOh.oh_tgt) = upcast msp.(ModSemPair.tgt).(ModSem.initial_owned_heap)>>)
  .

  Hypothesis MIDXNONE: SimMemOh.midx = None -> SMO = SimMemOh_default _.

  Hypothesis BAR: bar_True.

  Lemma match_states_lxsim
        i0 st_src0 st_tgt0 (sm0: SimMemOh.t)
        (SIMSKENV: ModSemPair.sim_skenv msp sm0)
        (* (MWF: SimMemOh.wf sm0) *)
        (* (MCOMPAT: mem_compat st_src0 st_tgt0 sm0) *)
        (MATCH: match_states i0 st_src0 st_tgt0 sm0):
        (* su0 *)
      (* <<LXSIM: lxsim ms_src ms_tgt (sound_state su0) sm_init i0.(to_idx WFORD) st_src0 st_tgt0 sm0>> *)
      <<LXSIM: lxsimL ms_src ms_tgt (fun st => forall si, exists su0 m_init, sound_states si su0 m_init st)
                      has_footprint mle_excl
                      (Ord.lift_idx (wf_lex_ord WFORD lt_wf) (i0, 1%nat)) st_src0 st_tgt0 sm0>>.
  Proof.
    (* move su0 at top. *)
    revert_until BAR. pcofix CIH. i. pfold. ii.
    generalize (classic (ModSem.is_call ms_src st_src0)). intro CALLSRC; des.
    { (* CALL *)
      - (* u in CALLSRC. des. *)
        exploit ATMWF; eauto. i; des. ii. eapply lxsim_at_external; eauto. ii. clear CALLSRC.
        exploit ATFSIM; eauto. { ii. eapply SUSTAR; eauto. eapply star_refl. } i; des.
        (* determ_tac ModSem.at_external_dtm. clear_tac. *)
        esplits; eauto. i. exploit AFTERFSIM; try apply SAFESRC; try apply SIMRET; eauto.
        { ii. eapply SUSTAR. eapply star_refl. }
        { econs; eauto. }
        { eapply SimMemOhLift.unlift_wf; eauto. }
        { eapply SimMemOhLift.lift_spec; eauto. }
        i; des.
        assert(MLE3: SimMemOh.le sm0 sm_after).
        { eapply FOOTEXCL; et. etrans; et. eapply SimMemOhLift.lift_spec; et. }
        spc H0. des. esplits; eauto. { etrans; et. eapply SimMemOhLift.unlift_unch. } right.
        eapply CIH; [..|eauto].
        { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto.
          apply rtc_once. left. eauto using SimMemOh.le_proj.
        }
    }
    generalize (classic (ModSem.is_return ms_src st_src0)). intro RETSRC; des.
    { (* RETURN *)
      u in RETSRC. des. exploit FINALFSIM; eauto. i; des. ii.
      eapply lxsim_final; try apply SIMRET; eauto.
    }
    exploit STEPSIM; eauto. { ii. eapply SUSTAR; eauto. eapply star_refl. } clear STEPSIM. intro STEPSIM.
    destruct STEPSIM as [STEPFSIM0|STEPBSIM0].
    { eapply lxsim_step_forward; eauto. i.
      r in STEPFSIM0. des.
      esplits; eauto. econs 1; eauto. ii. exploit STEPFSIM1; eauto. i; des_safe. esplits; eauto.
      - des.
        + left. eauto.
        + right. esplits; eauto. eapply Ord.lift_idx_spec; eauto. econs 1; eauto.
      - left. pfold. ii. eapply lxsim_step_backward; eauto. ii.
        econs 2; eauto.
        { esplits; eauto. eapply Ord.lift_idx_spec; eauto. econs 2; eauto. }
        { refl. }
        { refl. }
        right. eapply CIH; [..|eauto].
        { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto using SimMemOh.le_proj. }
    }
    { rr in STEPBSIM0.
      eapply lxsim_step_backward; eauto. ii. des.
      econs 1; eauto.
      - ii. exploit STEPBSIM1; eauto. i; des_safe. esplits; eauto.
        + des.
          * left. eauto.
          * right. esplits; eauto. eapply Ord.lift_idx_spec; eauto. econs 1; eauto.
        + right. eapply CIH; [..|eauto].
          { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto using SimMemOh.le_proj. }
      - eapply PROGRESS; eauto.
    }
  Qed.

  Theorem match_states_sim: <<SIM: msp.(ModSemPair.sim)>>.
  Proof.
    eapply sim_mod_sem_implies; et. inv INHAB. econs; eauto.
    { i. eapply local_preservation_noguarantee_weak; eauto. }
    ii; ss. folder.
    exploit SimSymb.sim_skenv_func_bisim; eauto. { apply SIMSKENV. } intro FSIM; des.
    inv FSIM. exploit FUNCFSIM; eauto. { apply SimMem.sim_args_sim_fptr; et. apply SIMARGS. } i; des.
    split; ii.
    - exploit INITBSIM; eauto. i; des.
      esplits; eauto with congruence.
      eapply match_states_lxsim; eauto.
      { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto using SimMemOh.le_proj. }
    - exploit INITPROGRESS; eauto.
  Unshelve.
    all: ss.
  Qed.

End MATCHSIMFORWARD.
