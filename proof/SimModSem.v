Require Import SimMem.
Require Import Simulation.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
Require Import Values Integers.
Require Import Globalenvs.
Require Import Program.
Require Import MemoryC.

Require Import Skeleton SimSymb Ord.
Require Import ModSem.
Require Import Sound Preservation.
Import ModSem.
Require Import ModSemProps.
Require Import Events.
Require Import SmallstepC.
From Paco Require Import hpattern.
Require Import Any.

Set Implicit Arguments.






Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SMO: SimMemOh.class}.
  (* TODO: make SS's argument "SM" implicit; like SMO *)
  Context {SS: SimSymb.class SM}.
  Variable sound_states: ms_src.(state) -> Prop.

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | fsim_step_step
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0)
      (STEP: forall st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1),
          exists i1 st_tgt1 smo1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            /\ <<MLE: SimMemOh.le smo0 smo1>>
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 smo1>>)
      (RECEP: receptive_at ms_src st_src0)
  | fsim_step_stutter
      i1 st_tgt1 smo1
      (PLUS: DPlus ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (MLE: SimMemOh.le smo0 smo1)
      (BSIM: fsim i1 st_src0 st_tgt1 smo1).

  Inductive bsim_step (bsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | bsim_step_step
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1),
          exists i1 st_src1 smo1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ ord i1 i0>>)
            /\ <<MLE: SimMemOh.le smo0 smo1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 smo1>>)
      (PROGRESS: <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)
  | bsim_step_stutter
      i1 st_src1 smo1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (MLE: SimMemOh.le smo0 smo1)
      (BSIM: bsim i1 st_src1 st_tgt0 smo1).


  Inductive _lxsim_pre (lxsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | lxsim_step_forward
      (SU: forall (SU: DUMMY_PROP),
      <<FSTEP: fsim_step lxsim i0 st_src0 st_tgt0 smo0>>)

  | lxsim_step_backward
      (SU: forall (SU: DUMMY_PROP),
      (<<BSTEP: forall
          (SAFESRC: safe_modsem ms_src st_src0),
         (<<BSTEP: bsim_step lxsim i0 st_src0 st_tgt0 smo0>>)>>))

  | lxsim_at_external
      (MWF: SimMemOh.wf smo0)
      (SAFESRC: ms_src.(is_call) st_src0)
      (SU: forall (SU: DUMMY_PROP),
      <<CALLFSIM: forall oh_src0 args_src
          (ATSRC: ms_src.(at_external) st_src0 oh_src0 args_src),
          exists oh_tgt0 args_tgt (smo_arg: SimMemOh.t),
            (<<SIMARGS: SimMemOh.sim_args (upcast oh_src0) (upcast oh_tgt0) args_src args_tgt smo_arg>>
            /\ (<<MWF: SimMemOh.wf smo_arg>>)
            /\ (<<MLE: SimMemOh.lepriv smo0 smo_arg>>)
            /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 oh_tgt0 args_tgt>>)
            /\ (<<K: forall smo_ret oh_src1 retv_src oh_tgt1 retv_tgt st_src1
                (MLE: SimMemOh.le smo_arg smo_ret)
                (MWF: SimMemOh.wf smo_ret)
                (SIMRETV: SimMemOh.sim_retv (upcast oh_src1) (upcast oh_tgt1) retv_src retv_tgt smo_ret)
                (AFTERSRC: ms_src.(after_external) st_src0 oh_src1 retv_src st_src1),
                exists st_tgt1 smo_after i1,
                  (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 oh_tgt1 retv_tgt st_tgt1>>) /\
                  (<<MLEPUB: SimMemOh.le smo0 smo_after>>) /\
                  (<<LXSIM: lxsim i1 st_src1 st_tgt1 smo_after>>)>>))>>)

  | lxsim_final
      smo_ret oh_src oh_tgt retv_src retv_tgt
      (MLE: SimMemOh.le smo0 smo_ret)
      (MWF: SimMemOh.wf smo_ret)
      (FINALSRC: ms_src.(final_frame) st_src0 oh_src retv_src)
      (FINALTGT: ms_tgt.(final_frame) st_tgt0 oh_tgt retv_tgt)
      (SIMRETV: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt smo_ret).


  Definition _lxsim (lxsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
             (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
    (forall (SUSTAR: forall st_src1 tr (STAR: Star ms_src st_src0 tr st_src1), sound_states st_src1),
        <<LXSIM: _lxsim_pre lxsim i0 st_src0 st_tgt0 smo0>>).

  Definition lxsim: _ -> _ -> _ -> _ -> Prop := paco4 _lxsim bot4.

  Lemma lxsim_mon: monotone4 _lxsim.
  Proof.
    repeat intro. rr in IN. hexploit1 IN; eauto. inv IN; eauto.
    - econs 1; ss. ii. spc SU. des. esplits; eauto. inv SU.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss. ii. exploit SU; eauto. i; des.
      inv H.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto. ii; ss. exploit SU; eauto. i; des.
      esplits; eauto. ii. exploit K; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsim.
Hint Resolve lxsim_mon: paco.




Module ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: ModSem.t;
    tgt: ModSem.t;
    ss: SimSymb.t;
    sm: SimMem.t;
    SMO: SimMemOh.class;
  }.

  Inductive sim_skenv (msp: t) (sm0: SimMem.t): Prop :=
  | sim_skenv_intro
    (SIMSKE: SimSymb.sim_skenv sm0 msp.(ss) msp.(src).(ModSem.skenv) msp.(tgt).(ModSem.skenv))
    ss_link
    (SIMSKELINK: SimSymb.sim_skenv sm0 ss_link msp.(src).(ModSem.skenv_link) msp.(tgt).(ModSem.skenv_link)).

  Lemma mfuture_preserves_sim_skenv
        msp sm0 sm1
        (MFUTURE: SimMem.future sm0 sm1)
        (SIMSKENV: sim_skenv msp sm0):
      <<SIMSKENV: sim_skenv msp sm1>>.
  Proof.
    inv SIMSKENV. econs; eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
  Qed.

  Inductive sim (msp: t): Prop :=
  | sim_intro
      sidx sound_states sound_state_ex
      (MIDX: msp.(src).(midx) = msp.(tgt).(midx))
      (PRSV: local_preservation msp.(src) sound_state_ex)
      (PRSVNOGR: forall (si: sidx), local_preservation_noguarantee msp.(src) (sound_states si))
      (INITOH: forall
          sm
          (WF: SimMem.wf sm)
        ,
          exists (smo: SimMemOh.t (class := msp.(SMO))),
            (<<WF: SimMemOh.wf smo>>) /\
            (<<SMEQ: smo.(SimMemOh.sm) = sm>>) /\
            (<<OHSRC: smo.(SimMemOh.oh_src) = upcast msp.(src).(initial_owned_heap)>>) /\
            (<<OHTGT: smo.(SimMemOh.oh_tgt) = upcast msp.(tgt).(initial_owned_heap)>>))
      (SIM: forall
          (sm_arg: SimMemOh.t (class := msp.(SMO))) oh_src oh_tgt args_src args_tgt
          sg_init_src sg_init_tgt
          (FINDFSRC: (Genv.find_funct msp.(src).(ModSem.skenv)) (Args.get_fptr args_src) =
                     Some (Internal sg_init_src))
          (FINDFTGT: (Genv.find_funct msp.(tgt).(ModSem.skenv)) (Args.get_fptr args_tgt) =
                     Some (Internal sg_init_tgt))
          (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg)
          (SIMSKENV: sim_skenv msp sm_arg)
          (MFUTURE: SimMem.future msp.(sm) sm_arg)
          (MWF: SimMemOh.wf sm_arg),
          (<<INITBSIM: forall st_init_tgt
              (INITTGT: msp.(tgt).(initial_frame) oh_tgt args_tgt st_init_tgt)
              (SAFESRC: exists _st_init_src, msp.(src).(initial_frame) oh_src args_src _st_init_src),
              exists st_init_src sm_init idx_init,
                (<<MLE: SimMemOh.le sm_arg sm_init>>) /\
                (<<INITSRC: msp.(src).(initial_frame) oh_src args_src st_init_src>>) /\
                (<<SIM: lxsim msp.(src) msp.(tgt) (fun st => forall si, exists su m_init, sound_states si su m_init st)
                                                  idx_init st_init_src st_init_tgt sm_init>>)>>) /\
          (<<INITPROGRESS: forall
              (SAFESRC: exists st_init_src, msp.(src).(initial_frame) oh_src args_src st_init_src),
              exists st_init_tgt, (<<INITTGT: msp.(tgt).(initial_frame) oh_tgt args_tgt st_init_tgt>>)>>))
  .

End MODSEMPAIR.
End ModSemPair.

Arguments ModSemPair.mk [SM] [SS] _ _ _.
Hint Constructors ModSemPair.sim_skenv.






Section FACTORTARGET.

  Variable ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.
  Context {SMO: SimMemOh.class}.
  Variable ss: SimSymb.t.
  Variable sm: SimMem.t.
  Hypothesis SINGLE: single_events ms_src.
  Hypothesis WBT: well_behaved_traces ms_tgt.

  Section LXSIM.

    Variable sound_states: state ms_src -> Prop.

    Inductive fbs_match: idx -> state ms_src -> (trace * state ms_tgt) -> SimMemOh.t -> Prop :=
    | fbs_match_intro
        idx0 st_src0 tr st_src1 st_tgt0 sm0
        (STAR: (st_src0 = st_src1 /\ tr = E0) \/ ((Plus ms_src st_src0 tr st_src1) /\ output_trace tr /\ tr <> []))
        (MATCH: lxsim ms_src ms_tgt sound_states idx0 st_src1 st_tgt0 sm0):
        fbs_match idx0 st_src0 (tr, st_tgt0) sm0.

    Lemma factor_lxsim_target: forall idx0 st_src0 tr st_tgt0 sm0
        (SIM: fbs_match idx0 st_src0 (tr, st_tgt0) sm0),
        <<SIM: lxsim ms_src (Atomic.trans ms_tgt) sound_states idx0 st_src0 (tr, st_tgt0) sm0>>.
    Proof.
      clear_tac. unfold NW. pcofix CIH.
      i. pfold. inv SIM. punfold MATCH. des; clarify; cycle 1.
      { rename st_src2 into st_src1. econs 2; eauto. ii. econs 1; ii.
        - (* bsim *)
          econs; eauto.
          exploit star_non_E0_split'_strong; eauto.
          { apply plus_star; eauto. }
          intro P; des. des_ifs. des_safe. i. inv STEPTGT. esplits; eauto.
          { refl. }
          pclearbot. right. eapply CIH; eauto. econs; eauto. ss. des; ss.
          { right. esplits; eauto. }
          { left. clarify. }
        - (* progress *)
          destruct tr; ss. ii. esplits; eauto. econs; eauto.
      }
      ii. rr in MATCH. hexploit1 MATCH.
      { ii. eapply SUSTAR; et. }
      inv MATCH.
      - econs 1. i. exploit SU; eauto. i; des_safe. esplits; eauto.
        clear - SINGLE WBT CIH H. inv H.
        + econs 1; eauto. i. exploit STEP; eauto. i; des_safe. esplits; eauto.
          { des.
            - left. exploit dplus_atomic_dplus; eauto.
            - right. esplits; eauto. exploit dstar_atomic_dstar; eauto.
          }
          pclearbot. right. eapply CIH; eauto. econs; eauto.
        + econs 2; eauto.
          { des. esplits; eauto. exploit dplus_atomic_dplus; eauto. }
          pclearbot. right. eapply CIH; eauto. econs; eauto.
      - econs 2. ii. exploit SU; eauto. i; des. inv H; ii.
        + (* bsim *)
          econs 1; eauto; cycle 1.
          { (* progress *)
            des. destruct tr.
            * esplits; eauto. instantiate (1:= (_, _)). econs 1; eauto.
            * esplits; eauto. instantiate (1:= (_, _)). econs 2; eauto.
          }
          clear - SINGLE WBT CIH STEP.
          * i. destruct tr; ss.
            { inv STEPTGT.
              exploit STEP; eauto. i; des_safe. esplits; eauto.
              pclearbot. right. eapply CIH; eauto. econs; eauto.
            }
            inv STEPTGT. destruct tr0; ss.
            { exploit STEP; eauto. i; des_safe. esplits; eauto.
              pclearbot. right. eapply CIH; eauto. econs; eauto.
            }
            exploit WBT; eauto. intro WBT0. ss.
            exploit STEP; eauto. i; des_safe. des.
            -- exploit star_non_E0_split'; eauto.
               { apply plus_star; eauto. }
               intro P. ss. des. esplits; eauto.
               pclearbot. right. eapply CIH; eauto. econs.
               { right. esplits; eauto; ss. eapply star_inv in P0. des; clarify; ss. eauto. }
               eauto.
            -- exploit star_non_E0_split'; eauto. intro P. ss. des. esplits; eauto.
               pclearbot. right. eapply CIH; eauto. econs.
               { right. esplits; eauto; ss. eapply star_inv in P0. des; clarify; ss. eauto. }
               eauto.
        + econs 2; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
      - econs 3; eauto. ii. exploit SU; eauto. i; des. esplits; eauto.
        { rr. ss. }
        i. exploit K; eauto. i; des. eexists (_, _). esplits; eauto.
        { rr. ss. esplits; eauto. }
        pclearbot. right. eapply CIH; eauto. econs; eauto.
      - econs 4; eauto. rr. esplits; eauto.
    Qed.

  End LXSIM.

  Theorem factor_simmodsem_target
          (SIM: ModSemPair.sim (ModSemPair.mk ms_src ms_tgt ss sm SMO)):
      ModSemPair.sim (ModSemPair.mk ms_src (ModSem.Atomic.trans ms_tgt) ss sm SMO).
  Proof.
    inv SIM. ss. econs; eauto. ss. i. exploit SIM0; eauto.
    { inv SIMSKENV. ss. econs; eauto. }
    i; des. split; ss.
    - ii. rr in INITTGT. des. destruct st_init_tgt; ss. clarify. exploit INITBSIM; eauto. i; des.
      esplits; eauto. eapply factor_lxsim_target; eauto. econs; eauto.
    - ii. des. exploit INITPROGRESS; eauto. i ;des. eexists (_, _). esplits; eauto. rr. ss. econs; eauto.
  Qed.

End FACTORTARGET.


