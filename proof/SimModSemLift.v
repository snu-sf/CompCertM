Require Import SimMem SimMemLift.
Require Import Simulation.
From compcertr Require Import AST.
From Paco Require Import paco.
From compcertr Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
From compcertr Require Import Values Integers.
From compcertr Require Import Globalenvs.
Require Import Program.
Require Import MemoryC.

Require Import Skeleton SimSymb Ord.
Require Import ModSem.
Require Import Sound Preservation.
Import ModSem.
Require Import ModSemProps.
From compcertr Require Import Events.
Require Import SmallstepC.
Require Import SimModSem.


Set Implicit Arguments.


Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context {SMLIFT: SimMemLift.class SM}.
  Variable sound_states: ms_src.(state) -> Prop.

  Variable has_footprint: forall
      (st_init_src: ms_src.(ModSem.state)) (st_init_tgt: ms_tgt.(ModSem.state)) (sm0: SimMem.t),
      Prop.

  Variable mle_excl: forall
      (st_init_src: ms_src.(ModSem.state)) (st_init_tgt: ms_tgt.(ModSem.state)) (sm0: SimMem.t) (sm1: SimMem.t),
      Prop.

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | fsim_step_step
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0)
      (STEP: forall st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1),
          exists i1 st_tgt1 sm1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            /\ <<MLE: SimMem.le sm0 sm1>>
(* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 sm1>>)
      (RECEP: receptive_at ms_src st_src0)
  | fsim_step_stutter
      i1 st_tgt1 sm1
      (PLUS: DPlus ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (MLE: SimMem.le sm0 sm1)
      (BSIM: fsim i1 st_src0 st_tgt1 sm1).

  Inductive bsim_step (bsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | bsim_step_step
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1),
          exists i1 st_src1 sm1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ ord i1 i0>>)
            /\ <<MLE: SimMem.le sm0 sm1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 sm1>>)
      (PROGRESS: <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)
  | bsim_step_stutter
      i1 st_src1 sm1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (MLE: SimMem.le sm0 sm1)
      (BSIM: bsim i1 st_src1 st_tgt0 sm1).

  Inductive _lxsim_pre (lxsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | lxsim_step_forward
      (SU: forall (SU: DUMMY_PROP),
      <<FSTEP: fsim_step lxsim i0 st_src0 st_tgt0 sm0>>
      (* Note: We used coercion on determinate_at. See final_state, which is bot2. *)
      (* sd_determ_at_final becomes nothing, but it is OK. *)
      (* In composed semantics, when it stepped, it must not be final *))

  | lxsim_step_backward
      (SU: forall (SU: DUMMY_PROP),
      (<<BSTEP:
         forall (SAFESRC: safe_modsem ms_src st_src0) ,
         (<<BSTEP: bsim_step lxsim i0 st_src0 st_tgt0 sm0>>)>>))

  | lxsim_at_external
      (* (MCOMPAT: mem_compat st_src0 st_tgt0 sm0) *)
      (MWF: SimMem.wf sm0)
      (* (CALLPROGRESS: forall *)
      (*     rs_arg_src m_arg_src *)
      (*     (ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src) *)
      (*   , *)
      (*     exists rs_arg_tgt m_arg_tgt, <<ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt>>) *)
      (* (SAFESRC: exists rs_arg_src m_arg_src, <<ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src>>) *)
      (* (SAFESRC: ms_tgt.(is_call) st_tgt0) *)
      (SAFESRC: ms_src.(is_call) st_src0)
      (* (PROGSRC: ms_src.(is_call) st_src0) *)
      (SU: forall (SU: DUMMY_PROP),
      <<CALLFSIM: forall args_src
          (ATSRC: ms_src.(at_external) st_src0 args_src),
          exists args_tgt sm_arg,
            (<<SIMARGS: SimMem.sim_args args_src args_tgt sm_arg>>
            /\ (<<MWF: SimMem.wf sm_arg>>)
            /\ (<<MLE: SimMem.le sm0 sm_arg>>)
            /\ (<<FOOT: has_footprint st_src0 st_tgt0 sm0>>)
            /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 args_tgt>>)
            /\ (<<K: forall sm_ret retv_src retv_tgt st_src1
                (MLE: SimMem.le (SimMemLift.lift sm_arg) sm_ret)
                (MWF: SimMem.wf sm_ret)
                (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret)
                (AFTERSRC: ms_src.(after_external) st_src0 retv_src st_src1),
                exists st_tgt1 sm_after i1,
                  (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 retv_tgt st_tgt1>>) /\
                  (* (<<MLE: SimMem.le sm0 sm_after>>) /\ *)
                  (<<MLE: mle_excl st_src0 st_tgt0 (SimMemLift.unlift sm_arg sm_ret) sm_after>>) /\
                  (<<LXSIM: lxsim i1 st_src1 st_tgt1 sm_after>>)>>))>>)

  | lxsim_final
      sm_ret retv_src retv_tgt
      (MLE: SimMem.le sm0 sm_ret)
      (MWF: SimMem.wf sm_ret)
      (* (PROGRESS: ms_tgt.(is_return) rs_init_tgt st_tgt0) *)
      (* (RETBSIM: forall           *)
      (*     rs_ret_tgt m_ret_tgt *)
      (*     (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)
      (*   , *)
      (*     exists rs_ret_src m_ret_src, *)
      (*       (<<RSREL: sm0.(SimMem.sim_regset) rs_ret_src rs_ret_tgt>>) *)
      (*       /\ (<<FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src>>)) *)
      (FINALSRC: ms_src.(final_frame) st_src0 retv_src)
      (FINALTGT: ms_tgt.(final_frame) st_tgt0 retv_tgt)
      (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret).

      (* Note: Actually, final_frame can be defined as a function. *)

      (* (FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src) *)
      (* (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)


  Definition _lxsim (lxsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
             (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
    (forall (SUSTAR: forall st_src1 tr (STAR: Star ms_src st_src0 tr st_src1), sound_states st_src1),
        <<LXSIM: _lxsim_pre lxsim i0 st_src0 st_tgt0 sm0>>).

  Definition lxsimL: _ -> _ -> _ -> _ -> Prop := paco4 _lxsim bot4.

  Lemma lxsim_mon: monotone4 _lxsim.
  Proof.
    repeat intro. rr in IN. hexploit1 IN; eauto. inv IN; eauto.
    - econs 1; ss. ii. spc SU. des. esplits; eauto. inv SU.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss. ii. exploit SU; eauto. i; des. inv H.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto. ii; ss. exploit SU; eauto. i; des.
      esplits; eauto. ii. exploit K; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsimL.
Hint Resolve lxsim_mon: paco.


Module ModSemPair.
Include SimModSem.ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.
Context {SMLIFT: SimMemLift.class SM}.

  Inductive simL (msp: ModSemPair.t): Prop :=
  | simL_intro
      (* (SIMSKENV: sim_skenv msp msp.(sm)) *)
      sidx sound_states sound_state_ex
      (PRSV: local_preservation msp.(ModSemPair.src) sound_state_ex)
      (PRSVNOGR: forall (si: sidx), local_preservation_noguarantee msp.(ModSemPair.src) (sound_states si))

      (has_footprint: msp.(ModSemPair.src).(ModSem.state) -> msp.(ModSemPair.tgt).(ModSem.state) -> SimMem.t -> Prop)
      (mle_excl: msp.(ModSemPair.src).(ModSem.state) -> msp.(ModSemPair.tgt).(ModSem.state) -> SimMem.t -> SimMem.t -> Prop)
      (FOOTEXCL: forall st_at_src st_at_tgt sm0 sm1 sm2
          (MWF: SimMem.wf sm0)
          (FOOT: has_footprint st_at_src st_at_tgt sm0)
          (MLEEXCL: (mle_excl st_at_src st_at_tgt) sm1 sm2)
          (MLE: SimMem.le sm0 sm1),
          <<MLE: SimMem.le sm0 sm2>>)
      (EXCLPRIV: forall st_init_src st_init_tgt sm0 sm1 (MWF: SimMem.wf sm0),
          mle_excl st_init_src st_init_tgt sm0 sm1 -> SimMem.lepriv sm0 sm1)
      (SIM: forall
          sm_arg args_src args_tgt
          sg_init_src sg_init_tgt
          (FINDFSRC: (Genv.find_funct msp.(ModSemPair.src).(ModSem.skenv)) (Args.get_fptr args_src) =
                     Some (Internal sg_init_src))
          (FINDFTGT: (Genv.find_funct msp.(ModSemPair.tgt).(ModSem.skenv)) (Args.get_fptr args_tgt) =
                     Some (Internal sg_init_tgt))
          (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
          (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
          (MFUTURE: SimMem.future msp.(ModSemPair.sm) sm_arg)
          (MWF: SimMem.wf sm_arg),
          (<<INITBSIM: forall st_init_tgt
              (INITTGT: msp.(ModSemPair.tgt).(initial_frame) args_tgt st_init_tgt)
              (SAFESRC: exists _st_init_src, msp.(ModSemPair.src).(initial_frame) args_src _st_init_src),
              exists st_init_src sm_init idx_init,
                (<<MLE: SimMem.le sm_arg sm_init>>) /\
                (<<INITSRC: msp.(ModSemPair.src).(initial_frame) args_src st_init_src>>) /\
                (<<SIM: lxsimL msp.(ModSemPair.src) msp.(ModSemPair.tgt)
                          (fun st => forall si, exists su m_init, sound_states si su m_init st)
                          has_footprint mle_excl idx_init st_init_src st_init_tgt sm_init>>)>>) /\
          (<<INITPROGRESS: forall
              (SAFESRC: exists st_init_src, msp.(ModSemPair.src).(initial_frame) args_src st_init_src),
              exists st_init_tgt, (<<INITTGT: msp.(ModSemPair.tgt).(initial_frame) args_tgt st_init_tgt>>)>>)).

End MODSEMPAIR.
End ModSemPair.

Hint Constructors ModSemPair.sim_skenv.





Section IMPLIES.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.
  Context {SMLIFT: SimMemLift.class SM}.

  Lemma lxsim_lxsim
        ms_src ms_tgt sound_state idx_init st_init_src st_init_tgt sm_init
        (has_footprint: ms_src.(ModSem.state) -> ms_tgt.(ModSem.state) -> SimMem.t -> Prop)
        (mle_excl: ms_src.(ModSem.state) -> ms_tgt.(ModSem.state) -> SimMem.t -> SimMem.t -> Prop)
        (FOOTEXCL: forall st_at_src st_at_tgt sm0 sm1 sm2
            (MWF: SimMem.wf sm0)
            (FOOT: has_footprint st_at_src st_at_tgt sm0)
            (MLEEXCL: (mle_excl st_at_src st_at_tgt) sm1 sm2)
            (MLE: SimMem.le sm0 sm1),
            <<MLE: SimMem.le sm0 sm2>>)
        (EXCLPRIV: forall st_init_src st_init_tgt sm0 sm1 (MWF: SimMem.wf sm0),
            mle_excl st_init_src st_init_tgt sm0 sm1 -> SimMem.lepriv sm0 sm1)
        (SIM: lxsimL ms_src ms_tgt sound_state has_footprint mle_excl idx_init st_init_src st_init_tgt sm_init):
      <<SIM: SimModSem.lxsim ms_src ms_tgt sound_state idx_init st_init_src st_init_tgt sm_init>>.
  Proof.
    move has_footprint at top. move mle_excl at top. move FOOTEXCL at top.
    revert_until sound_state. pcofix CIH. i. pfold.
    punfold SIM. rr in SIM. ii. exploit SIM; eauto. intro T. inv T.
    - econs 1; eauto. i. hexploit1 SU0; ss. inv SU0.
      + econs 1; eauto. i. exploit STEP; eauto. i; des_safe. esplits; et. right. pclearbot. eapply CIH; et.
      + pclearbot. econs 2; eauto.
    - econs 2; eauto. i. hexploit1 SU0; ss. des. esplits; eauto. i. hexploit SU0; ss. intro T. inv T.
      + econs 1; eauto. i. exploit STEP; eauto. i; des_safe. esplits; et. right. pclearbot. eapply CIH; et.
      + pclearbot. econs 2; eauto.
    - econs 3; et.
      ii. exploit SU0; et. i; des.
      eexists. exists (SimMemLift.lift sm_arg).
      esplits; eauto.
      { eapply SimMemLift.lift_args; et. }
      { eapply SimMemLift.lift_wf; et. }
      { eapply SimMemLift.le_lift_lepriv; et. }
      i; des.
      exploit K; eauto. i; des. pclearbot.
      eexists _, sm_after.
      esplits; eauto.
      { eapply FOOTEXCL; et. etrans; et. eapply SimMemLift.lift_spec; et. }
      { etrans.
        - eapply SimMemLift.unlift_priv with (sm_at := sm_arg); eauto.
          eapply SimMemLift.lift_priv; eauto.
        - eapply EXCLPRIV; eauto. eapply SimMemLift.unlift_wf; eauto.
      }
    - econs 4; et.
  Qed.

  Theorem sim_mod_sem_implies
          msp
          (SIMMS: ModSemPair.simL msp):
      <<SIMMS: SimModSem.ModSemPair.sim msp>>.
  Proof.
    inv SIMMS. econs; eauto.
    i. exploit SIM; eauto. i; des. esplits; eauto.
    i. exploit INITBSIM; eauto. i; des.
    esplits; eauto. eapply lxsim_lxsim; et.
  Qed.

End IMPLIES.
