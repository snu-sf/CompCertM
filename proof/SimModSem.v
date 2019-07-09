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

Set Implicit Arguments.


Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable sound_states: ms_src.(state) -> Prop.

  (* Record mem_compat (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop := { *)
  (*   mcompat_src: <<MCOMPATSRC: ms_src.(get_mem) st_src0 = sm0.(SimMem.src)>>; *)
  (*   mcompat_tgt: <<MCOMPATTGT: ms_tgt.(get_mem) st_tgt0 = sm0.(SimMem.tgt)>>; *)
  (* } *)
  (* . *)

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | fsim_step_step
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0)
      (STEP: forall
          st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1)
        ,
          exists i1 st_tgt1 sm1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            (* /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>> *)
            /\ <<MLE: SimMem.le sm0 sm1>>
(* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 sm1>>)
      (RECEP: receptive_at ms_src st_src0)
  | fsim_step_stutter
      i1 st_tgt1 sm1
      (PLUS: DPlus ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (MLE: SimMem.le sm0 sm1)
      (BSIM: fsim i1 st_src0 st_tgt1 sm1)
  .

  Inductive bsim_step (bsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | bsim_step_step
      (STEP: forall
          st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1)
        ,
          exists i1 st_src1 sm1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ ord i1 i0>>)
            (* /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>> *)
            /\ <<MLE: SimMem.le sm0 sm1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 sm1>>)
  | bsim_step_stutter
      i1 st_src1 sm1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (MLE: SimMem.le sm0 sm1)
      (BSIM: bsim i1 st_src1 st_tgt0 sm1)
  .

  Print xsim.

  Inductive _lxsim_pre (lxsim: SimMem.t ->
                               idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (sm_init: SimMem.t)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | lxsim_step_forward
      (SU: forall (SU: DUMMY_PROP),
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (* (SAFESRC: ms_src.(ModSem.is_step) st_src0) *)
      <<FSTEP: fsim_step (lxsim sm_init) i0 st_src0 st_tgt0 sm0>>
      (* Note: We used coercion on determinate_at. See final_state, which is bot2. *)
      (* sd_determ_at_final becomes nothing, but it is OK. *)
      (* In composed semantics, when it stepped, it must not be final *))

  | lxsim_step_backward
      (SU: forall (SU: DUMMY_PROP),
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (<<BSTEP:
         forall
          (SAFESRC: safe_modsem ms_src st_src0)
        ,
         (<<BSTEP: bsim_step (lxsim sm_init) i0 st_src0 st_tgt0 sm0>>)>>) /\
      (<<PROGRESS:
         forall
           (* (STEPSRC: ms_src.(ModSem.is_step) st_src0) *)
           (STEPSRC: safe_modsem ms_src st_src0)
         ,
           (<<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)>>))

  (* | lxsim_at_external *)
  (*     rs_arg_src rs_arg_tgt *)
  (*     (MCOMPAT: mem_compat st_src0 st_tgt0 sm0) *)
  (*     m_arg_src m_arg_tgt *)
  (*     (ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src) *)
  (*     (ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt) *)
  (*     (RSREL: sm0.(SimMem.sim_regset) rs_arg_src rs_arg_tgt) *)
  (*     (VALID: SimMem.wf sm0) *)
  (*     (AFTER: forall *)
  (*         sm1 rs_ret_src rs_ret_tgt *)
  (*         (MLE: SimMem.le (SimMem.lift sm0) sm1) *)
  (*         (VALID: SimMem.wf sm1) *)
  (*         (RETVREL: sm1.(SimMem.sim_regset) rs_ret_src rs_ret_tgt) *)
  (*         st_tgt1 *)
  (*         (AFTERTGT: ms_tgt.(after_external) st_tgt0 rs_arg_tgt rs_ret_tgt sm1.(SimMem.tgt) *)
  (*                                                                                st_tgt1) *)
  (*       , *)
  (*         exists i1 st_src1, *)
  (*         (<<AFTERSRC: ms_src.(after_external) st_src0 rs_arg_src rs_ret_src sm1.(SimMem.src) *)
  (*                                                                                  st_src1>>) *)
  (*         /\ *)
  (*         (<<LXSIM: lxsim i1 st_src1 st_tgt1 (SimMem.unlift sm0 sm1)>>)) *)

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
      <<CALLFSIM: forall
          args_src
          (ATSRC: ms_src.(at_external) st_src0 args_src)
        ,
          exists args_tgt sm_arg,
            (<<SIMARGS: SimMem.sim_args args_src args_tgt sm_arg>>
            /\ (<<MWF: SimMem.wf sm_arg>>)
            /\ (<<MLE: SimMem.lepriv sm0 sm_arg>>)
            /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 args_tgt>>)
            /\
            (<<K: forall
                sm_ret retv_src retv_tgt
                (MLE: SimMem.le sm_arg sm_ret)
                (MWF: SimMem.wf sm_ret)
                (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret)
                st_src1
                (AFTERSRC: ms_src.(after_external) st_src0 retv_src st_src1)
              ,
                exists st_tgt1 sm_after i1,
                  (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 retv_tgt st_tgt1>>)
                  /\
                  (* (<<MLEPRIV: SimMem.lepriv sm_ret sm_after>>) *)
                  (* /\ *)
                  (<<MLEPUB: SimMem.le sm0 sm_after>>)
                  /\
                  (<<LXSIM: lxsim sm_init i1 st_src1 st_tgt1 sm_after>>)>>)
                  )>>)

  | lxsim_final
      sm_ret
      (MLE: SimMem.le sm_init sm_ret)
      (MWF: SimMem.wf sm_ret)
      (* (PROGRESS: ms_tgt.(is_return) rs_init_tgt st_tgt0) *)
      (* (RETBSIM: forall           *)
      (*     rs_ret_tgt m_ret_tgt *)
      (*     (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)
      (*   , *)
      (*     exists rs_ret_src m_ret_src, *)
      (*       (<<RSREL: sm0.(SimMem.sim_regset) rs_ret_src rs_ret_tgt>>) *)
      (*       /\ (<<FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src>>)) *)
      retv_src retv_tgt
      (FINALSRC: ms_src.(final_frame) st_src0 retv_src)
      (FINALTGT: ms_tgt.(final_frame) st_tgt0 retv_tgt)
      (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret)

      (* Note: Actually, final_frame can be defined as a function. *)

      (* (FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src) *)
      (* (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)

  .

  Definition _lxsim (lxsim: SimMem.t -> idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop) (sm_init: SimMem.t)
             (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
    (forall (SUSTAR: forall st_src1 tr (STAR: Star ms_src st_src0 tr st_src1), sound_states st_src1),
        <<LXSIM: _lxsim_pre lxsim sm_init i0 st_src0 st_tgt0 sm0>>)
  .

  Definition lxsim: _ -> _ -> _ -> _ -> _ -> Prop := paco5 _lxsim bot5.

  Lemma lxsim_mon:
    monotone5 _lxsim.
  Proof.
    repeat intro. rr in IN. hexploit1 IN; eauto. inv IN; eauto.
    - econs 1; ss.
      ii. spc SU. des. esplits; eauto.
      inv SU.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss.
      i. (* specialize (BSTEP SAFESRC0). *)
      exploit SU; eauto. i; des.
      esplits; eauto.
      ii. hexploit BSTEP; eauto. i.
      inv H.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto.
      ii; ss. exploit SU; eauto. i; des.
      esplits; eauto. ii.
      exploit K; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsim.
Hint Resolve lxsim_mon: paco.

Print HintDb typeclass_instances.



Module ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: ModSem.t;
    tgt: ModSem.t;
    ss: SimSymb.t;
    sm: SimMem.t;
  }
  .

  Inductive sim_skenv (msp: t) (sm0: SimMem.t): Prop :=
  | sim_skenv_intro
    (SIMSKE: SimSymb.sim_skenv sm0 msp.(ss) msp.(src).(ModSem.skenv) msp.(tgt).(ModSem.skenv))
    ss_link
    (SIMSKELINK: SimSymb.sim_skenv sm0 ss_link msp.(src).(ModSem.skenv_link) msp.(tgt).(ModSem.skenv_link))
  .

  Lemma mfuture_preserves_sim_skenv
        msp sm0 sm1
        (MFUTURE: SimMem.future sm0 sm1)
        (SIMSKENV: sim_skenv msp sm0)
    :
      <<SIMSKENV: sim_skenv msp sm1>>
  .
  Proof.
    inv SIMSKENV.
    econs.
    - eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
    - eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
  Qed.

  Inductive sim (msp: t): Prop :=
  | sim_intro
      (* (SIMSKENV: sim_skenv msp msp.(sm)) *)
      sidx
      sound_states
      sound_state_ex
      (PRSV: local_preservation msp.(src) sound_state_ex)
      (PRSVNOGR: forall (si: sidx), local_preservation_noguarantee msp.(src) (sound_states si))
      (SIM: forall
          sm_arg
          args_src args_tgt
          sg_init_src sg_init_tgt
          (FINDFSRC: msp.(src).(ModSem.skenv).(Genv.find_funct) args_src.(Args.get_fptr) =
                     Some (Internal sg_init_src))
          (FINDFTGT: msp.(tgt).(ModSem.skenv).(Genv.find_funct) args_tgt.(Args.get_fptr) =
                     Some (Internal sg_init_tgt))
          (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
          (SIMSKENV: sim_skenv msp sm_arg)
          (MFUTURE: SimMem.future msp.(sm) sm_arg)
          (MWF: SimMem.wf sm_arg)
        ,
          (<<INITBSIM: forall
              st_init_tgt
              (INITTGT: msp.(tgt).(initial_frame) args_tgt st_init_tgt)
              (SAFESRC: exists _st_init_src, msp.(src).(initial_frame) args_src _st_init_src)
            ,
              exists st_init_src sm_init idx_init,
                (<<MLE: SimMem.le sm_arg sm_init>>) /\
                (<<INITSRC: msp.(src).(initial_frame) args_src st_init_src>>) /\
                (<<SIM: lxsim msp.(src) msp.(tgt) (fun st => forall si, exists su m_init, sound_states si su m_init st)
                                                  sm_arg idx_init st_init_src st_init_tgt sm_init>>)>>)
          /\
          (<<INITPROGRESS: forall
              (SAFESRC: exists st_init_src, msp.(src).(initial_frame) args_src st_init_src)
            ,
              exists st_init_tgt,
                (<<INITTGT: msp.(tgt).(initial_frame) args_tgt st_init_tgt>>)>>))
  .

End MODSEMPAIR.
End ModSemPair.

Hint Constructors ModSemPair.sim_skenv.






Section FACTORTARGET.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.
  Variable ms_src ms_tgt: ModSem.t.
  Variable ss: SimSymb.t.
  Variable sm: SimMem.t.
  Hypothesis SINGLE: single_events ms_src.
  Hypothesis WBT: well_behaved_traces ms_tgt.

  Section LXSIM.

    Variable sound_states: state ms_src -> Prop.
    Variable sm_arg: SimMem.t.

    Inductive fbs_match: idx -> state ms_src -> (trace * state ms_tgt) -> SimMem.t -> Prop :=
    | fbs_match_intro
        idx0 st_src0 tr st_src1 st_tgt0 sm0
        (STAR: (st_src0 = st_src1 /\ tr = E0) \/ ((Plus ms_src st_src0 tr st_src1) /\ output_trace tr /\ tr <> []))
        (MATCH: lxsim ms_src ms_tgt sound_states sm_arg idx0 st_src1 st_tgt0 sm0)
      :
        fbs_match idx0 st_src0 (tr, st_tgt0) sm0
    .

    Lemma factor_lxsim_target: forall
        idx0 st_src0 tr st_tgt0 sm0
        (SIM: fbs_match idx0 st_src0 (tr, st_tgt0) sm0)
      ,
        <<SIM: lxsim ms_src (Atomic.trans ms_tgt) sound_states sm_arg idx0 st_src0 (tr, st_tgt0) sm0>>
    .
    Proof.
      clear_tac. unfold NW.
      pcofix CIH.
      i. pfold. inv SIM. punfold MATCH.
      des; clarify; cycle 1.
      {
        rename st_src2 into st_src1.
        econs 2; eauto.
        i.
        split; i.
        - (* bsim *)
          econs; eauto.
          exploit star_non_E0_split'_strong; eauto.
          { apply plus_star; eauto. }
          intro P; des. des_ifs. des_safe.
          i. inv STEPTGT.
          esplits; eauto.
          { refl. }
          pclearbot. right. eapply CIH; eauto.
          econs; eauto.
          ss. des; ss.
          { right. esplits; eauto. }
          { left. clarify. }
        - (* progress *)
          destruct tr; ss.
          ii. esplits; eauto. econs; eauto.
      }
      ii. rr in MATCH. hexploit1 MATCH.
      { ii. eapply SUSTAR; et. }
      inv MATCH.
      - econs 1.
        i. exploit SU; eauto. i; des_safe. esplits; eauto.
        clear - SINGLE WBT CIH H. inv H.
        + econs 1; eauto. i. exploit STEP; eauto. i; des_safe. esplits; eauto.
          { des.
            - left. exploit dplus_atomic_dplus; eauto.
            - right. esplits; eauto. exploit dstar_atomic_dstar; eauto.
          }
          pclearbot. right. eapply CIH; eauto.
          econs; eauto.
        + econs 2; eauto.
          { des.
            - esplits; eauto. exploit dplus_atomic_dplus; eauto.
          }
          pclearbot. right. eapply CIH; eauto.
          econs; eauto.
      - econs 2.
        i. exploit SU; eauto. i; des. esplits; eauto.
        + (* bsim *)
          clear - SINGLE WBT CIH BSTEP. i. hexploit1 BSTEP; eauto. inv BSTEP.
          * econs 1; eauto. i.
            destruct tr; ss.
            {
              inv STEPTGT.
              exploit STEP; eauto. i; des_safe. esplits; eauto.
              pclearbot. right. eapply CIH; eauto.
              econs; eauto.
            }
            inv STEPTGT.
            destruct tr0; ss.
            {
              exploit STEP; eauto. i; des_safe. esplits; eauto.
              pclearbot. right. eapply CIH; eauto.
              econs; eauto.
            }
            exploit WBT; eauto. intro WBT0. ss.
            exploit STEP; eauto. i; des_safe.
            des.
            -- exploit star_non_E0_split'; eauto.
               { apply plus_star; eauto. }
               intro P. ss. des. esplits; eauto.
               pclearbot. right. eapply CIH; eauto.
               econs.
               { right. esplits; eauto; ss. eapply star_inv in P0. des; clarify; ss. eauto. }
               eauto.
            -- exploit star_non_E0_split'; eauto.
               intro P. ss. des. esplits; eauto.
               pclearbot. right. eapply CIH; eauto.
               econs.
               { right. esplits; eauto; ss. eapply star_inv in P0. des; clarify; ss. eauto. }
               eauto.
          * econs 2; eauto.
            pclearbot. right. eapply CIH; eauto.
            econs; eauto.
        + (* progress *)
          i. exploit PROGRESS; eauto.
          i; des. destruct tr.
          * esplits; eauto. instantiate (1:= (_, _)). econs 1; eauto.
          * esplits; eauto. instantiate (1:= (_, _)). econs 2; eauto.
      - econs 3; eauto.
        ii. exploit SU; eauto. i; des.
        esplits; eauto.
        { rr. ss. }
        i. exploit K; eauto. i; des. eexists (_, _). esplits; eauto.
        { rr. ss. esplits; eauto. }
        pclearbot. right. eapply CIH; eauto.
        econs; eauto.
      - econs 4; eauto.
        rr. esplits; eauto.
    Qed.

  End LXSIM.

  Theorem factor_simmodsem_target
          (SIM: ModSemPair.sim (ModSemPair.mk ms_src ms_tgt ss sm))
    :
      ModSemPair.sim (ModSemPair.mk ms_src ms_tgt.(ModSem.Atomic.trans) ss sm)
  .
  Proof.
    inv SIM. ss.
    econs; eauto. ss.
    i. exploit SIM0; eauto.
    { inv SIMSKENV. ss. econs; eauto. }
    i; des.
    split; ss.
    - ii. rr in INITTGT. des. destruct st_init_tgt; ss. clarify. exploit INITBSIM; eauto. i; des.
      esplits; eauto.
      eapply factor_lxsim_target; eauto.
      econs; eauto.
    - ii. des. exploit INITPROGRESS; eauto. i ;des. eexists (_, _). esplits; eauto. rr. ss. econs; eauto.
  Qed.

End FACTORTARGET.
