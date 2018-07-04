Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import SimModSem SimMem SimSymb.

Set Implicit Arguments.


Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM}.

  Variable msp: ModSemPair.t.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).
  Let mem_compat (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMem.t): Prop :=
    mem_compat ms_src ms_tgt st_src0 st_tgt0 sm0
  .

  Variable match_states: forall
    (rs_arg_src rs_arg_tgt: regset) (sm_arg: SimMem.t)
    (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMem.t)
    ,
      Prop
  .

  Hypothesis INITFSIM: forall
      sm_arg
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      rs_arg_src rs_arg_tgt
      (SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt)
      st_init_src
      (INITSRC: ms_src.(ModSem.initial_frame) rs_arg_src sm_arg.(SimMem.src_mem) st_init_src)
    ,
      exists st_init_tgt sm_init idx_init,
        (<<INITTGT: ms_tgt.(ModSem.initial_frame) rs_arg_tgt sm_arg.(SimMem.tgt_mem) st_init_tgt>>)
        /\
        (<<MLE: SimMem.le sm_arg sm_init>>)
        /\
        (<<MCOMPAT: mem_compat st_init_src st_init_tgt sm_init>>)
        /\
        (<<MATCH: match_states rs_arg_src rs_arg_tgt sm_arg
                               idx_init st_init_src st_init_tgt sm_init>>)
  .

  Hypothesis ATPROGRESS: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.is_call) st_src0)
    ,
      (<<CALLTGT: ms_tgt.(ModSem.is_call) st_tgt0>>)
      /\
      (<<MWF: SimMem.wf sm0>>)
  .

  Hypothesis ATBSIM: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      rs_arg_tgt m_arg_tgt
      (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 rs_arg_tgt m_arg_tgt)
    ,
      exists rs_arg_src m_arg_src sm_arg,
        (<<CALLSRC: ms_src.(ModSem.at_external) st_src0 rs_arg_src m_arg_src>>)
        /\
        (<<MSRC: sm_arg.(SimMem.src_mem) = m_arg_src>>)
        /\
        (<<MTGT: sm_arg.(SimMem.tgt_mem) = m_arg_tgt>>)
        /\
        (<<SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt>>)
        /\
        (<<MLE: SimMem.le sm0 sm_arg>>)
        /\
        (<<MWF: SimMem.wf sm_arg>>)
  .

  Hypothesis AFTERFSIM: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      sm_arg
      (MLE: SimMem.le sm0 sm_arg)
      (* (MWF: SimMem.wf sm_arg) *)
      sm_arg rs_arg_src rs_arg_tgt
      (SIMRSARG: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt)
      sm_ret
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
      (MWF: SimMem.wf sm_ret)
      rs_ret_src rs_ret_tgt
      (SIMRSRET: SimMem.sim_regset sm_ret rs_ret_src rs_ret_tgt)
      st_src1
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 rs_arg_src rs_ret_src sm_ret.(SimMem.src_mem) st_src1)
    ,
      exists idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 rs_arg_tgt rs_ret_tgt
                                                    sm_ret.(SimMem.tgt_mem) st_tgt1>>)
        /\
        (<<MATCH: match_states rs_init_src rs_init_tgt sm_init
                               idx1 st_src1 st_tgt1 (SimMem.unlift sm_arg sm_ret)>>)
  .

  Hypothesis FINALFSIM: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      (MCOMPAT: mem_compat st_src0 st_tgt0 sm0)
      rs_ret_src
      (FINALSRC: ms_src.(ModSem.final_frame) rs_init_src st_src0 rs_ret_src)
    ,
      exists rs_ret_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) rs_init_tgt st_tgt0 rs_ret_tgt>>)
        /\
        (<<SIMRS: SimMem.sim_regset sm0 rs_ret_src rs_ret_tgt>>)
        /\
        (<<MWF: SimMem.wf sm0>>)
  .

  Hypothesis STEPFSIM: forall
      rs_init_src rs_init_tgt sm_init idx0 st_src0 st_tgt0 sm0
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src rs_init_src st_src0)
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
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
               /\ (<<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>>) (* TODO: <-------- is this needed??????? *)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states rs_init_src rs_init_tgt sm_init idx1 st_src1 st_tgt1 sm1>>)
                    >>)
  .

  Hypothesis BAR: bar_True.

  Lemma init_match_states
        sm_arg
        sg_init_src sg_init_tgt
        rs_init_src rs_init_tgt
        (FINDFSRC: msp.(ModSemPair.src).(ModSem.skenv).(Genv.find_funct) (rs_init_src PC) =
                 Some (Internal sg_init_src))
        (FINDFTGT: msp.(ModSemPair.tgt).(ModSem.skenv).(Genv.find_funct) (rs_init_tgt PC) =
                 Some (Internal sg_init_tgt))
        (SIMRS: sm_arg.(SimMem.sim_regset) rs_init_src rs_init_tgt)
        (MWF: SimMem.wf sm_arg)
        (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
    :
      (<<INITSIM: forall
          st_init_src
          (INITSRC: msp.(ModSemPair.src).(ModSem.initial_frame) rs_init_src
                                                                sm_arg.(SimMem.src_mem) st_init_src)
        ,
          exists st_init_tgt sm_init idx_init,
            (<<MCOMPAT: mem_compat st_init_src st_init_tgt sm_init>>)
            /\
            (<<INITTGT: msp.(ModSemPair.tgt).(ModSem.initial_frame) rs_init_tgt
                                                                    sm_arg.(SimMem.tgt_mem) st_init_tgt>>)
            /\
            (<<MLE: SimMem.le sm_arg sm_init>>)
            /\
            (<<SIM: match_states rs_init_src rs_init_tgt sm_arg
                                 idx_init st_init_src st_init_tgt sm_init>>)>>)
  .
  Proof.
    ii; ss.
    u in SIMSKENV.
    exploit SimSymb.sim_skenv_func_bisim; eauto. intro FSIM; des.
    exploit INITFSIM; eauto. 
    Print SimSymb.sim_skenv.
    inv FSIM. exploit FUNCFSIM; eauto. i; des.
    esplits; try apply MATCH; eauto.
  Qed.

  Definition to_idx (i0: index): Ord.idx := (Ord.mk WFORD i0).

  Hint Unfold to_idx.

  Lemma to_idx_spec
        i0 i1
        (ORD: order i0 i1)
    :
      <<ORD: Ord.ord i0.(to_idx) i1.(to_idx)>>
  .
  Proof.
    econs; eauto. cbn. instantiate (1:= eq_refl). cbn. ss.
  Qed.

  Lemma match_states_lxsim
        rs_init_src rs_init_tgt sm_init i0 st_src0 st_tgt0 sm0
        (SIMSKENV: ModSemPair.sim_skenv msp sm0)
        (MLE: SimMem.le sm_init sm0)
        (* (MWF: SimMem.wf sm0) *)
        (MCOMPAT: mem_compat st_src0 st_tgt0 sm0)
        (MATCH: match_states rs_init_src rs_init_tgt sm_init i0 st_src0 st_tgt0 sm0)
    :
      <<LXSIM: lxsim ms_src ms_tgt rs_init_src rs_init_tgt sm_init i0.(to_idx) st_src0 st_tgt0 sm0>>
  .
  Proof.
    revert_until BAR.
    pcofix CIH. i. pfold.
    generalize (classic (ModSem.is_call ms_src st_src0)). intro CALLSRC; des.
    {
      exploit ATPROGRESS; eauto. i; des.
      eapply lxsim_at_external; eauto.
      (* { *)
      (*   u in CALLSRC. des. rename rs_arg into rs_arg_src. rename m_arg into m_arg_src. *)
      (*   exploit ATPROGRESS; eauto. *)
      (* } *)
      clear CALLSRC.
      i.
      exploit ATBSIM; eauto. i; des.
      esplits; eauto.
      { rewrite MSRC. ss. }
      i; des.
      exploit AFTERFSIM; try apply SAFESRC; try apply SIMRS; eauto.
      i; des.
      esplits; eauto.
      - i.
        revert SAFESRC. determ_tac ModSem.after_external_dtm. clear_tac.
        esplits; eauto.
        right.
        eapply CIH; eauto.
        { eapply SimSymb.mle_preserves_sim_skenv; eauto.
          etransitivity; eauto. eapply SimMem.unlift_spec; eauto. }
        { etransitivity; cycle 1.
          - eapply SimMem.unlift_spec; eauto.
          - etransitivity; eauto.
        }
        { econs.
          - erewrite ModSem.after_external_get_mem; try eassumption. erewrite SimMem.unlift_src; eauto.
          - erewrite ModSem.after_external_get_mem; try eassumption. erewrite SimMem.unlift_tgt; eauto.
        }
    }
    generalize (classic (ModSem.is_return ms_src rs_init_src st_src0)). intro RETSRC; des.
    {
      u in RETSRC. des.
      exploit FINALFSIM; eauto. i; des.
      eapply lxsim_final; eauto.
    }
    {
      eapply lxsim_step_forward; eauto.
      exploit STEPFSIM; eauto. i; des.
      econs 1; eauto.
      ii. exploit STEPFSIM0; eauto. i; des_safe.
      esplits; eauto.
      - des.
        + left. eauto.
        + right. esplits; eauto. eapply to_idx_spec; eauto.
      - right. eapply CIH; eauto.
        { eapply SimSymb.mle_preserves_sim_skenv; eauto. }
        { etransitivity; eauto. }
    }
  Qed.

  Theorem match_states_sim
    :
      <<SIM: msp.(ModSemPair.sim)>>
  .
  Proof.
    econs.
    ii; ss.
    u in SIMSKENV.
    exploit SimSymb.sim_skenv_func_bisim; eauto. intro FSIM; des.
    Print SimSymb.sim_skenv.
    inv FSIM. exploit FUNCFSIM; eauto. i; des.
    exploit init_match_states; eauto. i; des.
    esplits; eauto.
    eapply match_states_lxsim; eauto.
    { eapply SimSymb.mle_preserves_sim_skenv; eauto. }
  Qed.

End MATCHSIMFORWARD.


      (* (<<BSIM: *)
      (*    (<<BSIMSTEP: forall *)
      (*        tr st_tgt1 *)
      (*        (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1) *)
      (*      , *)
      (*        exists idx1 st_src1 sm1, *)
      (*          (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ *)
      (*                   <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>) *)
      (*          /\ (<<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>>) (* TODO: <-------- is this needed??????? *) *)
      (*          /\ (<<MLE: SimMem.le sm0 sm1>>) *)
      (*          (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *) *)
      (*          /\ (<<MATCH: match_states rs_init_src rs_init_tgt sm_init idx1 st_src1 st_tgt1 sm1>>) *)
      (*               >>) *)
      (*    /\ *)
      (*    (<<PROGRESS: forall *)
      (*        (SAFESRC: safe ms_src st_src0) *)
      (*      , *)
      (*        <<FINAL: exists retv, final_state ms_tgt st_tgt0 retv>> \/ *)
      (*        <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>>>) *)
      (*    >>) *)
