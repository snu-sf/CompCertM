Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import SimModSem SimMem SimSymb.

Set Implicit Arguments.


Section ORD.

  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.

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

End ORD.



Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM}.

  Variable msp: ModSemPair.t.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).

  Variable match_states: forall
      (sm_arg: SimMem.t)
      (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMem.t)
    ,
      Prop
  .

  Hypothesis INITBSIM: forall
      sm_arg
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      args_src args_tgt
      (SIMARGS: sim_args args_src args_tgt sm_arg)
      st_init_tgt
      (INITTGT: ms_tgt.(ModSem.initial_frame) args_tgt st_init_tgt)
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
      (SIMARGS: sim_args args_src args_tgt sm_arg)
      (SAFESRC: exists st_init_src, ms_src.(ModSem.initial_frame) args_src st_init_src)
    ,
      exists st_init_tgt,
        (<<INITTGT: ms_tgt.(ModSem.initial_frame) args_tgt st_init_tgt>>)
  .

  Hypothesis ATMWF: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.may_call) st_src0)
    ,
      <<MWF: SimMem.wf sm0>>
  .

  Hypothesis ATFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      skenv_link_src skenv_link_tgt
      (SIMSKENVLINK: SimSymb.skenv_func_bisim sm0.(SimMem.sim_val) skenv_link_src skenv_link_tgt)
      args_src
      (CALLSRC: ms_src.(ModSem.at_external) skenv_link_src st_src0 args_src)
    ,
      exists args_tgt sm_arg,
        (<<CALLTGT: ms_tgt.(ModSem.at_external) skenv_link_tgt st_tgt0 args_tgt>>)
        /\
        (<<SIMARGS: sim_args args_src args_tgt sm_arg>>)
        /\
        (<<MLE: SimMem.le sm0 sm_arg>>)
        /\
        (<<MWF: SimMem.wf sm_arg>>)
  .

  Hypothesis AFTERFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      sm_arg
      (MLE: SimMem.le sm0 sm_arg)
      (* (MWF: SimMem.wf sm_arg) *)
      sm_ret
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
      (MWF: SimMem.wf sm_ret)
      retv_src retv_tgt
      (SIMRET: sim_retv retv_src retv_tgt sm_ret)
      st_src1
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 retv_src st_src1)

      (* just helpers *)
      (MWFAFTR: SimMem.wf (SimMem.unlift sm_arg sm_ret))
      (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret))
    ,
      exists sm_after idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 retv_tgt st_tgt1>>)
        /\
        (<<MATCH: match_states sm_init idx1 st_src1 st_tgt1 sm_after>>)
        /\
        (<<MLE: SimMem.le (SimMem.unlift sm_arg sm_ret) sm_after>>)
  .

  Hypothesis FINALFSIM: forall
      sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
      retv_src
      (FINALSRC: ms_src.(ModSem.final_frame) st_src0 retv_src)
    ,
      exists retv_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 retv_tgt>>)
        /\
        (<<SIMRET: sim_retv retv_src retv_tgt sm0>>)
        /\
        (<<MWF: SimMem.wf sm0>>)
  .

  Hypothesis STEPFSIM: forall
      sm_init idx0 st_src0 st_tgt0 sm0
      (NOTCALL: ~ ModSem.may_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states sm_init idx0 st_src0 st_tgt0 sm0)
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

  Hypothesis BAR: bar_True.

  Lemma match_states_lxsim
        sm_init i0 st_src0 st_tgt0 sm0
        (SIMSKENV: ModSemPair.sim_skenv msp sm0)
        (MLE: SimMem.le sm_init sm0)
        (* (MWF: SimMem.wf sm0) *)
        (* (MCOMPAT: mem_compat st_src0 st_tgt0 sm0) *)
        (MATCH: match_states sm_init i0 st_src0 st_tgt0 sm0)
    :
      <<LXSIM: lxsim ms_src ms_tgt sm_init i0.(to_idx WFORD) st_src0 st_tgt0 sm0>>
  .
  Proof.
    revert_until BAR.
    pcofix CIH. i. pfold.
    generalize (classic (ModSem.may_call ms_src st_src0)). intro CALLSRC; des.
    {
      - (* u in CALLSRC. des. *)
        exploit ATMWF; eauto. i; des.
        eapply lxsim_at_external; eauto.
        i. clear CALLSRC.
        exploit ATFSIM; eauto. i; des.
        (* determ_tac ModSem.at_external_dtm. clear_tac. *)
        esplits; eauto. i.
        exploit AFTERFSIM; try apply SAFESRC; try apply SIMRET; eauto.
        { eapply SimMem.unlift_wf; eauto. }
        { eapply SimMem.unlift_spec; eauto. }
        i; des.
        esplits; eauto.
        right.
        eapply CIH; eauto.
        { eapply SimSymb.mle_preserves_sim_skenv; try apply SIMSKENV; eauto.
          etransitivity; eauto. etransitivity; eauto. eapply SimMem.unlift_spec; eauto. }
        { etransitivity; eauto. etransitivity; eauto. etransitivity; eauto. eapply SimMem.unlift_spec; eauto. }
    }
    generalize (classic (ModSem.is_return ms_src st_src0)). intro RETSRC; des.
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
    econs; eauto.
    ii; ss.
    folder.
    exploit SimSymb.sim_skenv_func_bisim; eauto. intro FSIM; des.
    Print SimSymb.sim_skenv.
    inv FSIM. exploit FUNCFSIM; eauto. { apply SIMARGS. } i; des.
    split; ii.
    - exploit INITBSIM; eauto. i; des.
      esplits; eauto.
      eapply match_states_lxsim; eauto.
      { eapply SimSymb.mle_preserves_sim_skenv; eauto. }
    - exploit INITPROGRESS; eauto.
  Admitted. (* TODO: COQ BUG !!!!!!!!!!!!!!!!!!!!!!!!!!! *)

End MATCHSIMFORWARD.

