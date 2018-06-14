Require Import CoqlibC.
Require Import SmallstepC.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import SimModSem SimMem SimSymb.

Set Implicit Arguments.


Section MATCHSIMMODSEM.

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

  (* Hypothesis INITMATCHBACKWARD: forall *)
  (*     sm_arg *)
  (*     (MWF: SimMem.wf sm_arg) *)
  (*     fptr_src fptr_tgt *)
  (*     (FPTRREL: SimMem.sim_val sm_arg fptr_src fptr_tgt) *)
  (*     rs_arg_src rs_arg_tgt *)
  (*     (RSREL: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt) *)
  (*     st_init_tgt *)
  (*     (INITTGT: ms_tgt.(ModSem.initial_frame) rs_arg_tgt sm_arg.(SimMem.tgt_mem) st_init_tgt) *)
  (*   , *)
  (*     exists st_init_src sm_init, *)
  (*       (<<INITSRC: ms_src.(ModSem.initial_frame) rs_arg_src sm_arg.(SimMem.src_mem) st_init_src>>) *)
  (*       /\ *)
  (*       (<<MLE: SimMem.le sm_arg sm_init>>) *)
  (*       /\ *)
  (*       (<<MCOMPAT: mem_compat st_init_src st_init_tgt sm_init>>) *)
  (*       /\ *)
  (*       (<<MATCH: match_states rs_arg_src rs_arg_tgt sm_init st_init_src st_init_tgt sm_init>>) *)
  (* . *)

  Hypothesis INITFSIM: forall
      sm_arg
      (MWF: SimMem.wf sm_arg)
      fptr_src fptr_tgt
      (FPTRREL: SimMem.sim_val sm_arg fptr_src fptr_tgt)
      rs_arg_src rs_arg_tgt
      (RSREL: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt)
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
        (<<MATCH: match_states rs_arg_src rs_arg_tgt sm_init
                               idx_init st_init_src st_init_tgt sm_init>>)
  .

  Hypothesis ATPROGRESS: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.is_call) st_src0)
    ,
      (<<CALLTGT: ms_tgt.(ModSem.is_call) st_tgt0>>)
  .

  Hypothesis ATBSIM: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
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
        (<<RSREL: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt>>)
        /\
        (<<MLE: SimMem.le sm0 sm_arg>>)
        /\
        (<<MWF: SimMem.wf sm_arg>>)
  .

  Hypothesis AFTERFSIM: forall
      rs_init_src rs_init_tgt sm_init
      idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states rs_init_src rs_init_tgt sm_init
                           idx0 st_src0 st_tgt0 sm0)
      sm_arg
      (MLE: SimMem.le sm0 sm_arg)
      sm_arg rs_arg_src rs_arg_tgt
      (RSRELARG: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt)
      sm_ret
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
      rs_ret_src rs_ret_tgt
      (RSRELRET: SimMem.sim_regset sm_ret rs_ret_src rs_ret_tgt)
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

  Hypothesis BAR: bar_True.

  Lemma init_match_states
        sm_arg
        fptr_init_src fptr_init_tgt
        (FPTRREL: sm_arg.(SimMem.sim_val) fptr_init_src fptr_init_tgt)
        sg_init_src sg_init_tgt
        (SIGSRC: msp.(ModSemPair.src).(ModSem.skenv).(Genv.find_funct) fptr_init_src =
                 Some (Internal sg_init_src))
        (SIGTGT: msp.(ModSemPair.tgt).(ModSem.skenv).(Genv.find_funct) fptr_init_tgt =
                 Some (Internal sg_init_tgt))
        (* (SIGREL: sim_sig sg_init_src sg_init_tgt) *)
        rs_init_src rs_init_tgt
        (RSREL: sm_arg.(SimMem.sim_regset) rs_init_src rs_init_tgt)
        (MWF: SimMem.wf sm_arg)
        (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
    :
      (<<INITSIM: forall
          st_init_src
          (INITSRC: msp.(ModSemPair.src).(ModSem.initial_frame) rs_init_src
                                                                sm_arg.(SimMem.src_mem) st_init_src)
        ,
          exists st_init_tgt sm_init idx_init,
            (* (<<MCOMPAT: mem_compat ms_src ms_tgt st_init_src st_init_tgt sm_init>>) /\ *)
            (* Can be proved with initial_states_get_mem *)
            (<<INITTGT: msp.(ModSemPair.tgt).(ModSem.initial_frame) rs_init_tgt
                                                                    sm_arg.(SimMem.tgt_mem) st_init_tgt>>)
            /\
            (<<MLE: SimMem.le sm_arg sm_init>>)
            /\
            (<<SIM: match_states rs_init_src rs_init_tgt sm_init
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

  Lemma match_states_lxsim
        rs_init_src rs_init_tgt sm_init i0 st_src0 st_tgt0 sm0
        (MWF: SimMem.wf sm0)
        (MATCH: match_states rs_init_src rs_init_tgt sm_init i0 st_src0 st_tgt0 sm0)
    :
      <<LXSIM: lxsim ms_src ms_tgt rs_init_src rs_init_tgt sm_init i0.(to_idx) st_src0 st_tgt0 sm0>>
  .
  Proof.
    revert_until BAR.
    pcofix CIH. i. pfold.
    generalize (classic (ModSem.is_call ms_src st_src0)). intro CALLSRC; des.
    {
      eapply lxsim_at_external; eauto.
      { admit "easy". }
      {
        u in CALLSRC. des. rename rs_arg into rs_arg_src. rename m_arg into m_arg_src.
        exploit ATPROGRESS; eauto.
      }
      clear CALLSRC.
      i.
      exploit ATBSIM; eauto. i; des.
      esplits; eauto.
      { rewrite MSRC. ss. }
      i; des.
      exploit AFTERFSIM; try apply SAFESRC; try apply RSREL; eauto.
      i; des.
      esplits; eauto.
      - i.
        esplits; eauto.
        right. eapply CIH; eauto.
        { eapply SimMem.unlift_wf; eauto. }
        clear SAFESRC. determ_tac ModSem.after_external_dtm. eauto.
    }
    generalize (classic (ModSem.may_return ms_src st_src0)). intro RETSRC; des.
    (* generalize (classic (ModSem.is_return ms_src rs_init_src st_src0)). intro RETSRC; des. *)
    {
      u in RETSRC.
      eapply lxsim_final; eauto.
      - admit "easy".
      - admit "???".
      -
      -
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
    split.
    - i.
    exploit INITMATCHFORWARD; eauto.
    {
    esplits; eauto.
    - econs; eauto.
      exploit INITMATCH; eauto.
  Qed.

End MATCHSIMMODSEM.

