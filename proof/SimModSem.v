Require Import ModSem.
Require Import SimMem.
Require Import Simulation.
Require Import AST.
From Paco Require Import paco.
Import ModSem.
Require Import Asmregs.
Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
Require Import Values Integers.
Require Import Globalenvs.
Require Import Program.

Require Import SimDef SimSymb Ord.

Set Implicit Arguments.



Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  (* Inductive mem_compat (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop := *)
  (* | mem_compat_intro *)
  (*     (MCOMPATSRC: ms_src.(get_mem) st_src0 = sm0.(SimMem.src_mem)) *)
  (*     (MCOMPATTGT: ms_tgt.(get_mem) st_tgt0 = sm0.(SimMem.tgt_mem)) *)
  (* . *)
  Record mem_compat (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop := {
    mcompat_src: <<MCOMPATSRC: ms_src.(get_mem) st_src0 = sm0.(SimMem.src_mem)>>;
    mcompat_tgt: <<MCOMPATTGT: ms_tgt.(get_mem) st_tgt0 = sm0.(SimMem.tgt_mem)>>;
  }
  .

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | fsim_step_step
      (STEP: forall
          st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1)
        ,
          exists i1 st_tgt1 sm1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>> (* TODO: <-------- is this needed??????? *)
            /\ <<MLE: SimMem.le sm0 sm1>>
(* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 sm1>>)
  | fsim_step_stutter
      i1 st_tgt1
      (STAR: DStar ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (BSIM: fsim i1 st_src0 st_tgt1 sm0)
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
            /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>>
            /\ <<MLE: SimMem.le sm0 sm1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 sm1>>)
  | bsim_step_stutter
      i1 st_src1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (BSIM: bsim i1 st_src1 st_tgt0 sm0)
  .

  Print xsim.

  Inductive _lxsim (lxsim: regset -> regset -> SimMem.t ->
                           idx -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (rs_init_src rs_init_tgt: regset) (sm_init: SimMem.t)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | lxsim_step_forward
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (* (SAFESRC: ms_src.(ModSem.is_step) st_src0) *)
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) rs_init_src st_src0)
      (FSTEP: fsim_step (lxsim rs_init_src rs_init_tgt sm_init) i0 st_src0 st_tgt0 sm0)
      (RECEP: receptive_at ms_src st_src0)
      (* Note: We used coercion on determinate_at. See final_state, which is bot2. *)
      (* sd_determ_at_final becomes nothing, but it is OK. *)
      (* In composed semantics, when it stepped, it must not be final *)

  | lxsim_step_backward
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (SAFESRC: ms_src.(ModSem.is_step) st_src0)
      (BSTEP:
        (*  forall *)
        (*   (SAFESRC: safe ms_src st_src0) *)
        (* , *)
          <<BSTEP: bsim_step (lxsim rs_init_src rs_init_tgt sm_init) i0 st_src0 st_tgt0 sm0>>)
      (PROGRESS:
        (*  forall *)
        (*   (SAFESRC: safe ms_src st_src0) *)
        (* , *)
          <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)

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
  (*         (AFTERTGT: ms_tgt.(after_external) st_tgt0 rs_arg_tgt rs_ret_tgt sm1.(SimMem.tgt_mem) *)
  (*                                                                                st_tgt1) *)
  (*       , *)
  (*         exists i1 st_src1, *)
  (*         (<<AFTERSRC: ms_src.(after_external) st_src0 rs_arg_src rs_ret_src sm1.(SimMem.src_mem) *)
  (*                                                                                  st_src1>>) *)
  (*         /\ *)
  (*         (<<LXSIM: lxsim i1 st_src1 st_tgt1 (SimMem.unlift sm0 sm1)>>)) *)

  | lxsim_at_external
      (MCOMPAT: mem_compat st_src0 st_tgt0 sm0)
      (MWF: SimMem.wf sm0)
      (* (CALLPROGRESS: forall *)
      (*     rs_arg_src m_arg_src *)
      (*     (ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src) *)
      (*   , *)
      (*     exists rs_arg_tgt m_arg_tgt, <<ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt>>) *)
      (* (SAFESRC: exists rs_arg_src m_arg_src, <<ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src>>) *)
      (SAFESRC: ms_tgt.(is_call) st_tgt0)
      (* (PROGSRC: ms_src.(is_call) st_src0) *)
      (CALLBSIM: forall
          rs_arg_tgt m_arg_tgt
          (ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt)
        ,
          exists rs_arg_src sm_arg,
            (<<MTGT: sm_arg.(SimMem.tgt_mem) = m_arg_tgt>>)
            /\ (<<MWF: SimMem.wf sm_arg>>)
            /\ (<<MLE: SimMem.le sm0 sm_arg>>)
            /\ (<<ATSRC: ms_src.(at_external) st_src0 rs_arg_src sm_arg.(SimMem.src_mem)>>)
            /\ (<<RSREL: sm_arg.(SimMem.sim_regset) rs_arg_src rs_arg_tgt>>)
            /\
            (<<K: forall
                sm_ret rs_ret_src rs_ret_tgt
                (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
                (MWF: SimMem.wf sm_ret)
                (RSREL: sm_ret.(SimMem.sim_regset) rs_ret_src rs_ret_tgt)
                (SAFESRC: exists st_src1,
                    <<AFTERSRC: ms_src.(after_external) st_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src_mem))
                                                        st_src1>>)
              ,
                (<<KSTEP: forall
                    st_tgt1
                    (AFTERTGT: ms_tgt.(after_external) st_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt_mem))
                                                       st_tgt1)
                  ,
                    exists i1 st_src1,
                      (<<AFTERSRC:
                         ms_src.(after_external) st_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src_mem))
                                                           st_src1>>)
                      /\
                      (<<LXSIM: lxsim rs_init_src rs_init_tgt sm_init
                                      i1 st_src1 st_tgt1 (sm_arg.(SimMem.unlift) sm_ret)>>)>>)
                /\
                (<<KPROGRESS:(*  forall *)
                  (*   st_src1 *)
                  (*   (AFTERSRC: ms_src.(after_external) st_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src_mem)) *)
                  (*                                      st_src1) *)
                  (* , *)
                    exists st_tgt1,
                      (<<AFTERTGT:
                         ms_tgt.(after_external) st_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt_mem))
                                                 st_tgt1>>)>>)>>))

  | lxsim_final
      (MCOMPAT: mem_compat st_src0 st_tgt0 sm0)
      (MLE: SimMem.le sm_init sm0)
      (MWF: SimMem.wf sm0)
      (* (PROGRESS: ms_tgt.(is_return) rs_init_tgt st_tgt0) *)
      (* (RETBSIM: forall           *)
      (*     rs_ret_tgt m_ret_tgt *)
      (*     (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)
      (*   , *)
      (*     exists rs_ret_src m_ret_src, *)
      (*       (<<RSREL: sm0.(SimMem.sim_regset) rs_ret_src rs_ret_tgt>>) *)
      (*       /\ (<<FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src>>)) *)
      rs_ret_src rs_ret_tgt
      (FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src)
      (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt)
      (RSREL: sm0.(SimMem.sim_regset) rs_ret_src rs_ret_tgt)

      (* Note: Actually, final_frame can be defined as a function. *)

      (* (FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src) *)
      (* (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)

  .

  Definition lxsim: _ -> _ -> _ -> _ -> _ -> _ -> _ -> Prop := paco7 _lxsim bot7.

  Lemma lxsim_mon:
    monotone7 _lxsim.
  Proof.
    repeat intro. inv IN; eauto.
    - econs 1; ss.
      inv FSTEP. 
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss.
      i. (* specialize (BSTEP SAFESRC0). *)
      inv BSTEP.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto.
      i; ss. exploit CALLBSIM; eauto. i; des.
      esplits; eauto. ii.
      exploit K; eauto. i; des. esplits; eauto.
      ii. exploit KSTEP; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsim.
Hint Resolve lxsim_mon: paco.

Print HintDb typeclass_instances.



Module ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SS: SimSymb.class SM}.

  Record t: Type := mk {
    src: ModSem.t;
    tgt: ModSem.t;
    ss: SimSymb.t;
    (* TODO: which unary/binary property it expects *)
    (* TODO: analysis *)
  }
  .

  Definition sim_skenv (msp: t) (sm0: SimMem.t): Prop :=
    SimSymb.sim_skenv sm0 msp.(ss) msp.(src).(ModSem.skenv) msp.(tgt).(ModSem.skenv).

  (* ####################### TODO: Rename initial_machine/final_machine into initial_frame/final_frame *)
  Inductive sim (msp: t): Prop :=
  | sim_intro
      (SIM: forall
          sm_init
          fptr_init_src fptr_init_tgt
          (FPTRREL: sm_init.(SimMem.sim_val) fptr_init_src fptr_init_tgt)
          sg_init_src sg_init_tgt
          (SIGSRC: msp.(src).(ModSem.skenv).(Genv.find_funct) fptr_init_src = Some (Internal sg_init_src))
          (SIGTGT: msp.(tgt).(ModSem.skenv).(Genv.find_funct) fptr_init_tgt = Some (Internal sg_init_tgt))
          (* (SIGREL: sim_sig sg_init_src sg_init_tgt) *)
          rs_init_src rs_init_tgt
          (RSREL: sm_init.(SimMem.sim_regset) rs_init_src rs_init_tgt)
          (WF: SimMem.wf sm_init)
          (SIMSKENV: sim_skenv msp sm_init)
        ,
          (<<INITSIM: forall
              st_init_tgt
              (INITTGT: msp.(tgt).(initial_frame) rs_init_tgt
                                                 sm_init.(SimMem.tgt_mem) st_init_tgt)
            ,
              exists st_init_src idx_init,
                (* (<<MCOMPAT: mem_compat ms_src ms_tgt st_init_src st_init_tgt sm_init>>) /\ *)
                (* Can be proved with initial_states_get_mem *)
                (<<INITSRC: msp.(src).(initial_frame) rs_init_src sm_init.(SimMem.src_mem) st_init_src>>) /\
                (<<SIM: lxsim msp.(src) msp.(tgt) rs_init_src rs_init_tgt sm_init
                              idx_init st_init_src st_init_tgt sm_init>>)>>)
          /\
          (<<INITPROGRESS: forall
              st_init_src
              (INITSRC: msp.(src).(initial_frame) rs_init_src
                                                 sm_init.(SimMem.src_mem) st_init_src)
            ,
              exists st_init_tgt,
                (<<INITTGT: msp.(tgt).(initial_frame) rs_init_tgt sm_init.(SimMem.tgt_mem) st_init_tgt>>)>>))
  .

End MODSEMPAIR.
End ModSemPair.

Hint Unfold ModSemPair.sim_skenv.


