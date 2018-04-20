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

Set Implicit Arguments.



Inductive sim_sig (sg_src sg_tgt: option signature): Prop :=
| sim_sig_same
    sg
    (SRC: sg_src = Some sg)
    (TGT: sg_tgt = Some sg)
| sim_sig_drop
    (TGT: sg_tgt = None)
.

Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem}.

  Inductive mem_compat (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | mem_compat_intro
      (MCOMPAT_SRC: ms_src.(get_mem) st_src0 = sm0.(src_mem))
      (MCOMPAT_TGT: ms_tgt.(get_mem) st_tgt0 = sm0.(tgt_mem))
  .
  Variable index: Type.
  Variable order: index -> index -> Prop.

  Variable sg_init_src: option signature.
  Variable sg_init_tgt: option signature.
  Variable rs_init_src: regset.
  Variable rs_init_tgt: regset.
  Variable sm_init: SimMem.t.
  (* initial_machine : Values.block -> option signature -> Asmregs.regset -> Memory.Mem.mem -> state -> Prop; *)

  Inductive fsim_step (fsim: index -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: index) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | fsim_step_step
      (STEP: forall
          st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1)
        ,
          exists i1 st_tgt1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order i1 i0>>)
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 sm0>>)
  | fsim_step_stutter
      i1 st_tgt1
      (STAR: DStar ms_tgt st_tgt0 nil st_tgt1 /\ order i1 i0)
      (BSIM: fsim i1 st_src0 st_tgt1 sm0)
  .

  Inductive bsim_step (bsim: index -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
            (i0: index) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | bsim_step_step
      (STEP: forall
          st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1)
        ,
          exists i1 st_src1 sm1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ order i1 i0>>)
            /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 sm1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 sm1>>)
  | bsim_step_stutter
      i1 st_src1
      (STAR: Star ms_src st_src0 nil st_src1 /\ order i1 i0)
      (BSIM: bsim i1 st_src1 st_tgt0 sm0)
  .

  Print xsim.

  CoInductive _lxsim (lxsim: index -> state ms_src -> state ms_tgt -> SimMem.t -> Prop)
              (i0: index) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop :=
  | lxsim_step_forward
      (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0)
      (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0)
      (FSTEP: fsim_step lxsim i0 st_src0 st_tgt0 sm0)
      (RECEP: receptive_at ms_src st_src0)
      (* Note: We used coercion on determinate_at. See final_state, which is bot2. *)
      (* sd_determ_at_final becomes nothing, but it is OK. *)
      (* In composed semantics, when it stepped, it must not be final *)

  | lxsim_step_backward
      (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0)
      (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0)
      (BSTEP: forall
          (SAFESRC: safe ms_src st_src0)
        ,
          <<BSTEP: bsim_step lxsim i0 st_src0 st_tgt0 sm0>>)
      (PROGRESS: forall
          (SAFESRC: safe ms_src st_src0)
        ,
          <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)

  (* TODO: is this the best spec? *)
  (* 1) forall src tgt -> src~tgt *)
  (* 2) forall src, exists tgt -> src~tgt *)
  (* Two different forall->exists, then "exists" may give two different value? determinacy to rescue? *)
  | lxsim_at_external
      fptr_src fptr_tgt sg_arg_src sg_arg_tgt rs_arg_src rs_arg_tgt
      (MCOMPAT: mem_compat st_src0 st_tgt0 sm0)
      m_arg_src m_arg_tgt
      (ATSRC: ms_src.(at_external) st_src0 fptr_src sg_arg_src rs_arg_src m_arg_src)
      (ATTGT: ms_tgt.(at_external) st_tgt0 fptr_tgt sg_arg_tgt rs_arg_tgt m_arg_tgt)
      (FPTRREL: sm0.(sim_val) fptr_src fptr_tgt)
      (ARGSREL: sm0.(sim_regset) rs_arg_src rs_arg_tgt)
      (VALID: valid sm0)
      (AFTER: forall
          rs_ret_src rs_ret_tgt sm1
          (MLE: le (lift sm0) sm1)
          (VALID: valid sm1)
          (RETVREL: sm1.(sim_regset) rs_ret_src rs_ret_tgt)
          st_tgt1
          (AFTERTGT: ms_tgt.(after_external) st_tgt0 sg_arg_tgt rs_arg_tgt rs_ret_tgt sm1.(tgt_mem) st_tgt1)
        ,
          exists i1 st_src1,
          (<<AFTERSRC: ms_src.(after_external) st_src0 sg_arg_src rs_arg_src rs_ret_src sm1.(src_mem) st_src1>>)
          /\
          (<<LXSIM: lxsim i1 st_src1 st_tgt1 (unlift sm0 sm1)>>))

  | lxsim_exit
      retv_src retv_tgt
      (MLE: le sm_init sm0)
      (VALID: valid sm0)
      (RETVREL: sm0.(sim_val) retv_src retv_tgt)
      rs_ret_src rs_ret_tgt m_ret_src m_ret_tgt
      (EXITSRC: ms_src.(final_machine) sg_init_src rs_init_src st_src0 rs_ret_src m_ret_src)
      (EXITTGT: ms_tgt.(final_machine) sg_init_tgt rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt)

  .

  Definition lxsim: _ -> _ -> _ -> _ -> Prop := paco4 _lxsim bot4.

  Lemma lxsim_mon:
    monotone4 _lxsim.
  Proof.
    repeat intro. inv IN; eauto.
    - econs 1; ss.
      inv FSTEP. 
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss.
      i. specialize (BSTEP SAFESRC).
      inv BSTEP.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto.
      i; ss. exploit AFTER; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsim.
Hint Resolve lxsim_mon: paco.


(* ####################### TODO: Rename initial_machine/final_machine into initial_frame/final_frame *)
Inductive sim_modsem `{SM: SimMem} (ms_src ms_tgt: ModSem.t): Prop :=
| sim_modsem_intro
    (idx: Type) (order: idx -> idx -> Prop)
    (SIM: forall
        fptr_init_src fptr_init_tgt
        sm_init
        (FPTRREL: sm_init.(sim_val) fptr_init_src fptr_init_tgt)
        sg_init_src sg_init_tgt
        (SIGREL: sim_sig sg_init_src sg_init_tgt)
        rs_init_src rs_init_tgt
        (RSREL: sm_init.(sim_regset) rs_init_src rs_init_tgt)
        (VALID: valid sm_init)
      ,
        (<<STEP: forall
            st_init_tgt
            (INITTGT: ms_tgt.(initial_machine) fptr_init_tgt sg_init_tgt rs_init_tgt
                                               sm_init.(tgt_mem) st_init_tgt)
          ,
            exists st_init_src idx_init,
              (* (<<MCOMPAT: mem_compat ms_src ms_tgt st_init_src st_init_tgt sm_init>>) /\ *)
              (* Can be proved with initial_states_get_mem *)
              (<<INITSRC: ms_src.(initial_machine) fptr_init_src sg_init_src
                                              rs_init_src sm_init.(src_mem) st_init_src>>) /\
              (<<SIM: lxsim ms_src ms_tgt order sg_init_src sg_init_tgt rs_init_src rs_init_tgt sm_init
                            idx_init st_init_src st_init_tgt sm_init>>)>>)
        /\
        (<<PROGRESS: forall
            st_init_src
            (INITSRC: ms_src.(initial_machine) fptr_init_src sg_init_src rs_init_src
                                               sm_init.(src_mem) st_init_src)
          ,
            exists st_init_tgt,
              (<<INITTGT: ms_tgt.(initial_machine) fptr_init_tgt sg_init_tgt
                                                   rs_init_tgt sm_init.(tgt_mem) st_init_tgt>>)>>))
.
