Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Asmregs Conventions1.

Require Import Mod ModSem Skeleton.

Set Implicit Arguments.



Section SYSMODSEM.

  Inductive state: Type :=
  | state_call
      (fptr_arg: val)
      (rs_arg: regset)
      (m_arg: mem)
  | state_return
      (rs_ret: regset)
      (m_ret: mem)
  .

  Definition genv: Type := Genv.t external_function unit.

  Inductive step (ge: genv): state -> trace -> state -> Prop :=
  | step_intro
      fptr_arg rs_arg m_arg ef
      (FPTR: ge.(Genv.find_funct) fptr_arg = Some ef)
      vs
      (ARGS: extcall_arguments rs_arg m_arg ef.(ef_sig) vs)
      tr v_ret m_ret
      (EXTCALL: external_call ef ge vs m_arg tr v_ret m_ret)
      rs_ret
      (RET: rs_ret = (set_pair (loc_external_result (ef_sig ef)) v_ret
                               (undef_regs (List.map preg_of destroyed_at_call) rs_arg)))
    :
      step ge (state_call fptr_arg rs_arg m_arg) tr (state_return rs_ret m_ret)
  .

  Definition get_mem (st0: state): mem :=
    match st0 with
    | state_call _ _ m => m
    | state_return _ m => m
    end
  .

  Inductive initial_frame (fptr_arg: val) (sg_arg: option signature) (rs_arg: regset) (m_arg: mem):
    state -> Prop :=
  | initial_frame_intro
    :
      initial_frame fptr_arg sg_arg rs_arg m_arg (state_call fptr_arg rs_arg m_arg)
  .

  Inductive final_frame (sg_init: option signature) (rs_init: regset): state -> regset -> mem -> Prop :=
  | final_frame_intro
      rs_ret m_ret
    :
      final_frame sg_init rs_init (state_return rs_ret m_ret) rs_ret m_ret
  .

  Program Definition modsem: ModSem.t := {|
    ModSem.state := state;
    ModSem.genvtype := genv;
    ModSem.step := step;
    ModSem.get_mem := get_mem;
    ModSem.at_external := bot5;
    ModSem.initial_frame := initial_frame;
    ModSem.final_frame := final_frame;
    ModSem.after_external := bot6;
    
  |}
  .
  Next Obligation.
  Qed.



End SYSMODSEM.

Section SYSMOD.

  Variable prog_main: ident.

  Program Definition mod: Mod.t := {|
    Mod.datatype := unit;
    Mod.get_sk := fun _ => (mkprogram [] [] prog_main);
    Mod.get_modsem := admit;
    Mod.data := tt;
  |}
  .

End SYSMOD.

