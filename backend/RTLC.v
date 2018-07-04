Require Import CoqlibC Maps.
Require Import ASTC Integers Values Events Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
(** newly added **)
Require Export RTL.
Require Import ModSem.
Require Import AsmregsC.
Require Import Conventions.
(* Require Import Locations. *)

Set Implicit Arguments.





Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end
.

Section MODSEM.

  Variable p: program.
  Let ge := p.(Genv.globalenv).

  Inductive at_external: state -> regset -> mem -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg vs_arg m0
      m_arg sp
      (ALLOC: Mem.alloc m_arg Stacklayout.fe_ofs_arg (size_arguments sg_arg) = (m_arg, sp))
      rs_arg
      (STORE: extcall_arguments rs_arg m_arg sg_arg vs_arg)
      (EXTERNAL: Genv.find_funct ge fptr_arg = None)
    :
      at_external (Callstate stack fptr_arg sg_arg vs_arg m0)
                  rs_arg m_arg
  .

  Inductive initial_frame (rs_arg: regset) (m_arg: mem)
    : state -> Prop :=
  | initial_frame_intro
      fptr_arg fd
      (FPTR: fptr_arg = rs_arg PC)
      (FINDF: Genv.find_funct ge fptr_arg = Some (Internal fd))
      vs_arg m_init
      (LOAD: load_arguments rs_arg m_arg fd.(fn_sig) vs_arg m_init)
    :
      initial_frame rs_arg m_arg
                    (Callstate [] fptr_arg fd.(fn_sig) vs_arg m_init)
  .

  Inductive final_frame (rs_init: regset): state -> regset -> Prop :=
  | final_frame_intro
      fd
      (FINDF: Genv.find_funct ge (rs_init PC) = Some (Internal fd))
      v_ret m_ret rs_ret
      (STORE: store_result rs_init v_ret fd.(fn_sig) rs_ret)
    :
      final_frame rs_init (Returnstate [] v_ret m_ret) rs_ret
  .

  Inductive after_external: state -> regset -> regset -> mem -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg vs_arg m_arg
      rs_ret m_ret
      v_ret rs_arg
      (LOAD: load_result rs_arg rs_ret sg_arg v_ret)
    :
      after_external (Callstate stack fptr_arg sg_arg vs_arg m_arg)
                     rs_arg
                     rs_ret m_ret
                     (Returnstate stack v_ret m_ret)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.get_mem := get_mem;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge; (* TODO: Change this properly *)
      ModSem.skenv := (admit "TODO")
    |}
  .
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    all_once_fast ltac:(fun H => try inv H).
    rewrite FINDF in *. clarify.
    determ_tac load_arguments_dtm.
  Qed.
  Next Obligation.
    all_once_fast ltac:(fun H => try inv H); rewrite FINDF in *; clarify. determ_tac store_result_dtm.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H); rewrite EXTERNAL in *; clarify.
  Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H); rewrite EXTERNAL in *; clarify.
  Qed.
  Next Obligation.
    ii; ss; des; all_once_fast ltac:(fun H => try inv H).
  Qed.

End MODSEM.

