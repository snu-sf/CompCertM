Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Skeleton.

Set Implicit Arguments.



Module ModSem.

  (* Stores callee data that will be used only in meta-steps. *)
  Definition aux_data: Type := (option signature * regset)%type.

  Record t: Type := mk {
    state: Type;
    genvtype: Type;
    step (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop;
    (* TOOD: is ge needed? I follow compcert for now. *)

    get_mem (st0: state): mem;
    (* set_mem (m0: mem) (st0: state): state; *) (* This is not used, after_external is enough *)
    at_external (st0: state)
                (fptr_arg: val) (sg_arg: option signature) (rs_arg: regset) (m_arg: mem): Prop;
    initial_frame (fptr_arg: val) (sg_arg: option signature) (rs_arg: regset) (m_arg: mem)
                    (st0: state): Prop;
    (* time: rs_arg >> st0 *)
    final_frame (sg_init: option signature) (rs_init: regset)
    (* What is sg_arg/rs_arg for? Just auxiliary data. rs_arg: returning from C/ *)
                  (st0: state)
                  (rs_ret: regset) (m_ret: mem): Prop;
    (* time: st0 >> rs_arg *)
    after_external (st0: state) (sg_arg: option signature) (rs_arg: regset)
                   (rs_ret: regset) (m_ret: mem)
                   (st1: state): Prop;
    globalenv: genvtype;
    (* internals: list block; *)
    (* internals: block -> Prop; *)
    (* main_fptr: block; *)
    (* Note: "internals" is not enough! A ModSemPair should be able to specify which SimMem it relys. *)
    skenv: SkEnv.t;
    (* skenv: SkEnv.t; *)
    (* ########################################## I added SkEnv.t only for defining "compat" in sim_mem. *)
    (* If it is not used, remove it *)


    (* good properties *)
    initial_machine_get_mem: forall
        fptr_arg sg_arg rs_arg m_arg st0
        (INIT: initial_frame fptr_arg sg_arg rs_arg m_arg st0)
      ,
        <<MEM: st0.(get_mem) = m_arg>>
    ;
    step_at_external_disjoint: forall
        st0
        tr st1
        (STEP: step globalenv st0 tr st1)
        fptr_arg sg_arg rs_arg m_arg
        (ATEXT: at_external st0 fptr_arg sg_arg rs_arg m_arg)
      ,
        False
    ;
    at_external_final_machine_disjoint: forall
        st0
        fptr_arg sg_arg rs_arg m_arg
        (ATEXT: at_external st0 fptr_arg sg_arg rs_arg m_arg)
        sg_init rs_init rs_ret m_ret
        (FINAL: final_frame sg_init rs_init st0 rs_ret m_ret)
      ,
        False
    ;
    step_final_machine_disjoint: forall
        st0
        tr st1
        (STEP: step globalenv st0 tr st1)
        sg_init rs_init rs_ret m_ret
        (FINAL: final_frame sg_init rs_init st0 rs_ret m_ret)
      ,
        False
    ;
  }.


  (* Definition is_internal (ms0: t) (st0: ms0.(state)) (sg_arg: option signature) (rs_arg: regset): Prop := *)
  (*   <<NOTCALL: forall fptr_arg sg_arg rs_arg m_arg, ~ ms0.(at_external) st0 fptr_arg sg_arg rs_arg m_arg>> /\ *)
  (*   <<NOTRETURN: forall rs_ret m_ret, ~ ms0.(final_machine) sg_arg rs_arg st0 rs_ret m_ret>> *)
  (* . *)

  (* TODO: which one is right? above or below? *)
  (* Definition is_internal (ms0: t) (st0: ms0.(state)): Prop := *)
  (*   <<NOTCALL: forall fptr_arg sg_arg rs_arg m_arg, ~ ms0.(at_external) st0 fptr_arg sg_arg rs_arg m_arg>> /\ *)
  (*   <<NOTRETURN: forall sg_arg rs_arg rs_ret m_ret, ~ ms0.(final_machine) sg_arg rs_arg st0 rs_ret m_ret>> *)
  (* . *)

  Definition to_semantics (ms: t) :=
    (Semantics_gen ms.(step) bot1 bot2 ms.(globalenv) (admit "dummy for now"))
  .

End ModSem.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
(* I want to use definitions like "Star" or "determinate_at" *)


