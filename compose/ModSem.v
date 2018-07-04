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
Require Import CoqlibC.

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
                (rs_arg: regset) (m_arg: mem): Prop;
    initial_frame (rs_arg: regset) (m_arg: mem)
                    (st0: state): Prop;
    (* time: rs_arg >> st0 *)
    final_frame (rs_init: regset)
    (* What is sg_arg/rs_arg for? Just auxiliary data. rs_arg: returning from C/ *)
                  (st0: state)
                  (rs_ret: regset) (* (m_ret: mem) *): Prop;
    (* time: st0 >> rs_arg *)
    after_external (st0: state) (rs_arg: regset)
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
    (* We need to drop permission ! *)
    (* initial_machine_get_mem: forall *)
    (*     rs_arg m_arg st0 *)
    (*     (INIT: initial_frame rs_arg m_arg st0) *)
    (*   , *)
    (*     <<MEM: st0.(get_mem) = m_arg>> *)
    (* ; *)
    after_external_get_mem: forall
        st0 rs_arg rs_ret m_ret st1
        (AFTER: after_external st0 rs_arg rs_ret m_ret st1)
      ,
        <<MEM: st1.(get_mem) = m_ret>>
    ;

    initial_frame_dtm: forall
        rs_arg m_arg
        st0 st1
        (INIT0: initial_frame rs_arg m_arg st0)
        (INIT1: initial_frame rs_arg m_arg st1)
      ,
        st0 = st1
    ;
    final_frame_dtm: forall
        rs_init st rs_ret0 rs_ret1
        (FINAL0: final_frame rs_init st rs_ret0)
        (FINAL1: final_frame rs_init st rs_ret1)
      ,
        rs_ret0 = rs_ret1
    ;
    (* final_frame_dtm: forall *)
    (*     rs_init st rs_ret0 m_ret0 rs_ret1 m_ret1 *)
    (*     (FINAL0: final_frame rs_init st rs_ret0 m_ret0) *)
    (*     (FINAL1: final_frame rs_init st rs_ret1 m_ret1) *)
    (*   , *)
    (*     rs_ret0 = rs_ret1 /\ m_ret0 = m_ret1 *)
    (* ; *)
    after_external_dtm: forall
        st_call rs_arg rs_ret m_ret st0 st1
        (AFTER0: after_external st_call rs_arg rs_ret m_ret st0)
        (AFTER1: after_external st_call rs_arg rs_ret m_ret st1)
      ,
        st0 = st1
    ;


    is_call (st0: state): Prop := exists rs_arg m_arg, at_external st0 rs_arg m_arg;
    is_step (st0: state): Prop := exists tr st1, step globalenv st0 tr st1;
    is_return (rs_init: regset) (st0: state): Prop := exists rs_ret, final_frame rs_init st0 rs_ret;
    may_return (st0: state): Prop := exists rs_init, is_return rs_init st0;
      (* exists rs_init rs_ret m_ret, final_frame rs_init st0 rs_ret m_ret; *)
    (* Note: "forall" or "exists" for rs_init? *)
    (* "forall" -> easy for opt/hard for meta *)
    (* "exists" -> hard for opt/easy for meta *)
    (* I think "exists" is OK here. *)
    (* We can think of something like "forall rs_init (FUTURE: st0 is future of rs_init)", but is overkill. *)

    call_step_disjoint: is_call /1\ is_step <1= bot1;
    step_return_disjoint: is_step /1\ may_return <1= bot1;
    call_return_disjoint: is_call /1\ may_return <1= bot1;

    (* step_at_external_disjoint: forall *)
    (*     st0 *)
    (*     tr st1 *)
    (*     (STEP: step globalenv st0 tr st1) *)
    (*     rs_arg m_arg *)
    (*     (ATEXT: at_external st0 rs_arg m_arg) *)
    (*   , *)
    (*     False *)
    (* ; *)
    (* at_external_final_machine_disjoint: forall *)
    (*     st0 *)
    (*     rs_arg m_arg *)
    (*     (ATEXT: at_external st0 rs_arg m_arg) *)
    (*     rs_init rs_ret m_ret *)
    (*     (FINAL: final_frame rs_init st0 rs_ret m_ret) *)
    (*   , *)
    (*     False *)
    (* ; *)
    (* step_final_machine_disjoint: forall *)
    (*     st0 *)
    (*     tr st1 *)
    (*     (STEP: step globalenv st0 tr st1) *)
    (*     rs_init rs_ret m_ret *)
    (*     (FINAL: final_frame rs_init st0 rs_ret m_ret) *)
    (*   , *)
    (*     False *)
    (* ; *)
  }.

  (* Note: I didn't want to define this tactic. I wanted to use eauto + Hint Resolve, but it didn't work. *)
  Ltac tac :=
    try(
        let TAC := u; esplits; eauto in
        u in *; des_safe;
        first[
            exfalso; eapply ModSem.call_step_disjoint; TAC; fail
          |
          exfalso; eapply ModSem.step_return_disjoint; TAC; fail
          |
          exfalso; eapply ModSem.call_return_disjoint; TAC; fail
          ]
      )
  .

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
    (Semantics_gen ms.(step) bot1 bot2 ms.(globalenv) ms.(skenv))
  .

End ModSem.

Hint Unfold ModSem.is_call ModSem.is_step ModSem.may_return ModSem.is_return ModSem.get_mem.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
(* I want to use definitions like "Star" or "determinate_at" *)


