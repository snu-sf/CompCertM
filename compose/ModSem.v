Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Skeleton.
Require Import CoqlibC.

Set Implicit Arguments.



Module Args.

  Record t := mk {
    fptr: val;
    (* sg: signature; *)
    vs: list val;
    m: mem;
  }.

End Args.

Module Retv.

  Record t := mk {
    v: val;
    m: mem;
  }.

End Retv.

Module ModSem.

  Record t: Type := mk {
    state: Type;
    genvtype: Type;
    step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop;
    (* TOOD: is ge needed? I follow compcert for now. *)

    (* set_mem (m0: mem) (st0: state): state; *) (* This is not used, after_external is enough *)
    at_external (st0: state) (args: Args.t): Prop;
    initial_frame (args: Args.t) (st0: state): Prop;
    (* time: rs_arg >> st0 *)
    final_frame (* (st_init: state) *) (st0: state)
                (retv: Retv.t): Prop;
    (* time: st0 >> rs_arg *)
    after_external (st0: state) (retv: Retv.t)
                   (st1: state): Prop;
    globalenv: genvtype;
    (* internals: list block; *)
    (* internals: block -> Prop; *)
    (* main_fptr: block; *)
    (* Note: "internals" is not enough! A ModSemPair should be able to specify which SimMem it relys. *)
    skenv: SkEnv.t;
    skenv_link: SkEnv.t;
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

    at_external_dtm: forall
        st args0 args1
        (AT0: at_external st args0)
        (AT1: at_external st args1)
      ,
        args0 = args1
    ;

    final_frame_dtm: forall
        st retv0 retv1
        (FINAL0: final_frame st retv0)
        (FINAL1: final_frame st retv1)
      ,
        retv0 = retv1
    ;
    (* final_frame_dtm: forall *)
    (*     rs_init st rs_ret0 m_ret0 rs_ret1 m_ret1 *)
    (*     (FINAL0: final_frame rs_init st rs_ret0 m_ret0) *)
    (*     (FINAL1: final_frame rs_init st rs_ret1 m_ret1) *)
    (*   , *)
    (*     rs_ret0 = rs_ret1 /\ m_ret0 = m_ret1 *)
    (* ; *)
    after_external_dtm: forall
        st_call retv st0 st1
        (AFTER0: after_external st_call retv st0)
        (AFTER0: after_external st_call retv st1)
      ,
        st0 = st1
    ;


    is_call (st0: state): Prop := exists args, at_external st0 args;
    is_step (st0: state): Prop := exists tr st1, step skenv_link globalenv st0 tr st1;
    is_return (st0: state): Prop := exists retv, final_frame st0 retv;
      (* exists rs_init rs_ret m_ret, final_frame rs_init st0 rs_ret m_ret; *)
    (* Note: "forall" or "exists" for rs_init? *)
    (* "forall" -> easy for opt/hard for meta *)
    (* "exists" -> hard for opt/easy for meta *)
    (* I think "exists" is OK here. *)
    (* We can think of something like "forall rs_init (FUTURE: st0 is future of rs_init)", but is overkill. *)

    call_step_disjoint: is_call /1\ is_step <1= bot1;
    step_return_disjoint: is_step /1\ is_return <1= bot1;
    call_return_disjoint: is_call /1\ is_return <1= bot1;
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

  Definition to_semantics (ms: t) :=
    (Semantics_gen ms.(step) bot1 bot2 ms.(globalenv) ms.(skenv_link))
  .

End ModSem.

Hint Unfold ModSem.is_call ModSem.is_step ModSem.is_return.

Coercion ModSem.to_semantics: ModSem.t >-> semantics.
(* I want to use definitions like "Star" or "determinate_at" *)
