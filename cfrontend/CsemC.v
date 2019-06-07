Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC Events Memory Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
(** newly added **)
Require Export Simulation Csem CopC Ctypes Ctyping Csyntax.
Require Import Skeleton Mod ModSem.
Require Import AsmregsC CtypesC.
Require Import Conventions.
Require Import CtypingC.

Set Implicit Arguments.




Definition is_call_cont_strong (k0: cont): Prop :=
  match k0 with
  | Kcall _ _ _ _ _ => True
  | _ => False
  end
.

(* copied from Cshmgen *)
Definition signature_of_function (fd: function) :=
  {| sig_args := map typ_of_type (map snd (fn_params fd));
     sig_res  := opttyp_of_type (fn_return fd);
     sig_cc   := fn_callconv fd |}.

Definition get_mem (st: state): option mem :=
  match st with
  | State _ _ _ _ m0 => Some m0
  | ExprState _ _ _ _ m0 => Some m0
  | Callstate _ _ _ _ m0 => Some m0
  | Returnstate _ _ m0 => Some m0
  | Stuckstate => None
  end
.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  (* Set Printing All. *)
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(CSk.of_program signature_of_function).
  Let ce_ge: composite_env := prog_comp_env p.
  Let ge_ge: Genv.t fundef type := SkEnv.revive skenv p.
  Let ge: genv := Build_genv ge_ge ce_ge.

  Inductive at_external : state -> Args.t -> Prop :=
  | at_external_intro
      fptr_arg vs_arg targs tres cconv k0 m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd
                        /\ signature_of_type targs tres cconv = SkEnv.get_sig skd)
      (CALL: is_call_cont_strong k0)
    (* how can i check sg_args and tyf are same type? *)
    (* typ_of_type function is a projection type to typ. it delete some info *)
    :
      at_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k0 m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd tyf
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (TYPE: type_of_fundef (Internal fd) = tyf) (* TODO: rename this into sig *)
      (TYP: typecheck args.(Args.vs) (type_of_params (fn_params fd)))
    :
      initial_frame args
                    (Callstate args.(Args.fptr) tyf args.(Args.vs) Kstop args.(Args.m))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      v_ret m_ret
      (* (CONT: forall f e C ty k', k <> Kcall f e C ty k') *)
    :
      final_frame (Returnstate v_ret Kstop m_ret) (Retv.mk v_ret m_ret)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      fptr_arg vs_arg m_arg
      k retv tv
      (* tyf *)
      targs tres cconv
      (TYP: typify_c retv.(Retv.v) tres tv)
    :
      after_external (Callstate fptr_arg (Tfunction targs tres cconv) vs_arg k m_arg)
                     retv
                     (Returnstate tv k retv.(Retv.m))
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify. des.
    f_equal.
    determ_tac typify_c_dtm.
  Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. inv H.
                   inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once. inv H. inv H. Qed.
                   (* specialize (CONT f e C ty k0). clarify. Qed. *)
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Ltac inv_single_events :=
    repeat
      match goal with
      | [H: _ |- _ ] => try (exploit external_call_trace_length; eauto; check_safe; intro T; des); inv H; ss; try xomega
      end.
  
  Lemma single_events_at
        st
    :
      single_events_at modsem st
  .
  Proof.
    ii. inv H.
    - inv H0; ss; try xomega. clear - H. inv_single_events.
    - inv_single_events.
  Qed.

End MODSEM.

Section MODULE.

  Variable p: program.

  Program Definition module: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := CSk.of_program signature_of_function ;
      Mod.get_modsem := modsem;
    |}
  .

End MODULE.


(* Definition geof (skenv_link: SkEnv.t) (cp: program): genv := *)
(*   (Build_genv (revive (SkEnv.project skenv_link (defs cp)) cp) cp.(prog_comp_env)) *)
(* . *)
(* Hint Unfold geof. *)


Inductive typechecked (builtins: list (ident * globdef (Ctypes.fundef function) type)) (p: program): Prop :=
| typechecked_intro
    (TYPCHECK: typecheck_program p = Errors.OK p)
    (* this can be executed and checked. *)
    (WT_EXTERNAL: forall se id ef args res cc vargs m t vres m'
      ,
        In (id, Gfun (External ef args res cc)) p.(prog_defs) ->
        external_call ef se vargs m t vres m' ->
        wt_retval vres res)
    (* Introduced as "WT_EXTERNAL" in Ctyping.v (of original CompCert).
       This is a consequence of using "external_call", which takes IR type and not C type, in C language.
       This can be removed if we use better semantics/axiom for high-level (including C) languages.
       (current Axiom "external_call_well_typed" says about IR type only)
     *)
    (WF: Sk.wf (module p))
    (* this property is already checked by the compiler, though they are not in Coq side *)
    (BINCL: incl builtins p.(prog_defs))
    (BCOMPLETE: forall
        id fd
        (IN: In (id, (Gfun fd)) p.(prog_defs))
        (BUILTIN: ~ is_external_fd fd)
      ,
        In (id, Gfun fd) builtins)
    (* The sum of the sizes of the function parameters must be less than INT_MAX. *)
    (WFPARAM: forall
        id fd
        (IN: In (id, (Gfun (Internal fd))) p.(prog_defs))
      ,
          4 * size_arguments_64 (typlist_of_typelist (type_of_params (fn_params fd))) 0 0 0 <= Ptrofs.max_unsigned
)

.