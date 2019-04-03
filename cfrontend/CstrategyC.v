Require Import Axioms.
Require Import Classical.
Require Import CoqlibC.
Require Import Errors.
Require Import MapsC.
Require Import IntegersC.
Require Import Floats.
Require Import ValuesC.
Require Import ASTC.
Require Import MemoryC.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import CsemC.
Require Import sflib.
(** newly added **)
Require Export Simulation Cstrategy CopC Ctypes Ctyping Csyntax Cexec.
Require Import Skeleton Mod ModSem.
Require Import CtypesC.
Require Import Conventions.
Require Import CtypingC.

Set Implicit Arguments.




(* copied from Cshmgen *)
Definition signature_of_function (fd: function) :=
  {| sig_args := map typ_of_type (map snd (fn_params fd));
     sig_res  := opttyp_of_type (fn_return fd);
     sig_cc   := fn_callconv fd |}.

Section CSTREXTRA.

  Definition is_external (ge: genv) (s:state) : Prop :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | External ef targs tres cconv => is_external_ef ef
        | _ => False
        end
      | None => False
      end
    | _ => False
    end
  .

  Definition internal_function_state (ge: genv) (s:state) : Prop :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | Internal func => type_of_fundef f = Tfunction Tnil type_int32s cc_default
        | _ => False
        end
      | None => False
      end
    | _ => False
    end
  .

  Definition external_state (ge: genv) (s:state) : bool :=
    match s with
    | Callstate fptr ty args k m  =>
      match Genv.find_funct ge fptr with
      | Some f =>
        match f with
        | External ef targs tres cconv => is_external_ef ef
        | _ => false
        end
      | None => false
      end
    | _ => false
    end
  .

End CSTREXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)


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
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. inv H. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once. inv H. inv H. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.

  Hypothesis (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function p)).
  Hypothesis (WF: SkEnv.wf skenv_link).

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply CSkEnv.project_revive_no_external; ss; eauto.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. admit "this should hold". Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. admit "this should hold". Qed.

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











(** newly added **)
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.

Set Implicit Arguments.








Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog: program.
Let md_src: Mod.t := (CsemC.module prog).
Let md_tgt: Mod.t := (Top.module prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WFSRC: SkEnv.wf skenv_link).
Hypothesis (WFTGT: SkEnv.wf skenv_link).
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src.(Mod.modsem) skenv_link) (md_tgt.(Mod.modsem) skenv_link) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Csem.state) (st_tgt0: Csem.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: st_src0 = st_tgt0)
    (MCOMPAT: st_src0.(get_mem) = Some sm0.(SimMem.src) \/ st_src0.(get_mem) = None)
    (MWF: SimMem.wf sm0)
.

Require Import Classes.Equivalence. Ltac inv H := inversion H; clear H; subst *.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS. ss. subst *. destruct args_src, args_tgt; ss. subst *.
    inv INITTGT.
    eexists. eexists (SimMemId.mk _ _).
    esplits; eauto; cycle 1.
    + econs; ss; eauto. ss. eauto.
    + econs; eauto; ss.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    destruct args_src, args_tgt; ss. subst *.
    inv TYP.
    esplits; eauto. econs; eauto. ss.
  - (* call wf *)
    inv MATCH; ss.
  - (* call fsim *)
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. ss. des; ss. clarify.
    folder.
    eexists _, (SimMemId.mk _ _).
    esplits; ss; eauto.
    + econs; eauto.
  - (* after fsim *)
    inv AFTERSRC.
    inv SIMRET. ss. exists sm_ret. destruct sm_ret; ss. clarify.
    inv MATCH; ss. des; ss. clarify. destruct retv_src, retv_tgt; ss. clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
  - (* final fsim *)
    inv MATCH. inv FINALSRC. ss. des; ss. clarify.
    eexists (SimMemId.mk _ _). esplits; ss; eauto.
  - esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@step_simulation prog skenv_link_src skenv_link_tgt); eauto.
    { inv SIMSKENV. ss. rr in SIMSKELINK. clarify. }
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate; et.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy - see DeadcodeproofC".
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.

