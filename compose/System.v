Require Import EventsC.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep Simulation.
Require Import CoqlibC.

Require Import Mod ModSem Skeleton.

Set Implicit Arguments.

Local Obligation Tactic := ii; des; ss; all_prop_inv; ss.



Section SYSMODSEM.

  Variable sk_link: Sk.t.
  (* Let skenv_link := Sk.load_skenv sk_link. *)
  Variable skenv_link: SkEnv.t.

  Definition genvtype: Type := SkEnv.t.

  Definition globalenv: genvtype := skenv_link.

  Definition skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.invert sk_link).

  Inductive state: Type :=
  | Callstate
      (fptr: val)
      (vs: list val)
      (m: mem)
  | Returnstate
      (v: val)
      (m: mem).

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  | step_intro
      ef fptr vs m0 v m1 tr
      (FPTR: (Genv.find_funct ge) fptr = Some (External ef))
      (EXTCALL: external_call ef ge vs m0 tr v m1):
      step se ge (Callstate fptr vs m0) tr (Returnstate v m1).

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fptr vs m
      (CSTYLE: args = Args.Cstyle fptr vs m)
    :
      initial_frame args (Callstate fptr vs m).

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro v m :
      final_frame (Returnstate v m) (Retv.Cstyle v m).

  Program Definition modsem: ModSem.t := {|
    ModSem.state := state;
    ModSem.genvtype := genvtype;
    ModSem.step := step;
    ModSem.at_external := bot2;
    ModSem.initial_frame := initial_frame;
    ModSem.final_frame := final_frame;
    ModSem.after_external := bot3;
    ModSem.globalenv:= globalenv;
    ModSem.skenv := skenv;
    ModSem.skenv_link := skenv_link;
  |}.

  Hypothesis (LOAD: Sk.load_skenv sk_link = skenv_link).

  Lemma modsem_receptive st:receptive_at modsem st.
  Proof.
    econs; ii; ss.
    - inv H. exploit external_call_receptive; eauto. { unfold globalenv. rewrite <- LOAD; eauto. } i; des.
      esplits; et. econs; et.
    - unfold globalenv, skenv in *. inv H. eapply external_call_trace_length; et.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; ii; ss.
    - unfold globalenv in *. inv H; inv H0. clarify.
      determ_tac external_call_match_traces.
      esplits; et.
      i; clarify.
      determ_tac external_call_deterministic.
    - unfold globalenv, skenv in *. inv H. eapply external_call_trace_length; et.
  Qed.

End SYSMODSEM.

Program Definition module (sk_link: Sk.t): Mod.t :=
  {| Mod.data := unit; Mod.get_sk := fun _ => Sk.invert sk_link;
     Mod.get_modsem := fun skenv_link _ => @modsem sk_link skenv_link; |}.
