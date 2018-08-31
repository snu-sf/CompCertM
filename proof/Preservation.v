Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.
Require Import Smallstep.
Require Import ModSem.
Require Import Skeleton SimSymb Ord.
Require Import Sound.

Set Implicit Arguments.



(* Section SOUNDMODSEM. *)

(*   Variables ms: ModSem.t. *)
(*   Context {SU: Sound.class}. *)

(*   Inductive _lprsv (lprsv: mem -> Sound.t -> ms.(ModSem.state) -> Prop) *)
(*             (m_init: mem) (su: Sound.t) (st0: ms.(ModSem.state)): Prop := *)
(*   | lprsv_step *)
(*       (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0) *)
(*       (STEP: forall *)
(*           tr st1 *)
(*           (STEP: Step ms st0 tr st1) *)
(*         , *)
(*           <<SU: lprsv m_init su st1>>) *)
(*   | lprsv_at_external *)
(*       (* (ATEXT: forall *) *)
(*       (*     args *) *)
(*       (*     (AT: ms.(ModSem.at_external) st0 args) *) *)
(*       (*   , *) *)
(*       (*     exists su_lifted, *) *)
(*       (*       (<<ARGS: su_lifted.(Sound.args) args>>) *) *)
(*       (*       /\ (<<K: forall *) *)
(*       (*              retv st1 *) *)
(*       (*              (RETV: su_lifted.(Sound.retv) retv) *) *)
(*       (*              (MLE: Sound.mle su_lifted args.(Args.m) retv.(Retv.m)) *) *)
(*       (*              (AFTER: ms.(ModSem.after_external) st0 retv st1) *) *)
(*       (*            , *) *)
(*       (*              <<SU: lprsv m_init su st1>>>>)) *) *)
(*       su_lifted args *)
(*       (AT: ms.(ModSem.at_external) st0 args) *)
(*       (LE: Sound.le su su_lifted) *)
(*       (ARGS: su_lifted.(Sound.args) args) *)
(*       (K: forall *)
(*           retv st1 *)
(*           (RETV: su_lifted.(Sound.retv) retv) *)
(*           (MLE: Sound.mle su_lifted args.(Args.m) retv.(Retv.m)) *)
(*           (AFTER: ms.(ModSem.after_external) st0 retv st1) *)
(*         , *)
(*           <<SU: lprsv m_init su st1>>) *)
(*   | lprsv_final *)
(*       retv *)
(*       (FINAL: ms.(ModSem.final_frame) st0 retv) *)
(*       (MLE: Sound.mle su m_init retv.(Retv.m)) *)
(*       (RETV: su.(Sound.retv) retv) *)
(*   . *)

(*   Definition lprsv: _ -> _ -> _ -> Prop := paco3 _lprsv bot3. *)

(*   Lemma lprsv_mon: *)
(*     monotone3 _lprsv. *)
(*   Proof. *)
(*     ii. inv IN; eauto. *)
(*     - econs 1; ii; ss; eauto. eapply LE; eauto. eapply STEP; eauto. *)
(*     - econs 2; ii; ss; eauto. *)
(*       (* exploit ATEXT; eauto. i; des. esplits; eauto. ii. hexpl K. *) *)
(*       exploit K; eauto. *)
(*     - econs 3; ii; ss; eauto. *)
(*   Qed. *)

(* End SOUNDMODSEM. *)


Section SOUND.

Context `{SU: Sound.class}.

Inductive local_preservation (ms: ModSem.t) (sound_state: Sound.t -> mem -> ms.(state) -> Prop): Prop :=
| local_preservation_intro
    (INIT: forall
        su_init args st_init
        (SUARG: Sound.args su_init args)
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        <<SUST: sound_state su_init args.(Args.m) st_init>>)
    (STEP: forall
        m_arg su0 st0 tr st1
        (SUST: sound_state m_arg su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        <<SUST: sound_state m_arg su0 st1>>)
    (CALL: forall
        m_arg su0 st0 args
        (SUST: sound_state su0 m_arg st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        (<<ARGS: su0.(Sound.args) args>>) /\
        exists su_gr,
          (<<GR: Sound.get_greatest args su_gr>>) /\
          (* (<<LE: Sound.le su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              retv st1
              (RETV: su_gr.(Sound.retv) retv)
              (MLE: Sound.mle su_gr args.(Args.m) retv.(Retv.m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              (<<SUST: sound_state su0 m_arg st1>>)>>))
    (RET: forall
        m_arg su0 st0 retv
        (SUST: sound_state su0 m_arg st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        <<RETV: su0.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) m_arg retv.(Retv.m)>>)
.

Definition system_sound_state: Sound.t -> mem -> System.state -> Prop :=
  fun su m_arg st =>
    match st with
    | System.Callstate args => su.(Sound.args) args /\ su.(Sound.mle) m_arg args.(Args.m)
    | System.Returnstate retv => su.(Sound.retv) retv /\ su.(Sound.mle) m_arg retv.(Retv.m)
    end
.

Lemma system_local_preservation
      skenv
  :
    exists system_sound_state, local_preservation (System.modsem skenv) system_sound_state
.
Proof.
  exists system_sound_state.
  econs; ii; ss; eauto.
  - inv INIT. inv SUARG. econs; eauto.
    + econs; eauto.
    + refl.
  - inv STEP. ss. inv SUST. des. exploit Sound.system_axiom; try apply H; eauto. i; des. esplits; eauto.
    + econs; eauto.
    + etrans; eauto.
  - inv FINAL. ss.
Qed.

End SOUND.
