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
(*       (LE: Sound.lift su su_lifted) *)
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


Section PRSV.

Context `{SU: Sound.class}.

Variable ms: ModSem.t.

Inductive local_preservation (sound_state: Sound.t -> mem -> ms.(state) -> Prop): Prop :=
| local_preservation_intro
    (INIT: forall
        su_init args st_init
        (SUARG: Sound.args su_init args)
        (SKENV: Sound.skenv su_init args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        <<SUST: sound_state su_init args.(Args.get_m) st_init>>)
    (STEP: forall
        m_arg su0 st0 tr st1
        (SUST: sound_state su0 m_arg st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        <<SUST: sound_state su0 m_arg st1>>)
    (CALL: forall
        m_arg su0 st0 args
        (SUST: sound_state su0 m_arg st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        (* (<<ARGS: su0.(Sound.args) args>>) /\ *)
        <<MLE: Sound.mle su0 m_arg args.(Args.get_m)>> /\
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: Sound.lepriv su0 su_gr>>) /\
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              (* (<<SUST: sound_state su0 args.(Args.m) st1>>)>>)) *)
              (<<SUST: sound_state su0 m_arg st1>>)>>))
    (RET: forall
        m_arg su0 st0 retv
        (SUST: sound_state su0 m_arg st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) m_arg retv.(Retv.get_m)>>)
.

(* It does not need to show "mle". *)
Inductive local_preservation_noguarantee (sound_state: Sound.t -> mem -> ms.(state) -> Prop): Prop :=
| local_preservation_noguarantee_intro
    (INIT: forall
        su_init args st_init
        (SUARG: Sound.args su_init args)
        (SKENV: Sound.skenv su_init args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        <<SUST: sound_state su_init args.(Args.get_m) st_init>>)
    (STEP: forall
        m_arg su0 st0 tr st1
        (SUST: sound_state su0 m_arg st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        <<SUST: sound_state su0 m_arg st1>>)
    (CALL: forall
        m_arg su0 st0 args
        (SUST: sound_state su0 m_arg st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        (* (<<ARGS: su0.(Sound.args) args>>) /\ *)
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: Sound.lepriv su0 su_gr>>) /\
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              (* (<<SUST: sound_state su0 args.(Args.get_m) st1>>)>>)) *)
              (<<SUST: sound_state su0 m_arg st1>>)>>))
.

Lemma local_preservation_noguarantee_weak
  :
    <<INCL: local_preservation <1= local_preservation_noguarantee>>
.
Proof.
  ii. inv PR. econs; eauto.
  - ii; ss. exploit CALL; eauto. i; des. esplits; eauto.
  (* - ii. exploit RET; eauto. i; des. esplits; eauto. *)
Qed.

Variable get_mem: ms.(ModSem.state) -> mem.

(* "strong_horizontal" without "lift" *)
Inductive local_preservation_standard (sound_state: Sound.t -> ms.(state) -> Prop): Prop :=
| local_preservation_standard_intro
    (INIT: forall
        su_arg args st_init
        (SUARG: Sound.args su_arg args)
        (SKENV: Sound.skenv su_arg args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        exists su_init, (<<LE: Sound.hle su_arg su_init>>) /\
                        (<<SUST: sound_state su_init st_init>>)
                        /\ (<<MLE: su_init.(Sound.mle) args.(Args.get_m) st_init.(get_mem)>>))
    (STEP: forall
        su0 st0 tr st1
        (SUST: sound_state su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        (* <<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>) *)
        exists su1, <<LE: Sound.hle su0 su1>> /\ <<SUST: sound_state su1 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)
    (CALL: forall
        su0 st0 args
        (SUST: sound_state su0 st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        <<MLE: Sound.mle su0 st0.(get_mem) args.(Args.get_m)>> /\
        (* (exists su_lifted, <<LE: Sound.lift su0 su_lifted>> /\ <<ARGS: su_lifted.(Sound.args) args>>) /\ *)
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: Sound.lepriv su0 su_gr>>) /\
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              exists su1,
                <<LE: Sound.hle su0 su1>> /\
              (* (<<SUST: sound_state su0 args.(Args.get_m) st1>>)>>)) *)
              (* (<<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)>>)) *)
              (<<SUST: sound_state su1 st1>> /\ <<MLE: su0.(Sound.mle) args.(Args.get_m) st1.(get_mem)>>)>>))
    (RET: forall
        su0 st0 retv
        (SUST: sound_state su0 st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) retv.(Retv.get_m)>>)
.

Theorem local_preservation_standard_spec
        sound_state
        (PRSV: local_preservation_standard sound_state)
  :
    <<PRSV: local_preservation (fun su m_init st =>
                                  <<MLE: su.(Sound.mle) m_init st.(get_mem)>> /\
                                  <<WF: Sound.wf su>> /\
                                  exists su_h,
                                    <<LE: Sound.hle su su_h>> /\ sound_state su_h st)>>
.
Proof.
  inv PRSV.
  econs; eauto.
  - ii. exploit INIT; eauto. i; des. r in SUARG. des_ifs; des; esplits; eauto; eapply Sound.hle_mle; eauto.
  - ii. des. exploit STEP; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
    + etrans; eauto.
  - ii. des. exploit CALL; eauto. i; des.
    (* exploit Sound.get_greatest_hle; eauto. intro GRH. des. *)
    (* assert(LE1: Sound.lift su_h su_gr). *)
    (* { eapply Sound.greatest_adq; eauto. } *)
    esplits; eauto.
    { etrans; eauto.
      + eapply Sound.hle_mle; eauto.
    }
    { etrans; eauto. eapply Sound.hle_lepriv; eauto. }
    ii. exploit K; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
      etrans; eauto.
    + etrans; eauto.
  - ii; des. exploit RET; eauto. i; des. esplits; try apply RETV; eauto.
    + etrans; eauto.
    + etrans; eauto. eapply Sound.hle_mle; eauto.
Qed.

Variable lift: Sound.t -> Sound.t -> Prop.
(* Hypothesis lift_spec: forall su0 su1 m0 m1 (MLE: Sound.mle su1 m0 m1) (LE: lift su0 su1), <<MLE: Sound.mle su0 m0 m1>>. *)
(* Hypothesis lift_lepriv: lift <2= Sound.lepriv. *)

Inductive local_preservation_strong (sound_state: Sound.t -> ms.(state) -> Prop): Prop :=
| local_preservation_strong_intro
    (LIFTSPEC: forall su0 su1 m0 m1 (MLE: Sound.mle su1 m0 m1) (LE: lift su0 su1), <<MLE: Sound.mle su0 m0 m1>>)
    (LIFTPRIV: lift <2= Sound.lepriv)
    (INIT: forall
        su_init args st_init
        (SUARG: Sound.args su_init args)
        (SKENV: Sound.skenv su_init args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        <<SUST: sound_state su_init st_init>> /\ <<MLE: su_init.(Sound.mle) args.(Args.get_m) st_init.(get_mem)>>)
    (STEP: forall
        su0 st0 tr st1
        (SKENV: Sound.skenv su0 st0.(get_mem) ms.(ModSem.skenv))
        (SUST: sound_state su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        <<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)
    (CALL: forall
        su0 st0 args
        (SKENV: Sound.skenv su0 st0.(get_mem) ms.(ModSem.skenv))
        (SUST: sound_state su0 st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        <<MLE: Sound.mle su0 st0.(get_mem) args.(Args.get_m)>> /\
        <<WF: Sound.wf su0>> /\
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: exists su_imd, Sound.hle su0 su_imd /\ lift su_imd su_gr>>) /\
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              (* (<<SUST: sound_state su0 args.(Args.get_m) st1>>)>>)) *)
              (* (<<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)>>)) *)
              (<<SUST: forall
                 (MLE: su0.(Sound.mle) retv.(Retv.get_m) st1.(get_mem))
                 (SKENV: Sound.skenv su0 st1.(get_mem) ms.(ModSem.skenv)),
                 sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) retv.(Retv.get_m) st1.(get_mem)>>)>>))
    (RET: forall
        su0 st0 retv
        (SKENV: Sound.skenv su0 st0.(get_mem) ms.(ModSem.skenv))
        (SUST: sound_state su0 st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) retv.(Retv.get_m)>>)
.

Theorem local_preservation_strong_spec
        sound_state
        (PRSV: local_preservation_strong sound_state)
  :
    <<PRSV: local_preservation (fun su m_init st => sound_state su st
                                                    /\ su.(Sound.skenv) st.(get_mem) ms.(ModSem.skenv)
                                                    /\ su.(Sound.mle) m_init st.(get_mem))>>
.
Proof.
  inv PRSV.
  econs; eauto.
  - i. exploit INIT; et. i; des. esplits; et. eapply Sound.skenv_mle; et.
  - ii. des. exploit STEP; eauto. i; des. esplits; eauto.
    { eapply Sound.skenv_mle; et. }
    etrans; eauto.
  - ii. des. exploit CALL; eauto. i; des. esplits; eauto.
    { etrans; eauto. }
    { etrans; eauto. eapply Sound.hle_lepriv; et. }
    ii. exploit K; try apply RETV; eauto.
    i; des.
    assert(SKENV: Sound.skenv su0 (get_mem st1) (ModSem.skenv ms)).
    { eapply Sound.skenv_mle; et. etrans; et. etrans; et.
      eapply Sound.hle_mle; [eapply LIFTSPEC; eauto|..]; ss.
    }
    esplits; eauto.
    etrans; eauto.
    etrans; eauto. etrans; eauto. eapply Sound.hle_mle; [eapply LIFTSPEC; eauto|..]; ss.
  - ii; des. exploit RET; eauto. i; des. esplits; eauto.
    etrans; eauto.
Qed.

Inductive local_preservation_strong_horizontal (sound_state: Sound.t -> ms.(state) -> Prop): Prop :=
| local_preservation_strong_horizontal_intro
    (LIFTSPEC: forall su0 su1 m0 m1 (MLE: Sound.mle su1 m0 m1) (LE: lift su0 su1), <<MLE: Sound.mle su0 m0 m1>>)
    (LIFTPRIV: lift <2= Sound.lepriv)
    (INIT: forall
        su_arg args st_init
        (SUARG: Sound.args su_arg args)
        (SKENV: Sound.skenv su_arg args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        exists su_init, (<<LE: Sound.hle su_arg su_init>>) /\
                        (<<SUST: sound_state su_init st_init>>)
                        /\ (<<MLE: su_init.(Sound.mle) args.(Args.get_m) st_init.(get_mem)>>))
    (STEP: forall
        su0 st0 tr st1
        (SUST: sound_state su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        (* <<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>) *)
        exists su1, <<LE: Sound.hle su0 su1>> /\ <<SUST: sound_state su1 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)
    (CALL: forall
        su0 st0 args
        (SUST: sound_state su0 st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        <<MLE: Sound.mle su0 st0.(get_mem) args.(Args.get_m)>> /\
        (* (exists su_lifted, <<LE: Sound.lift su0 su_lifted>> /\ <<ARGS: su_lifted.(Sound.args) args>>) /\ *)
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: lift su0 su_gr>>) /\
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              exists su1,
                <<LE: Sound.hle su0 su1>> /\
              (* (<<SUST: sound_state su0 args.(Args.get_m) st1>>)>>)) *)
              (* (<<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)>>)) *)
              (<<SUST: sound_state su1 st1>> /\ <<MLE: su0.(Sound.mle) retv.(Retv.get_m) st1.(get_mem)>>)>>))
    (RET: forall
        su0 st0 retv
        (SUST: sound_state su0 st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) retv.(Retv.get_m)>>)
.

Theorem local_preservation_strong_horizontal_spec
        sound_state
        (PRSV: local_preservation_strong_horizontal sound_state)
  :
    <<PRSV: local_preservation (fun su m_init st =>
                                  <<MLE: su.(Sound.mle) m_init st.(get_mem)>> /\
                                  <<WF: Sound.wf su>> /\
                                  exists su_h,
                                    <<LE: Sound.hle su su_h>> /\ sound_state su_h st)>>
.
Proof.
  inv PRSV.
  econs; eauto.
  - ii. exploit INIT; eauto. i; des. r in SUARG. des_ifs; des; esplits; eauto; eapply Sound.hle_mle; eauto.
  - ii. des. exploit STEP; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
    + etrans; eauto.
  - ii. des. exploit CALL; eauto. i; des.
    (* exploit Sound.get_greatest_hle; eauto. intro GRH. des. *)
    (* assert(LE1: Sound.lift su_h su_gr). *)
    (* { eapply Sound.greatest_adq; eauto. } *)
    esplits; eauto.
    { etrans; eauto.
      + eapply Sound.hle_mle; eauto.
    }
    { etrans; eauto. eapply Sound.hle_lepriv; eauto. }
    ii. exploit K; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
      etrans; eauto.
      etrans; eauto.
      eapply LIFTSPEC; eauto.
    + etrans; eauto.
  - ii; des. exploit RET; eauto. i; des. esplits; try apply RETV; eauto.
    + etrans; eauto.
    + etrans; eauto. eapply Sound.hle_mle; eauto.
Qed.

Inductive local_preservation_strong_excl (sound_state: Sound.t -> ms.(state) -> Prop): Prop :=
| local_preservation_strong_excl_intro
    (LIFTSPEC: forall su0 su1 m0 m1 (MLE: Sound.mle su1 m0 m1) (LE: lift su0 su1), <<MLE: Sound.mle su0 m0 m1>>)
    (LIFTPRIV: lift <2= Sound.lepriv)
    (has_footprint: ms.(state) -> Sound.t -> mem -> Prop) (mle_excl: ms.(state) -> Sound.t -> mem -> mem -> Prop)
    (FOOTEXCL: forall
        su0 st_at m0 m1 m2
        (FOOT: has_footprint st_at su0 m0)
        (MLEEXCL: (mle_excl st_at) su0 m1 m2)
        (MLE: su0.(Sound.mle) m0 m1)
      ,
        <<MLE: Sound.mle su0 m0 m2>>)
    (INIT: forall
        su_init args st_init
        (SUARG: Sound.args su_init args)
        (SKENV: Sound.skenv su_init args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        <<SUST: sound_state su_init st_init>> /\ <<MLE: su_init.(Sound.mle) args.(Args.get_m) st_init.(get_mem)>>)
    (STEP: forall
        su0 st0 tr st1
        (SUST: sound_state su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        <<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)
    (CALL: forall
        su0 st0 args
        (SUST: sound_state su0 st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        <<MLE: Sound.mle su0 st0.(get_mem) args.(Args.get_m)>> /\
        <<FOOT: has_footprint st0 su0 st0.(get_mem)>> /\
        <<WF: Sound.wf su0>> /\
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: lift su0 su_gr>>) /\
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              (<<SUST: sound_state su0 st1>> /\ <<MLE: (mle_excl st0) su0 retv.(Retv.get_m) st1.(get_mem)>>)>>))
    (RET: forall
        su0 st0 retv
        (SUST: sound_state su0 st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) retv.(Retv.get_m)>>)
.

Theorem local_preservation_strong_excl_spec
        sound_state
        (PRSV: local_preservation_strong_excl sound_state)
  :
    <<PRSV: local_preservation (fun su m_init st => sound_state su st /\ su.(Sound.mle) m_init st.(get_mem))>>
.
Proof.
  inv PRSV.
  econs; eauto.
  - ii. des. exploit STEP; eauto. i; des. esplits; eauto. etrans; eauto.
  - ii. des. exploit CALL; eauto. i; des. esplits; eauto.
    { etrans; eauto. }
    ii. exploit K; eauto. i; des. esplits; eauto.
    etrans; eauto.
    eapply FOOTEXCL; try apply MLE1; eauto.
    { etrans; eauto. eapply LIFTSPEC; eauto. }
  - ii; des. exploit RET; eauto. i; des. esplits; eauto.
    etrans; eauto.
Qed.

Inductive local_preservation_strong_horizontal_excl (sound_state: Sound.t -> ms.(state) -> Prop): Prop :=
| local_preservation_strong_horizontal_excl_intro
    (LIFTSPEC: forall su0 su1 m0 m1 (MLE: Sound.mle su1 m0 m1) (LE: lift su0 su1), <<MLE: Sound.mle su0 m0 m1>>)
    (LIFTPRIV: lift <2= Sound.lepriv)
    (has_footprint: ms.(state) -> Sound.t -> mem -> Prop) (mle_excl: ms.(state) -> Sound.t -> mem -> mem -> Prop)
    (FOOTEXCL: forall
        su0 st_at m0 m1 m2
        (FOOT: has_footprint st_at su0 m0)
        (MLEEXCL: (mle_excl st_at) su0 m1 m2)
        (MLE: su0.(Sound.mle) m0 m1)
      ,
        <<MLE: Sound.mle su0 m0 m2>>)
    (INIT: forall
        su_arg args st_init
        (SUARG: Sound.args su_arg args)
        (SKENV: Sound.skenv su_arg args.(Args.get_m) ms.(ModSem.skenv))
        (INIT: ms.(ModSem.initial_frame) args st_init)
      ,
        exists su_init, (<<LE: Sound.hle su_arg su_init>>) /\
                        (<<SUST: sound_state su_init st_init>>)
                        /\ (<<MLE: su_init.(Sound.mle) args.(Args.get_m) st_init.(get_mem)>>))
    (STEP: forall
        su0 st0 tr st1
        (SUST: sound_state su0 st0)
        (SAFE: ~ ms.(ModSem.is_call) st0 /\ ~ ms.(ModSem.is_return) st0)
        (STEP: Step ms st0 tr st1)
      ,
        (* <<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>) *)
        exists su1, <<LE: Sound.hle su0 su1>> /\ <<SUST: sound_state su1 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)
    (CALL: forall
        su0 st0 args
        (SUST: sound_state su0 st0)
        (AT: ms.(ModSem.at_external) st0 args)
      ,
        <<MLE: Sound.mle su0 st0.(get_mem) args.(Args.get_m)>> /\
        <<FOOT: has_footprint st0 su0 st0.(get_mem)>> /\
        exists su_gr,
          (<<ARGS: Sound.args su_gr args>>) /\
          (<<LE: lift su0 su_gr>>) /\
          (* (<<GR: Sound.get_greatest su0 args su_gr>>) /\ *)
          (* (<<LE: Sound.lift su0 su_lifted>>) /\ *)
          (* (<<ARGS: su_lifted.(Sound.args) args>>) /\ *)
          (<<K: forall
              su_ret retv st1
              (LE: Sound.hle su_gr su_ret)
              (RETV: su_ret.(Sound.retv) retv)
              (* retv st1 *)
              (* (RETV: su_gr.(Sound.retv) retv) *)
              (MLE: Sound.mle su_gr args.(Args.get_m) retv.(Retv.get_m))
              (AFTER: ms.(ModSem.after_external) st0 retv st1)
            ,
              exists su1,
                <<LE: Sound.hle su0 su1>> /\
              (* (<<SUST: sound_state su0 args.(Args.get_m) st1>>)>>)) *)
              (* (<<SUST: sound_state su0 st1>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) st1.(get_mem)>>)>>)) *)
              (<<SUST: sound_state su1 st1>> /\ <<MLE: (mle_excl st0) su0 retv.(Retv.get_m) st1.(get_mem)>>)>>))
    (RET: forall
        su0 st0 retv
        (SUST: sound_state su0 st0)
        (FINAL: ms.(ModSem.final_frame) st0 retv)
      ,
        exists su_ret, <<LE: Sound.hle su0 su_ret>> /\
        <<RETV: su_ret.(Sound.retv) retv>> /\ <<MLE: su0.(Sound.mle) st0.(get_mem) retv.(Retv.get_m)>>)
.

Theorem local_preservation_strong_horizontal_excl_spec
        sound_state
        (PRSV: local_preservation_strong_horizontal_excl sound_state)
  :
    <<PRSV: local_preservation (fun su m_init st =>
                                  <<MLE: su.(Sound.mle) m_init st.(get_mem)>> /\
                                  <<WF: Sound.wf su>> /\
                                  exists su_h,
                                    <<LE: Sound.hle su su_h>> /\ sound_state su_h st)>>
.
Proof.
  inv PRSV.
  econs; eauto.
  - ii. exploit INIT; eauto. i; des. r in SUARG. des_ifs; des; esplits; eauto; eapply Sound.hle_mle; eauto.
  - ii. des. exploit STEP; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
    + etrans; eauto.
  - ii. des. exploit CALL; eauto. i; des.
    (* exploit Sound.get_greatest_hle; eauto. intro GRH. des. *)
    (* assert(LE1: Sound.lift su_h su_gr). *)
    (* { eapply Sound.greatest_adq; eauto. } *)
    esplits; eauto.
    { etrans; eauto.
      + eapply Sound.hle_mle; eauto.
    }
    { etrans; eauto. eapply Sound.hle_lepriv; eauto. }
    ii. exploit K; eauto. i; des. esplits; try apply SUST; eauto.
    + etrans; eauto.
      eapply Sound.hle_mle; eauto.
      eapply FOOTEXCL; eauto.
      etrans; eauto.
      eapply LIFTSPEC; eauto.
    + etrans; eauto.
  - ii; des. exploit RET; eauto. i; des. esplits; try apply RETV; eauto.
    + etrans; eauto.
    + etrans; eauto. eapply Sound.hle_mle; eauto.
Qed.

End PRSV.



Definition system_sound_state `{SU: Sound.class} (ms: ModSem.t): Sound.t -> mem -> System.state -> Prop :=
  fun su m_arg st =>
    match st with
    | System.Callstate fptr vs m => su.(Sound.args) (Args.Cstyle fptr vs m) /\ su.(Sound.mle) m_arg m
                               /\ su.(Sound.skenv) m_arg ms.(ModSem.skenv)
    | System.Returnstate v m =>
      exists su_ret, Sound.hle su su_ret /\ su_ret.(Sound.retv) (Retv.Cstyle v m) /\ su.(Sound.mle) m_arg m 
      (* su.(Sound.retv) retv /\ su.(Sound.mle) m_arg retv.(Retv.get_m) *)
        /\ su.(Sound.skenv) m ms.(ModSem.skenv)
    end
.

Lemma system_local_preservation
      `{SU: Sound.class}
      skenv
  :
    exists system_sound_state, local_preservation (System.modsem skenv) system_sound_state
.
Proof.
  exists (system_sound_state (System.modsem skenv)).
  econs; ii; ss; eauto.
  - inv INIT. rr. esplits; eauto.
    + refl.
  - inv STEP. ss. inv SUST. des. exploit Sound.system_axiom; try apply EXTCALL; eauto.
    { instantiate (1:= Args.Cstyle _ _ _). ss. }
    { rr. esplits; eauto. }
    { eapply Sound.system_skenv; eauto. eapply Sound.skenv_mle; eauto. }
    { eauto. }
    i; des. r in RETV. ss. des. ss. esplits; eauto.
    + etrans; eauto.
    + eapply Sound.skenv_mle; eauto. etrans; eauto.
  - inv FINAL. ss. des. esplits; eauto.
Qed.

