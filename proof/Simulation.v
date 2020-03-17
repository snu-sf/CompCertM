Require Export Smallstep.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Integers.
Require Import Events.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import CoqlibC.
Require Import Axioms.
Require Import Relations.
Require Import Wellfounded.
Require Import Program.Equality.

Set Implicit Arguments.



(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Lemma well_founded_clos_trans
      index
      (order: index -> index -> Prop)
      (WF: well_founded order):
    <<WF: well_founded (clos_trans index order)>>.
Proof.
  hnf in WF. hnf. i. eapply Acc_clos_trans. eauto.
Qed.

Lemma clos_t_rt:
  forall (A : Type) (R : relation A) (x y z : A),
  clos_trans A R x y -> clos_refl_trans A R y z -> clos_trans A R x z.
Proof.
  i. induction H0; ss.
  - eapply t_trans; eauto.
  - eapply IHclos_refl_trans2; eauto.
Qed.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

(* DO NOT USE THIS MODULE DIRECTLY. THIS IS ONLY FOR PROVING "bsim => compcert bsim". *)
Module NOSTUTTER.

Section BACKWARD_SIM.

  Variables L1 L2: semantics.
  Variable index: Type.
  Variable order: index -> index -> Prop.

  Inductive _bsim bsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | bsim_intro
      (FINAL: forall retv
          (FINALTGT: final_state L2 st_tgt0 retv)
          (SAFESRC: safe L1 st_src0),
          exists st_src1, <<STEPSRC: Star L1 st_src0 E0 st_src1>> /\
                                     <<FINALSRC: final_state L1 st_src1 retv>>)
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step L2 st_tgt0 tr st_tgt1)
          (SAFESRC: safe L1 st_src0),
          exists i1 st_src1,
            (<<PLUS: Plus L1 st_src0 tr st_src1>> \/ <<STAR: Star L1 st_src0 tr st_src1 /\ order i1 i0>>)
            /\ <<BSIM: bsim i1 st_src1 st_tgt1>>)
      (PROGRESS: forall
         (SAFESRC: safe L1 st_src0),
          <<FINAL: exists retv, final_state L2 st_tgt0 retv>> \/
          <<STEP: exists tr st_tgt1, Step L2 st_tgt0 tr st_tgt1>>).

  Definition bsim: _ -> _ -> _ -> Prop := paco3 _bsim bot3.

  Lemma bsim_mon: monotone3 _bsim.
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. esplits; eauto.
  Qed.

End BACKWARD_SIM.

Hint Unfold bsim.
Hint Resolve bsim_mon: paco.

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop): Prop := {
    bsim_order_wf: <<WF: well_founded order>>;
    bsim_initial_states_exist: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>;
    bsim_match_initial_states: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt),
      exists i0 st_init_src, <<INITSRC: initial_state L1 st_init_src>> /\
                             <<BSIM: bsim L1 L2 order i0 st_init_src st_init_tgt>>;
}.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (props: bsim_properties L1 L2 index order).

Arguments Backward_simulation {L1 L2 index} order props.



Lemma to_compcert_backward_simulation
      L1 L2
      (BSIM: backward_simulation L1 L2):
    <<BSIM: Smallstep.backward_simulation L1 L2>>.
Proof.
  inv BSIM. inv props.
  econs. econs; eauto.
  - i. exploit bsim_initial_states_exist0; eauto. exploit bsim_match_initial_states0; eauto.
  - i. punfold H. inv H. exploit FINAL; eauto.
  - (* progress *)
    i. rename H into BSIM. rename H0 into SAFE. punfold BSIM. inv BSIM. exploit PROGRESS; eauto.
  - i. rename H into STEP. rename H0 into BSIM. rename H1 into SAFE.
    punfold BSIM. inv BSIM. exploit STEP0; eauto. i; des_safe. esplits; eauto. pclearbot. ss.
Qed.

End NOSTUTTER.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Section BACKWARD_SIM.

  Variables L1 L2: semantics.
  Variable index: Type.
  Variable order: index -> index -> Prop.

  Inductive bsim_step bsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)): Prop :=
  | bsim_step_step
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step L2 st_tgt0 tr st_tgt1),
          exists i1 st_src1,
            (<<PLUS: Plus L1 st_src0 tr st_src1>> \/ <<STAR: Star L1 st_src0 tr st_src1 /\ order i1 i0>>)
            /\ <<BSIM: bsim i1 st_src1 st_tgt1>>)
      (PROGRESS: forall
         (SAFESRC: safe L1 st_src0),
          <<FINAL: exists retv, final_state L2 st_tgt0 retv>> \/
          <<STEP: exists tr st_tgt1, Step L2 st_tgt0 tr st_tgt1>>)
      (FINAL: forall retv
          (FINALTGT: final_state L2 st_tgt0 retv),
          exists st_src1, <<STEPSRC: Star L1 st_src0 E0 st_src1>> /\
                                     <<FINALSRC: final_state L1 st_src1 retv>>)
  | bsim_step_stutter
      i1 st_src1
      (STAR: Star L1 st_src0 nil st_src1 /\ order i1 i0)
      (BSIM: bsim i1 st_src1 st_tgt0).

  Inductive _bsim bsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | bsim_intro
      (STEP: forall
          (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step bsim i0 st_src0 st_tgt0>>).

  Definition bsim: _ -> _ -> _ -> Prop := paco3 _bsim bot3.

  Lemma bsim_mon: monotone3 _bsim.
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - eleft; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - eright; eauto.
  Qed.

End BACKWARD_SIM.

Hint Unfold bsim.
Hint Resolve bsim_mon: paco.

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop): Prop := {
    bsim_order_wf: <<WF: well_founded order>>;
    bsim_initial_states_exist: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>;
    bsim_match_initial_states: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt),
      exists i0 st_init_src, <<INITSRC: initial_state L1 st_init_src>> /\
                             <<BSIM: bsim L1 L2 order i0 st_init_src st_init_tgt>>;
}.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (props: bsim_properties L1 L2 index order).

Arguments Backward_simulation {L1 L2 index} order props.



Lemma bsim_to_nostutter_bsim
      (L1 L2: semantics)
      index i0 st_src0 st_tgt0
      (ord: index -> index -> Prop)
      (WF: well_founded ord)
      (BSIM: bsim L1 L2 ord i0 st_src0 st_tgt0):
    <<BSIM: NOSTUTTER.bsim L1 L2 (clos_trans _ ord) i0 st_src0 st_tgt0>>.
Proof.
  red. generalize dependent i0. generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold. econs; eauto.
  - generalize dependent BSIM. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH. clear i0.
    punfold BSIM. inv BSIM. hexploit1 STEP; eauto. inv STEP.
    + eapply FINAL; eauto.
    + pclearbot. des. exploit IH; eauto. { eapply star_safe; eauto. } i; des. esplits; try apply FINALSRC.
      eapply star_trans; eauto.
  - generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH.
    punfold BSIM. inv BSIM. exploit STEP; eauto. i; des_safe. inv H.
    + exploit STEP0; eauto. i; des_safe. pclearbot. esplits; eauto. des.
      * left; ss.
      * right; ss. esplits; eauto.
    + pclearbot. des. specialize (IH _ STAR0).
      exploit IH; eauto.
      { ii. eapply SAFESRC. eapply star_trans; eauto. }
      i; des_safe. esplits; eauto. des.
      * left. eapply star_plus_trans; eauto.
      * right. esplits; eauto. eapply star_trans; eauto.
        apply clos_trans_tn1_iff. econs 2; eauto. apply clos_trans_tn1_iff. ss.
  - generalize dependent BSIM. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH. clear i0.
    punfold BSIM. inv BSIM. specialize (STEP SAFESRC). inv STEP.
    + exploit PROGRESS; eauto.
    + des. pclearbot. exploit IH; eauto. eapply star_safe; eauto.
Qed.

Lemma backward_to_nostutter_backward_simulation
      L1 L2
      (BS: backward_simulation L1 L2):
    <<BS: NOSTUTTER.backward_simulation L1 L2>>.
Proof.
  inv BS. inv props. econs; eauto.
  instantiate (1:= (clos_trans _ order)). econs; eauto.
  { eapply well_founded_clos_trans. eauto. }
  i. exploit bsim_match_initial_states0; eauto. i; des.
  esplits; eauto. eapply bsim_to_nostutter_bsim; eauto.
Qed.

Lemma backward_to_compcert_backward_simulation
      L1 L2
      (BSIM: backward_simulation L1 L2):
    <<BSIM: Smallstep.backward_simulation L1 L2>>
.
Proof.
  eapply NOSTUTTER.to_compcert_backward_simulation; eauto.
  eapply backward_to_nostutter_backward_simulation; eauto.
Qed.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Definition single_events_at (L: semantics) (s:L.(state)) : Prop :=
  forall t s', Step L s t s' -> (length t <= 1)%nat.

(* These "strict_determinate" definitions are merely for convenience. *)
Record strict_determinate_at (L: semantics) (s:L.(state)) : Prop :=
  Strict_determinate_at {
      ssd_determ_at: forall t1 s1 t2 s2
        (STEP0: Step L s t1 s1)
        (STEP1 :Step L s t2 s2),
        <<EQ: t1 = t2>> /\ <<EQ: s1 = s2>>;
    ssd_determ_at_final: forall tr s' retv
        (FINAL: final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    ssd_traces_at:
      single_events_at L s
  }.

Definition SDStep (L: semantics) :=
  (fun s1 t s2 => strict_determinate_at L s1 /\ Step L s1 t s2).

Definition SDStar (L: semantics) :=
  (star (fun _ _ => SDStep L)) L.(symbolenv) L.(globalenv).

Definition SDStarN (L: semantics) :=
  (starN (fun _ _ => SDStep L)) L.(symbolenv) L.(globalenv).

Definition SDPlus (L: semantics) :=
  (plus (fun _ _ => SDStep L)) L.(symbolenv) L.(globalenv).

Hint Unfold SDStep SDStar SDStarN SDPlus.

Inductive Dfinal_state (L: semantics) (st: L.(state)) (retv: int): Prop :=
| Dfinal_state_intro
    (FINAL: final_state L st retv)
    (DTM: forall retv0 retv1
        (FINAL0: final_state L st retv0)
        (FINAL1: final_state L st retv1),
        retv0 = retv1)
    (DTM: forall retv0
        (FINAL: final_state L st retv0),
        Nostep L st).

Inductive Dinitial_state (L: semantics) (st: L.(state)): Prop :=
| Dinitial_state_intro
    (INIT: initial_state L st)
    (DTM: forall st0 st1
        (INIT0: initial_state L st0)
        (INIT1: initial_state L st1),
        st0 = st1).


Record preservation {L: semantics} (sound_state: L.(state) -> Prop): Prop :=
{
  prsv_initial: forall st (INIT: L.(initial_state) st), (<<SS: sound_state st>>);
  prsv_step: forall st0 tr st1 (SS: sound_state st0) (STEP: Step L st0 tr st1), (<<SS: sound_state st1>>);
}
.

Theorem preservation_top: forall L, <<PRSV: @preservation L top1>>.
Proof. ii. econs; eauto. Qed.

Theorem prsv_star
        L sound_state
        (PRSV: preservation sound_state)
  :
    (<<PRSVSTAR: forall st0 tr st1 (SS: sound_state st0) (STAR: Star L st0 tr st1), (<<SS: sound_state st1>>)>>)
.
Proof.
  ii. ginduction STAR; ii; ss. eapply IHSTAR; eauto. eapply prsv_step; eauto.
Qed.

Module GENMT.

Record match_traces: Type := {
  mt_match :> trace -> trace -> Prop;
  mt_nil_left: forall x (NIL: mt_match E0 x), x = E0;
  mt_nil_right: forall x (NIL: mt_match x E0), x = E0;
}.

Record receptive_at (mt: match_traces) (L: semantics) (s:L.(state)) : Prop :=
  Receptive_at {
    sr_receptive_at: forall t1 s1 t2,
      Step L s t1 s1 -> mt t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces_at:
      single_events_at L s
  }.

Record determinate_at (mt: match_traces) (L: semantics) (s:L.(state)) : Prop :=
  Determinate_at {
    sd_determ_at: forall t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      mt t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_determ_at_final: forall
        tr s' retv
        (FINAL: final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    sd_traces_at:
      single_events_at L s
  }.

Program Definition match_traces_default (se: Senv.t): match_traces :=
  Build_match_traces (Events.match_traces se) _ _.
Next Obligation. inv NIL. ss. Qed.
Next Obligation. inv NIL. ss. Qed.

Program Definition match_traces_strict: match_traces :=
  Build_match_traces eq _ _.

Lemma no_event_receptive L s mt
      (DETERM: forall t1 s1, Step L s t1 s1 -> t1 = E0):
  receptive_at mt L s.
Proof.
  econstructor; intros.
  - exploit DETERM; eauto. intro. subst.
    exploit mt_nil_left; eauto. i; clarify. exists s1. auto.
  - repeat intro. exploit DETERM; eauto. intro. subst. auto.
Qed.

Definition DStep (mt: match_traces) (L: semantics) :=
  (fun s1 t s2 => determinate_at mt L s1 /\ Step L s1 t s2).

Definition DStar (mt: match_traces) (L: semantics) :=
  (star (fun _ _ => DStep mt L)) L.(symbolenv) L.(globalenv).

Definition DStarN (mt: match_traces) (L: semantics) :=
  (starN (fun _ _ => DStep mt L)) L.(symbolenv) L.(globalenv).

Definition DPlus (mt: match_traces) (L: semantics) :=
  (plus (fun _ _ => DStep mt L)) L.(symbolenv) L.(globalenv).

Hint Unfold DStep DStar DStarN DPlus.

Remark strict_fsim_src:
    (<<SRC: forall L st0, single_events_at L st0 <-> receptive_at match_traces_strict L st0>>).
Proof.
  - split; i.
    + econs; eauto. intros. ss. clarify. eauto.
    + inv H. ss.
Qed.

Remark strict_fsim_tgt:
    (<<TGT: forall L st0, strict_determinate_at L st0 <-> determinate_at match_traces_strict L st0>>).
Proof.
  - split; i.
    + inv H. econs; eauto. i. ss.
      exploit ssd_determ_at0.
      { apply H. }
      { apply H0. }
      i; des. clarify.
    + inv H. econs; eauto. i. ss.
      exploit sd_determ_at0.
      { apply STEP0. }
      { apply STEP1. }
      i; des. clarify. exploit H0; eauto.
Qed.

Remark strict_fsim_tgt_step:
    (<<TGT: forall L st0 tr st1, SDStep L st0 tr st1 <-> DStep match_traces_strict L st0 tr st1>>).
Proof.
  unfold DStep. unfold SDStep. split; i; des; econs; eauto; apply strict_fsim_tgt; ss.
Qed.

Remark strict_fsim_tgt_star:
    (<<TGT: forall L st0 tr st1, SDStar L st0 tr st1 <-> DStar match_traces_strict L st0 tr st1>>).
Proof.
  split; i; induction H; ii; ss; try apply star_refl; econs; eauto; apply strict_fsim_tgt_step; eauto.
Qed.

Remark strict_fsim_tgt_plus:
    (<<TGT: forall L st0 tr st1, SDPlus L st0 tr st1 <-> DPlus match_traces_strict L st0 tr st1>>).
Proof.
  split; i; inv H; econs; eauto; try apply strict_fsim_tgt_star; eauto; try apply strict_fsim_tgt_step; eauto.
Qed.

Lemma DStep_E0_SDStep
      L st0 st1 mt_at
      (STEP: DStep mt_at L st0 E0 st1):
    SDStep L st0 E0 st1.
Proof.
  r in STEP. des. econs; eauto. inv STEP. econs; eauto. intros.
  exploit sd_determ_at0.
  { apply STEP0. }
  { apply STEP1. }
  i; des. apply mt_nil_left in H. clarify. exploit H0; eauto. i; des. clarify.
  exploit sd_determ_at0.
  { apply STEP0. }
  { apply STEP2. }
  i; des. apply mt_nil_left in H. clarify. exploit H1; eauto.
Qed.

Lemma DStarN_E0_SDStarN
      L st0 st1 mt_at n
      (STEP: DStarN mt_at L n st0 E0 st1):
    SDStarN L n st0 E0 st1.
Proof.
  dependent induction STEP; ii; ss.
  { econs; eauto. }
  destruct t1, t2; ss. econs; eauto.
  { eapply DStep_E0_SDStep; eauto. }
  { eapply IHSTEP. ss. }
  ss.
Qed.

Section MIXED_SIM.

  Variables L1 L2: semantics.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Variable sound_state_src: L1.(state) -> Prop.
  Variable sound_state_tgt: L2.(state) -> Prop.
  Hypothesis (PRSVSRC: preservation sound_state_src).
  Hypothesis (PRSVTGT: preservation sound_state_tgt).

  Inductive fsim_step xsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)): Prop :=
  | fsim_step_step
      (mt: match_traces)
      (STEP: forall st_src1 tr
          (STEPSRC: Step L1 st_src0 tr st_src1),
          exists i1 st_tgt1,
            ((<<PLUS: DPlus mt L2 st_tgt0 tr st_tgt1 /\ (<<RECEPTIVE: receptive_at mt L1 st_src0>>)>>) \/
             <<STUTTER: st_tgt0 = st_tgt1 /\ tr = E0 /\ order i1 i0>>)
            /\ <<XSIM: xsim i1 st_src1 st_tgt1>>)
      (FINAL: forall retv
          (FINALSRC: final_state L1 st_src0 retv),
          <<FINALTGT: Dfinal_state L2 st_tgt0 retv>>)
  | fsim_step_stutter
      i1 st_tgt1
      (PLUS: SDPlus L2 st_tgt0 nil st_tgt1 /\ order i1 i0)
      (XSIM: xsim i1 st_src0 st_tgt1).

  Inductive _xsim_forward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_forward_intro
      (STEP: fsim_step xsim i0 st_src0 st_tgt0).

  Let bsim_step := bsim_step L1 L2 order.

  Inductive _xsim_backward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_backward_intro
      (STEP: forall
          (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step xsim i0 st_src0 st_tgt0>>).

  Definition _xsim xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop := forall
      (SSSRC: sound_state_src st_src0)
      (SSTGT: sound_state_tgt st_tgt0)
    ,
      (<<XSIM: (_xsim_forward \4/ _xsim_backward) xsim i0 st_src0 st_tgt0>>)
  .

  Definition xsim: _ -> _ -> _ -> Prop := paco3 _xsim bot3.

  Lemma _xsim_forward_mon: monotone3 (_xsim_forward).
  Proof.
    ii. inv IN. econs; eauto. inv STEP.
    - econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - econs 2; eauto.
  Qed.

  Lemma _xsim_backward_mon: monotone3 (_xsim_backward).
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - eleft; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - eright; eauto.
  Qed.

  Lemma xsim_mon: monotone3 _xsim.
  Proof.
    ii. repeat spc IN. inv IN.
    - econs 1; eauto. eapply _xsim_forward_mon; eauto.
    - econs 2; eauto. eapply _xsim_backward_mon; eauto.
  Qed.

  Section TEST.
    Definition xsim2: _ -> _ -> _ -> Prop := paco3 (_xsim_forward \4/ _xsim_backward) bot3.
    Goal xsim2 <3= xsim.
      pcofix CIH. ii. pfold. ii. exploit CIH; eauto. i.
      rr in PR. punfold PR; cycle 1.
      { ii. des; eauto using _xsim_forward_mon, _xsim_backward_mon. }
      des.
      - left. eapply _xsim_forward_mon; eauto. ii. pclearbot. right. eauto.
      - right. eapply _xsim_backward_mon; eauto. ii. pclearbot. right. eauto.
    Qed.
    Definition xsim3: _ -> _ -> _ -> Prop := fun i st_src st_tgt =>
      forall (SSSRC: sound_state_src st_src) (SSTGT: sound_state_tgt st_tgt),
        (paco3 (_xsim_forward \4/ _xsim_backward) bot3) i st_src st_tgt.
    Goal xsim3 <3= xsim.
      pcofix CIH. ii. pfold. ii. exploit CIH; eauto. i.
      rr in PR. repeat spc PR. punfold PR; cycle 1.
      { ii. des; eauto using _xsim_forward_mon, _xsim_backward_mon. }
      des.
      - left. eapply _xsim_forward_mon; eauto. ii. pclearbot. right. eapply CIH; ii; eauto.
      - right. eapply _xsim_backward_mon; eauto. ii. pclearbot. right. eapply CIH; ii; eauto.
    Qed.
    Goal xsim <3= xsim3.
      pcofix CIH. ii. pfold. ii. exploit CIH; eauto. i.
      rr in PR. punfold PR; cycle 1.
      { eapply xsim_mon. }
      rr in PR. repeat spc PR. des.
      - left. eapply _xsim_forward_mon; eauto. ii. pclearbot. right.
    Abort.
  End TEST.

End MIXED_SIM.

Hint Unfold xsim.
Hint Resolve xsim_mon: paco.
Hint Resolve _xsim_forward_mon: paco.
Hint Resolve _xsim_backward_mon: paco.

Inductive xsim_init_sim (L1 L2: semantics) (index: Type) (order: index -> index -> Prop)
          (ss_src: L1.(state) -> Prop) (ss_tgt: L2.(state) -> Prop): Prop :=
| xsim_init_forward
    (INITSIM: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists i0 st_init_tgt,
          (<<INITTGT: Dinitial_state L2 st_init_tgt>>) /\
          (<<XSIM: xsim L1 L2 order ss_src ss_tgt i0 st_init_src st_init_tgt>>))
| xsim_init_backward
    (INITEXISTS: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>)
    (INITSIM: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt),
        exists i0 st_init_src,
          (<<INITSRC: initial_state L1 st_init_src>>) /\
          (<<XSIM: xsim L1 L2 order ss_src ss_tgt i0 st_init_src st_init_tgt>>)).

Record xsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop): Type := {
    ss_src: L1.(state) -> Prop;
    ss_tgt: L2.(state) -> Prop;
    preservation_src: preservation ss_src;
    preservation_tgt: preservation ss_tgt;
    xsim_order_wf: <<WF: well_founded order>>;
    xsim_initial_states_sim: <<INIT: xsim_init_sim L1 L2 order ss_src ss_tgt>>;
}.

Arguments xsim_properties: clear implicits.

Inductive mixed_simulation (L1 L2: semantics) : Prop :=
  Mixed_simulation (index: Type)
                   (order: index -> index -> Prop)
                   (props: xsim_properties L1 L2 index order).

Arguments Mixed_simulation {L1 L2 index} order props.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Section MIXED_TO_BACKWARD.

Variables L1 L2: semantics.
Variable index: Type.
Variable order: index -> index -> Prop.
Hypothesis MIXED_SIM: xsim_properties L1 L2 index order.

(* Let match_states := xsim L1 L2 order MIXED_SIM.(ss_src) MIXED_SIM.(ss_tgt). *)
Let match_states (i0: index) (st_src0: state L1) (st_tgt0: state L2) :=
  (<<MATCH: xsim L1 L2 order MIXED_SIM.(ss_src) MIXED_SIM.(ss_tgt) i0 st_src0 st_tgt0>>) /\
  (<<SSSRC: MIXED_SIM.(ss_src) st_src0>>) /\
  (<<SSTGT: MIXED_SIM.(ss_tgt) st_tgt0>>)
.

(** Orders *)

Inductive x2b_index : Type :=
  | X2BI_before (n: nat)
  | X2BI_after (n: nat) (i: index).

Inductive x2b_order: x2b_index -> x2b_index -> Prop :=
  | x2b_order_before: forall n n',
      (n' < n)%nat ->
      x2b_order (X2BI_before n') (X2BI_before n)
  | x2b_order_after: forall n n' i,
      (n' < n)%nat ->
      x2b_order (X2BI_after n' i) (X2BI_after n i)
  | x2b_order_after': forall n m i' i,
      clos_trans _ order i' i ->
      x2b_order (X2BI_after m i') (X2BI_after n i)
  | x2b_order_switch: forall n n' i,
      x2b_order (X2BI_before n') (X2BI_after n i).

Lemma wf_x2b_order:
  well_founded x2b_order.
Proof.
  assert (ACC1: forall n, Acc x2b_order (X2BI_before n)).
  { intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  }
  assert (ACC2: forall i n, Acc x2b_order (X2BI_after n i)).
  { intros i; pattern i. eapply well_founded_ind.
    { apply wf_clos_trans. eapply xsim_order_wf; eauto. }
    i. pattern n. apply lt_wf_ind; i. clear n. econs; eauto. i. inv H1; eauto.
  }
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive x2b_match_states: x2b_index -> state L1 -> state L2 -> Prop :=
  | x2b_match_at: forall i s1 s2,
      match_states i s1 s2 ->
      x2b_match_states (X2BI_after O i) s1 s2
  | x2b_match_before: forall s1 t s1' s2b s2 n s2a mt,
      Step L1 s1 t s1' ->  t <> E0 ->
      DStar mt L2 s2b E0 s2 ->
      DStarN mt L2 n s2 t s2a ->
      (forall t s1', Step L1 s1 t s1' ->
       exists i', exists s2',
            ((<<PLUS: DPlus mt L2 s2b t s2' /\ (<<RECEPTIVE: receptive_at mt L1 s1>>)>>) \/
             <<STUTTER: s2b = s2' /\ t = E0>>)
       /\ match_states i' s1' s2') ->
      x2b_match_states (X2BI_before n) s1 s2
  | x2b_match_after: forall n s2 s2a s1 i,
      SDStarN L2 (S n) s2 E0 s2a ->
      match_states i s1 s2a ->
      x2b_match_states (X2BI_after (S n) i) s1 s2.

Remark x2b_match_after':
  forall n s2 s2a s1 i,
  SDStarN L2 n s2 E0 s2a ->
  match_states i s1 s2a ->
  x2b_match_states (X2BI_after n i) s1 s2.
Proof.
  intros. inv H. econstructor; eauto. econstructor; eauto. econstructor; eauto.
Qed.

Lemma _xsim_backward_mon_x2b
      i0 st_src0 st_tgt0
      (BSIM: _xsim_backward L1 L2 order match_states i0 st_src0 st_tgt0):
    <<BSIM: _xsim_backward L1 L2 x2b_order x2b_match_states (X2BI_after 0 i0) st_src0 st_tgt0>>.
Proof.
  red. inv BSIM. econs; eauto. i. exploit STEP; eauto. i; des. inv H.
  - econs 1; eauto. i. exploit STEP0; eauto. i; des; pclearbot; esplits; eauto.
    econs; eauto. right. esplits; eauto. econs 3; eauto. econs; eauto.
  - pclearbot. des. econs 2; eauto. esplits; eauto. econs 3; eauto. econs; eauto.
Qed.

(** Exploiting mixed simulation *)

Inductive x2b_transitions: index -> state L1 -> state L2 -> Prop :=
  | x2b_trans_forward_final
      i st_src0 st_src1 st_tgt0 r
      (TAU: Star L1 st_src0 E0 st_src1)
      (FINALSRC: final_state L1 st_src1 r)
      (FINALTGT: Dfinal_state L2 st_tgt0 r):
      x2b_transitions i st_src0 st_tgt0
  | x2b_trans_forward_step: forall i s1 s2 s1' t s1'' s2' i' i'' mt,
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      DPlus mt L2 s2 t s2' ->
      forall (STEP: forall st_src1 tr
                 (STEPSRC: Step L1 s1' tr st_src1),
            exists i1 st_tgt1,
              ((<<PLUS: DPlus mt L2 s2 tr st_tgt1 /\ (<<RECEPTIVE: receptive_at mt L1 s1'>>)>>) \/
               <<STUTTER: s2 = st_tgt1 /\ tr = E0 /\ order i1 i'>>)
              /\ <<FSIM: match_states i1 st_src1 st_tgt1>>),
        match_states i'' s1'' s2' ->
        x2b_transitions i s1 s2
  | x2b_trans_forward_stutter: forall i s1 s2 s1' s2' i' i'',
      Star L1 s1 E0 s1' ->
      True ->
      SDPlus L2 s2 E0 s2' ->
      match_states i'' s1' s2' ->
      forall (ORD0: clos_refl_trans _ order i' i)
        (ORD1: order i'' i'),
        x2b_transitions i s1 s2
  | x2b_trans_backward
      i0 st_src0 st_tgt0
      (BSIM: _xsim_backward L1 L2 x2b_order x2b_match_states (X2BI_after 0 i0) st_src0 st_tgt0):
      x2b_transitions i0 st_src0 st_tgt0.

Lemma x2b_transitions_src_tau_rev
      s1 s1' i i' s2
      (STEPSRC: Star L1 s1 E0 s1')
      (ORDER: order i' i)
      (TRANS: x2b_transitions i' s1' s2):
    <<TRANS: x2b_transitions i s1 s2>>.
Proof.
  inv TRANS.
  * eapply x2b_trans_forward_final; try eapply star_trans; eauto.
  * eapply x2b_trans_forward_step; cycle 1; eauto. eapply star_trans; eauto.
  * eapply x2b_trans_forward_stutter; cycle 1; eauto.
    eapply rt_trans; eauto. constructor. auto. eapply star_trans; eauto.
  * eapply x2b_trans_backward; cycle 1; eauto. inv BSIM. econs; eauto. i. hexploit1 STEP.
    { eapply star_safe; eauto. }
    inv STEP.
    - econs 1; eauto.
      + i. exploit STEP0; eauto. i; des.
        { esplits; eauto. left. eapply star_plus_trans; eauto. }
        { esplits; eauto. right. split. eapply star_trans; eauto. inv STAR0; econs; eauto. eapply t_trans; eauto. }
      + { i. eapply PROGRESS. eapply star_safe; eauto. }
      + i. exploit FINAL; eauto. ii. des. esplits; try eapply FINALSRC; eauto. eapply star_trans; eauto.
    - econs 2; try apply BSIM; eauto. des. esplits; eauto. { eapply star_trans; eauto. } inv STAR0; econs; eauto.
      { eapply t_trans; eauto. }
Qed.

Lemma x2b_progress:
  forall i s1 s2, match_states i s1 s2 -> safe L1 s1 -> x2b_transitions i s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order). eapply xsim_order_wf; eauto.
  intros i REC s1 s2 MATCH SAFE. dup MATCH. rr in MATCH0. des.
  punfold MATCH1. repeat spc MATCH1. des.
  { (* forward *)
    inversion MATCH1; subst. unfold NW in *. destruct (SAFE s1) as [[r FINAL1] | [t [s1' STEP1]]]. apply star_refl.
    - (* final state reached *)
      inv STEP.
      + eapply x2b_trans_forward_final; try eapply star_refl; eauto. eapply FINAL; eauto.
      + des. pclearbot. inv PLUS.
        assert(XSIM': match_states i1 s1 st_tgt1).
        { rr. esplits; eauto.
          hexploit (prsv_star MIXED_SIM.(preservation_tgt)); eauto. intro T; des.
          eapply T; eauto. econs; eauto.
          { eapply H. } ss. eapply H0.
        }
        eapply x2b_trans_forward_stutter; try apply XSIM'; try eapply star_refl; debug eauto.
        { econs; eauto. }
        econs 2; eauto.

    - inv STEP.
      + (* L1 can make one step *)
        hexploit STEP0; eauto. intros [i' [s2' [A MATCH']]]. pclearbot.
        assert (B: DPlus mt L2 s2 t s2' \/ (s2 = s2' /\ t = E0 /\ order i' i)).
        { des; eauto. }
        clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
        { eapply x2b_trans_forward_step; eauto. apply star_refl.
          i. exploit STEP0; eauto. i; des_safe. pclearbot. esplits; eauto.
        }
        subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
        i. eapply x2b_transitions_src_tau_rev; eauto. apply star_one; ss.
      + des. pclearbot. clears t. clear t. inv PLUS.
        destruct t1, t2; ss. clear_tac.
        eapply x2b_trans_forward_stutter; eauto. apply star_refl. econs; eauto. apply rt_refl.
  }
  { (* backward *)
    econs 4. eapply _xsim_backward_mon_x2b; eauto. eapply _xsim_backward_mon; eauto. i. pclearbot. ss.
  }
Qed.

Lemma xsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall s2 mt,
    receptive_at mt L1 s1 ->
    (forall t s1', Step L1 s1 t s1' ->
     exists i', exists s2',
        (DPlus mt L2 s2 t s2' \/ (s2 = s2' /\ t = E0))
     /\ match_states i' s1' s2') ->
  exists i', exists s2', DPlus mt L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  intros. exploit H2; eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto. destruct A. auto. des. clarify.
Qed.

(** Exploiting determinacy *)

Lemma determinacy_inv:
  forall s2 t' s2' t'' s2'' (mt: match_traces),
  determinate_at mt L2 s2 ->
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ mt t' t'').
Proof.
  intros.
  assert (mt t' t'').
    eapply sd_determ_at; eauto.
  destruct (silent_or_not_silent t').
  - subst. eapply mt_nil_left in H2. clarify. left; intuition. eapply sd_determ_at; eauto.
  - destruct (silent_or_not_silent t'').
    + subst. eapply mt_nil_right in H2. clarify.
    + right; intuition.
Qed.

Lemma determinacy_star:
  forall s s1 mt_at, DStar mt_at L2 s E0 s1 ->
  forall t s2 s3,
  DStep mt_at L2 s1 t s2 -> t <> E0 ->
  DStar mt_at L2 s t s3 ->
  DStar mt_at L2 s1 t s3.
Proof.
  intros s0 s01 mt_at ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence. destruct H, H1, H4.
  exploit determinacy_inv. eexact H. eexact H3. eexact H7.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto. congruence.
Qed.

(** Backward simulation of L2 steps *)

Lemma x2b_match_states_bsim
      i0_x2b st_src0 st_tgt0
      (MATCH: x2b_match_states i0_x2b st_src0 st_tgt0):
    <<BSIM: bsim L1 L2 x2b_order i0_x2b st_src0 st_tgt0>>.
Proof.
  red. generalize dependent st_src0. generalize dependent st_tgt0. generalize dependent i0_x2b.
  pcofix CIH. i. rename r into rr. pfold.
  assert(PROGRESS: safe L1 st_src0 ->
                   <<FINAL: exists retv : int, final_state L2 st_tgt0 retv >> \/
                   <<STEP: exists (tr : trace) (st_tgt1 : state L2), Step L2 st_tgt0 tr st_tgt1 >>).
  { (* PROGRESS *)
    generalize dependent st_src0. generalize dependent st_tgt0. pattern i0_x2b.
    eapply (well_founded_ind wf_x2b_order). clear i0_x2b. intros ? IH ? ? ? SAFE. i. inv MATCH.
    + exploit x2b_progress; eauto. intros TRANS; inv TRANS.
      * left. esplits; eauto. apply FINALTGT.
      * rename H2 into PLUS. inv PLUS. unfold DStep in *. des. right; econstructor; econstructor; eauto.
      * right. rename H2 into PLUS. inv PLUS. rename H2 into STEP. inv STEP. esplits; eauto.
      * inv BSIM. specialize (STEP SAFE). inv STEP.
        { exploit PROGRESS; eauto. }
        { des. exploit IH; eauto. eapply star_safe; eauto. }
    + rename H2 into STARN. inv STARN. congruence. unfold DStep in *. des. right; econstructor; econstructor; eauto.
    + rename H into STARN. inv STARN. unfold SDStep in *. des. right; econstructor; econstructor; eauto.
  }
  econs; eauto.
  assert(FINALLEMMA: forall retv (SAFESRC: safe L1 st_src0) (FINALTGT: final_state L2 st_tgt0 retv),
            exists st_src1, <<STAR: Star L1 st_src0 E0 st_src1 >> /\ <<FINAL: final_state L1 st_src1 retv >>).
  { (* FINAL *)
    clear - MATCH CIH MIXED_SIM.
    generalize dependent MATCH. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0_x2b.
    eapply (well_founded_ind wf_x2b_order); eauto. i. rename H into IH. clear i0_x2b.
    i. inv MATCH.
    + exploit x2b_progress; eauto. intro TRANS. inv TRANS.
      * assert(retv = r). { inv FINALTGT0. eapply DTM; eauto. } clarify. esplits; eauto.
      * rename H2 into PLUS. inv PLUS. unfold DStep in *. des. exploit sd_determ_at_final; eauto. contradiction.
      * rename H2 into PLUS. inv PLUS. unfold SDStep in *. des. exploit ssd_determ_at_final; eauto. contradiction.
      * inv BSIM. hexploit1 STEP; eauto. inv STEP; eauto. des. exploit IH; eauto.
        { eapply star_safe; eauto. } i; des. esplits; try apply FINAL. eapply star_trans; eauto.
    + rename H2 into STARN. inv STARN. congruence. unfold DStep in *. des. exploit sd_determ_at_final; eauto. contradiction.
    + rename H into STARN. inv STARN. unfold SDStep in *. des. exploit ssd_determ_at_final; eauto. contradiction.
  }
  { (* STEP *)
    i. inv MATCH.
  - (* 1. At matching states *)
    exploit x2b_progress; eauto. intros TRANS; inv TRANS.
    { (* final *)
      (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
      econs 1; ss; eauto.
      i. inv FINALTGT. exploit DTM0; eauto. i; ss.
    }
    { (* forward *)
      (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
      econs 1; ss; eauto.
      i. rename H3 into H4. inv H2.
      exploit STEP; eauto. intros [i''' [s2''' [STEP''' MATCH''']]].
      destruct H3. exploit determinacy_inv. eexact H2. eexact H3. eexact STEPTGT.
      intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
      (* 1.2.1  L2 makes a silent transition *)
      + destruct (silent_or_not_silent t2).
        * (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
          subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
          exists (X2BI_after n i''); exists s1''; split.
          left. eapply plus_right; eauto. right. eapply CIH.
          eapply x2b_match_after'; eauto. eapply DStarN_E0_SDStarN; eauto.
        * (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
          subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
          exists (X2BI_before n); exists s1'; split. right; split. auto. constructor. right. eapply CIH.
          econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
          intros. exploit STEP; eauto. intros [i'''' [s2'''' [A MATCH'''']]].
          exists i''''. exists s2''''. destruct A as [?|[? ?]]; auto.
          des; clarify. esplits; eauto.
      + (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
        des; cycle 1.
        { clarify. destruct t1; ss. }
        exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ]. congruence.
        subst t2. rewrite E0_right in H1.
        (* Use receptiveness to equate the traces *)
        exploit (sr_receptive_at RECEPTIVE); eauto. intros [s1''' STEP1].
        exploit xsim_simulation_not_E0. eexact STEP1. auto. eauto.
        intros. exploit STEP; eauto. intros [i'''' [s2'''' [A MATCH'''']]].
        exists i''''. exists s2''''. destruct A as [?|[? ?]]; split; eauto.
        { des. left. eauto. }
        { des. clarify. right. esplits; eauto. }
        intros [i'''' [s2'''' [P Q]]]. inv P.
        (* Exploit determinacy *)
        destruct H6. exploit sd_determ_at. eauto. eexact STEPTGT. eexact H8.
        exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ].
        subst t0. simpl in *. intros. elim NOT2. destruct H9. eapply mt_nil_right in H9. clarify.
        subst t2. rewrite E0_right in *. intros [_ TRACES]. assert (s0 = st_tgt1). symmetry. eapply TRACES. auto. subst s0.
        (* Perform transition now and go to "after" state *)
        destruct (star_starN H7) as [n STEPS2]. exists (X2BI_after n i''''); exists s1'''; split. left. eapply plus_right; eauto.
        right. eapply CIH. eapply x2b_match_after'; eauto. eapply DStarN_E0_SDStarN; eauto.
    }
    { econs 1; ss; eauto.
      i. inv H2.
      - destruct t1, t2; ss. clear_tac.
        exploit ssd_determ_at. apply H4. apply H4. apply STEPTGT. i; des. clarify.
        destruct H4. clear_tac. destruct (star_starN H5) as [n STEPS2]. destruct n.
        + inv STEPS2. ss. exists (X2BI_after 0 i''). esplits; eauto.
          * right. esplits; eauto. econs; eauto. eapply clos_t_rt; eauto.
          * right. eapply CIH. econs; eauto.
        + exists (X2BI_after (S n) i''). esplits; eauto.
          * right. esplits; eauto. econs; eauto. eapply clos_t_rt; eauto.
          * right. eapply CIH. econs 3; eauto.
    }
    { (* backward *)
      inv BSIM. exploit STEP; eauto. i. inv H0.
      - econs 1; eauto. i. exploit STEP0; eauto. i; des; esplits; eauto.
      - econs 2; eauto.
    }

  - (* 2. Before *)
    econs 1; ss; eauto.
    i. assert(DUMMY_PROP) by ss. inv H2. congruence. destruct H5.
    exploit determinacy_inv. eauto. eexact H5. eexact STEPTGT.
    intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
    + (* 2.1 L2 makes a silent transition: remain in "before" state *)
      subst. simpl in *. exists (X2BI_before n0); exists st_src0; split.
      right; split. apply star_refl. constructor. omega. right. eapply CIH.
      econstructor; eauto. eapply star_right; eauto.
    + (* 2.2 L2 make a non-silent transition *)
      assert(RECEPTIVE : receptive_at mt L1 st_src0).
      { exploit H3; eauto. i; des; clarify. }
      exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ]. congruence.
      subst. rewrite E0_right in *.
      (* Use receptiveness to equate the traces *)
      exploit (sr_receptive_at RECEPTIVE); eauto. intros [s1''' STEP1].
      exploit xsim_simulation_not_E0. eexact STEP1. auto. eauto.
      { i. exploit H3; eauto. i; des; eauto. clarify. esplits; eauto. }
      intros [i''' [s2''' [P Q]]].
      (* Exploit determinacy *)
      exploit determinacy_star. eauto. split; auto. eexact STEPTGT. auto. apply plus_star; eauto.
      intro R. inv R. congruence.
      exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ].
      subst. simpl in *. destruct H7. exploit sd_determ_at. eauto. eexact STEPTGT. eexact H9.
      intros. elim NOT2. destruct H10. eapply mt_nil_right in H10. clarify.
      subst. rewrite E0_right in *.  destruct H7.
      assert (s2 = st_tgt1). eapply sd_determ_at; eauto. subst s2.
      (* Perform transition now and go to "after" state *)
      destruct (star_starN H8) as [n STEPS2]. exists (X2BI_after n i'''); exists s1'''; split.
      left. apply plus_one; auto. right. eapply CIH. eapply x2b_match_after'; eauto. eapply DStarN_E0_SDStarN; eauto.

  - (* 3. After *)
    econs 1; ss; eauto.
    i. inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
    destruct H2. exploit ssd_determ_at. eapply H. eexact H1. eexact STEPTGT. i; des. clarify.
    exists (X2BI_after n i); exists st_src0; split.
    right; split. apply star_refl. constructor. constructor; omega. right. eapply CIH.
    eapply x2b_match_after'; eauto.
  }
Qed.

Lemma bsim_to_xsim
      i0 st_src0 st_tgt0
      (BSIM: bsim L1 L2 order i0 st_src0 st_tgt0):
    <<XSIM: xsim L1 L2 order i0 st_src0 st_tgt0>>.
Proof.
  generalize dependent i0. generalize dependent st_src0. generalize dependent st_tgt0. pcofix CIH. i.
  pfold. right. punfold BSIM. inv BSIM. econs; eauto. i. exploit STEP; eauto. i; des. inv H.
  - econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. pclearbot. esplits; eauto.
  - econs 2; eauto. pclearbot. eauto.
Qed.

End MIXED_TO_BACKWARD.

(** The backward simulation *)

Lemma mixed_to_backward_simulation: forall L1 L2,
  mixed_simulation L1 L2 -> backward_simulation L1 L2.
Proof.
  intros L1 L2 XSIM. inversion XSIM.
  apply Backward_simulation with (order0 := x2b_order order). constructor.
  - eapply wf_x2b_order. apply props.
  - inv props. inv xsim_initial_states_sim0; eauto.
    i. exploit INITSIM; eauto. i; des. inv INITTGT. eauto.
  - inv props. i. inv xsim_initial_states_sim0; eauto.
    + exploit INITSIM; eauto. i; des. inv INITTGT0.
      assert(st_init_tgt = st_init_tgt0).
      { eapply DTM; eauto. }
      clarify. esplits; eauto. eapply x2b_match_states_bsim; eauto.
      econs; eauto. econs 1; eauto. econs; eauto.
    + exploit INITSIM; eauto. i; des. esplits; eauto. eapply x2b_match_states_bsim; eauto.
      econs; eauto. econs 2; eauto. econs; eauto.
Qed.

Lemma mixed_to_compcert_backward_simulation
      L1 L2
      (XSIM: mixed_simulation L1 L2):
    <<BSIM: Smallstep.backward_simulation L1 L2>>.
Proof.
  eapply backward_to_compcert_backward_simulation; eauto. eapply mixed_to_backward_simulation; eauto.
Qed.

Lemma backward_to_mixed_simulation
      L1 L2
      (BSIM: backward_simulation L1 L2):
    <<XSIM: mixed_simulation L1 L2>>.
Proof.
  inv BSIM. inv props. econs; eauto. econs; eauto. econs 2; eauto.
  i. exploit bsim_match_initial_states0; eauto. i; des.
  esplits; eauto. eapply bsim_to_xsim; eauto.
Qed.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Definition receptive_at_default (L: semantics): L.(state) -> Prop :=
  (receptive_at (match_traces_default L.(symbolenv)) L).
Definition determinate_at_default (L: semantics): L.(state) -> Prop :=
  (determinate_at (match_traces_default L.(symbolenv)) L).

Lemma match_traces_eta
      mt0 mt1
      (EQ: mt0.(mt_match) = mt1.(mt_match)):
    mt0 = mt1.
Proof.
  destruct mt0, mt1; ss. clarify. f_equal; eapply Axioms.proof_irr.
Qed.

End GENMT.



Record receptive_at (L: semantics) (s:L.(state)) : Prop :=
  Receptive_at {
    sr_receptive_at: forall t1 s1 t2,
      Step L s t1 s1 -> match_traces L.(symbolenv) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces_at:
      single_events_at L s
  }.

Definition well_behaved_traces_at (L: semantics) (s:L.(state)) : Prop :=
  forall t s', Step L s t s' ->
  match t with nil => True | ev :: t' => output_trace t' end.

Record strongly_receptive_at (L: semantics) (s:L.(state)) : Prop :=
  Strongly_receptive_at {
      ssr_receptive_at: forall ev1 t1 s1 ev2,
        Step L s (ev1 :: t1) s1 ->
        match_traces (symbolenv L) (ev1 :: nil) (ev2 :: nil) ->
        exists s2, exists t2, Step L s (ev2 :: t2) s2;
      ssr_traces_at:
        well_behaved_traces_at L s;
    }.

Record determinate_at (L: semantics) (s:L.(state)) : Prop :=
  Determinate_at {
    sd_determ_at: forall t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces L.(symbolenv) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_determ_at_final: forall
        tr s' retv
        (FINAL: final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    sd_traces_at:
      single_events_at L s
  }.

Definition DStep (L: semantics) :=
  (fun s1 t s2 => determinate_at L s1 /\ Step L s1 t s2).

Definition DStar (L: semantics) :=
  (star (fun _ _ => DStep L)) L.(symbolenv) L.(globalenv).

Definition DStarN (L: semantics) :=
  (starN (fun _ _ => DStep L)) L.(symbolenv) L.(globalenv).

Definition DPlus (L: semantics) :=
  (plus (fun _ _ => DStep L)) L.(symbolenv) L.(globalenv).

Hint Unfold DStep DStar DStarN DPlus.

Section MIXED_SIM.

  Variables L1 L2: semantics.
  Variable index: Type.
  Variable order: index -> index -> Prop.

  Inductive sfsim_step xsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)): Prop :=
  | sfsim_step_step
      (STEP: forall st_src1 tr
          (STEPSRC: Step L1 st_src0 tr st_src1),
          exists i1 st_tgt1,
            (<<PLUS: SDPlus L2 st_tgt0 tr st_tgt1>> \/ <<STAR: SDStar L2 st_tgt0 tr st_tgt1 /\ order i1 i0>>)
            /\ <<XSIM: xsim i1 st_src1 st_tgt1>>)
      (SINGLE: single_events_at L1 st_src0)
      (FINAL: forall retv
          (FINALSRC: final_state L1 st_src0 retv),
          <<FINALTGT: Dfinal_state L2 st_tgt0 retv>>)
  | sfsim_step_stutter
      i1 st_tgt1
      (PLUS: SDPlus L2 st_tgt0 nil st_tgt1 /\ order i1 i0)
      (XSIM: xsim i1 st_src0 st_tgt1).

  Inductive _xsim_strict_forward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_strict_forward_intro
      (STEP: sfsim_step xsim i0 st_src0 st_tgt0).

  Inductive fsim_step xsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)): Prop :=
  | fsim_step_step
      (STEP: forall st_src1 tr
          (STEPSRC: Step L1 st_src0 tr st_src1),
          exists i1 st_tgt1,
            ((<<PLUS: DPlus L2 st_tgt0 tr st_tgt1 /\ (<<RECEPTIVE: receptive_at L1 st_src0>>)>>) \/
             <<STUTTER: st_tgt0 = st_tgt1 /\ tr = E0 /\ order i1 i0>>)
            /\ <<XSIM: xsim i1 st_src1 st_tgt1>>)
      (FINAL: forall retv
          (FINALSRC: final_state L1 st_src0 retv),
          <<FINALTGT: Dfinal_state L2 st_tgt0 retv>>)
  | fsim_step_stutter
      i1 st_tgt1
      (PLUS: DPlus L2 st_tgt0 nil st_tgt1 /\ order i1 i0)
      (XSIM: xsim i1 st_src0 st_tgt1).

  Inductive _xsim_forward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_forward_intro
      (STEP: fsim_step xsim i0 st_src0 st_tgt0).

  Let bsim_step := bsim_step L1 L2 order.

  Inductive _xsim_backward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_backward_intro
      (STEP: forall
          (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step xsim i0 st_src0 st_tgt0>>).

  Definition xsim: _ -> _ -> _ -> Prop := paco3 (_xsim_strict_forward \4/ _xsim_forward \4/ _xsim_backward) bot3.

  Lemma _xsim_strict_forward_mon: monotone3 (_xsim_strict_forward).
  Proof.
    ii. inv IN. econs; eauto. inv STEP.
    - econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - econs 2; eauto.
  Qed.

  Lemma _xsim_forward_mon: monotone3 (_xsim_forward).
  Proof.
    ii. inv IN. econs; eauto. inv STEP.
    - econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - econs 2; eauto.
  Qed.

  Lemma _xsim_backward_mon: monotone3 (_xsim_backward).
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - eleft; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - eright; eauto.
  Qed.

  Lemma xsim_mon: monotone3 (_xsim_strict_forward \4/ _xsim_forward \4/ _xsim_backward).
  Proof.
    ii. des.
    - left. left. eapply _xsim_strict_forward_mon; eauto.
    - left. right. eapply _xsim_forward_mon; eauto.
    - right. eapply _xsim_backward_mon; eauto.
  Qed.

End MIXED_SIM.

Hint Unfold xsim.
Hint Resolve xsim_mon: paco.
Hint Resolve _xsim_strict_forward_mon: paco.
Hint Resolve _xsim_forward_mon: paco.
Hint Resolve _xsim_backward_mon: paco.

Inductive xsim_init_sim (L1 L2: semantics) (index: Type)
          (order: index -> index -> Prop): Prop :=
| xsim_init_forward
    (INITSIM: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists i0 st_init_tgt, <<INITTGT: Dinitial_state L2 st_init_tgt>> /\
                               <<XSIM: xsim L1 L2 order i0 st_init_src st_init_tgt>>)
| xsim_init_backward
    (INITEXISTS: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>)
    (INITSIM: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt),
        exists i0 st_init_src, <<INITSRC: initial_state L1 st_init_src>> /\
                               <<XSIM: xsim L1 L2 order i0 st_init_src st_init_tgt>>)
.

Record xsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop): Prop := {
    xsim_order_wf: <<WF: well_founded order>>;
    xsim_initial_states_sim: <<INIT: xsim_init_sim L1 L2 order>>;
    xsim_public_preserved: forall (SAFESRC: exists st_init_src, L1.(initial_state) st_init_src),
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id;
}.

Arguments xsim_properties: clear implicits.

Inductive mixed_simulation (L1 L2: semantics) : Prop :=
  Mixed_simulation (index: Type)
                   (order: index -> index -> Prop)
                   (props: xsim_properties L1 L2 index order).

Arguments Mixed_simulation {L1 L2 index} order props.


(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Lemma GENMT_determinate_at_iff
      L st0 se
      (DTM: determinate_at L st0)
      (PUBEQ: forall id, Senv.public_symbol L.(symbolenv) id = Senv.public_symbol se id):
    <<DTM: GENMT.determinate_at (GENMT.match_traces_default se) L st0>>.
Proof.
  inv DTM. econs; eauto. i. ss. exploit (sd_determ_at0 t1 s1 t2 s2); eauto. i; des.
  esplits; eauto. eapply match_traces_preserved; try apply H1; eauto.
Qed.

Lemma GENMT_DStar_iff
      L st0 tr st1 se
      (DSTAR: DStar L st0 tr st1)
      (PUBEQ: forall id, Senv.public_symbol L.(symbolenv) id = Senv.public_symbol se id):
    <<DSTAR: GENMT.DStar (GENMT.match_traces_default se) L st0 tr st1>>.
Proof.
  ginduction DSTAR; ii; ss; econs; eauto.
  { rr in H. rr. des. esplits; eauto. eapply GENMT_determinate_at_iff; eauto. }
  eapply IHDSTAR; eauto.
Qed.

Lemma GENMT_DPlus_iff
      L st0 tr st1 se
      (DPLUS: DPlus L st0 tr st1)
      (PUBEQ: forall id, Senv.public_symbol L.(symbolenv) id = Senv.public_symbol se id):
    <<DPLUS: GENMT.DPlus (GENMT.match_traces_default se) L st0 tr st1>>.
Proof.
  inv DPLUS; econs; eauto.
  { rr in H. des. rr. esplits; eauto. eapply GENMT_determinate_at_iff; eauto. }
  eapply GENMT_DStar_iff; eauto.
Qed.

Lemma GENMT_receptive_at_iff
      L st0
      (RCP: receptive_at L st0):
    <<RCP: GENMT.receptive_at (GENMT.match_traces_default L.(symbolenv)) L st0>>.
Proof.
  inv RCP. econs; eauto.
Qed.

Lemma DStar_E0_SDStar
      L st0 st1
      (STEP: DStar L st0 E0 st1):
    SDStar L st0 E0 st1.
Proof.
  dependent induction STEP; ii; ss.
  { econs; eauto. }
  destruct t1, t2; ss. econs; eauto; cycle 1.
  { eapply IHSTEP. ss. }
  { instantiate (1:= []). ss. }
  { rr in H. rr. des. esplits; eauto. inv H. econs; eauto.
    i. exploit (sd_determ_at0 t1 s0 E0 s2); eauto. i; des. inv H. exploit H2; eauto. i; clarify.
    exploit (sd_determ_at0 t2 s4 E0 s2); eauto. i; des. inv H. exploit H3; eauto. }
Qed.

Lemma DPlus_E0_SDPlus
      L st0 st1
      (STEP: DPlus L st0 E0 st1):
    SDPlus L st0 E0 st1.
Proof.
  inv STEP. rr in H. des. destruct t1, t2; ss. econs; eauto.
  { econs; eauto. inv H. econs; eauto. i. determ_tac sd_determ_at0. inv H. clear STEP1.
    determ_tac sd_determ_at0. inv H. esplits; eauto. rewrite <- H3; ss. rewrite <- H4; ss. }
  { eapply DStar_E0_SDStar; eauto. }
  ss.
Qed.

Lemma xsim_to_generalized_xsim
      L1 L2 index (order: index -> index -> Prop) i0 st_src0 st_tgt0
      (PUBEQ: forall id, Senv.public_symbol L1.(symbolenv) id = Senv.public_symbol L2.(symbolenv) id)
      (XSIM: xsim L1 L2 order i0 st_src0 st_tgt0):
    <<XSIM: GENMT.xsim L1 L2 order i0 st_src0 st_tgt0>>.
Proof.
  revert_until order. pcofix CIH. i. pfold. punfold XSIM. des.
  - left. inv XSIM. econs; eauto. inv STEP.
    + econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. pclearbot.
      assert(T: SDPlus L2 st_tgt0 tr st_tgt1 \/ (st_tgt0 = st_tgt1 /\ tr = E0 /\ order i1 i0)).
      { des; eauto. inv STAR; eauto. left. econs; eauto. }
      clear H. des.
      * esplits; eauto. left. esplits; eauto. eapply GENMT.strict_fsim_tgt_plus; eauto.
        eapply GENMT.strict_fsim_src; eauto.
      * esplits; eauto.
    + pclearbot. econs 2; eauto.
  - left. inv XSIM. econs; eauto. inv STEP.
    + econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. pclearbot. des.
      * esplits; eauto. instantiate (1:= GENMT.match_traces_default L1.(symbolenv)).
        left. esplits; eauto.
        { eapply GENMT_DPlus_iff; eauto. }
        eapply GENMT_receptive_at_iff; eauto.
      * esplits; eauto.
    + pclearbot. econs 2; eauto. des. esplits; eauto. eapply DPlus_E0_SDPlus; eauto.
  - right. inv XSIM. econs; eauto. i. exploit STEP; eauto. i; des. inv H.
    + econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. pclearbot. esplits; eauto.
    + pclearbot. econs 2; eauto.
Qed.

Lemma mixed_to_generalized_mixed_simulation: forall L1 L2,
  mixed_simulation L1 L2 -> GENMT.mixed_simulation L1 L2.
Proof.
  intros L1 L2 XSIM. inversion XSIM.
  inv props. econs. econs; eauto. inv xsim_initial_states_sim0.
  - econs 1; eauto. i. exploit INITSIM; eauto. i; des. esplits; eauto.
    eapply xsim_to_generalized_xsim; eauto. i. exploit xsim_public_preserved0; eauto.
  - econs 2; eauto. i. exploit INITSIM; eauto. i; des. esplits; eauto.
    eapply xsim_to_generalized_xsim; eauto. i. exploit xsim_public_preserved0; eauto.
Qed.

Lemma mixed_to_backward_simulation
      L1 L2
      (XSIM: mixed_simulation L1 L2):
    <<BSIM: backward_simulation L1 L2>>.
Proof.
  eapply GENMT.mixed_to_backward_simulation; eauto. eapply mixed_to_generalized_mixed_simulation; eauto.
Qed.
