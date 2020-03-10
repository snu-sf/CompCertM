Require Import SimMem.
Require Import Simulation.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
Require Import Values Integers.
Require Import Globalenvs.
Require Import Program.
Require Import MemoryC.

Require Import Skeleton SimSymb Ord.
Require Import ModSem.
Require Import Sound Preservation.
Import ModSem.
Require Import ModSemProps.
Require Import Events.
Require Import SmallstepC.
From Paco Require Import hpattern.

Set Implicit Arguments.


(* TODO: use Iso? *)
Class LeibEq (A B: Type) := { leibeq: A = B }.
Arguments LeibEq: clear implicits.
Definition cast_sigT (a: {ty: Type & ty}) (B: Type) `{LeibEq (projT1 a) B}: B.
  rewrite <- leibeq. destruct a. simpl. auto.
Defined.
Global Program Instance LeibEq_rev (A B: Type) `{LeibEq A B}: LeibEq B A.
Next Obligation. rewrite leibeq. eauto. Defined.
Definition cast (A B: Type) `{LeibEq A B} (a: A): B. rewrite <- leibeq. apply a. Defined.
Global Program Instance LeibEq_refl (A: Type): LeibEq A A.



(* Module Ohs. *)
Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SMOS: SimMemOhs.class}.
  (* TODO: make SS's argument "SM" implicit; like SMO *)
  Context {SS: SimSymb.class SM}.
  Variable sound_states: ms_src.(state) -> Prop.

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMemOhs.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smos0: SimMemOhs.t): Prop :=
  | fsim_step_step
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0)
      (STEP: forall st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1),
          exists i1 st_tgt1 smos1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            /\ <<MLE: SimMemOhs.le smos0 smos1>>
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 smos1>>)
      (RECEP: receptive_at ms_src st_src0)
  | fsim_step_stutter
      i1 st_tgt1 smos1
      (PLUS: DPlus ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (MLE: SimMemOhs.le smos0 smos1)
      (BSIM: fsim i1 st_src0 st_tgt1 smos1).

  Inductive bsim_step (bsim: idx -> state ms_src -> state ms_tgt -> SimMemOhs.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smos0: SimMemOhs.t): Prop :=
  | bsim_step_step
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1),
          exists i1 st_src1 smos1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ ord i1 i0>>)
            /\ <<MLE: SimMemOhs.le smos0 smos1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 smos1>>)
      (PROGRESS: <<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)
  | bsim_step_stutter
      i1 st_src1 smos1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (MLE: SimMemOhs.le smos0 smos1)
      (BSIM: bsim i1 st_src1 st_tgt0 smos1).

  Let midx_src: Midx.t := ms_src.(ModSem.midx).
  Let midx_tgt: Midx.t := ms_tgt.(ModSem.midx).

  Inductive _lxsim_pre (lxsim: idx -> state ms_src -> state ms_tgt -> SimMemOhs.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smos0: SimMemOhs.t): Prop :=
  | lxsim_step_forward
      (SU: forall (SU: DUMMY_PROP),
      <<FSTEP: fsim_step lxsim i0 st_src0 st_tgt0 smos0>>)

  | lxsim_step_backward
      (SU: forall (SU: DUMMY_PROP),
      (<<BSTEP: forall
          (SAFESRC: safe_modsem ms_src st_src0),
         (<<BSTEP: bsim_step lxsim i0 st_src0 st_tgt0 smos0>>)>>))

  (* | lxsim_at_external *)
  (*     (MWF: SimMemOhs.wf smos0) *)
  (*     (SAFESRC: ms_src.(is_call) st_src0) *)
  (*     (SU: forall (SU: DUMMY_PROP), *)
  (*     <<CALLFSIM: forall (ohs_src0: Sem.Ohs) oh_src0 args_src *)
  (*         (OHSRC: nth_error ohs_src0 midx = Some oh_src0) *)
  (*         (OHSWFSRC: LeibEq (projT1 oh_src0) ms_src.(ModSem.owned_heap)) *)
  (*         (ATSRC: ms_src.(at_external) st_src0 (cast_sigT oh_src0) args_src), *)
  (*         exists ohs_tgt0 oh_tgt0 args_tgt (smos_arg: SimMemOhs.t), *)
  (*           (<<OHTGT: nth_error ohs_tgt0 midx = Some oh_tgt0>>) /\ *)
  (*           exists (OHWFTGT: LeibEq (projT1 oh_tgt0) ms_tgt.(ModSem.owned_heap)), *)
  (*           (<<SIMARGS: SimMemOhs.sim_args midx ohs_src0 ohs_tgt0 args_src args_tgt smos_arg>> *)
  (*           /\ (<<MWF: SimMemOhs.wf smos_arg>>) *)
  (*           /\ (<<MLE: SimMemOhs.lepriv smos0 smos_arg>>) *)
  (*           /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 (cast_sigT oh_tgt0) args_tgt>>) *)
  (*           /\ (<<K: forall smos_ret ohs_src1 retv_src ohs_tgt1 retv_tgt st_src1 *)
  (*                           oh_src1 oh_tgt1 *)
  (*               (OHSRC: nth_error ohs_src1 midx = Some oh_src1) *)
  (*               (OHTGT: nth_error ohs_tgt1 midx = Some oh_tgt1) *)
  (*               (OHSWFSRC: LeibEq (projT1 oh_src1) ms_src.(ModSem.owned_heap)) *)
  (*               (OHSWFTGT: LeibEq (projT1 oh_tgt1) ms_tgt.(ModSem.owned_heap)) *)
  (*               (MLE: SimMemOhs.le smos_arg smos_ret) *)
  (*               (MWF: SimMemOhs.wf smos_ret) *)
  (*               (SIMRETV: SimMemOhs.sim_retv midx ohs_src1 ohs_tgt1 retv_src retv_tgt smos_ret) *)
  (*               (AFTERSRC: ms_src.(after_external) st_src0 (cast_sigT oh_src1) retv_src st_src1), *)
  (*               exists st_tgt1 smos_after i1, *)
  (*                 (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 (cast_sigT oh_tgt1) retv_tgt st_tgt1>>) /\ *)
  (*                 (<<MLEPUB: SimMemOhs.le smos0 smos_after>>) /\ *)
  (*                 (<<LXSIM: lxsim i1 st_src1 st_tgt1 smos_after>>)>>))>>) *)
  | lxsim_at_external
      (MWF: SimMemOhs.wf smos0)
      (SAFESRC: ms_src.(is_call) st_src0)
      (SU: forall (SU: DUMMY_PROP),
      <<CALLFSIM: forall oh_src0 args_src
          (* (OHSWFSRC: LeibEq (projT1 (ohs_src0 midx)) ms_src.(ModSem.owned_heap)) *)
          (* (ATSRC: ms_src.(at_external) st_src0 (cast_sigT (ohs_src0 midx)) args_src), *)
          (ATSRC: ms_src.(at_external) st_src0 oh_src0 args_src),
          exists oh_tgt0 args_tgt (smos_arg: SimMemOhs.t),
            (<<SIMARGS: SimMemOhs.sim_args
                          (Midx.update smos0.(SimMemOhs.ohs_src) midx_src (existT id _ oh_src0))
                          (Midx.update smos0.(SimMemOhs.ohs_tgt) midx_tgt (existT id _ oh_tgt0))
                          args_src args_tgt smos_arg>>
            /\ (<<MWF: SimMemOhs.wf smos_arg>>)
            /\ (<<MLE: SimMemOhs.lepriv smos0 smos_arg>>)
            /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 oh_tgt0 args_tgt>>)
            /\ (<<K: forall smos_ret ohs_src1 retv_src ohs_tgt1 retv_tgt st_src1
                (OHSWFSRC: LeibEq (projT1 (ohs_src1 midx_src)) ms_src.(ModSem.owned_heap))
                (OHSWFTGT: LeibEq (projT1 (ohs_tgt1 midx_tgt)) ms_tgt.(ModSem.owned_heap))
                (MLE: SimMemOhs.le smos_arg smos_ret)
                (MWF: SimMemOhs.wf smos_ret)
                (SIMRETV: SimMemOhs.sim_retv ohs_src1 ohs_tgt1 retv_src retv_tgt smos_ret)
                (AFTERSRC: ms_src.(after_external) st_src0 (cast_sigT (ohs_src1 midx_src)) retv_src st_src1),
                exists st_tgt1 smos_after i1,
                  (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 (cast_sigT (ohs_tgt1 midx_tgt)) retv_tgt st_tgt1>>) /\
                  (<<MLEPUB: SimMemOhs.le smos0 smos_after>>) /\
                  (<<LXSIM: lxsim i1 st_src1 st_tgt1 smos_after>>)>>))>>)

  (* | lxsim_final *)
  (*     smos_ret ohs_src ohs_tgt oh_src oh_tgt retv_src retv_tgt *)
  (*     (OHSRC: nth_error ohs_src midx = Some oh_src) *)
  (*     (OHTGT: nth_error ohs_tgt midx = Some oh_tgt) *)
  (*     (OHSWFSRC: LeibEq (projT1 oh_src) ms_src.(ModSem.owned_heap)) *)
  (*     (OHSWFTGT: LeibEq (projT1 oh_tgt) ms_tgt.(ModSem.owned_heap)) *)
  (*     (MLE: SimMemOhs.le smos0 smos_ret) *)
  (*     (MWF: SimMemOhs.wf smos_ret) *)
  (*     (FINALSRC: ms_src.(final_frame) st_src0 (cast_sigT oh_src) retv_src) *)
  (*     (FINALTGT: ms_tgt.(final_frame) st_tgt0 (cast_sigT oh_tgt) retv_tgt) *)
  (*     (SIMRETV: SimMemOhs.sim_retv midx ohs_src ohs_tgt retv_src retv_tgt smos_ret) *)

  | lxsim_final
      smos_ret oh_src oh_tgt retv_src retv_tgt
      (MLE: SimMemOhs.le smos0 smos_ret)
      (MWF: SimMemOhs.wf smos_ret)
      (FINALSRC: ms_src.(final_frame) st_src0 oh_src retv_src)
      (FINALTGT: ms_tgt.(final_frame) st_tgt0 oh_tgt retv_tgt)
      (UPDSRC: smos_ret.(SimMemOhs.ohs_src) =
               Midx.update smos0.(SimMemOhs.ohs_src) midx_src (existT id _ oh_src))
      (UPDTGT: smos_ret.(SimMemOhs.ohs_tgt) =
               Midx.update smos0.(SimMemOhs.ohs_tgt) midx_tgt (existT id _ oh_tgt))
      (SIMRETV: SimMemOhs.sim_retv
                  (smos_ret.(SimMemOhs.ohs_src))
                  (smos_ret.(SimMemOhs.ohs_tgt))
                  retv_src retv_tgt smos_ret)
  .


  Definition _lxsim (lxsim: idx -> state ms_src -> state ms_tgt -> SimMemOhs.t -> Prop)
             (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smos0: SimMemOhs.t): Prop :=
    (forall (SUSTAR: forall st_src1 tr (STAR: Star ms_src st_src0 tr st_src1), sound_states st_src1),
        <<LXSIM: _lxsim_pre lxsim i0 st_src0 st_tgt0 smos0>>).

  Definition lxsim: _ -> _ -> _ -> _ -> Prop := paco4 _lxsim bot4.

  Lemma lxsim_mon: monotone4 _lxsim.
  Proof.
    repeat intro. rr in IN. hexploit1 IN; eauto. inv IN; eauto.
    - econs 1; ss. ii. spc SU. des. esplits; eauto. inv SU.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss. ii. exploit SU; eauto. i; des.
      inv H.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto. ii; ss. exploit SU; eauto. i; des.
      esplits; eauto. ii. exploit K; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Module ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SMOS: SimMemOhs.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: ModSem.t;
    tgt: ModSem.t;
    ss: SimSymb.t;
    sm: SimMem.t;
  }.

  Inductive sim_skenv (msp: t) (sm0: SimMem.t): Prop :=
  | sim_skenv_intro
    (SIMSKE: SimSymb.sim_skenv sm0 msp.(ss) msp.(src).(ModSem.skenv) msp.(tgt).(ModSem.skenv))
    ss_link
    (SIMSKELINK: SimSymb.sim_skenv sm0 ss_link msp.(src).(ModSem.skenv_link) msp.(tgt).(ModSem.skenv_link)).

  Lemma mfuture_preserves_sim_skenv
        msp sm0 sm1
        (MFUTURE: SimMem.future sm0 sm1)
        (SIMSKENV: sim_skenv msp sm0):
      <<SIMSKENV: sim_skenv msp sm1>>.
  Proof.
    inv SIMSKENV. econs; eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
  Qed.

  Inductive sim (msp: t): Prop :=
  | sim_intro
      sidx sound_states sound_state_ex
      (MIDX: msp.(src).(midx) = msp.(tgt).(midx))
      (PRSV: local_preservation msp.(src) sound_state_ex)
      (PRSVNOGR: forall (si: sidx), local_preservation_noguarantee msp.(src) (sound_states si))
      (SIM: forall
          (sm_arg: SimMemOhs.t) ohs_src ohs_tgt
          (oh_src: msp.(src).(owned_heap)) (oh_tgt: msp.(tgt).(owned_heap))
          args_src args_tgt
          (* (OHSRC: nth_error ohs_src msp.(src).(midx) = Some oh_src) *)
          (* (OHTGT: nth_error ohs_tgt msp.(tgt).(midx) = Some oh_tgt) *)
          (* (TYSRC: LeibEq (projT1 oh_src) msp.(src).(ModSem.owned_heap)) *)
          (* (TYTGT: LeibEq (projT1 oh_tgt) msp.(tgt).(ModSem.owned_heap)) *)
          (* sg_init_src sg_init_tgt *)
          (* (FINDFSRC: (Genv.find_funct msp.(src).(ModSem.skenv)) (Args.get_fptr args_src) = *)
          (*            Some (Internal sg_init_src)) *)
          (* (FINDFTGT: (Genv.find_funct msp.(tgt).(ModSem.skenv)) (Args.get_fptr args_tgt) = *)
          (*            Some (Internal sg_init_tgt)) *)
          (* (SIMARGS: SimMemOhs.sim_args msp.(src).(midx) ohs_src ohs_tgt args_src args_tgt sm_arg) *)
          (TYSRC: LeibEq (projT1 (ohs_src msp.(src).(midx))) msp.(src).(ModSem.owned_heap))
          (TYTGT: LeibEq (projT1 (ohs_tgt msp.(tgt).(midx))) msp.(tgt).(ModSem.owned_heap))
          (OHSRC: oh_src = (cast_sigT (ohs_src msp.(src).(midx))))
          (OHTGT: oh_tgt = (cast_sigT (ohs_tgt msp.(tgt).(midx))))
          sg_init_src sg_init_tgt
          (FINDFSRC: (Genv.find_funct msp.(src).(ModSem.skenv)) (Args.get_fptr args_src) =
                     Some (Internal sg_init_src))
          (FINDFTGT: (Genv.find_funct msp.(tgt).(ModSem.skenv)) (Args.get_fptr args_tgt) =
                     Some (Internal sg_init_tgt))
          (SIMARGS: SimMemOhs.sim_args ohs_src ohs_tgt args_src args_tgt sm_arg)

          (SIMSKENV: sim_skenv msp sm_arg)
          (MFUTURE: SimMem.future msp.(sm) sm_arg)
          (MWF: SimMemOhs.wf sm_arg),
          (<<INITBSIM: forall st_init_tgt
              (INITTGT: (msp.(tgt).(initial_frame)) oh_tgt args_tgt st_init_tgt)
              (SAFESRC: exists _st_init_src,
                  (msp.(src).(initial_frame)) oh_src args_src _st_init_src),
              exists st_init_src sm_init idx_init,
                (<<MLE: SimMemOhs.le sm_arg sm_init>>) /\
                (<<INITSRC: msp.(src).(initial_frame) oh_src args_src st_init_src>>) /\
                (<<SIM: lxsim msp.(src) msp.(tgt) (fun st => forall si, exists su m_init, sound_states si su m_init st)
                                                  idx_init st_init_src st_init_tgt sm_init>>)>>) /\
          (<<INITPROGRESS: forall
              (SAFESRC: exists st_init_src, msp.(src).(initial_frame) oh_src args_src st_init_src),
              exists st_init_tgt, (<<INITTGT: msp.(tgt).(initial_frame) oh_tgt args_tgt st_init_tgt>>)>>)).

End MODSEMPAIR.
End ModSemPair.

Arguments ModSemPair.mk [SM] [SS] _ _ _.
Hint Constructors ModSemPair.sim_skenv.
(* End Ohs. *)

Hint Unfold lxsim.
Hint Resolve lxsim_mon: paco.




Require SimModSem.
Module _ModSemPair := SimModSem.ModSemPair.

Definition msp_to_msp SM SS (msp: @_ModSemPair.t SM SS): ModSemPair.t :=
  ModSemPair.mk (msp.(_ModSemPair.src)) (msp.(_ModSemPair.tgt))
                (msp.(_ModSemPair.ss)) (msp.(_ModSemPair.sm)).

Lemma cast_sigT_eq
      Y (x: {ty: Type & ty}) (y: Y)
      (JMEQ: projT2 x ~= y)
      (LEIBEQ: LeibEq (projT1 x) Y)
  :
    cast_sigT x = y
.
Proof.
  unfold cast_sigT. unfold eq_rect_r. ss. des_ifs. ss.
  unfold eq_rect. des_ifs.
Qed.

Lemma cast_sigT_proj
      Y (x: {ty: Type & ty}) (y: Y)
      (LEIBEQ: LeibEq (projT1 x) Y)
      (EQ: cast_sigT x = y)
  :
      <<JMEQ: projT2 x ~= y>>
.
Proof.
  unfold cast_sigT in *. ss. des_ifs. ss. unfold eq_rect. des_ifs.
Qed.

Coercion _ModSemPair.SMO: _ModSemPair.t >-> SimMemOh.class.
(* Definition sm_match SM SS {SMOS: SimMemOhs.class} (msp: @ModSemPair.t SM SS): *)
(*   (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)) -> SimMemOhs.t -> Prop := *)
(*   (* TODO: I want to remove @ *) *)
(*   fun smo smos => *)
(*     (smos.(SimMemOhs.sm) = smo.(SimMemOh.sm)) /\ *)
(*     (projT2 (smos.(SimMemOhs.ohs_src) (msp.(ModSemPair.src).(midx))) *)
(*             ~= smo.(SimMemOh.oh_src)) /\ *)
(*     (projT2 (smos.(SimMemOhs.ohs_tgt) (msp.(ModSemPair.src).(midx))) *)
(*             ~= smo.(SimMemOh.oh_tgt)) *)
(* . *)
Record sm_match SM SS {SMOS: SimMemOhs.class} (msp: @_ModSemPair.t SM SS)
  (smo: (@SimMemOh.t _ _ _ msp.(_ModSemPair.SMO))) (smos: SimMemOhs.t): Prop :=
  (* TODO: I want to remove @ *)
  { smeq: (smos.(SimMemOhs.sm) = smo.(SimMemOh.sm));
    ohsrcty: (projT1 (smos.(SimMemOhs.ohs_src) (msp.(_ModSemPair.src).(midx)))) =
             msp.(_ModSemPair.src).(owned_heap);
    ohtgtty: (projT1 (smos.(SimMemOhs.ohs_tgt) (msp.(_ModSemPair.tgt).(midx)))) =
             msp.(_ModSemPair.tgt).(owned_heap);
    ohsrc: (projT2 (smos.(SimMemOhs.ohs_src) (msp.(_ModSemPair.src).(midx)))
                   ~= smo.(SimMemOh.oh_src));
    ohtgt: (projT2 (smos.(SimMemOhs.ohs_tgt) (msp.(_ModSemPair.tgt).(midx)))
                   ~= smo.(SimMemOh.oh_tgt))
    (* oh_src: {oh: Type & oh}; *)
    (* oh_tgt: {oh: Type & oh}; *)
    (* OHSRC: (nth_error smos.(SimMemOhs.ohs_src) (msp.(ModSemPair.src).(midx))) = Some oh_src; *)
    (* OHTGT: (nth_error smos.(SimMemOhs.ohs_tgt) (msp.(ModSemPair.tgt).(midx))) = Some oh_tgt; *)
    (* ohsrcty: (projT1 oh_src) = msp.(ModSemPair.src).(owned_heap); *)
    (* ohtgtty: (projT1 oh_tgt) = msp.(ModSemPair.tgt).(owned_heap); *)
    (* ohsrc: (projT2 oh_src ~= smo.(SimMemOh.oh_src)); *)
    (* ohtgt: (projT2 oh_tgt ~= smo.(SimMemOh.oh_tgt)) *)
}
.

Lemma sigT_eta
      (a: { A: Type & A})
      (b: { B: Type & B})
      (EQTY: projT1 a = projT1 b)
      (EQVAL: projT2 a ~= projT2 b)
  :
    a = b
.
Proof.
  destruct a, b; ss. clarify. apply JMeq_eq in EQVAL. clarify.
Qed.

Inductive good_properties SM {SS: SimSymb.class SM}
          (SMOS: SimMemOhs.class) (msp: _ModSemPair.t): Prop :=
| good_properties_intro
    (SMPROJ: forall smos (MWF: SimMemOhs.wf smos),
        exists smo, sm_match msp smo smos /\ SimMemOh.wf smo)
    (SMSIM: forall (smos0: SimMemOhs.t)
                   (smo0 smo1: SimMemOh.t)
                   (LE: SimMemOh.le smo0 smo1)
                   (SMMATCH: sm_match msp smo0 smos0)
                   (WFWF: SimMemOh.wf smo0 -> SimMemOhs.wf smos0)
      ,
        exists smos1, (<<SMSTEPBIG: SimMemOhs.le smos0 smos1>>)
                      /\ (<<SMMATCH: sm_match msp smo1 smos1>>)
                      /\ (<<WFWF: SimMemOh.wf smo1 -> SimMemOhs.wf smos1>>))
    (SMSIMPRIV: forall (smos0: SimMemOhs.t)
                       (smo0 smo1: SimMemOh.t)
                       (SMMATCH: sm_match msp smo0 smos0)
                       (LE: SimMemOh.lepriv smo0 smo1)
                       (WFWF: SimMemOh.wf smo0 -> SimMemOhs.wf smos0)
      ,
        exists smos1, (<<SMSTEPBIG: SimMemOhs.lepriv smos0 smos1>>)
                      /\ (<<SMMATCH: sm_match msp smo1 smos1>>)
                      /\ (<<WFWF: SimMemOh.wf smo1 -> SimMemOhs.wf smos1>>))
    (SMMATCHLE: forall smo0 smo1 smos0 smos1
                       (SMMATCH0: sm_match msp smo0 smos0)
                       (SMMATCH1: sm_match msp smo1 smos1)
                       (SMLE: SimMemOhs.le smos0 smos1)
      ,
        <<SMLE: SimMemOh.le smo0 smo1>>
    )
.


Theorem fundamental_theorem
        SM SMOS SS SU
        msp
        (SIM: msp.(@_ModSemPair.sim SM SS SU))
  :
    (msp_to_msp msp).(@ModSemPair.sim SM SMOS SS SU)
.
Proof.
  inv SIM.
  econs; eauto.
  clear - MIDX SIM0. ss.
  ii.
  (* assert(SMPROJ: forall smos: SimMemOhs.t, *)
  (*           exists smo: SimMemOh.t, sm_match msp smo smos). *)
  assert(SMPROJ: forall smos (MWF: SimMemOhs.wf smos),
            exists smo, sm_match msp smo smos /\ SimMemOh.wf smo).
  { admit "". }
  assert(SMSIM: forall (smos0: SimMemOhs.t)
                       (smo0 smo1: SimMemOh.t)
                       (LE: SimMemOh.le smo0 smo1)
                       (SMMATCH: sm_match msp smo0 smos0)
                       (WFWF: SimMemOh.wf smo0 -> SimMemOhs.wf smos0)
          ,
            exists smos1, (<<SMSTEPBIG: SimMemOhs.le smos0 smos1>>)
                          /\ (<<SMMATCH: sm_match msp smo1 smos1>>)
                          /\ (<<WFWF: SimMemOh.wf smo1 -> SimMemOhs.wf smos1>>)
                          /\ (<<UNCHSRC: forall mi (NEQ: mi <> midx (_ModSemPair.src msp)),
                                 SimMemOhs.ohs_src smos0 mi = SimMemOhs.ohs_src smos1 mi>>)
                          /\ (<<UNCHTGT: forall mi (NEQ: mi <> midx (_ModSemPair.tgt msp)),
                                 SimMemOhs.ohs_tgt smos0 mi = SimMemOhs.ohs_tgt smos1 mi>>)
        ).
  { admit "". }
  assert(SMSIMPRIV: forall (smos0: SimMemOhs.t)
                           (smo0 smo1: SimMemOh.t)
                           (SMMATCH: sm_match msp smo0 smos0)
                           (LE: SimMemOh.lepriv smo0 smo1)
                           (WFWF: SimMemOh.wf smo0 -> SimMemOhs.wf smos0)
          ,
            exists smos1, (<<SMSTEPBIG: SimMemOhs.lepriv smos0 smos1>>)
                          /\ (<<SMMATCH: sm_match msp smo1 smos1>>)
                          /\ (<<WFWF: SimMemOh.wf smo1 -> SimMemOhs.wf smos1>>)
                          /\ (<<UNCHSRC: forall mi (NEQ: mi <> midx (_ModSemPair.src msp)),
                                 SimMemOhs.ohs_src smos0 mi = SimMemOhs.ohs_src smos1 mi>>)
                          /\ (<<UNCHTGT: forall mi (NEQ: mi <> midx (_ModSemPair.tgt msp)),
                                 SimMemOhs.ohs_tgt smos0 mi = SimMemOhs.ohs_tgt smos1 mi>>)
        ).
  { admit "". }
  assert(SMMATCHLE: forall smo0 smo1 smos0 smos1
                           (SMMATCH0: sm_match msp smo0 smos0)
                           (SMMATCH1: sm_match msp smo1 smos1)
                           (SMLE: SimMemOhs.le smos0 smos1)
          ,
            <<SMLE: SimMemOh.le smo0 smo1>>
        ).
  { admit "". }
  assert(PROJARGS := SMPROJ sm_arg MWF). des. rename smo into sm_arg_proj.
  assert(ARGS: SimMemOh.sim_args (sm_arg_proj.(SimMemOh.oh_src))
                                 (sm_arg_proj.(SimMemOh.oh_tgt))
                                 args_src args_tgt sm_arg_proj).
  { rr. esplits; eauto. rr in SIMARGS. des. erewrite <- smeq; eauto. }
  exploit SIM0; eauto.
  { erewrite <- smeq; eauto. inv SIMSKENV. econs; eauto. }
  { erewrite <- smeq; eauto. }
  ii; des.
  assert(OHSRC0: oh_src = (SimMemOh.oh_src sm_arg_proj)).
  { clear - MIDX SIMARGS OHSRC TYSRC PROJARGS. clarify.
    rr in SIMARGS. des.
    eapply cast_sigT_eq; eauto.
    etrans; try eapply ohsrc; eauto. rewrite OHSRC. ss.
  }
  assert(OHTGT0: oh_tgt = (SimMemOh.oh_tgt sm_arg_proj)).
  { clear - MIDX SIMARGS OHTGT TYTGT PROJARGS. clarify.
    rr in SIMARGS. des.
    eapply cast_sigT_eq; eauto. rewrite <- MIDX. ss.
    etrans; try eapply ohtgt; eauto. rewrite OHTGT. rewrite MIDX. ss.
  }
  (* assert(OHSRC0: (cast_sigT oh_src) = (SimMemOh.oh_src sm_arg_proj)). *)
  (* { rr in SIMARGS. des. eapply cast_sigT_eq; eauto. *)
  (*   inv PROJARGS. *)
  (*   rewrite <- OHSRC0 in *. rewrite MIDX in OHTGT0. rewrite <- OHTGT0 in *. clarify. *)
  (* } *)
  (* assert(OHTGT0: (cast_sigT oh_tgt) = (SimMemOh.oh_tgt sm_arg_proj)). *)
  (* { rr in SIMARGS. des. eapply cast_sigT_eq; eauto. *)
  (*   inv PROJARGS. *)
  (*   rewrite <- OHSRC0 in *. rewrite MIDX in OHTGT0. rewrite <- OHTGT0 in *. clarify. *)
  (* } *)
  split; ss.
  - clear INITPROGRESS. ii. exploit INITBSIM; eauto.
    { rewrite <- OHTGT0. eauto. }
    { des. esplits; eauto. rewrite <- OHSRC0. eauto. }
    i; des.
    exploit (SMSIM sm_arg); eauto. i; des.
    exists st_init_src. esplits; eauto.
    { rewrite OHSRC0. ss. }
    instantiate (1:= idx_init).
    clear - SIM SMSIM SMSIMPRIV SMPROJ SMMATCH SMMATCHLE MIDX WFWF.
    rename sm_init into smo0. rename smos1 into smos0.
    rename st_init_src into st_src0. rename st_init_tgt into st_tgt0.
    (* assert(WF: SimMemOhs.wf smos0). *)
    (* { admit "TODO". } *)
    (* assert(SMWFWF: SimMemOh.wf smo0 -> SimMemOhs.wf smos0). *)
    (* { i. } *)



    revert_until SMSIM. pcofix CIH. i. pfold.
    punfold SIM. rr in SIM. ii. exploit SIM; eauto. intro T; des. inv T.
    + econs 1; eauto. ii. hexploit1 SU0; ss. inv SU0.
      * econs 1; eauto. ii. exploit STEP; eauto. i; des_safe.
        exploit SMSIM; eauto. i; des_safe.
        esplits; eauto. pclearbot. right. eapply CIH; eauto.
      * exploit (SMSIM smos0); eauto. i; des.
        econs 2; eauto. pclearbot. right. eapply CIH; eauto.
    + econs 2; eauto. ii. hexploit1 SU0; ss. r in SU0. hexploit1 SU0; ss. inv SU0.
      * econs 1; eauto. ii. exploit STEP; eauto. i; des_safe.
        exploit SMSIM; eauto. i; des_safe.
        esplits; eauto. pclearbot. right. eapply CIH; eauto.
      * exploit (SMSIM smos0); eauto. i; des.
        econs 2; eauto. pclearbot. right. eapply CIH; eauto.
    + econs 3; eauto.
      (* { admit "WF - Hard: Small to big.". } *)
      ii. exploit SU0; eauto. i; des. exploit SMSIMPRIV; eauto. i; des.
      esplits; try apply WFWF0; eauto.
      * rr in SIMARGS. des. rr. esplits; eauto.
        { erewrite smeq; eauto. }
        { apply func_ext1. intro mi. unfold Midx.update. des_ifs; eauto.
          eapply sigT_eta; eauto.
          - erewrite ohsrcty; eauto.
          - ss. erewrite ohsrc; eauto.
        }
        { apply func_ext1. intro mi. unfold Midx.update. des_ifs; eauto.
          eapply sigT_eta; eauto.
          - erewrite ohtgtty; eauto.
          - ss. erewrite ohtgt; eauto.
        }
      * i. hexploit (SMPROJ smos_ret); eauto. intro T; des.
        exploit K.
        { eapply SMMATCHLE; et. }
        { ss. }
        { rr in SIMRETV. des. rr. erewrite <- smeq; eauto. }
        { rp; eauto. symmetry. eapply cast_sigT_eq; eauto.
          rr in SIMRETV. des. rewrite OHSRC. erewrite <- ohsrc; eauto. }
        i; des.
        hexploit (SMSIM _ _ _ MLEPUB SMMATCH); eauto. i; des.
        esplits; eauto.
        { rp; eauto. eapply cast_sigT_eq; eauto.
          rr in SIMRETV. des. rewrite OHTGT. erewrite <- ohtgt; eauto.
        }
        pclearbot. right. eapply CIH; eauto.
    + exploit SMSIM; eauto. i; des.
      assert(OHSWFSRC: LeibEq (projT1 (smos1.(SimMemOhs.ohs_src)
                                               (msp.(_ModSemPair.src).(midx))))
                              msp.(_ModSemPair.src).(owned_heap)).
      { econs. erewrite ohsrcty; eauto. }
      assert(OHSWFTGT: LeibEq (projT1 (smos1.(SimMemOhs.ohs_tgt)
                                               (msp.(_ModSemPair.tgt).(midx))))
                              msp.(_ModSemPair.tgt).(owned_heap)).
      { econs. erewrite ohtgtty; eauto. }

      rr in SIMRETV. des. rr. econs 4; eauto.
      * apply func_ext1. intro mi. unfold Midx.update. des_ifs.
        { eapply sigT_eta; eauto using ohsrcty, ohsrc. }
        erewrite UNCHSRC; eauto.
      * apply func_ext1. intro mi. unfold Midx.update. des_ifs.
        { eapply sigT_eta; eauto using ohtgtty, ohtgt. }
        erewrite UNCHTGT; eauto.
      * rr. esplits; eauto. erewrite smeq; eauto.
  - ii. des. exploit INITPROGRESS; eauto.
    { esplits; eauto. rewrite <- OHSRC0. eauto. }
    i; des. esplits; eauto. rewrite <- OHTGT0 in INITTGT. eauto.
Qed.
