Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem GlobalenvsC MemoryC ASTC.
Require Import Skeleton SimModSem SimMemLift SimSymb.
Require Import Sound Preservation.
Require Import ModSemProps.
Require MatchSimModSemExcl.
Require Import Any Cast.

Set Implicit Arguments.




Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.
  Context {SML: SimMemLift.class SM}.

  Variable msp: ModSemPair.t.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.
  Let ms_src: ModSem.t := msp.(ModSemPair.src).
  Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt).
  Variable sound_state: Sound.t -> mem -> ms_src.(state) -> Prop.
  Hypothesis PRSV: local_preservation ms_src sound_state.

  Variable match_states: forall
      (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMem.t),
      Prop.

  Variable match_states_at: forall
      (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMem.t),
      Prop.

  Hypothesis OHSRC: ms_src.(ModSem.owned_heap) = unit.
  Hypothesis OHTGT: ms_tgt.(ModSem.owned_heap) = unit.
  Let OHSRCCAST: LeibEq ms_src.(ModSem.owned_heap) unit. Proof. econs; ss. Qed.
  Let OHSRCCAST_REV: LeibEq unit ms_src.(ModSem.owned_heap). Proof. econs; ss. Qed.
  Let OHTGTCAST: LeibEq ms_tgt.(ModSem.owned_heap) unit. Proof. econs; ss. Qed.
  Let OHTGTCAST_REV: LeibEq unit ms_tgt.(ModSem.owned_heap). Proof. econs; ss. Qed.
  Local Existing Instance OHSRCCAST.
  Local Existing Instance OHSRCCAST_REV.
  Local Existing Instance OHTGTCAST.
  Local Existing Instance OHTGTCAST_REV.
  Hypothesis MIDXSRC: ms_src.(ModSem.midx) = None.
  Hypothesis MIDXTGT: ms_tgt.(ModSem.midx) = None.
  
  Let SMO := (ModSemPair.SMO msp).
  Local Existing Instance SMO.
  Hypothesis SMOCLASS: SMO = (SimMemOh_default _).
  Let SMOT: LeibEq SimMemOh.t SimMem.t. Proof. econs. rewrite SMOCLASS. ss. Qed.
  Let SMOT_REV: LeibEq SimMem.t SimMemOh.t. Proof. econs. rewrite SMOCLASS. ss. Qed.
  Local Existing Instance SMOT.
  Local Existing Instance SMOT_REV.

  Let SMOLE: forall (smo0 smo1: SimMemOh.t), SimMem.le smo0 smo1 -> SimMemOh.le smo0 smo1.
  Proof. rewrite SMOCLASS. ss. Qed.
  Let SMOLEPRIV: forall (smo0 smo1: SimMemOh.t), SimMem.lepriv smo0 smo1 -> SimMemOh.lepriv smo0 smo1.
  Proof. rewrite SMOCLASS. ss. Qed.
  Let SMOWF: forall (smo0: SimMemOh.t), SimMem.wf smo0 -> SimMemOh.wf smo0.
  Proof. rewrite SMOCLASS. ss. Qed.

  Let SMLE: forall (smo0 smo1: SimMemOh.t), SimMemOh.le smo0 smo1 -> SimMem.le smo0 smo1.
  Proof. rewrite SMOCLASS. ss. Qed.
  Let SMLEPRIV: forall (smo0 smo1: SimMemOh.t), SimMemOh.lepriv smo0 smo1 -> SimMem.lepriv smo0 smo1.
  Proof. rewrite SMOCLASS. ss. Qed.
  Let SMWF: forall (smo0: SimMemOh.t), SimMemOh.wf smo0 -> SimMem.wf smo0.
  Proof. rewrite SMOCLASS. ss. Qed.

  Let SMOOHSRC: forall (smo0: SimMemOh.t), SimMemOh.oh_src smo0 = upcast tt.
  Proof. rewrite SMOCLASS. ss. Qed.
  Let SMOOHTGT: forall (smo0: SimMemOh.t), SimMemOh.oh_tgt smo0 = upcast tt.
  Proof. rewrite SMOCLASS. ss. Qed.

  Let CASTELIMSRC: forall (oh_src: ms_src.(ModSem.owned_heap)), (cast tt = oh_src).
  Proof.
    remember (ModSem.owned_heap ms_src) as X. clear HeqX. ii. clarify.
    des_u. rewrite cast_elim. ss.
  Qed.

  Let CASTELIMTGT: forall (oh_tgt: ms_tgt.(ModSem.owned_heap)), (cast tt = oh_tgt).
  Proof.
    remember (ModSem.owned_heap ms_tgt) as X. clear HeqX. ii. clarify.
    des_u. rewrite cast_elim. ss.
  Qed.

  Let CASTELIMSM: forall (sm0: SimMem.t), SimMemOh.sm (@cast SimMem.t SimMemOh.t _ sm0) = sm0.
  Proof.
    remember SMO as X. clear HeqX. ii. clarify. ss.
    rewrite cast_elim. ss.
  Qed.

  Let CASTELIMSMO: forall (sm0: SimMemOh.t), cast sm0 = (SimMemOh.sm sm0).
  Proof.
    remember SMO as X. clear HeqX. ii. clarify. ss.
    rewrite cast_elim. ss.
  Qed.

  Inductive match_states_at_helper
            (idx_at: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMem.t): Prop :=
  | match_states_at_intro
      (MATCH: match_states idx_at st_src0 st_tgt0 sm_at)
      args_src args_tgt
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 (cast tt) args_src)
      (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 (cast tt) args_tgt)
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      (MLE: SimMem.le sm_at sm_arg)
      (MWF: SimMem.wf sm_arg)
      (MATCHARG: match_states_at st_src0 st_tgt0 sm_at sm_arg).

  Hypothesis INITBSIM: forall sm_arg args_src args_tgt st_init_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      (INITTGT: ms_tgt.(ModSem.initial_frame) (cast tt) args_tgt st_init_tgt)
      (SAFESRC: exists _st_init_src, ms_src.(ModSem.initial_frame) (cast tt) args_src _st_init_src),
      exists st_init_src sm_init idx_init,
        (<<INITSRC: ms_src.(ModSem.initial_frame) (cast tt) args_src st_init_src>>) /\
        (<<MLE: SimMem.le sm_arg sm_init>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm_arg sm_init>>) /\
        (<<MATCH: match_states idx_init st_init_src st_init_tgt sm_init>>).

  Hypothesis INITPROGRESS: forall sm_arg args_src args_tgt
      (SIMSKENV: ModSemPair.sim_skenv msp sm_arg)
      (MWF: SimMem.wf sm_arg)
      (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
      (SAFESRC: exists st_init_src, ms_src.(ModSem.initial_frame) (cast tt) args_src st_init_src),
      exists st_init_tgt, (<<INITTGT: ms_tgt.(ModSem.initial_frame) (cast tt) args_tgt st_init_tgt>>).

  Hypothesis ATMWF: forall idx0 st_src0 st_tgt0 sm0
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.is_call) st_src0),
      <<MWF: SimMem.wf sm0>>.

  Hypothesis ATFSIM: forall idx0 st_src0 st_tgt0 sm0 args_src
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (CALLSRC: ms_src.(ModSem.at_external) st_src0 (cast tt) args_src)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0),
      exists args_tgt sm_arg,
        (<<CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 (cast tt) args_tgt>>) /\
        (<<SIMARGS: SimMem.sim_args args_src args_tgt sm_arg>>) /\
        (<<MLE: SimMem.le sm0 sm_arg>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_arg>>) /\
        (<<MWF: SimMem.wf sm_arg>>) /\
        (<<MATCHAT: match_states_at st_src0 st_tgt0 sm0 sm_arg>>).

  Hypothesis AFTERFSIM: forall idx0 st_src0 st_tgt0 sm0 sm_arg sm_ret retv_src retv_tgt st_src1
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (MLE: SimMem.le sm0 sm_arg)
      (* (MWF: SimMem.wf sm_arg) *)
      (MLE: SimMem.le (SimMemLift.lift sm_arg) sm_ret)
      (MWF: SimMem.wf sm_ret)
      (SIMRET: SimMem.sim_retv retv_src retv_tgt sm_ret)
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 (cast tt) retv_src st_src1)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0)

      (* history *)
      (HISTORY: match_states_at_helper idx0 st_src0 st_tgt0 sm0 sm_arg)

      (* just helpers *)
      (MWFAFTR: SimMem.wf (SimMemLift.unlift sm_arg sm_ret))
      (MLEAFTR: SimMem.le sm_arg (SimMemLift.unlift sm_arg sm_ret)),
      exists sm_after idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 (cast tt) retv_tgt st_tgt1>>) /\
        (<<MATCH: match_states idx1 st_src1 st_tgt1 sm_after>>) /\
        (<<MLE: SimMem.le (SimMemLift.unlift sm_arg sm_ret) sm_after>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx (SimMemLift.unlift sm_arg sm_ret) sm_after>>)
  .

  Hypothesis FINALFSIM: forall idx0 st_src0 st_tgt0 sm0 retv_src
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (FINALSRC: ms_src.(ModSem.final_frame) st_src0 (cast tt) retv_src),
      exists sm_ret retv_tgt,
        (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 (cast tt) retv_tgt>>) /\
        (<<SIMRET: SimMem.sim_retv retv_src retv_tgt sm_ret>>) /\
        (<<MLE: SimMem.le sm0 sm_ret>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_ret>>) /\
        (<<MWF: SimMem.wf sm_ret>>).

  Let STEPFSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<RECEP: receptive_at ms_src st_src0>>) /\
      (<<STEPFSIM: forall tr st_src1
             (STEPSRC: Step ms_src st_src0 tr st_src1) ,
             exists idx1 st_tgt1 sm1,
               (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/
                           <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Let STEPBSIM idx0 st_src0 st_tgt0 sm0 :=
      (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) /\
      (<<STEPBSIM: forall tr st_tgt1
             (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1)
             (SAFESRC: safe_modsem ms_src st_src0),
             exists idx1 st_src1 sm1,
               (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/
                           <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Hypothesis STEPSIM: forall idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0),
      STEPFSIM idx0 st_src0 st_tgt0 sm0 \/ STEPBSIM idx0 st_src0 st_tgt0 sm0.

  Remark safe_modsem_is_smaller
         st_src0
         (NOTCALL: ~ ModSem.is_call ms_src st_src0)
         (NOTRET: ~ ModSem.is_return ms_src st_src0)
         (SAFE: safe_modsem ms_src st_src0):
      ModSem.is_step ms_src st_src0.
  Proof. rr. specialize (SAFE _ (star_refl _ _ _ _)). des; ss. eauto. Qed.

  Hypothesis BAR: bar_True.

  (** TODO: Changing this definition to "Let" breaks the proof -- why ?? **)
  Definition mle_excl: ms_src.(ModSem.state) -> ms_tgt.(ModSem.state) -> SimMemOh.t -> SimMemOh.t -> Prop :=
    fun _ _ => SimMem.le.

  Let _match_states (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state))
             (sm0: SimMemOh.t): Prop := match_states idx st_src0 st_tgt0 sm0
  .

  Let _match_states_at (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state))
                                                         (sm_at sm_arg: SimMem.t): Prop :=
    match_states_at st_src0 st_tgt0 sm_at sm_arg
  .

  Theorem match_states_sim: <<SIM: msp.(ModSemPair.sim)>>.
  Proof.
    eapply MatchSimModSemExcl.match_states_sim with
        (has_footprint := top3) (mle_excl := mle_excl) (sidx := unit) (match_states0 := _match_states)
        (match_states_at0 := _match_states_at)
    ;
      eauto using SimMemOh.wf_proj; ss.
    { ii. eapply PRSV. }
    { ii. r. etrans; eauto. }
    { clear - SMOCLASS MIDXSRC. subst SMO. rewrite SMOCLASS. subst ms_src. rewrite MIDXSRC. ss. }
    { clear - MIDXSRC MIDXTGT. subst ms_src. rewrite MIDXSRC. subst ms_tgt. rewrite MIDXTGT. ss. }
    { ii. rr in SIMARGS. des.
      (* rewrite SMOOHSRC in *. rewrite SMOOHTGT in *. clarify. *)
      exploit INITBSIM; ss; et.
      { rp; et. }
      { esplits; et. rp; et. }
      i; des.
      clear SAFESRC.
      esplits; et.
      { rp; et. }
      { instantiate (1:= cast sm_init). eapply SMOLE; et. rp; et. }
      { rp; et. }
      r. rp; et.
    }
    { ii. rr in SIMARGS. des.
      exploit INITPROGRESS; et.
      { esplits; et. rp; et. }
      i; des. esplits; et. rp; et.
    }
    { ii. exploit ATMWF; et. }
    { ii. exploit ATFSIM; et.
      { rp; et. }
      { exploit SOUND; et. ss. }
      i; des.
      esplits; et.
      { rr. esplits; et.
        - rp; et.
        - clear - CASTELIMSRC SMOOHSRC SMOCLASS OHSRCCAST OHSRCCAST_REV OHSRC.
          subst SMO. subst ms_src. rewrite SMOOHSRC. ss.
          revert oh_src.
          rewrite OHSRC. ii; ss. clarify.
        - clear - CASTELIMTGT SMOOHTGT SMOCLASS OHTGTCAST OHTGTCAST_REV OHTGT.
          subst SMO. subst ms_tgt. rewrite SMOOHTGT.
          eapply Any_eta; ss. rewrite ! upcast_projT2.
          remember (@cast unit (ModSem.owned_heap (@ModSemPair.tgt SM SS msp)) OHTGTCAST_REV tt) as X.
          clear HeqX. clear CASTELIMTGT. revert X. rewrite OHTGT. i; clarify.
      }
      { eapply SMOLE; et. rp; et. }
      { rp; et. }
      { eapply SMOWF; et. rp; et. Undo 1. (*** TODO :Fix it ***)
        erewrite f_equal with (f:=SimMem.wf); et.
      }
      { rp; et. }
    }
    { ii. rr in SIMRET. des.
      exploit (@AFTERFSIM idx0 st_src0 st_tgt0 sm0 sm_arg sm_ret); et.
      { eapply SMLE in MLE0. erewrite (SimMemOh.getset_sm (class := SMO)) in *. ss. }
      { rp; et. }
      { exploit SOUND; ss; et. }
      { inv HISTORY. rr in SIMARGS. des. econs; et.
        - rp; et.
        - rp; et.
      }
      { eapply SMWF in MWFAFTR. erewrite (SimMemOh.getset_sm (class := SMO)) in *. ss. }
      { eapply SMLE in MLEAFTR. erewrite (SimMemOh.getset_sm (class := SMO)) in *. ss. }
      i; des.
      esplits; et.
      { r. erewrite (SimMemOh.getset_sm (class := SMO)) in *. instantiate (1:= cast sm_after).
        rp; et. Undo 1. (*** TODO: FIX IT ***)
        erewrite f_equal2 with (f:=SimMem.le); et.
      }
      { rp; et. erewrite (SimMemOh.getset_sm (class := SMO)) in *. ss. }
      { i; des. esplits; et.
        - rp; et.
        - r. rp; et.
      }
    }
    { ii. exploit FINALFSIM; et.
      { rp; et. }
      i; des.
      esplits; et.
      { rr. esplits; et.
        - rp; et.
        - clear - CASTELIMSRC SMOOHSRC SMOCLASS OHSRCCAST OHSRCCAST_REV OHSRC.
          subst SMO. subst ms_src. rewrite SMOOHSRC. ss.
          revert oh_src.
          rewrite OHSRC. ii; ss. clarify.
        - clear - CASTELIMTGT SMOOHTGT SMOCLASS OHTGTCAST OHTGTCAST_REV OHTGT.
          subst SMO. subst ms_tgt. rewrite SMOOHTGT.
          eapply Any_eta; ss. rewrite ! upcast_projT2.
          remember (@cast unit (ModSem.owned_heap (@ModSemPair.tgt SM SS msp)) OHTGTCAST_REV tt) as X.
          clear HeqX. clear CASTELIMTGT. revert X. rewrite OHTGT. i; clarify.
      }
      { eapply SMOLE; et. rp; et. }
      { rp; et. }
      { eapply SMOWF; et. rp; et. Undo 1. (*** TODO: FIX IT ***)
        erewrite f_equal with (f:=SimMem.wf); et. }
    }
    {
      ii. exploit STEPSIM; eauto. { eapply SOUND; ss. } i; des; r in H; des; eauto.
      - left. esplits; eauto. i. exploit STEPFSIM0; eauto. i; des_safe. esplits; eauto.
        { apply star_refl. }
        { eapply SMOLE; et. rp; et. }
        { rp; et. }
        { r. rp; et. }
      - right. esplits; eauto. i. exploit STEPBSIM0; eauto. i; des_safe. esplits; eauto.
        { eapply SMOLE; et. rp; et. }
        { rp; et. }
        { r. rp; et. }
    }
    { i. esplits; et.
      { eapply SMOWF; et. (*** TODO: FIX IT ***)
        erewrite f_equal with (f:=SimMem.wf); et. }
      { rp; et. eapply upcast_eta; et. eapply unit_JMeq; ss. }
      { rewrite SMOOHTGT. eapply upcast_eta; et. sym. eapply unit_JMeq; ss. }
    }
  Qed.

End MATCHSIMFORWARD.

Global Existing Instance SimMemOh_default.
Global Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].

(* Section MATCHSIMFORWARD. *)

(*   Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}. *)

(*   Variable msp: ModSemPair.t. *)
(*   Let SMO := (ModSemPair.SMO msp). *)
(*   Context {SML: SimMemLift.class SM}. *)
(*   Local Existing Instance SMO. *)
(*   Variable index: Type. *)
(*   Variable order: index -> index -> Prop. *)
(*   Hypothesis WFORD: well_founded order. *)
(*   Let ms_src: ModSem.t := msp.(ModSemPair.src). *)
(*   Let ms_tgt: ModSem.t := msp.(ModSemPair.tgt). *)
(*   Variable sound_state: Sound.t -> mem -> ms_src.(state) -> Prop. *)
(*   Hypothesis PRSV: local_preservation ms_src sound_state. *)

(*   Variable match_states: forall *)
(*       (idx: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm0: SimMemOh.t), *)
(*       Prop. *)

(*   Variable match_states_at: forall *)
(*       (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t), *)
(*       Prop. *)

(*   Inductive match_states_at_helper *)
(*             (idx_at: index) (st_src0: ms_src.(ModSem.state)) (st_tgt0: ms_tgt.(ModSem.state)) (sm_at sm_arg: SimMemOh.t): Prop := *)
(*   | match_states_at_intro *)
(*       (MATCH: match_states idx_at st_src0 st_tgt0 sm_at) *)
(*       oh_src oh_tgt args_src args_tgt *)
(*       (CALLSRC: ms_src.(ModSem.at_external) st_src0 oh_src args_src) *)
(*       (CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt) *)
(*       (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg) *)
(*       (MLE: SimMemOh.le sm_at sm_arg) *)
(*       (MWF: SimMemOh.wf sm_arg) *)
(*       (MATCHARG: match_states_at st_src0 st_tgt0 sm_at sm_arg). *)

(*   Hypothesis MIDX: SimMemOh.midx = ms_src.(ModSem.midx). *)
(*   Hypothesis MIDX0: ms_src.(ModSem.midx) = ms_tgt.(ModSem.midx). *)

(*   Hypothesis INITBSIM: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt st_init_tgt *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm_arg) *)
(*       (MWF: SimMemOh.wf sm_arg) *)
(*       (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg) *)
(*       (INITTGT: ms_tgt.(ModSem.initial_frame) oh_tgt args_tgt st_init_tgt) *)
(*       (SAFESRC: exists _st_init_src, ms_src.(ModSem.initial_frame) oh_src args_src _st_init_src), *)
(*       exists st_init_src sm_init idx_init, *)
(*         (<<INITSRC: ms_src.(ModSem.initial_frame) oh_src args_src st_init_src>>) /\ *)
(*         (<<MLE: SimMemOh.le sm_arg sm_init>>) /\ *)
(*         (<<UNCH: SimMem.unch SimMemOh.midx sm_arg sm_init>>) /\ *)
(*         (<<MATCH: match_states idx_init st_init_src st_init_tgt sm_init>>). *)

(*   Hypothesis INITPROGRESS: forall (sm_arg: SimMemOh.t) oh_src oh_tgt args_src args_tgt *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm_arg) *)
(*       (MWF: SimMemOh.wf sm_arg) *)
(*       (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg) *)
(*       (SAFESRC: exists st_init_src, ms_src.(ModSem.initial_frame) oh_src args_src st_init_src), *)
(*       exists st_init_tgt, (<<INITTGT: ms_tgt.(ModSem.initial_frame) oh_tgt args_tgt st_init_tgt>>). *)

(*   Hypothesis ATMWF: forall idx0 st_src0 st_tgt0 sm0 *)
(*       (MATCH: match_states idx0 st_src0 st_tgt0 sm0) *)
(*       (CALLSRC: ms_src.(ModSem.is_call) st_src0), *)
(*       <<MWF: SimMemOh.wf sm0>>. *)

(*   Hypothesis ATFSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) oh_src args_src *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm0) *)
(*       (MATCH: match_states idx0 st_src0 st_tgt0 sm0) *)
(*       (CALLSRC: ms_src.(ModSem.at_external) st_src0 oh_src args_src) *)
(*       (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0), *)
(*       exists oh_tgt args_tgt sm_arg, *)
(*         (<<CALLTGT: ms_tgt.(ModSem.at_external) st_tgt0 oh_tgt args_tgt>>) /\ *)
(*         (<<SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt sm_arg>>) /\ *)
(*         (<<MLE: SimMemOh.le sm0 sm_arg>>) /\ *)
(*         (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_arg>>) /\ *)
(*         (<<MWF: SimMemOh.wf sm_arg>>) /\ *)
(*         (<<MATCHAT: match_states_at st_src0 st_tgt0 sm0 sm_arg>>). *)

(*   Hypothesis AFTERFSIM: forall *)
(*       idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) sm_arg sm_ret *)
(*       oh_src oh_tgt retv_src retv_tgt st_src1 *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm0) *)
(*       (MATCH: match_states idx0 st_src0 st_tgt0 sm0) *)
(*       (MLE: SimMemOh.le sm0 sm_arg) *)
(*       (* (MWF: SimMemOh.wf sm_arg) *) *)
(*       (MLE: SimMemOh.le (SimMemOhLift.lift sm_arg) sm_ret) *)
(*       (MWF: SimMemOh.wf sm_ret) *)
(*       (SIMRET: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt sm_ret) *)
(*       (AFTERSRC: ms_src.(ModSem.after_external) st_src0 oh_src retv_src st_src1) *)
(*       (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0) *)

(*       (* history *) *)
(*       (HISTORY: match_states_at_helper idx0 st_src0 st_tgt0 sm0 sm_arg) *)

(*       (* just helpers *) *)
(*       (MWFAFTR: SimMemOh.wf (SimMemOhLift.unlift sm_arg sm_ret)) *)
(*       (MLEAFTR: SimMemOh.le sm_arg (SimMemOhLift.unlift sm_arg sm_ret)), *)
(*       exists sm_after idx1 st_tgt1, *)
(*         (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 oh_tgt retv_tgt st_tgt1>>) /\ *)
(*         (<<MATCH: match_states idx1 st_src1 st_tgt1 sm_after>>) /\ *)
(*         (<<MLE: SimMemOh.le (SimMemOhLift.unlift sm_arg sm_ret) sm_after>>) /\ *)
(*         (<<UNCH: SimMem.unch SimMemOh.midx (SimMemOhLift.unlift sm_arg sm_ret) sm_after>>) *)
(*   . *)

(*   Hypothesis FINALFSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) oh_src retv_src *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm0) *)
(*       (MATCH: match_states idx0 st_src0 st_tgt0 sm0) *)
(*       (FINALSRC: ms_src.(ModSem.final_frame) st_src0 oh_src retv_src), *)
(*       exists sm_ret oh_tgt retv_tgt, *)
(*         (<<FINALTGT: ms_tgt.(ModSem.final_frame) st_tgt0 oh_tgt retv_tgt>>) /\ *)
(*         (<<SIMRET: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt sm_ret>>) /\ *)
(*         (<<MLE: SimMemOh.le sm0 sm_ret>>) /\ *)
(*         (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm_ret>>) /\ *)
(*         (<<MWF: SimMemOh.wf sm_ret>>). *)

(*   Let STEPFSIM idx0 st_src0 st_tgt0 sm0 := *)
(*       (<<RECEP: receptive_at ms_src st_src0>>) /\ *)
(*       (<<STEPFSIM: forall tr st_src1 *)
(*              (STEPSRC: Step ms_src st_src0 tr st_src1) , *)
(*              exists idx1 st_tgt1 sm1, *)
(*                (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ *)
(*                            <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>) *)
(*                /\ (<<MLE: SimMemOh.le sm0 sm1>>) *)
(*                (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *) *)
(*                /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>) *)
(*                /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>). *)

(*   Let STEPBSIM idx0 st_src0 st_tgt0 sm0 := *)
(*       (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) /\ *)
(*       (<<STEPBSIM: forall tr st_tgt1 *)
(*              (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1) , *)
(*              exists idx1 st_src1 sm1, *)
(*                (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ *)
(*                            <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>) *)
(*                /\ (<<MLE: SimMemOh.le sm0 sm1>>) *)
(*                /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>) *)
(*                (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *) *)
(*                /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>). *)

(*   Hypothesis STEPSIM: forall idx0 st_src0 st_tgt0 (sm0: SimMemOh.t) *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm0) *)
(*       (NOTCALL: ~ ModSem.is_call ms_src st_src0) *)
(*       (NOTRET: ~ ModSem.is_return ms_src st_src0) *)
(*       (MATCH: match_states idx0 st_src0 st_tgt0 sm0) *)
(*       (SOUND: exists su0 m_init, (sound_state) su0 m_init st_src0), *)
(*       STEPFSIM idx0 st_src0 st_tgt0 sm0 \/ STEPBSIM idx0 st_src0 st_tgt0 sm0. *)

(*   Hypothesis INITOH: forall *)
(*       sm *)
(*       (SIMSKENV: ModSemPair.sim_skenv msp sm) *)
(*       (WF: SimMem.wf sm) *)
(*     , *)
(*       exists (smo: SimMemOh.t), *)
(*         (<<WF: SimMemOh.wf smo>>) /\ *)
(*         (<<SMEQ: smo.(SimMemOh.sm) = sm>>) /\ *)
(*         (<<OHSRC: smo.(SimMemOh.oh_src) = upcast msp.(ModSemPair.src).(ModSem.initial_owned_heap)>>) /\ *)
(*         (<<OHTGT: smo.(SimMemOh.oh_tgt) = upcast msp.(ModSemPair.tgt).(ModSem.initial_owned_heap)>>) *)
(*   . *)

(*   Remark safe_modsem_is_smaller *)
(*          st_src0 *)
(*          (NOTCALL: ~ ModSem.is_call ms_src st_src0) *)
(*          (NOTRET: ~ ModSem.is_return ms_src st_src0) *)
(*          (SAFE: safe_modsem ms_src st_src0): *)
(*       ModSem.is_step ms_src st_src0. *)
(*   Proof. rr. specialize (SAFE _ (star_refl _ _ _ _)). des; ss. eauto. Qed. *)

(*   Hypothesis MIDXNONE: SimMemOh.midx = None -> SMO = SimMemOh_default _. *)

(*   Hypothesis BAR: bar_True. *)

(*   Theorem match_states_sim: <<SIM: msp.(ModSemPair.sim)>>. *)
(*   Proof. *)
(*     eapply MatchSimModSemExcl.match_states_sim with *)
(*         (has_footprint := top3) (mle_excl := fun _ _ => SimMemOh.le) (sidx := unit); eauto; ss. *)
(*     { ii. eapply PRSV. } *)
(*     { ii. r. etrans; eauto. } *)
(*     { ii. exploit ATFSIM; eauto. { eapply SOUND. ss. } i; des. esplits; eauto. } *)
(*     { i. exploit AFTERFSIM; et. *)
(*       { eapply SOUND. ss. } *)
(*       { inv HISTORY; econs; eauto. } *)
(*       i; des. esplits; eauto. *)
(*     } *)
(*     { ii. exploit STEPSIM; eauto. { eapply SOUND; ss. } i; des; r in H; des; eauto. *)
(*       left. esplits; eauto. i. exploit STEPFSIM0; eauto. i; des_safe. esplits; eauto. apply star_refl. *)
(*     } *)
(*   Qed. *)

(* End MATCHSIMFORWARD. *)
