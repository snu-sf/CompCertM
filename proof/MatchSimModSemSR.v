Require Import CoqlibC.
Require Import SmallstepC.
Require Import Simulation.
Require Import ModSem AsmregsC GlobalenvsC MemoryC ASTC.
Require Import Skeleton SimModSemSR SimMem SimSymb.
Require Import Sound Preservation.
Require Import ModSemProps.
Require Import Any.

Set Implicit Arguments.






Require Import Program.
Class LeibEq (A B: Type) := { leibeq: A = B }.
Arguments LeibEq: clear implicits.
Definition cast_sigT (a: {ty: Type & ty}) (B: Type) `{LeibEq (projT1 a) B}: B.
  rewrite <- leibeq. destruct a. simpl. auto.
Defined.
(* Global Program Instance LeibEq_rev (A B: Type) `{LeibEq A B}: LeibEq B A. *)
(* Next Obligation. rewrite leibeq. eauto. Defined. *)
Program Definition LeibEq_rev (A B: Type) (LEQ: LeibEq A B): LeibEq B A.
Proof. rewrite leibeq. econstructor. refl. Defined.
Definition cast (A B: Type) `{LeibEq A B} (a: A): B. rewrite <- leibeq. apply a. Defined.
Global Program Instance LeibEq_refl (A: Type): LeibEq A A.

Lemma cast_sigT_existT
      (x: { ty: Type & ty }) X
      (TY: LeibEq (projT1 x) X)
  :
    x = existT id _ (@cast_sigT x X TY)
.
Proof.
  destruct x. destruct TY. ss. clarify.
Qed.

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

Lemma cast_elim
      A LEQ (a: A)
  :
    <<EQ: (@cast A A LEQ a) = a>>
.
Proof.
  r. destruct LEQ.
  unfold cast. ss.
  unfold eq_rect. dependent destruction leibeq0. ss.
Qed.




Lemma upcast_eta
      A B a b
      (EQTY: A = B)
      (EQVAL: a ~= b)
  :
    <<EQ: @upcast A a = @upcast B b>>
.
Proof.
  clarify. eapply JMeq_eq in EQVAL. clarify.
Qed.

Lemma unit_JMeq
      X (x: X)
      (TY: X = unit)
  :
    <<EQ: x ~= tt>>
.
Proof.
  revert x. rewrite TY.
  ii. clarify.
Qed.







Section MATCHSIMFORWARD.

  Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

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

  Let CASTELIMSRC: forall (oh_src: ms_src.(ModSem.owned_heap)), (cast () = oh_src).
  Proof.
    remember (ModSem.owned_heap ms_src) as X. clear HeqX. ii. clarify.
    des_u. rewrite cast_elim. ss.
  Qed.

  Let CASTELIMTGT: forall (oh_tgt: ms_tgt.(ModSem.owned_heap)), (cast () = oh_tgt).
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
      (SOUND: exists su0 m_init, sound_state su0 m_init st_src0),
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
      (MLE: SimMem.lepriv sm_arg sm_ret)
      (MWF: SimMem.wf sm_ret)
      (SIMRET: SimMem.sim_retv retv_src retv_tgt sm_ret)
      (AFTERSRC: ms_src.(ModSem.after_external) st_src0 (cast tt) retv_src st_src1)
      (SOUND: exists su0 m_init, sound_state su0 m_init st_src0)

      (* history *)
      (HISTORY: match_states_at_helper idx0 st_src0 st_tgt0 sm0 sm_arg),

      (* just helpers *)
      (* (MWFAFTR: SimMem.wf (SimMem.unlift sm_arg sm_ret)) *)
      (* (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret)) *)
      exists sm_after idx1 st_tgt1,
        (<<AFTERTGT: ms_tgt.(ModSem.after_external) st_tgt0 (cast tt) retv_tgt st_tgt1>>) /\
        (<<MATCH: match_states idx1 st_src1 st_tgt1 sm_after>>) /\
        (<<MLE: SimMem.lepriv sm_ret sm_after>>) /\
        (<<MLE: SimMem.le sm0 sm_after>>) /\
        (<<UNCH: SimMem.unch SimMemOh.midx sm_ret sm_after>>)
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

  Let STEPFSIM := forall idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, sound_state su0 m_init st_src0),
      (<<RECEP: strongly_receptive_at ms_src st_src0>>) /\
      (<<STEPFSIM: forall tr st_src1
             (STEPSRC: Step ms_src st_src0 tr st_src1),
             exists idx1 st_tgt1 sm1,
               (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/
                           <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Let STEPBSIM := forall idx0 st_src0 st_tgt0 sm0
      (SIMSKENV: ModSemPair.sim_skenv msp sm0)
      (NOTCALL: ~ ModSem.is_call ms_src st_src0)
      (NOTRET: ~ ModSem.is_return ms_src st_src0)
      (MATCH: match_states idx0 st_src0 st_tgt0 sm0)
      (SOUND: exists su0 m_init, sound_state su0 m_init st_src0),
      (* (<<PROGRESS: ModSem.is_step ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) *)
      (<<PROGRESS: safe_modsem ms_src st_src0 -> ModSem.is_step ms_tgt st_tgt0>>) /\
      (<<STEPBSIM: forall tr st_tgt1
             (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1) ,
             exists idx1 st_src1 sm1,
               (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/
                           <<STAR: Star ms_src st_src0 tr st_src1 /\ order idx1 idx0>>)
               /\ (<<MLE: SimMem.le sm0 sm1>>)
               /\ (<<UNCH: SimMem.unch SimMemOh.midx sm0 sm1>>)
               (* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMem.wf, beacuse of DCEproof *)
               /\ (<<MATCH: match_states idx1 st_src1 st_tgt1 sm1>>)>>).

  Remark safe_modsem_is_smaller
         st_src0
         (NOTCALL: ~ ModSem.is_call ms_src st_src0)
         (NOTRET: ~ ModSem.is_return ms_src st_src0)
         (SAFE: safe_modsem ms_src st_src0):
      ModSem.is_step ms_src st_src0.
  Proof. rr. specialize (SAFE _ (star_refl _ _ _ _)). des; ss. eauto. Qed.

  Hypothesis STEPSIM: STEPFSIM \/ STEPBSIM.

  Hypothesis BAR: bar_True.

  Lemma match_states_lxsimSR
        i0 st_src0 st_tgt0 sm0
        (SIMSKENV: ModSemPair.sim_skenv msp sm0)
        (* (MWF: SimMem.wf sm0) *)
        (* (MCOMPAT: mem_compat st_src0 st_tgt0 sm0) *)
        (MATCH: match_states i0 st_src0 st_tgt0 sm0):
        (* su0 *)
      (* <<LXSIM: lxsim ms_src ms_tgt (sound_state su0) sm_init i0.(to_idx WFORD) st_src0 st_tgt0 sm0>> *)
      <<LXSIM: lxsimSR ms_src ms_tgt (fun st => unit -> exists su0 m_init, sound_state su0 m_init st)
                       (Ord.lift_idx WFORD i0) st_src0 st_tgt0 (cast sm0)>>.
  Proof.
    (* move su0 at top. *)
    revert_until BAR. pcofix CIH. i. pfold. ii.
    generalize (classic (ModSem.is_call ms_src st_src0)). intro CALLSRC; des.
    { (* CALL *)
      - (* u in CALLSRC. des. *)
        exploit ATMWF; eauto. i; des. eapply lxsimSR_at_external; eauto.
        { eapply SMOWF; et. erewrite f_equal; et. } ii. clear CALLSRC.
        exploit ATFSIM; eauto.
        { rp; et. }
        { ii. eapply SUSTAR; eauto. eapply star_refl. apply tt. } i; des.
        (* determ_tac ModSem.at_external_dtm. clear_tac. *)
        esplits; eauto.
        { rr. esplits; ss; et.
          - rp; et.
          - ss. rewrite SMOOHSRC. eapply upcast_eta; et. clear - OHSRC.
            revert OHSRC. remember (ModSem.owned_heap ms_src) as X. clear HeqX. ii; clarify. clarify.
          - ss. rewrite SMOOHTGT. eapply upcast_eta; et. clear - OHTGT.
            revert OHTGT. remember (ModSem.owned_heap ms_tgt) as X. clear HeqX. ii; clarify. clarify.
            rewrite cast_elim. ss.
        }
        { eapply SMOWF; et. erewrite f_equal; et. }
        { eapply SMOLE; et. rp; et. }
        { rp; et. }
        i. rr in SIMRETV; des. clarify.
        exploit AFTERFSIM; try apply SAFESRC; try apply SIMRETV0; eauto.
        { eapply SMLEPRIV in MLE0; et. rp; et. }
        { rp; et. }
        { ii. eapply SUSTAR; eauto. eapply star_refl. apply tt. }
        { econs; eauto. rp; et. }
        i; des.
        assert(MLE4: SimMem.le sm0 sm_after).
        { etrans; cycle 1. { et. } refl. }
        esplits; eauto.
        { rp; et. }
        { eapply SMOLE; et. rp; et. }
        { eapply SMOLEPRIV; et. rp; et. }
        { rp; et. }
        right. eapply CIH; [..|eauto].
        { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once. left. et. }
    }
    generalize (classic (ModSem.is_return ms_src st_src0)). intro RETSRC; des.
    { (* RETURN *)
      u in RETSRC. des. exploit FINALFSIM; eauto. { rp ;et. } i; des.
      eapply lxsimSR_final; try apply SIMRET; eauto.
      { eapply SMOLE; et. rp; et. }
      { rp; et. }
      { eapply SMOWF; et. erewrite f_equal; et. }
      { rr. esplits; ss; et.
        - rp; et.
        - rewrite SMOOHSRC; ss. eapply upcast_eta; et. clear - OHSRC.
          remember (ModSem.owned_heap ms_src) as X. clear HeqX. ii; clarify. clarify.
        - rewrite SMOOHTGT; ss. eapply upcast_eta; et. clear - OHTGT.
          remember (ModSem.owned_heap ms_tgt) as X. clear HeqX. ii; clarify. rewrite cast_elim; ss.
      }
    }
    destruct STEPSIM as [STEPFSIM0|STEPBSIM0].
    { eapply lxsimSR_step_forward; eauto. i.
      (* hexploit1 SU0; ss. *)
      exploit STEPFSIM0; eauto. { ii. eapply SUSTAR; eauto. eapply star_refl. apply tt. } i; des.
      esplits; eauto. econs 1; eauto.
      ii. exploit STEPFSIM1; eauto. i; des_safe. esplits; eauto.
      - des.
        + left. eauto.
        + right. esplits; eauto. eapply Ord.lift_idx_spec; eauto.
      - eapply SMOLE; et. rp; et.
      - rp; et.
      - right. eapply CIH; [..|eauto].
        { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto. }
    }
    { rr in STEPBSIM0. eapply lxsimSR_step_backward; eauto. i.
      (* hexploit1 SU0; ss. *)
      exploit STEPBSIM0; eauto. { ii. eapply SUSTAR; eauto. eapply star_refl. apply tt. } i; des. rr in PROGRESS. des.
      esplits; eauto; cycle 1. econs 1; eauto. ii. exploit STEPBSIM1; eauto. i; des_safe. esplits; eauto.
      - des.
        + left. eauto.
        + right. esplits; eauto. eapply Ord.lift_idx_spec; eauto.
      - eapply SMOLE; et. rp; et.
      - rp; et.
      - right. eapply CIH; [..|eauto].
        { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto. }
    }
  Qed.

  Theorem match_states_sim: <<SIM: msp.(ModSemPair.simSR)>>.
  Proof.
    econs.
    { clear - SMOCLASS MIDXSRC. subst SMO. rewrite SMOCLASS. subst ms_src. rewrite MIDXSRC. ss. }
    { clear - MIDXSRC MIDXTGT. subst ms_src. rewrite MIDXSRC. subst ms_tgt. rewrite MIDXTGT. ss. }
    { ss. }
    { eauto. }
    { instantiate (2 := unit). ii. eapply local_preservation_noguarantee_weak; eauto. eapply PRSV. }
    { esplits; ss; et.
      - eapply SMOWF; et. erewrite f_equal; et.
      - rewrite SMOOHSRC. eapply upcast_eta; ss. clear - OHSRC. subst ms_src.
        remember (ModSem.initial_owned_heap (@ModSemPair.src SM SS msp)) as X. clear HeqX.
        revert X. rewrite OHSRC. ii; clarify.
      - rewrite SMOOHTGT. eapply upcast_eta; ss. clear - OHTGT. subst ms_tgt.
        remember (ModSem.initial_owned_heap (@ModSemPair.tgt SM SS msp)) as X. clear HeqX.
        revert X. rewrite OHTGT. ii; clarify.
    }
    ii; ss. folder. rr in SIMARGS; des.
    exploit SimSymb.sim_skenv_func_bisim; eauto. { apply SIMSKENV. } intro FSIM; des.
    inv FSIM. exploit FUNCFSIM; eauto. { apply SimMem.sim_args_sim_fptr; et. } i; des.
    split; ii.
    - exploit INITBSIM; eauto.
      { rp; et. }
      { des. esplits; et. rp; et. }
      i; des. clear SAFESRC.
      esplits; eauto.
      { eapply SMOLE; et. rp; et. }
      { rp; et. rewrite SMOCLASS. ss. }
      { rp; et. }
      eapply match_states_lxsimSR; eauto.
      { eapply ModSemPair.mfuture_preserves_sim_skenv; try apply SIMSKENV; eauto. apply rtc_once; eauto. }
    - exploit INITPROGRESS; eauto.
      { des. rp; et. }
      i; des. esplits; et. rp; et.
  Unshelve.
    all: ss.
  Qed.

End MATCHSIMFORWARD.

Global Existing Instance SimMemOh_default.
Global Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].
