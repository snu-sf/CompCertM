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
Require Import SimModSemUnified SimMod SimProg Sem.
Require Import Any.
Require Import SemProps.

Set Implicit Arguments.




Module SimMemOhUnify.
Section SimMemOhUnify.

  Context `{SM: SimMem.class} {SU: Sound.class} {SS: SimSymb.class SM}.
  Variable msps: list ModSemPair.t.
  Hypothesis SIM: Forall ModSemPair.sim msps.
  Hypothesis UNIQ: forall
      msp0 msp1 mi
      (IN0: In msp0 msps)
      (IN1: In msp1 msps)
      (IDX0: msp0.(ModSemPair.src).(ModSem.midx) = Some mi)
      (IDX1: msp1.(ModSemPair.src).(ModSem.midx) = Some mi)
    ,
      msp0 = msp1
  .
  (* Hypothesis MIDXWF: forall n msp (NTH: nth_error msps n = Some msp), *)
  (*     <<MIDX: msp.(ModSemPair.src).(ModSem.midx) = n>>. *)
  (* Let MIDXWF2: forall n msp (NTH: nth_error msps n = Some msp), *)
  (*     <<MIDX: SimMemOh.midx (class := msp.(ModSemPair.SMO)) = n>>. *)
  (* Proof. *)
  (*   ii. r. exploit MIDXWF; et. i; des. clarify. rewrite Forall_forall in *. *)
  (*   eapply nth_error_In in NTH. exploit SIM; et. intro T. inv T. congruence. *)
  (* Qed. *)

  Record t: Type := mk {
    sm:> SimMem.t;
    anys: Midx.t -> (SimMemOh.class * Any);
    WTYFST: forall
        msp SMO a0
        (NTH: In msp msps)
        (ANY: anys (SimMemOh.midx (class := msp.(ModSemPair.SMO))) = (SMO, a0))
      ,
        SMO = msp.(ModSemPair.SMO)
    ;
    WTYSND: forall
        mi SMO a0
        (ANY: anys mi = (SMO, a0))
      ,
        exists smo0, (<<DOWNCAST: @downcast SimMemOh.t a0 = Some smo0>>) /\
                     (<<SMEQ: smo0.(SimMemOh.sm) = sm>>) /\
                     (<<MIDX: SimMemOh.midx = mi>>)
    ;
    (* WTYNONE: anys None = (SimMemOh_default _, @upcast (SimMemOh.t (class := SimMemOh_default _)) sm) *)
    WTYNONE: anys None = (SimMemOh_default _, upcast sm)
    ;
  }.

  Program Definition set_sm (smos0: t) (sm0: SimMem.t): t :=
    @mk
      sm0
      (fun mi => let '(SMO, a0) := smos0.(anys) mi in
                 match @downcast SimMemOh.t a0 with
                 | Some smo0 => (SMO, upcast (SimMemOh.set_sm smo0 sm0))
                 | _ => (SMO, a0)
                 end
      )
      _
      _
      _
  .
  Next Obligation.
    des_ifs_safe. des_ifs; eapply smos0.(WTYFST); eauto.
  Qed.
  Next Obligation.
    des_ifs_safe. des_ifs.
    { rewrite upcast_downcast. esplits; eauto.
      - simpl_depind. clarify. rewrite SimMemOh.getset_sm; ss.
      - simpl_depind. clarify. exploit WTYSND; eauto. i; des. clarify.
    }
    { exploit smos0.(WTYSND); eauto. i; des. esplits; eauto. clarify. }
  Qed.
  Next Obligation.
    hexploit smos0.(WTYNONE); et. intro T.
    ss. des_ifs. rewrite upcast_downcast in *. clarify.
  Qed.

  Inductive le (smos0 smos1: t): Prop :=
  | le_intro
      (LESM: SimMem.le smos0.(sm) smos1.(sm))
      (LESMO: forall
          mi SMO0 SMO1 a0 a1
          (ANY0: smos0.(anys) mi = (SMO0, a0))
          (ANY1: smos1.(anys) mi = (SMO1, a1))
        ,
          (<<EQSMO: SMO0 = SMO1>>) /\
          (<<LESMO:
             forall
               smo0 smo1
               (CAST0: downcast a0 = Some smo0)
               (CAST1: downcast a1 = Some smo1)
             ,
               <<LE: SimMemOh.le (class := SMO0) smo0 smo1>>>>)
      )
      (* (LESMO: forall *)
      (*     n a0 a1 msp (smo0 smo1: SimMemOh.t (class := msp.(ModSemPair.SMO))) *)
      (*     (NTH: nth_error msps n = Some msp) *)
      (*     (NTH: nth_error smos0.(anys) n = Some a0) *)
      (*     (NTH: nth_error smos1.(anys) n = Some a1) *)
      (*     (CAST: downcast a0 = Some smo0) *)
      (*     (CAST: downcast a1 = Some smo1) *)
      (*   , *)
      (*     <<LESMO: SimMemOh.le (class := msp.(ModSemPair.SMO)) smo0 smo1>> *)
      (* ) *)
  .

  (* Definition proj (mi: Midx.t) (msp: ModSemPair.t) (NTH: nth_error msps mi = Some msp) *)
  (*            (smos: t): option (SimMemOh.t (class := msp.(ModSemPair.SMO))) := *)
  (*   match nth_error smos.(anys) mi with *)
  (*   | Some a0 => downcast a0 *)
  (*   | _ => None *)
  (*   end *)
  (* . *)

  Inductive lepriv (smos0 smos1: t): Prop :=
  | lepriv_intro
      (LEPRIVSM: SimMem.lepriv smos0.(sm) smos1.(sm))
      (* (LEPRIVSMO: forall *)
      (*     n a0 a1 msp (smo0 smo1: SimMemOh.t (class := msp.(ModSemPair.SMO))) *)
      (*     (NTH: nth_error msps n = Some msp) *)
      (*     (NTH: nth_error smos0.(anys) n = Some a0) *)
      (*     (NTH: nth_error smos1.(anys) n = Some a1) *)
      (*     (CAST: downcast a0 = Some smo0) *)
      (*     (CAST: downcast a1 = Some smo1) *)
      (*   , *)
      (*     <<LEPRIVSMO: SimMemOh.lepriv (class := msp.(ModSemPair.SMO)) smo0 smo1>> *)
      (* ) *)
      (LEPRIVSMO: forall
          mi SMO0 a0 SMO1 a1
          (ANY0: smos0.(anys) mi = (SMO0, a0))
          (ANY1: smos1.(anys) mi = (SMO1, a1))
        ,
          (<<EQSMO: SMO0 = SMO1>>) /\
          (<<LEPRIVSMO:
             forall
               smo0 smo1
               (CAST0: downcast a0 = Some smo0)
               (CAST1: downcast a1 = Some smo1)
             ,
               <<LE: SimMemOh.lepriv (class := SMO0) smo0 smo1>>>>)
      )
  .

  Inductive wf (smos0: t): Prop :=
  | wf_intro
      (WFSM: SimMem.wf smos0.(sm))
      (WFSMO: forall
          mi SMO0 a0 smo0
          (ANY: smos0.(anys) mi = (SMO0, a0))
          (CAST: downcast a0 = Some smo0)
        ,
          (<<WFSMO: SimMemOh.wf smo0>>)
          (* /\ *)
          (* (<<SMEQ: smo0.(SimMemOh.sm) = smos0.(sm)>>) *)
      )
  .

  Inductive wf_weak (mj: Midx.t) (smos0: t): Prop :=
  | wf_weak_intro
      (* (WFSM: SimMem.wf smos0.(sm)) *)
      (WFSMO: forall
          mi SMO0 a0 (smo0: SimMemOh.t) sm0
          (EXCEPT: mi <> mj)
          (ANY: smos0.(anys) mi = (SMO0, a0))
          (CAST: downcast a0 = Some smo0)
          (MWF: SimMem.wf sm0)
          (UNCHSRC: SimMem.unchanged_on (privmods mi smo0.(SimMem.ptt_src))
                                        smo0.(SimMem.src) sm0.(SimMem.src))
          (UNCHTGT: SimMem.unchanged_on (privmods mi smo0.(SimMem.ptt_tgt))
                                        smo0.(SimMem.tgt) sm0.(SimMem.tgt))
        ,
          (<<WFSMO: SimMemOh.wf (SimMemOh.set_sm smo0 sm0)>>)
          (* /\ *)
          (* (<<SMEQ: smo0.(SimMemOh.sm) = smos0.(sm)>>) *)
      )
  .

  Lemma wf_weak_wf
        mi smos0 SMO0 a0 smo0
        (WFW: wf_weak mi smos0)
        (ANY0: smos0.(anys) mi = (SMO0, a0))
        (CAST: downcast a0 = Some smo0)
        (WF: SimMemOh.wf smo0)
    :
      <<WF: wf smos0>>
  .
  Proof.
    assert(WF0: SimMem.wf smos0).
    { exploit smos0.(WTYSND); eauto. i; des. clarify.
      rewrite <- SMEQ.
      eapply SimMemOh.wf_proj; eauto.
    }
    econs; eauto. ii.
    destruct (Midx.eq_dec mi mi0).
    - clarify. rewrite ANY in *. clarify.
    - inv WFW.
      exploit smos0.(WTYSND); eauto. i; des. clarify.
      rewrite <- SMEQ in *.
      exploit WFSMO; eauto; try refl. intro T.
      rewrite SimMemOh.setget_sm in T. ss.
  Qed.

  Lemma wf_wf_weak
        smos0 mi
        (WF: wf smos0)
    :
      <<WFW: wf_weak mi smos0>>
  .
  Proof.
    inv WF.
    econs; eauto. ii.
    exploit WTYSND; eauto. i; des. clarify.
    eapply SimMemOh.set_sm_wf; eauto.
    { eapply WFSMO; eauto. }
  Qed.

  Definition ohs_src (smos0: t): Ohs :=
    fun mi => let '(SMO0, a0) := smos0.(anys) mi in
              match downcast a0 with
              | Some smo0 => smo0.(SimMemOh.oh_src)
              | _ => upcast tt
              end
  .
  (* Definition ohs_src (smos0: t): Sem.Ohs := *)
  (*   fun mi => *)
  (*     match nth_error msps mi, nth_error smos0.(anys) mi with *)
  (*     | Some msp, Some a0 => *)
  (*       match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with *)
  (*       | Some smo0 => SimMemOh.oh_src smo0 *)
  (*       | _ => upcast tt *)
  (*       end *)
  (*     | _, _ => upcast tt *)
  (*     end *)
  (* . *)

  Definition ohs_tgt (smos0: t): Ohs :=
    fun mi => let '(SMO0, a0) := smos0.(anys) mi in
              match downcast a0 with
              | Some smo0 => smo0.(SimMemOh.oh_tgt)
              | _ => upcast tt
              end
  .
  (* Definition ohs_tgt (smos0: t): Sem.Ohs := *)
  (*   fun mi => *)
  (*     match nth_error msps mi, nth_error smos0.(anys) mi with *)
  (*     | Some msp, Some a0 => *)
  (*       match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with *)
  (*       | Some smo0 => SimMemOh.oh_tgt smo0 *)
  (*       | _ => upcast tt *)
  (*       end *)
  (*     | _, _ => upcast tt *)
  (*     end *)
  (* . *)

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    - ii. econs; eauto.
      + refl.
      + ii. rewrite ANY0 in *. clarify. esplits; eauto. ii. clarify. refl.
  Qed.
  Next Obligation.
    - ii. inv H. inv H0. econs; eauto.
      + etrans; eauto.
      + ii.
        destruct (anys y mi) eqn:ANY2. rename c into SMO2. rename s into a2.
        exploit WTYSND; eauto. i; des.
        hexploit (LESMO mi SMO0 SMO2 a0 a2); eauto. i; des.
        hexploit (LESMO0 mi SMO2 SMO1 a2 a1); eauto. i; des. clarify.
        esplits; eauto.
        ii.
        etrans.
        { eapply LESMO1; eauto. }
        { eapply LESMO2; eauto. }
  Qed.

  Program Instance lepriv_PreOrder: PreOrder lepriv.
  Next Obligation.
    - ii. econs; eauto.
      + refl.
      + ii. rewrite ANY0 in *. clarify. esplits; eauto. ii. clarify. refl.
  Qed.
  Next Obligation.
    - ii. inv H. inv H0. econs; eauto.
      + etrans; eauto.
      + ii.
        destruct (anys y mi) eqn:ANY2. rename c into SMO2. rename s into a2.
        exploit WTYSND; eauto. i; des.
        hexploit (LEPRIVSMO mi SMO0 a0 SMO2 a2); eauto. i; des.
        hexploit (LEPRIVSMO0 mi SMO2 a2 SMO1 a1); eauto. i; des. clarify.
        esplits; eauto.
        ii.
        etrans.
        { eapply LEPRIVSMO1; eauto. }
        { eapply LEPRIVSMO2; eauto. }
  Qed.



  Program Instance SimMemOhs_intro: SimMemOhs.class :=
    {|
      SimMemOhs.t := t;
      SimMemOhs.sm := sm;
      SimMemOhs.le := le;
      SimMemOhs.lepriv := lepriv;
      SimMemOhs.wf := wf;
      SimMemOhs.ohs_src := ohs_src;
      SimMemOhs.ohs_tgt := ohs_tgt;
    |}
  .
  Next Obligation.
    inv H.
    econs; eauto.
    ii. exploit (LESMO mi SMO0 SMO1 a0 a1); eauto. i; des. clarify. esplits; eauto.
    ii. eapply SimMemOh.pub_priv; eauto. eapply LESMO0; eauto.
  Qed.
  Next Obligation.
    ii. apply PR.
  Qed.
  Next Obligation.
    ii. apply H.
  Qed.
  Next Obligation.
    ii. apply H.
  Qed.

  Section SETSMO.

    Variable smos0: t.
    Variable msp: ModSemPair.t.
    Hypothesis (IN: In msp msps).
    Variable smo': SimMemOh.t (class := msp.(ModSemPair.SMO)).
    (* Hypothesis (SMMATCH: sm_match (S n) smo' smos0). *)

    Program Definition set_smo: t :=
      @mk
        smo'
        (fun mi =>
           let '(SMO0, a0) := smos0.(anys) mi in
           if Midx.eq_dec mi (SimMemOh.midx (class := msp.(ModSemPair.SMO)))
           then (SMO0, upcast smo')
           else
             match downcast a0 with
             | Some smo0 => (SMO0, upcast (SimMemOh.set_sm smo0 smo'.(SimMemOh.sm)))
             | _ => (SMO0, a0)
             end
        )
        (* (Midx.mapi_aux (fun m a0 => *)
        (*                   if Nat.eq_dec n m then @upcast SimMemOh.t smo' else *)
        (*                     match nth_error msps m with *)
        (*                     | Some msp => *)
        (*                       match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with *)
        (*                       | Some smo0 => *)
        (*                         @upcast SimMemOh.t ((SimMemOh.set_sm smo0 smo'.(SimMemOh.sm)): SimMemOh.t) *)
        (*                       | _ => upcast tt *)
        (*                       end *)
        (*                     | _ => upcast tt *)
        (*                     end *)
        (*                ) 0%nat (smos0.(anys))) *)
        _
        _
        _
    .
    Next Obligation.
      des_ifs_safe. exploit WTYFST; eauto. i; clarify.
      dup Heq. eapply WTYSND in Heq. des.
      des_ifs.
    Qed.
    Next Obligation.
      des_ifs_safe. destruct (Midx.eq_dec mi SimMemOh.midx).
      { clarify.
        exploit WTYFST; eauto. i; clarify.
        simpl_depind. clarify.
        rewrite upcast_downcast. esplits; eauto.
      }
      exploit WTYSND; eauto. i; des; clarify.
      des_ifs. simpl_depind. clarify.
      esplits; eauto.
      { rewrite upcast_downcast. eauto. }
      rewrite SimMemOh.getset_sm; ss.
    Qed.
    Next Obligation.
      rewrite Forall_forall in *. exploit SIM; et. intro T.
      hexploit smos0.(WTYNONE); et. intro U.
      des_ifs.
      - f_equal; ss.
        inv T. exploit MIDXNONE; et. intro V; clarify. rewrite V in *. ss.
        clear - V.
        remember (@ModSemPair.SMO SM SS msp) as X. clear HeqX. subst. ss.
      - rewrite upcast_downcast in *. ss.
    Qed.

  End SETSMO.

  Record sm_match {SMO: SimMemOh.class}
         (smo: SimMemOh.t) (smos: SimMemOhs.t): Prop :=
    (* TODO: I want to remove @ *)
    { smeq: (smos.(SimMemOhs.sm) = smo.(SimMemOh.sm));
      smnth: smos.(anys) SimMemOh.midx = (SMO, upcast smo);
      ohsrc: (smos.(SimMemOhs.ohs_src) SimMemOh.midx) = smo.(SimMemOh.oh_src);
      ohtgt: (smos.(SimMemOhs.ohs_tgt) SimMemOh.midx) = smo.(SimMemOh.oh_tgt);
      wfwf: wf_weak SimMemOh.midx smos;
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

  Theorem respects_intro
    :
      (<<RESPECTS: forall msp (IN: In msp msps),
          (<<RESPECTS: respects msp.(ModSemPair.SMO) SimMemOhs_intro>>)>>)
  .
  Proof.
    ii.
    econstructor 1 with (sm_match_strong := sm_match)
                        (is_set_smo := fun smos0 mi smo1 smos1 =>
                                         smos1 = set_smo smos0 msp IN smo1); ss; eauto.
    - ii. inv PR. econs; ec. ii. eapply wf_weak_wf; ec. rewrite upcast_downcast; ss.
    - ii. inv MWF.
      destruct (anys smos (SimMemOh.midx (class := msp.(ModSemPair.SMO)))) eqn:T.
      exploit WTYFST; eauto. i; clarify. exploit WTYSND; eauto. i; des.
      exists smo0. esplits; eauto.
      + econs; ss; eauto.
        * rewrite T. f_equal; ss. eapply upcast_downcast_iff; eauto.
        * unfold ohs_src. des_ifs.
        * unfold ohs_tgt. des_ifs.
        * ii. eapply wf_wf_weak; try rewrite Q in *; eauto. econs; eauto.
      + eapply WFSMO; et; ss.
    - ii.
      eexists (set_smo smos0 msp IN smo1).
      esplits; eauto.
      + econs; ss; eauto.
        * replace sm with (SimMemOhs.sm) by ss.
          erewrite SMMATCH.(smeq); eauto.
          eapply SimMemOh.le_proj; eauto.
        * ii; ss.
          des_ifs.
          { exploit WTYFST; eauto. i; des. clarify.
            exploit WTYSND; eauto. i; des. clarify.
            assert(smo0 = smo2).
            { hexploit SMMATCH.(smnth); ss. intro T. rewrite T in *. clarify. rewrite upcast_downcast in *. clarify. }
            clarify.
            esplits; eauto.
            ii. rewrite upcast_downcast in *. clarify.
          }
          rewrite upcast_downcast in *. esplits; eauto. ii. clarify.
          erewrite <- SimMemOh.setget_sm with smo2. erewrite SimMemOh.setset_sm.
          eapply SimMemOh.set_sm_le; try refl; eauto.
          replace sm with (SimMemOhs.sm) by ss.
          eapply SimMemOh.le_proj in LE. etrans; eauto.
          erewrite <- SMMATCH.(smeq); eauto.
          exploit smos0.(WTYSND); et. i; des. clarify. rewrite SMEQ. refl.
      + econs; ss; eauto.
        * ii.
          des_ifs. exploit WTYFST; eauto. i; des. clarify.
        * unfold ohs_src; ss. des_ifs_safe. exploit WTYFST; eauto. i; clarify.
          rewrite upcast_downcast. ss.
        * unfold ohs_tgt; ss. des_ifs_safe. exploit WTYFST; eauto. i; clarify.
          rewrite upcast_downcast. ss.
        * ii. hexploit (SMMATCH.(wfwf)); eauto. intro WF; ss.
          econs. ii. ss.
          des_ifs. rewrite upcast_downcast in *. clarify.
          set (SimMemOh.midx) as mj in *.
          rewrite SimMemOh.setset_sm.
          exploit WTYSND; eauto. i; des. clarify.
          set (SimMemOh.midx (class := SMO0)) as mi in *.
          eapply WF; eauto.
          { erewrite SimMemOh.getset_sm in UNCHSRC; et.
            rewrite SMEQ.
            inv UNCH.
            etrans; et.
            {
              erewrite <- smeq in UNCHSRC0; et. eapply SimMem.unchanged_on_monotone; et.
              clear - EXCEPT.
              ii. unfold privmods in *. unfold privmod_others in *.
              des_ifs_safe. des_sumbool. clarify. ss. des_ifs. simpl_bool. des_sumbool. ii; clarify.
            }
            {
              eapply SimMem.unchanged_on_monotone; et. intros b ofs.
              hexploit LESRC; et. intro T. specialize (T b ofs); ss.
              Fail erewrite smeq; eauto; fail.
              erewrite (@smeq (@ModSemPair.SMO SM SS msp)). eexact T. et.
              (* TODO: "erewrite smeq" does not work and I am sure it is a Coq's bug!!!
                 What an annoying bug... *)
            }
          }
          { erewrite SimMemOh.getset_sm in UNCHTGT; et.
            rewrite SMEQ.
            inv UNCH.
            etrans; et.
            {
              erewrite <- smeq in UNCHTGT0; et. eapply SimMem.unchanged_on_monotone; et.
              clear - EXCEPT.
              ii. unfold privmods in *. unfold privmod_others in *.
              des_ifs_safe. des_sumbool. clarify. ss. des_ifs. simpl_bool. des_sumbool. ii; clarify.
            }
            {
              eapply SimMem.unchanged_on_monotone; et. intros b ofs.
              hexploit LETGT; et. intro T. specialize (T b ofs); ss.
              Fail erewrite smeq; eauto; fail.
              erewrite (@smeq (@ModSemPair.SMO SM SS msp)). eexact T. et.
              (* TODO: "erewrite smeq" does not work and I am sure it is a Coq's bug!!!
                 What an annoying bug... *)
            }
          }
      + ii.
        do 2 (unfold ohs_src, ohs_tgt; ss).
        des_ifs_safe. des_ifs.
        { rewrite upcast_downcast in *. clarify.
          rewrite SimMemOh.set_sm_oh_src.
          rewrite SimMemOh.set_sm_oh_tgt.
          ss.
        }
        { rewrite upcast_downcast in *. clarify. }
    - ii.
      eexists (set_smo smos0 msp IN smo1).
      esplits; eauto.
      + econs; ss; eauto.
        * replace sm with (SimMemOhs.sm) by ss.
          erewrite SMMATCH.(smeq); eauto.
          eapply SimMemOh.lepriv_proj; eauto.
        * ii; ss.
          des_ifs.
          { exploit WTYFST; eauto. i; des. clarify.
            exploit WTYSND; eauto. i; des. clarify.
            assert(smo0 = smo2).
            { hexploit SMMATCH.(smnth); ss. intro T. rewrite T in *. clarify. rewrite upcast_downcast in *. clarify. }
            clarify.
            esplits; eauto.
            ii. rewrite upcast_downcast in *. clarify.
          }
          rewrite upcast_downcast in *. esplits; eauto. ii. clarify.
          erewrite <- SimMemOh.setget_sm with smo2. erewrite SimMemOh.setset_sm.
          eapply SimMemOh.set_sm_lepriv; try refl; eauto.
          replace sm with (SimMemOhs.sm) by ss.
          eapply SimMemOh.lepriv_proj in LE. etrans; eauto.
          erewrite <- SMMATCH.(smeq); eauto.
          exploit smos0.(WTYSND); et. i; des. clarify. rewrite SMEQ. refl.
      + econs; ss; eauto.
        * ii.
          des_ifs. exploit WTYFST; eauto. i; des. clarify.
        * unfold ohs_src; ss. des_ifs_safe. exploit WTYFST; eauto. i; clarify.
          rewrite upcast_downcast. ss.
        * unfold ohs_tgt; ss. des_ifs_safe. exploit WTYFST; eauto. i; clarify.
          rewrite upcast_downcast. ss.
        * ii. hexploit (SMMATCH.(wfwf)); eauto. intro WF; ss.
          econs. ii. ss.
          des_ifs. rewrite upcast_downcast in *. clarify.
          set (SimMemOh.midx) as mj in *.
          rewrite SimMemOh.setset_sm.
          exploit WTYSND; eauto. i; des. clarify.
          set (SimMemOh.midx (class := SMO0)) as mi in *.
          eapply WF; eauto.
          { erewrite SimMemOh.getset_sm in UNCHSRC; et.
            rewrite SMEQ.
            inv UNCH.
            etrans; et.
            {
              erewrite <- smeq in UNCHSRC0; et. eapply SimMem.unchanged_on_monotone; et.
              clear - EXCEPT.
              ii. unfold privmods in *. unfold privmod_others in *.
              des_ifs_safe. des_sumbool. clarify. ss. des_ifs. simpl_bool. des_sumbool. ii; clarify.
            }
            {
              eapply SimMem.unchanged_on_monotone; et. intros b ofs.
              hexploit LESRC; et. intro T. specialize (T b ofs); ss.
              Fail erewrite smeq; eauto; fail.
              erewrite (@smeq (@ModSemPair.SMO SM SS msp)). eexact T. et.
              (* TODO: "erewrite smeq" does not work and I am sure it is a Coq's bug!!!
                 What an annoying bug... *)
            }
          }
          { erewrite SimMemOh.getset_sm in UNCHTGT; et.
            rewrite SMEQ.
            inv UNCH.
            etrans; et.
            {
              erewrite <- smeq in UNCHTGT0; et. eapply SimMem.unchanged_on_monotone; et.
              clear - EXCEPT.
              ii. unfold privmods in *. unfold privmod_others in *.
              des_ifs_safe. des_sumbool. clarify. ss. des_ifs. simpl_bool. des_sumbool. ii; clarify.
            }
            {
              eapply SimMem.unchanged_on_monotone; et. intros b ofs.
              hexploit LETGT; et. intro T. specialize (T b ofs); ss.
              Fail erewrite smeq; eauto; fail.
              erewrite (@smeq (@ModSemPair.SMO SM SS msp)). eexact T. et.
              (* TODO: "erewrite smeq" does not work and I am sure it is a Coq's bug!!!
                 What an annoying bug... *)
            }
          }
      + ii.
        do 2 (unfold ohs_src, ohs_tgt; ss).
        des_ifs_safe. des_ifs.
        { rewrite upcast_downcast in *. clarify.
          rewrite SimMemOh.set_sm_oh_src.
          rewrite SimMemOh.set_sm_oh_tgt.
          ss.
        }
        { rewrite upcast_downcast in *. clarify. }
    - ii; ss. inv SMMATCH0. inv SMMATCH1. ss. des_ifs_safe.
      exploit (WTYSND smos0); eauto. i; des.
      exploit (WTYSND smos1); eauto. i; des.
      des_ifs. inv SMLE.
      eapply LESMO; eauto.
      { rewrite upcast_downcast. ss. }
      { rewrite upcast_downcast. ss. }
    - ii.
      des. clarify.
      (* set msp.(ModSemPair.src).(midx) as n in *. *)
      set (set_smo smos0 msp IN smo1) as smos1 in *.
      set (set_smo smos2 msp IN smo3) as smos3 in *.
      clarify. clear_tac.
      econs; eauto.
      { ss. erewrite smeq; et. eapply SimMemOh.le_proj; et. }
      ii.
      destruct (classic (mi = (SimMemOh.midx (class := msp.(ModSemPair.SMO))))).
      { clarify.
        Fail erewrite smnth in *.
        erewrite smnth in ANY0; eauto.
        erewrite smnth in ANY1; eauto.
        clarify. esplits; eauto. ii. rewrite upcast_downcast in *. clarify. }
      ss.
      des_ifs; cycle 1.
      { exploit (WTYSND smos2); eauto. i; des. clarify. }

      inv MLEPUBOHS; eauto.
      specialize (LESMO mi SMO0 SMO1).
      exploit smos2.(WTYSND); eauto. i; des. clarify.
      assert(T := ANY0). eapply WTYSND in T. des. clarify.
      subst smos3. subst smos1. simpl in LESMO. des_ifs_safe.
      exploit LESMO; eauto. ii. des. clarify. esplits; eauto.
      rewrite upcast_downcast in *. ii. clarify.
      rename smo5 into smo_other0.
      rename t0 into smo_other2.
      exploit LESMO0; eauto. intro T; des.
      eapply SimMemOh.set_sm_le in T.
      + rewrite SimMemOh.setset_sm in T.
        erewrite <- SimMemOh.setget_sm with smo_other0. eauto.
      + eapply SimMemOh.le_proj in MLEPUB. rp; try apply MLEPUB; et.
        rewrite SMEQ0. erewrite <- smeq; et.
  Qed.

End SimMemOhUnify.

Section SimMemOhUnify.

  Context `{SM: SimMem.class} {SU: Sound.class} {SS: SimSymb.class SM}.

  Local Opaque upcast.
  (** TODO: make it global opaque **)

  Theorem unification_smo
          msps
          (SIM: Forall ModSemPair.sim msps)
          (UNIQ: Midx.NoDup (map ModSem.midx (map ModSemPair.src msps)))
          (* (UNIQ: Midx.NoDup (map (fun msp => SimMemOh.midx (class := msp.(ModSemPair.SMO))) msps)) *)
    :
      exists SMOS,
        (<<RESPECTS: forall msp (IN: In msp msps),
            (<<RESPECTS: respects msp.(ModSemPair.SMO) SMOS>>)>>)
        /\
        (<<INITOH: forall
            sm
            (SIMSKENV: Forall (fun msp => ModSemPair.sim_skenv msp sm) msps)
            (WF: SimMem.wf sm)
          ,
            exists (smos: SimMemOhs.t (class := (SMOS))),
              (<<WF: SimMemOhs.wf smos>>) /\
              (<<SMEQ: smos.(SimMemOhs.sm) = sm>>) /\
              (<<OHSRC: smos.(SimMemOhs.ohs_src) = load_owned_heaps (map ModSemPair.src msps)>>) /\
              (<<OHTGT: smos.(SimMemOhs.ohs_tgt) = load_owned_heaps (map ModSemPair.tgt msps)>>)>>)
  .
  Proof.
    assert(UNIQ0: Midx.NoDup (map ModSem.midx (map ModSemPair.tgt msps))).
    { erewrite f_equal; et.
      rewrite Forall_forall in *. rewrite ! map_map.
      eapply map_ext; et. ii. exploit SIM; et. intro T; des. inv T; ec.
    }
    exists (SimMemOhs_intro msps). ss.
    split.
    { eapply respects_intro; eauto. }
    ginduction msps; ii; ss.
    { unshelve eexists (@mk _ _ [] sm0 (fun mi => (SimMemOh_default_aux _ mi, upcast sm0)) _ _ _); ss.
      { ii. clarify. rewrite upcast_downcast. esplits; eauto. }
      esplits; ss; eauto.
      - econs; ss. ii. clarify. rewrite upcast_downcast in *. clarify.
      - unfold ohs_src. apply func_ext1. intro n. ss. rewrite upcast_downcast. ss.
      - unfold ohs_tgt. apply func_ext1. intro n. ss. rewrite upcast_downcast. ss.
    }
    rename a into msp.
    inv SIM. rename H1 into HD. rename H2 into TL.
    inv SIMSKENV. rename H1 into SKEHD. rename H2 into SKETL.
    exploit IHmsps; eauto.
    { rr in UNIQ. ss. des_ifs. eapply NoDup_cons_iff in UNIQ; des; et. }
    { rr in UNIQ0. ss. des_ifs. eapply NoDup_cons_iff in UNIQ0; des; et. }
    i; des.
    des_ifs.
    bar. inv HD. move INITOH at top. move MIDXNONE at top. move MIDX at top. move MIDX0 at top.
    clear_until_bar. exploit INITOH; eauto. i; des.
    unshelve eexists (@mk _ _ _ (smos.(sm))
                          (Midx.update smos.(anys) (SimMemOh.midx (class := msp.(ModSemPair.SMO)))
                                                   (msp.(ModSemPair.SMO), (upcast smo)))
                          _ _ _).
    { ii. ss. des; clarify.
      - unfold Midx.update in *. des_ifs.
      - unfold Midx.update in *. des_ifs.
        { clear - UNIQ e NTH MIDXNONE TL MIDX MIDX0.
          rewrite Forall_forall in *. exploit TL; et. intro U.
          rr in UNIQ. unfold id in *. ss. des_ifs.
          + eapply NoDup_cons_iff in UNIQ. des.
            contradict UNIQ. eapply in_filter_map_iff. esplits; try refl.
            rewrite in_map_iff. eexists msp0.(ModSemPair.src). inv U. esplits; ec.
            rewrite in_map_iff. esplits; et.
          + erewrite MIDXNONE; et. inv U.
            erewrite MIDXNONE0; ec.
        }
        eapply WTYFST; et.
    }
    { ii. unfold Midx.update in *. des_ifs.
      - rewrite upcast_downcast. esplits; eauto.
      - exploit WTYSND; et.
    }
    { ii. unfold Midx.update in *. des_ifs.
      - f_equal; ss.
        + remember (@ModSemPair.SMO SM SS msp) as X. clear HeqX. erewrite MIDXNONE; et.
        + hexploit1 MIDXNONE ;ss.
          remember (@ModSemPair.SMO SM SS msp) as X. clear HeqX. subst. ss. rewrite SMEQ. ss.
      - exploit WTYNONE; et.
    }
    unfold ohs_src. unfold ohs_tgt. ss.
    esplits; eauto.
    - econs; ss; eauto.
      ii. unfold Midx.update in *. des_ifs.
      + rewrite upcast_downcast in *. clarify.
      + eapply WF0; eauto.
    - apply func_ext1. ii. des_ifs_safe.
      unfold Midx.update in *.
      destruct (Midx.eq_dec SimMemOh.midx x0); ss; clarify.
      { rewrite upcast_downcast. rewrite OHSRC0.
        unfold load_owned_heaps.
        erewrite Midx.list_to_set_spec2; et.
        { rewrite map_map; ss. }
        { ii. rewrite in_map_iff in *. des. clarify. exploit ModSem.midx_none; et. intro T.
          clear - T.
          generalize x.(initial_owned_heap). rewrite T. intro u. destruct u; ss.
        }
        { rewrite in_map_iff. ss. esplits; ec. f_equal. ec. }
      }
      exploit WTYSND; et. i; des. clarify. des_ifs.
      replace (load_owned_heaps (ModSemPair.src msp :: map ModSemPair.src msps) SimMemOh.midx)
        with (load_owned_heaps (map ModSemPair.src msps) SimMemOh.midx); cycle 1.
      { eapply load_owned_heaps_diff; ec. }
      rewrite <- OHSRC.
      unfold load_owned_heaps.
      unfold ohs_src. des_ifs.
    - apply func_ext1. ii. des_ifs_safe.
      unfold Midx.update in *.
      destruct (Midx.eq_dec SimMemOh.midx x0); ss; clarify.
      { rewrite upcast_downcast. rewrite OHTGT0.
        unfold load_owned_heaps.
        erewrite Midx.list_to_set_spec2; et.
        { rewrite map_map; ss. }
        { ii. rewrite in_map_iff in *. des. clarify. exploit ModSem.midx_none; et. intro T.
          clear - T.
          generalize x.(initial_owned_heap). rewrite T. intro u. destruct u; ss.
        }
        { rewrite in_map_iff. ss. esplits; ec. f_equal. ec. }
      }
      exploit WTYSND; et. i; des. clarify. des_ifs.
      replace (load_owned_heaps (ModSemPair.tgt msp :: map ModSemPair.tgt msps) SimMemOh.midx)
        with (load_owned_heaps (map ModSemPair.tgt msps) SimMemOh.midx); cycle 1.
      { eapply load_owned_heaps_diff; ec. }
      rewrite <- OHTGT.
      unfold load_owned_heaps.
      unfold ohs_tgt. des_ifs.
  Qed.

End SimMemOhUnify.
End SimMemOhUnify.










(* Section SimMemOhsIntro. *)

(*   Context `{SM: SimMem.class} {SS: SimSymb.class SM}. *)
(*   Variable msps: list ModSemPair.t. *)

(*   Ltac des_let := *)
(*     match goal with *)
(*     | [ H: context[let y := ?x in _ ] |- _ ] => *)
(*       let name := fresh "let" in destruct x eqn:name *)
(*     end. *)

(*   Inductive SimMemOhs_t_aux: Midx.t -> Type := *)
(*   | TyNil: SimMemOhs_t_aux 0%nat *)
(*   | TyCons *)
(*       n msp *)
(*       (MSP: List.nth_error msps n = Some msp) *)
(*       (hd: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) *)
(*       (tl: SimMemOhs_t_aux n) *)
(*     : *)
(*       SimMemOhs_t_aux (S n) *)
(*   . *)

(*   (* TODO: change to Let *) *)
(*   Definition SimMemOhs_t: Type := SimMem.t * SimMemOhs_t_aux (length msps). *)

(*   Inductive SimMemOhs_le_aux: *)
(*     forall (midx: Midx.t) (smos0 smos1: SimMemOhs_t_aux midx), Prop := *)
(*   | LeNil smos0 smos1: @SimMemOhs_le_aux (0%nat) smos0 smos1 *)
(*   | LeCons *)
(*       n msp *)
(*       (MSP: List.nth_error msps n = Some msp) *)
(*       (hd0 hd1: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) *)
(*       (tl0 tl1: SimMemOhs_t_aux n) *)
(*     : *)
(*       @SimMemOhs_le_aux (S n) (@TyCons n msp MSP hd0 tl0) *)
(*                         (@TyCons n msp MSP hd0 tl0) *)
(*   . *)

(*   (* TODO: change to Let *) *)
(*   Definition SimMemOhs_le: SimMemOhs_t -> SimMemOhs_t -> Prop := *)
(*     fun smos0 smos1 => *)
(*       SimMem.le (fst smos0) (fst smos1) /\ *)
(*       @SimMemOhs_le_aux (length msps) (snd smos0) (snd smos1). *)

(*   Program Instance PreOrder_SimMemOhs_le_aux: PreOrder SimMemOhs_le. *)
(*   Next Obligation. *)
(*     ii. rr. split; try refl. abstr (snd x) y. *)
(*     induction y; ii; ss. *)
(*     - econs. *)
(*     - econs; eauto. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     unfold SimMemOhs_le. *)
(*     ii. des. split; try etrans; eauto. clear H H0. *)
(*     abstr (snd x) a. abstr (snd y) b. abstr (snd z) c. *)
(*     ginduction a; ii; ss. *)
(*     - inv H2. simpl_depind. clarify. econs. *)
(*     - inv H2. simpl_depind. clarify. inv H1. simpl_depind. clarify. *)
(*       replace MSP2 with MSP. *)
(*       { econs; eauto. } *)
(*       eapply Axioms.proof_irr. *)
(*   Qed. *)

(*   Inductive SimMemOhs_wf_aux (sm: SimMem.t): *)
(*     forall (midx: Midx.t) (smos: SimMemOhs_t_aux midx), Prop := *)
(*   | WfNil smos: @SimMemOhs_wf_aux sm 0%nat smos *)
(*   | WfCons *)
(*       n msp *)
(*       (MSP: List.nth_error msps n = Some msp) *)
(*       (hd: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) *)
(*       (tl: @SimMemOhs_t_aux n) *)
(*       (HDEQ: hd.(SimMemOh.sm) = sm) *)
(*       (HD: SimMemOh.wf hd) *)
(*       (TL: @SimMemOhs_wf_aux sm n tl) *)
(*     : *)
(*       @SimMemOhs_wf_aux sm (S n) (@TyCons n msp MSP hd tl) *)
(*   . *)

(*   (* TODO: change to Let *) *)
(*   Definition SimMemOhs_wf: SimMemOhs_t -> Prop := *)
(*     fun smos => SimMem.wf (fst smos) *)
(*                 /\ @SimMemOhs_wf_aux (fst smos) (length msps) (snd smos). *)

(*   (* Let SimMemOhs_t: Type := *) *)
(*   (*   SimMem.t * *) *)
(*   (*   (forall midx, *) *)
(*   (*       match List.nth_error msps midx with *) *)
(*   (*       | Some msp => (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)) *) *)
(*   (*       | None => SimMemOh.t *) *)
(*   (*       end *) *)
(*   (*   ). *) *)
           
(*   Fail Inductive SimMemOhs_ohs_src_aux: *)
(*     forall (midx: Midx.t) (smos: SimMemOhs_t_aux midx), list { oh: Type & oh } := *)
(*   | OhsSrcNil smos: @SimMemOhs_ohs_src_aux 0%nat smos *)
(*   . *)

(*   Fixpoint SimMemOhs_ohs_src_aux2 (midx: Midx.t) (smos: SimMemOhs_t_aux midx): *)
(*     list { oh: Type & oh } := *)
(*     match smos with *)
(*     | TyNil => nil *)
(*     | TyCons n msp MSP hd tl => *)
(*       (* (@existT Type _ _ hd) *) *)
(*       (existT id _ hd.(SimMemOh.oh_src)) :: @SimMemOhs_ohs_src_aux2 n tl *)
(*     end *)
(*   . *)

(*   (* TODO: make it Let *) *)
(*   Definition SimMemOhs_ohs_src_aux: forall midx, SimMemOhs_t_aux midx -> Sem.Ohs := *)
(*     fun midx smos_aux n => *)
(*       match nth_error (rev (@SimMemOhs_ohs_src_aux2 midx smos_aux)) n with *)
(*       | Some oh_src => oh_src *)
(*       | _ => (existT id _ tt) *)
(*       end *)
(*   . *)

(*   (* TODO: make it Let *) *)
(*   Definition SimMemOhs_ohs_src: SimMemOhs_t -> Sem.Ohs := *)
(*     fun smos => @SimMemOhs_ohs_src_aux (length msps) (snd smos) *)
(*   . *)
(*   (* Let SimMemOhs_ohs_src: SimMemOhs_t -> Sem.Ohs := *) *)
(*   (*   fun smos midx => *) *)
(*   (*     match nth_error (@SimMemOhs_ohs_src_aux (length msps) (snd smos)) midx with *) *)
(*   (*     | Some oh_src => oh_src *) *)
(*   (*     | _ => (existT id _ tt) *) *)
(*   (*     end *) *)
(*   (* . *) *)
(*   Obligation Tactic := idtac. *)

(*   Ltac dep_destruct E := *)
(*     let x := fresh "x" in *)
(*     remember E as x; simpl in x; dependent destruction x; *)
(*     try match goal with *)
(*         | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H *)
(*         end. *)

(* Program Instance SimMemOhs_intro: SimMemOhs.class := *)
(* {| *)
(*   (* SimMemOhs.t := SimMem.t * list SimMemOh.t; *) *)
(*   SimMemOhs.t := SimMemOhs_t; *)
(*   SimMemOhs.sm := fst; *)
(*   SimMemOhs.le := SimMemOhs_le; *)
(*   (* SimMemOhs.le_PreOrder := _; *) *)
(* |} *)
(* . *)
(* Next Obligation. *)
(*   (* SimMemOhs.ohs_src *) *)
(*   uo. *)
(*   ii. destruct X. specialize (y H). *)
(*   cbv zeta in y. *)
(*   des_ifs. *)
(*   - eexists. eapply y. *)
(*   - eexists. eapply y. *)
(* Defined. *)
(* Next Obligation. *)
(*   (* SimMemOhs.ohs_tgt *) *)
(*   uo. *)
(*   ii. destruct X. specialize (y H). *)
(*   cbv zeta in y. *)
(*   des_ifs. *)
(*   - eexists. eapply y. *)
(*   - eexists. eapply y. *)
(* Defined. *)
(* Next Obligation. *)
(*   (* SimMemOhs.wf *) *)
(*   uo. *)
(*   ii. destruct X. *)
(*   eapply and. *)
(*   { eapply t0.(SimMem.wf). } *)
(*   refine (forall midx: nat, _: Prop). *)
(*   specialize (y midx). *)
(*   cbv zeta in y. des_ifs. *)
(*   - eapply and. { eapply (y.(SimMemOh.sm) = t0). } eapply y.(SimMemOh.wf). *)
(*   - eapply True. *)
(*     (* eapply and. { eapply (y.(SimMemOh.sm) = t0). } eapply y.(SimMemOh.wf). *) *)
(* Defined. *)
(* Next Obligation. *)
(*   (* SimMemOhs.lepriv *) *)
(*   uo. *)
(*   intros X Y. *)
(*   destruct X as [X0 X1], Y as [Y0 Y1]. *)
(*   eapply and. *)
(*   { eapply (SimMem.le X0 Y0). } *)
(*   refine (forall midx: nat, _: Prop). *)
(*   specialize (X1 midx). specialize (Y1 midx). *)
(*   cbv zeta in *. des_ifs. *)
(*   - eapply (SimMemOh.le X1 Y1). *)
(*   - eapply True. *)
(* Defined. *)
(* Next Obligation. *)
(*   econs. *)
(*   - ii. r. des_ifs. *)
(*     split; ss; try refl. *)
(*     i. rename y into yyy. *)
(*     Fail subst yyy. *)
(*     Fail hrewrite yyy. *)
(*     Fail rewrite yyy. *)
(*     Fail unfold yyy. *)
(*     (* dup y. specialize (y0 midx0). *) *)
(*     Fail dep_destruct (nth_error msps midx0). *)
(*     (* dependent destruction (nth_error msps midx0). *) *)
(*     (* depdes (nth_error msps midx0). *) *)
(*     generalize (yyy midx0). *)
(*     destruct (nth_error msps midx0). *)
(*     TTTTTTTTTTTTTTTTTTTTTT above two  lines !!!!  *)
(*     unfold yyy. *)
(*     revert yyy. *)
(*     generalize (nth_error msps midx0). *)
(*     destruct (nth_error msps midx0). *)
(*     pattern (nth_error msps midx0) at 2. ss. *)
(*     remember (nth_error msps midx0) as tmp. *)
(*     pattern (nth_error msps midx0) at 2. ss. *)
(*     destruct (nth_error msps midx0). *)
(*     hpattern (nth_error msps midx0). *)
(*     hresolve (nth_error msps midx0). *)
(*     destruct (nth_error msps midx0). *)
(*     hpattern *)
(*     destruct (nth_error msps midx0) eqn:T. *)
(* Qed. *)
(* Next Obligation. *)
(*   (* SimMemOhs.lepriv *) *)
(*   intros ? ? ? X Y. *)
(*   destruct X as [X0 X1], Y as [Y0 Y1]. *)
(*   eapply and. *)
(*   { eapply (SimMem.le X0 Y0). } *)
(*   refine (forall midx: nat, _: Prop). *)
(*   specialize (X1 midx). specialize (Y1 midx). *)
(*   cbv zeta in *. des_ifs. *)
(*   - eapply (SimMemOh.le X1 Y1). *)
(*   - eapply True. *)
(* Defined. *)

(*     ohs_src : t -> Sem.Ohs; *)
(*     ohs_tgt : t -> Sem.Ohs; *)
(*     wf : t -> Prop; *)
(*     le : t -> t -> Prop; *)
(*     lepriv : t -> t -> Prop; *)
(*     le_PreOrder : PreOrder le; *)
(*     pub_priv : forall smo0 smo1 : t, le smo0 smo1 -> lepriv smo0 smo1; *)
(*     wf_proj : wf <1= SimMem.wf <*> sm; *)
(*     le_proj : Morphisms.respectful le SimMem.le sm sm; *)
(*     lepriv_proj : Morphisms.respectful lepriv SimMem.lepriv sm sm } *)

(* Record sm_match_tmp_aux (msp: @ModSemPair.t SM SS) *)
(*   (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) m (smos: SimMemOhs_t_aux m): Prop := *)
(*   (* TODO: I want to remove @ *) *)
(*   { *)
(*     ohsrcty_tmp: (projT1 ((@SimMemOhs_ohs_src_aux m smos) (msp.(ModSemPair.src).(midx)))) = *)
(*              msp.(ModSemPair.src).(owned_heap); *)
(*     ohsrc_tmp: (projT2 ((@SimMemOhs_ohs_src_aux m smos) (msp.(ModSemPair.src).(midx))) *)
(*                    ~= smo.(SimMemOh.oh_src)); *)
(*   }. *)

(* Definition sm_match_tmp (msp: @ModSemPair.t SM SS) *)
(*   (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) (smos: SimMemOhs_t): Prop := *)
(*   @sm_match_tmp_aux msp smo (length msps) (snd smos) /\ fst smos = smo. *)

(*   (* Fixpoint get_nth (midx: Midx.t) (smos: SimMemOhs_t_aux midx) *) *)
(*   (*          (n: Midx.t) msp (MSP: List.nth_error msps n = Some msp): *) *)
(*   (*   (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)) := *) *)
(*   (*   match smos with *) *)
(*   (*   | TyNil => nil *) *)
(*   (*   | TyCons n msp MSP hd tl => *) *)
(*   (*     nil *) *)
(*   (*   end *) *)
(*   (* . *) *)

(* End SimMemOhsIntro. *)
(* Arguments sm_match_tmp {_ _}. *)
(* Arguments sm_match_tmp_aux {_ _}. *)
(* Arguments SimMemOhs_t {_ _}. *)
(* Arguments SimMemOhs_wf {_ _}. *)
(* Arguments SimMemOhs_wf_aux {_ _}. *)
(* Arguments SimMemOh.t {_}. *)
(* (* Arguments sm_match_tmp: clear implicits. *) *)

(*   (* Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *) *)
(*   (*             (msps: list ModSemPair.t) *) *)
(*   (*             len n (LT: (len > n)%nat) msp *) *)
(*   (*             (MSP: nth_error msps n = Some msp), *) *)
(*   (*     (<<SMPROJ: forall sm (smos: SimMemOhs_t_aux msps len) *) *)
(*   (*                       (MWF0: SimMem.wf sm) *) *)
(*   (*                       (MWF1: SimMemOhs_wf_aux msps sm len smos), *) *)
(*   (*         exists (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))), *) *)
(*   (*           sm = smo /\ *) *)
(*   (*           (projT1 ((SimMemOhs_ohs_src_aux smos) *) *)
(*   (*                      (msp.(ModSemPair.src).(midx)))) = *) *)
(*   (*            msp.(ModSemPair.src).(owned_heap) /\ *) *)
(*   (*           (projT2 ((SimMemOhs_ohs_src_aux smos) *) *)
(*   (*                      (msp.(ModSemPair.src).(midx))) *) *)
(*   (*                  ~= smo.(SimMemOh.oh_src)) /\ *) *)
(*   (*           (* sm_match_tmp msps msp smo (sm, smos) /\ *) *) *)
(*   (*           SimMemOh.wf smo>>). *) *)
(*   (* Proof. *) *)
(*   (*   (* intros ? ? ?. *) *) *)
(*   (*   (* ginduction len; ii; ss. *) *) *)
(*   (*   ii. gen n. *) *)
(*   (*   dependent induction smos; ii; ss. *) *)
(*   (*   { omega. } *) *)
(*   (*   destruct n0; ss. *) *)
(*   (*   { destruct msps; ss. clarify. *) *)
(*   (*     exists hd. *) *)
(*   (* hd : @SimMemOh.t SM (owned_heap (@ModSemPair.src SM SS msp0)) *) *)
(*   (*        (owned_heap (@ModSemPair.tgt SM SS msp0)) msp0 *) *)
(*   (*   smo : @SimMemOh.t SM (owned_heap (@ModSemPair.src SM SS msp)) *) *)
(*   (*           (owned_heap (@ModSemPair.tgt SM SS msp)) msp, *) *)
(*   (*   } *) *)
(*   (* Qed. *) *)

(*   Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n msp *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall (smos: SimMemOhs_t_aux msps (length msps)), *)
(*           exists smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)), True>>). *)
(*   Proof. *)
(*     ii. *)
(*     assert((n < length msps)%nat). *)
(*     { eapply nth_error_Some; eauto. rewrite MSP; ss. } *)
(*     abstr (length msps) m. gen n. *)
(*     dependent induction smos; ii; ss. *)
(*     { omega. } *)
(*     destruct (classic (n0 = n)). *)
(*     { clarify. } *)
(*     eapply IHsmos; eauto. *)
(*     omega. *)
(*   Qed. *)

(*   Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n msp *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos), *)
(*           exists smo, sm_match_tmp msps msp smo smos /\ SimMemOh.wf smo>>). *)
(*   Proof. *)
(*     ii. *)
(*     destruct smos as [sm smos]. *)
(*     assert((n < length msps)%nat). *)
(*     { eapply nth_error_Some; eauto. rewrite MSP; ss. } *)
(*     rr in MWF. des. ss. *)
(*     (* Set Printing Implicit. *) *)
(*     pattern (length msps) in smos. *)
(*     Fail remember (length msps). *)
(*     Fail generalize (length msps). *)
(*   Abort. *)

(*   Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n msp *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos), *)
(*           exists smo, sm_match_tmp_aux msps msp smo (length msps) (snd smos) *)
(*                       /\ SimMemOh.sm smo = fst smos *)
(*                       /\ SimMemOh.wf smo>>). *)
(*   Proof. *)
(*     ii. *)
(*     assert((n < length msps)%nat). *)
(*     { eapply nth_error_Some; eauto. rewrite MSP; ss. } *)
(*     destruct smos as [sm smos]; ss. *)
(*     gen smos. *)
(*     Fail generalize (length msps). *)
(*   Abort. *)

(*   Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n msp *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall (smos: SimMemOhs_t msps), exists smo, fst smos = smo>>). *)
(*   Proof. *)
(*     ii. *)
(*     gen n. *)
(*     destruct smos as [sm smos]. *)
(*     dependent induction smos; ii; ss. *)
(*     { destruct msps; ss. clarify. destruct n; ss. } *)
(*     destruct msps; ss. clarify. *)
(*     dependent destruction smos0. *)
(*     simpl_depind. clarify. simpl_depind. clarify. *)
(*     idtac "IHsmos-is-not well-formed". *)
(*   Abort. *)

(*   Lemma ohs_src_aux2_length *)
(*         `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*         (msps: list ModSemPair.t) *)
(*         m (smos: SimMemOhs_t_aux msps m) *)
(*     : *)
(*       length (SimMemOhs_ohs_src_aux2 smos) = m *)
(*   . *)
(*   Proof. *)
(*     ginduction m; ii; ss. *)
(*     { dependent destruction smos. ss. } *)
(*     { dependent destruction smos. ss. *)
(*       f_equal. eapply IHm; eauto. *)
(*     } *)
(*   Qed. *)

(*   Lemma tmp_lemma_aux: forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n m msp *)
(*               (LT: (n < m)%nat) *)
(*               (MIDXFACT: forall o msp_o, *)
(*                   nth_error msps o = Some msp_o -> *)
(*                   msp_o.(ModSemPair.src).(midx) = o) *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall smos (MWF: SimMem.wf (fst smos) /\ *)
(*                                    SimMemOhs_wf_aux msps (fst smos) m (snd smos)), *)
(*           exists smo, sm_match_tmp_aux msps msp smo m (snd smos) *)
(*                       /\ SimMemOh.sm smo = fst smos *)
(*                       /\ SimMemOh.wf smo>>). *)
(*   Proof. *)
(*     ii. *)
(*     destruct smos as [sm smos]; ss. des. *)
(*     gen n. *)
(*     dependent induction smos; ii; ss. *)
(*     { omega. } *)
(*     dependent destruction MWF0. *)
(*     assert(LEN: length (rev (SimMemOhs_ohs_src_aux2 smos)) = n). *)
(*     { rewrite rev_length. eapply ohs_src_aux2_length; eauto. } *)
(*     destruct (classic (n0 = n)). *)
(*     { *)
(*       clarify. *)
(*       exists hd. esplits; eauto. *)
(*       - econs; ss. *)
(*         + unfold SimMemOhs_ohs_src_aux. ss. *)
(*           exploit (MIDXFACT n); eauto. intro T. rewrite T. *)
(*           clear_tac. *)
(*           rewrite nth_error_app2; cycle 1. *)
(*           { omega. } *)
(*           rewrite LEN. replace (n - n)%nat with 0%nat by omega. *)
(*           ss. *)
(*         + unfold SimMemOhs_ohs_src_aux. ss. *)
(*           exploit (MIDXFACT n); eauto. intro T. rewrite T. *)
(*           clear_tac. *)
(*           rewrite nth_error_app2; cycle 1. *)
(*           { omega. } *)
(*           rewrite LEN. replace (n - n)%nat with 0%nat by omega. *)
(*           ss. *)
(*     } *)
(*     exploit IHsmos; eauto. *)
(*     { omega. } *)
(*     i; des. *)
(*     clarify. *)
(*     exploit (MIDXFACT n0); eauto. intro T. *)
(*     assert(LT2: (n0 < n)%nat) by omega. *)
(*     esplits; eauto. *)
(*     { *)
(*       clear - LT2 T H0 LEN. *)
(*       clear_tac. *)
(*       inv H0. *)
(*       econs; eauto. *)
(*       - unfold SimMemOhs_ohs_src_aux in *. ss. *)
(*         rewrite nth_error_app1; try omega. ss. *)
(*       - unfold SimMemOhs_ohs_src_aux in *. ss. *)
(*         rewrite nth_error_app1; try omega. ss. *)
(*     } *)
(*   Qed. *)

(*   Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
(*               (msps: list ModSemPair.t) *)
(*               n msp *)
(*               (MSP: nth_error msps n = Some msp), *)
(*       (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos), *)
(*           exists smo, sm_match_tmp msps msp smo smos /\ SimMemOh.wf smo>>). *)
(*   Proof. *)
(*     ii. destruct smos as [sm smos]. rr in MWF. des. *)
(*     exploit (@tmp_lemma_aux _ _ msps n (length msps)); eauto. *)
(*     { eapply nth_error_Some; eauto. rewrite MSP; ss. } *)
(*     { admit "". } *)
(*     i; des. ss. *)
(*     esplits; eauto. rr. esplits; eauto. *)
(*   Qed. *)




(* Theorem fundamental_theorem_merge *)
(*         SM (SS: SimSymb.class SM) *)
(*         (msps: list ModSemPair.t) *)
(*   : *)
(*     exists SMOS: SimMemOhs.class, Forall (good_properties SMOS) msps *)
(* . *)
(* Proof. *)
(*   eexists (SimMemOhs.Build_class _ _ _ _ _ _ _ _ _ _ _ _). *)
(* Qed. *)
