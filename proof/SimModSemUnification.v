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
Require Import SimModSemUnified SimMod SimProg.
Require Import Any.

Set Implicit Arguments.



(*********** TODO: move to Midx module ************)
(*********** TODO: move to Midx module ************)
(*********** TODO: move to Midx module ************)
Lemma mapi_aux_length
      A B (f: Midx.t -> A -> B) m la
  :
    <<LEN: length (Midx.mapi_aux f m la) = length la>>
.
Proof.
  ginduction la; ii; ss.
  erewrite IHla; eauto.
Qed.

Lemma nth_error_mapi_none_aux_iff
      A B  (f : Midx.t -> A -> B) la idx m
  :
    <<NTH: nth_error (Midx.mapi_aux f m la) idx = None>> <->
    <<LEN: (length la <= idx)%nat>>
.
Proof.
  split; i.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss. r. xomega.
    + destruct idx; ii; ss. r. exploit IHla; eauto. i; des. xomega.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss.
    + destruct idx; ii; ss. { xomega. } eapply IHla; eauto. r. xomega.
Qed.



Module SimMemOhUnify.
Section SimMemOhUnify.

  Context `{SM: SimMem.class} {SU: Sound.class} {SS: SimSymb.class SM}.
  Variable msps: list ModSemPair.t.
  Hypothesis SIM: Forall ModSemPair.sim msps.
  Hypothesis MIDXWF: forall n msp (NTH: nth_error msps n = Some msp),
      <<MIDX: msp.(ModSemPair.src).(ModSem.midx) = n>>.
  Let MIDXWF2: forall n msp (NTH: nth_error msps n = Some msp),
      <<MIDX: SimMemOh.midx (class := msp.(ModSemPair.SMO)) = n>>.
  Proof.
    ii. r. exploit MIDXWF; et. i; des. clarify. rewrite Forall_forall in *.
    eapply nth_error_In in NTH. exploit SIM; et. intro T. inv T. congruence.
  Qed.

  Record t: Type := mk {
    sm:> SimMem.t;
    anys: list Any;
    LEN: <<LEN: length anys = length msps>>;
    WTY: forall n msp a0 (NTH: nth_error msps n = Some msp) (NTH: nth_error anys n = Some a0),
         exists smo0, (<<DOWNCAST: @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 = Some smo0>>)
                      /\
                      (<<SMEQ: smo0.(SimMemOh.sm) = sm>>)
    ;
  }.

  Lemma WTY2
        smos0 n msp
        (NTH: nth_error msps n = Some msp)
    :
      exists a0 smo0, (<<NTH: nth_error smos0.(anys) n = Some a0>>)
                      /\
                      (<<DOWNCAST: @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 = Some smo0>>)
                      /\
                      (<<SMEQ: smo0.(SimMemOh.sm) = smos0.(sm)>>)
  .
  Proof.
    destruct (nth_error smos0.(anys) n) eqn:T.
    - exploit WTY; eauto. i; des. esplits; eauto.
    - exfalso. eapply nth_error_None in T. exploit nth_error_Some; eauto. rewrite NTH.
      i; des. exploit H; ss; et. intro U. rewrite LEN in *. xomega.
  Qed.

  Program Definition set_sm (smos0: t) (sm0: SimMem.t): t :=
    @mk
      sm0
      (Midx.mapi_aux (fun n a0 =>
                        match nth_error msps n with
                        | Some msp =>
                          match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with
                          | Some smo0 => upcast ((SimMemOh.set_sm smo0 sm0): SimMemOh.t)
                          | _ => upcast tt
                          end
                        | _ => upcast tt
                        end
                     ) 0%nat (smos0.(anys)))
      _
      _
  .
  Next Obligation.
    erewrite <- (smos0.(LEN)). rewrite mapi_aux_length. ss.
  Qed.
  Next Obligation.
    rewrite Midx.nth_error_mapi_aux_iff in *. des.
    ss. des_ifs_safe.
    destruct (downcast a) eqn:T.
    - unfold upcast in *. simpl_depind.
      des_ifs. unfold eq_rect_r.
      erewrite <- eq_rect_eq; eauto.
      esplits; eauto. rewrite SimMemOh.getset_sm; ss.
    - exfalso. exploit smos0.(WTY); eauto. i; des. clarify.
  Qed.

  Inductive le (smos0 smos1: t): Prop :=
  | le_intro
      (LESM: SimMem.le smos0.(sm) smos1.(sm))
      (LESMO: forall
          n a0 a1 msp (smo0 smo1: SimMemOh.t (class := msp.(ModSemPair.SMO)))
          (NTH: nth_error msps n = Some msp)
          (NTH: nth_error smos0.(anys) n = Some a0)
          (NTH: nth_error smos1.(anys) n = Some a1)
          (CAST: downcast a0 = Some smo0)
          (CAST: downcast a1 = Some smo1)
        ,
          <<LESMO: SimMemOh.le (class := msp.(ModSemPair.SMO)) smo0 smo1>>
      )
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
      (LEPRIVSMO: forall
          n a0 a1 msp (smo0 smo1: SimMemOh.t (class := msp.(ModSemPair.SMO)))
          (NTH: nth_error msps n = Some msp)
          (NTH: nth_error smos0.(anys) n = Some a0)
          (NTH: nth_error smos1.(anys) n = Some a1)
          (CAST: downcast a0 = Some smo0)
          (CAST: downcast a1 = Some smo1)
        ,
          <<LEPRIVSMO: SimMemOh.lepriv (class := msp.(ModSemPair.SMO)) smo0 smo1>>
      )
  .

  Inductive wf_weak (midx: Midx.t) (smos0: t): Prop :=
  | wf_weak_intro
      (WFSMO: forall
          n a0 msp sm0 (smo0: SimMemOh.t (class := msp.(ModSemPair.SMO)))
          (WFSM: SimMem.wf sm0)
          (EXCEPT: n <> midx)
          (NTH: nth_error msps n = Some msp)
          (NTH: nth_error smos0.(anys) n = Some a0)
          (CAST: downcast a0 = Some smo0)
          (UNCH: SimMem.unchanged_on (privmods n smo0.(SimMem.ptt_src))
                                     smo0.(SimMem.src) sm0.(SimMem.src))
        ,
          (<<WFSMO: SimMemOh.wf (class := msp.(ModSemPair.SMO)) (SimMemOh.set_sm smo0 sm0)>>)
          (* /\ *)
          (* (<<SMEQ: smo0.(SimMemOh.sm) = smos0.(sm)>>) *)
      )
  .

  Inductive wf (smos0: t): Prop :=
  | wf_intro
      (WFSM: SimMem.wf smos0.(sm))
      (WFSMO: forall
          n a0 msp (smo0: SimMemOh.t (class := msp.(ModSemPair.SMO)))
          (NTH: nth_error msps n = Some msp)
          (NTH: nth_error smos0.(anys) n = Some a0)
          (CAST: downcast a0 = Some smo0)
        ,
          (<<WFSMO: SimMemOh.wf (class := msp.(ModSemPair.SMO)) smo0>>)
          (* /\ *)
          (* (<<SMEQ: smo0.(SimMemOh.sm) = smos0.(sm)>>) *)
      )
  .

  Lemma wf_weak_wf
        n smos0 msp a0
        (WFW: wf_weak n smos0)
        (NTH0: nth_error msps n = Some msp)
        (NTH1: nth_error smos0.(anys) n = Some a0)
        (smo0: SimMemOh.t (class := msp.(ModSemPair.SMO)))
        (CAST: downcast a0 = Some smo0)
        (WF: SimMemOh.wf smo0)
    :
      <<WF: wf smos0>>
  .
  Proof.
    assert(WF0: SimMem.wf smos0).
    { exploit smos0.(WTY); eauto. i; des. clarify.
      rewrite <- SMEQ.
      eapply SimMemOh.wf_proj; eauto.
    }
    econs; eauto. ii.
    destruct (Nat.eq_dec n n0).
    - clarify.
    - inv WFW.
      exploit smos0.(WTY); eauto. i; des. clarify.
      rewrite <- SMEQ in *.
      exploit WFSMO; eauto. { refl. } intro T.
      rewrite SimMemOh.setget_sm in T. ss.
  Qed.

  Lemma wf_wf_weak
        n smos0 msp a0
        (WF: wf smos0)
        (NTH0: nth_error msps n = Some msp)
        (NTH1: nth_error smos0.(anys) n = Some a0)
        (smo0: SimMemOh.t (class := msp.(ModSemPair.SMO)))
        (CAST: downcast a0 = Some smo0)
    :
      <<WFW: wf_weak n smos0>>
  .
  Proof.
    econs; eauto. ii.
    inv WF. exploit WFSMO; eauto.
    ii. eapply SimMemOh.set_sm_wf; eauto.
    rp; et. apply func_ext2. ii. repeat f_equal. apply MIDXWF2; et.
  Qed.

  Definition ohs_src (smos0: t): Sem.Ohs :=
    fun mi =>
      match nth_error msps mi, nth_error smos0.(anys) mi with
      | Some msp, Some a0 =>
        match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with
        | Some smo0 => SimMemOh.oh_src smo0
        | _ => upcast tt
        end
      | _, _ => upcast tt
      end
  .

  Definition ohs_tgt (smos0: t): Sem.Ohs :=
    fun mi =>
      match nth_error msps mi, nth_error smos0.(anys) mi with
      | Some msp, Some a0 =>
        match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with
        | Some smo0 => SimMemOh.oh_tgt smo0
        | _ => upcast tt
        end
      | _, _ => upcast tt
      end
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    - ii. econs; eauto.
      + refl.
      + ii. clarify. r. refl.
  Qed.
  Next Obligation.
    - ii. inv H. inv H0. econs; eauto.
      + etrans; eauto.
      + ii. r.
        rename a0 into ax. rename a1 into az.
        assert(CASTY: exists ay, nth_error (anys y) n = Some ay).
        { destruct (nth_error (anys y) n) eqn:T; eauto. exfalso.
          eapply nth_error_None in T. rewrite y.(LEN) in T.
          exploit nth_error_Some; eauto.
          { rewrite NTH. intro Q; ss. des. exploit Q; ss. i. xomega. }
        }
        des. exploit y.(WTY); eauto. i; des. rename smo2 into smoy.
        transitivity smoy.
        { eapply LESMO; eauto. }
        { eapply LESMO0; eauto. }
  Qed.

  Program Instance lepriv_PreOrder: PreOrder lepriv.
  Next Obligation.
    - ii. econs; eauto.
      + refl.
      + ii. clarify. r. refl.
  Qed.
  Next Obligation.
    - ii. inv H. inv H0. econs; eauto.
      + etrans; eauto.
      + ii. r.
        rename a0 into ax. rename a1 into az.
        assert(CASTY: exists ay, nth_error (anys y) n = Some ay).
        { destruct (nth_error (anys y) n) eqn:T; eauto. exfalso.
          eapply nth_error_None in T. rewrite y.(LEN) in T.
          exploit nth_error_Some; eauto.
          { rewrite NTH. intro Q; ss. des. exploit Q; ss. i. xomega. }
        }
        des. exploit y.(WTY); eauto. i; des. rename smo2 into smoy.
        transitivity smoy.
        { eapply LEPRIVSMO; eauto. }
        { eapply LEPRIVSMO0; eauto. }
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
    ii. exploit LESMO; eauto.
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
    Variable n: Midx.t.
    Variable msp: ModSemPair.t.
    Hypothesis (NTH: nth_error msps n = Some msp).
    Variable smo': SimMemOh.t (class := msp.(ModSemPair.SMO)).
    (* Hypothesis (SMMATCH: sm_match (S n) smo' smos0). *)

    Program Definition set_smo: t :=
      @mk
        smo'
        (Midx.mapi_aux (fun m a0 =>
                          if Nat.eq_dec n m then @upcast SimMemOh.t smo' else
                            match nth_error msps m with
                            | Some msp =>
                              match @downcast (SimMemOh.t (class := msp.(ModSemPair.SMO))) a0 with
                              | Some smo0 =>
                                @upcast SimMemOh.t ((SimMemOh.set_sm smo0 smo'.(SimMemOh.sm)): SimMemOh.t)
                              | _ => upcast tt
                              end
                            | _ => upcast tt
                            end
                       ) 0%nat (smos0.(anys)))
        _
        _
    .
    Next Obligation.
      erewrite <- (smos0.(LEN)). rewrite mapi_aux_length. ss.
    Qed.
    Next Obligation.
      rewrite Midx.nth_error_mapi_aux_iff in *. des.
      ss. des_ifs_safe.
      destruct (Nat.eq_dec n n0).
      { clarify.
        unfold upcast in *. simpl_depind.
        des_ifs. unfold eq_rect_r. erewrite <- eq_rect_eq; eauto.
      }
      destruct (downcast a) eqn:T.
      - unfold upcast in *. simpl_depind.
        des_ifs. unfold eq_rect_r. erewrite <- eq_rect_eq; eauto.
        esplits; eauto. rewrite SimMemOh.getset_sm; ss.
      - exfalso. exploit smos0.(WTY); eauto. i; des. clarify.
    Qed.

  End SETSMO.

  Record sm_match (midx: Midx.t) {SMO: SimMemOh.class}
         (smo: SimMemOh.t) (smos: SimMemOhs.t): Prop :=
    (* TODO: I want to remove @ *)
    { smeq: (smos.(SimMemOhs.sm) = smo.(SimMemOh.sm));
      smnth: nth_error smos.(anys) midx = Some (upcast smo);
      ohsrc: (smos.(SimMemOhs.ohs_src) midx) = smo.(SimMemOh.oh_src);
      ohtgt: (smos.(SimMemOhs.ohs_tgt) midx) = smo.(SimMemOh.oh_tgt);
      wfwf: wf_weak midx smos;
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
      (<<RESPECTS: forall n msp (NTH: nth_error msps n = Some msp),
          (<<RESPECTS: respects msp.(ModSemPair.SMO) SimMemOhs_intro>>)>>)
  .
  Proof.
    (* exists SimMemOhs_intro. *)
    ii.
    exploit MIDXWF2; et. intro Q. des.
    (* econstructor 1 with (sm_match_strong := @sm_match n); ss; eauto. *)
    econstructor 1 with (sm_match_strong := @sm_match (SimMemOh.midx) _)
                        (is_set_smo := fun smos0 mi smo1 smos1 =>
                                         exists NTH, smos1 = set_smo smos0 n NTH smo1); ss; eauto.
    - ii. inv PR. econs; ec. ii. eapply wf_weak_wf; ec. rewrite upcast_downcast; ss.
    - ii. exploit (WTY2 smos); et. i; des. exists smo0. esplits; eauto.
      + econs; ss; eauto.
        * inv MWF; ss. exploit WTY; et. i; des; ss. clarify. rp; eauto. f_equal.
          sym. eapply upcast_downcast_iff; ss.
        * unfold ohs_src. des_ifs.
        * unfold ohs_tgt. des_ifs.
        * ii. eapply wf_wf_weak; try rewrite Q in *; eauto.
      + inv MWF. eapply WFSMO; et; ss.
    - ii.
      hexploit smos0.(LEN); eauto. intro LEN.
      eexists (set_smo smos0 n NTH smo1).
      esplits; eauto.
      + econs; ss; eauto.
        * replace sm with (SimMemOhs.sm) by ss.
          erewrite SMMATCH.(smeq); eauto.
          eapply SimMemOh.le_proj; eauto.
        * ii; ss.
          rewrite Midx.nth_error_mapi_aux_iff in *. des. ss. des_ifs_safe.
          des_ifs.
          { rewrite upcast_downcast in *. clarify.
            assert(smo0 = smo2).
            { hexploit SMMATCH.(smnth); ss. intro T. clarify. rewrite upcast_downcast in *. clarify. }
            clarify.
          }
          rewrite upcast_downcast in *. clarify.
          erewrite <- SimMemOh.setget_sm with smo2. erewrite SimMemOh.setset_sm.
          eapply SimMemOh.set_sm_le; try refl; eauto.
          replace sm with (SimMemOhs.sm) by ss.
          eapply SimMemOh.le_proj in LE. etrans; eauto.
          erewrite <- SMMATCH.(smeq); eauto.
          exploit smos0.(WTY); et. i; des. clarify. rewrite SMEQ. refl.
      + econs; ss; eauto.
        * ii.
          rewrite Midx.nth_error_mapi_aux_iff in *. ss. des_ifs_safe.
          exploit (WTY2 smos0); eauto. i; des. esplits; eauto.
        * unfold ohs_src; ss. des_ifs_safe.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. }
          { rewrite upcast_downcast in *. clarify. }
          { eapply nth_error_mapi_none_aux_iff in Heq0. r in Heq0.
            assert(nth_error msps (SimMemOh.midx (class := msp.(ModSemPair.SMO))) = None).
            { eapply nth_error_None; eauto. xomega. }
            clarify.
          }
        * unfold ohs_tgt; ss. des_ifs_safe.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. }
          { rewrite upcast_downcast in *. clarify. }
          { eapply nth_error_mapi_none_aux_iff in Heq0. r in Heq0.
            assert(nth_error msps (SimMemOh.midx (class := msp.(ModSemPair.SMO))) = None).
            { eapply nth_error_None; eauto. xomega. }
            clarify.
          }
        * ii. hexploit (SMMATCH.(wfwf)); eauto. intro WF; ss.
          bar. econs. ii. ss.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          exploit smos0.(WTY); eauto. i; des. clarify.
          des_ifs.
          rewrite upcast_downcast in *. clarify. rewrite SimMemOh.setset_sm.
          eapply WF; eauto. erewrite SimMemOh.getset_sm in UNCH0; et.
          rewrite SMEQ.
          inv UNCH.
          etrans; et.
          {
            erewrite <- smeq in UNCHSRC; et. eapply SimMem.unchanged_on_monotone; et.
            exploit MIDXWF; et. i; des. clarify.
            clear - EXCEPT.
            ii. unfold privmods in *. unfold privmod_others in *.
            des_ifs_safe. des_sumbool. clarify. ss. rewrite Heq. simpl_bool. des_sumbool. ii; clarify.
            xomega.
          }
          { eapply SimMem.unchanged_on_monotone; et. intros b ofs.
            hexploit LESRC; et. intro T. specialize (T b ofs); ss.
            erewrite smeq; et.
          }
      + ii.
        do 2 (unfold ohs_src, ohs_tgt; ss).
        des_ifs_safe. exploit (WTY2 smos0); eauto. i; des. des_ifs_safe.
        split.
        * des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. rewrite SimMemOh.set_sm_oh_src. ss. }
          { rewrite upcast_downcast in *. clarify. }
          { apply nth_error_mapi_none_aux_iff in Heq2. des.
            assert(NTH0: nth_error (anys smos0) mj <> None).
            { destruct (nth_error (anys smos0) mj); ss. }
            eapply nth_error_Some in NTH0; eauto. xomega.
          }
        * des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. rewrite SimMemOh.set_sm_oh_tgt. ss. }
          { rewrite upcast_downcast in *. clarify. }
          { apply nth_error_mapi_none_aux_iff in Heq2. des.
            assert(NTH0: nth_error (anys smos0) mj <> None).
            { destruct (nth_error (anys smos0) mj); ss. }
            eapply nth_error_Some in NTH0; eauto. xomega.
          }
    - ii.
      hexploit smos0.(LEN); eauto. intro LEN.
      eexists (set_smo smos0 n NTH smo1).
      esplits; eauto.
      + econs; ss; eauto.
        * replace sm with (SimMemOhs.sm) by ss.
          erewrite SMMATCH.(smeq); eauto.
          eapply SimMemOh.lepriv_proj; eauto.
        * ii; ss.
          rewrite Midx.nth_error_mapi_aux_iff in *. des. ss. des_ifs_safe.
          des_ifs.
          { rewrite upcast_downcast in *. clarify.
            assert(smo0 = smo2).
            { hexploit SMMATCH.(smnth); ss. intro T. clarify. rewrite upcast_downcast in *. clarify. }
            clarify.
          }
          rewrite upcast_downcast in *. clarify.
          erewrite <- SimMemOh.setget_sm with smo2. erewrite SimMemOh.setset_sm.
          eapply SimMemOh.set_sm_lepriv; try refl; eauto.
          replace sm with (SimMemOhs.sm) by ss.
          eapply SimMemOh.lepriv_proj in LE. etrans; eauto.
          erewrite <- SMMATCH.(smeq); eauto.
          exploit smos0.(WTY); et. i; des. clarify. rewrite SMEQ. refl.
      + econs; ss; eauto.
        * ii.
          rewrite Midx.nth_error_mapi_aux_iff in *. ss. des_ifs_safe.
          exploit (WTY2 smos0); eauto. i; des. esplits; eauto.
        * unfold ohs_src; ss. des_ifs_safe.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. }
          { rewrite upcast_downcast in *. clarify. }
          { eapply nth_error_mapi_none_aux_iff in Heq0. r in Heq0.
            assert(nth_error msps (SimMemOh.midx (class := msp.(ModSemPair.SMO))) = None).
            { eapply nth_error_None; eauto. xomega. }
            clarify.
          }
        * unfold ohs_tgt; ss. des_ifs_safe.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. }
          { rewrite upcast_downcast in *. clarify. }
          { eapply nth_error_mapi_none_aux_iff in Heq0. r in Heq0.
            assert(nth_error msps (SimMemOh.midx (class := msp.(ModSemPair.SMO))) = None).
            { eapply nth_error_None; eauto. xomega. }
            clarify.
          }
        * ii. hexploit (SMMATCH.(wfwf)); eauto. intro WF; ss.
          bar. econs. ii. ss.
          des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          exploit smos0.(WTY); eauto. i; des. clarify.
          des_ifs.
          rewrite upcast_downcast in *. clarify. rewrite SimMemOh.setset_sm.
          eapply WF; eauto. erewrite SimMemOh.getset_sm in UNCH0; et.
          rewrite SMEQ.
          inv UNCH.
          etrans; et.
          {
            erewrite <- smeq in UNCHSRC; et. eapply SimMem.unchanged_on_monotone; et.
            exploit MIDXWF; et. i; des. clarify.
            clear - EXCEPT.
            ii. unfold privmods in *. unfold privmod_others in *.
            des_ifs_safe. des_sumbool. clarify. ss. rewrite Heq. simpl_bool. des_sumbool. ii; clarify.
            xomega.
          }
          { eapply SimMem.unchanged_on_monotone; et. intros b ofs.
            hexploit LESRC; et. intro T. specialize (T b ofs); ss.
            erewrite smeq; et.
          }
      + ii.
        do 2 (unfold ohs_src, ohs_tgt; ss).
        des_ifs_safe. exploit (WTY2 smos0); eauto. i; des. des_ifs_safe.
        split.
        * des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. rewrite SimMemOh.set_sm_oh_src. ss. }
          { rewrite upcast_downcast in *. clarify. }
          { apply nth_error_mapi_none_aux_iff in Heq2. des.
            assert(NTH0: nth_error (anys smos0) mj <> None).
            { destruct (nth_error (anys smos0) mj); ss. }
            eapply nth_error_Some in NTH0; eauto. xomega.
          }
        * des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
          { rewrite upcast_downcast in *. clarify. rewrite SimMemOh.set_sm_oh_tgt. ss. }
          { rewrite upcast_downcast in *. clarify. }
          { apply nth_error_mapi_none_aux_iff in Heq2. des.
            assert(NTH0: nth_error (anys smos0) mj <> None).
            { destruct (nth_error (anys smos0) mj); ss. }
            eapply nth_error_Some in NTH0; eauto. xomega.
          }
    - ii; ss. inv SMMATCH0. inv SMMATCH1. ss. des_ifs_safe.
      exploit (WTY2 smos0); eauto. i; des.
      exploit (WTY2 smos1); eauto. i; des.
      des_ifs. inv SMLE.
      eapply LESMO; eauto.
      { rewrite upcast_downcast. ss. }
      { rewrite upcast_downcast. ss. }
    - ii.
      des. clarify.
      (* set msp.(ModSemPair.src).(midx) as n in *. *)
      set (set_smo smos0 (SimMemOh.midx (class := msp.(ModSemPair.SMO))) NTH1 smo1) as smos1 in *.
      set (set_smo smos2 (SimMemOh.midx (class := msp.(ModSemPair.SMO))) NTH0 smo3) as smos3 in *.
      clarify. clear_tac.
      econs; eauto.
      { ss. erewrite smeq; et. eapply SimMemOh.le_proj; et. }
      ii.
      destruct (classic (n = (SimMemOh.midx (class := msp.(ModSemPair.SMO))))).
      { clarify. erewrite smnth in *; et. clarify. rewrite upcast_downcast in *. clarify. }
      ss.
      des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto.
      des_ifs; cycle 1.
      { exploit (WTY2 smos2); eauto. i; des. clarify. }
      rewrite upcast_downcast in *. clarify.
      rename smo4 into smo_other0.
      rename t0 into smo_other2.

      (* bar. *)
      (* exploit (WTY2 smos3); et. i; des. *)
      (* rename smo4 into smo_other3. *)
      (* ss. *)
      (* des_ifs; try rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto. clear_tac. *)
      (* rewrite upcast_downcast in *. clarify. *)



      assert(T: SimMemOh.le (SimMemOh.set_sm smo_other0 smo1) smo_other2).
      { inv MLEPUBOHS.
        exploit (WTY2 smos1 n); et. i; des. clarify.
        exploit (LESMO n a1 a); et. intro T. ss. clear LESMO.
        rewrite Midx.nth_error_mapi_aux_iff in *; des; ss; des_ifs_safe; eauto. clear_tac.
        rewrite upcast_downcast in *. clarify.
      }
      eapply SimMemOh.set_sm_le in T.
      + rewrite SimMemOh.setset_sm in T.
        erewrite <- SimMemOh.setget_sm with smo_other0. eauto.
      + eapply SimMemOh.le_proj in MLEPUB. rp; et.
        exploit (WTY2 smos0 n); et. i; des. clarify.
        rewrite SMEQ. erewrite smeq; et.
  Qed.

End SimMemOhUnify.

Section SimMemOhUnify.

  Context `{SM: SimMem.class} {SU: Sound.class} {SS: SimSymb.class SM}.

  Definition initial_ohs_src (msps: list ModSemPair.t): Sem.Ohs :=
    (* let ohs_src := map (fun msp => upcast (msp.(ModSemPair.src).(ModSem.initial_owned_heap))) msps in *)
    (* fun midx => *)
    (*   match nth_error ohs_src midx with *)
    (*   | Some oh_src => oh_src *)
    (*   | None => upcast tt *)
    (*   end *)
    fun midx =>
      match nth_error (map ModSemPair.src msps) midx with
      | Some ms => upcast ms.(ModSem.initial_owned_heap)
      | None => upcast tt
      end
  .

  Let initial_ohs_tgt (msps: list ModSemPair.t): Sem.Ohs :=
    (* let ohs_tgt := map (fun msp => upcast (msp.(ModSemPair.tgt).(ModSem.initial_owned_heap))) msps in *)
    (* fun midx => *)
    (*   match nth_error ohs_tgt midx with *)
    (*   | Some oh_tgt => oh_tgt *)
    (*   | None => upcast tt *)
    (*   end *)
    fun midx =>
      match nth_error (map ModSemPair.tgt msps) midx with
      | Some ms => upcast ms.(ModSem.initial_owned_heap)
      | None => upcast tt
      end
  .

  Local Opaque upcast.
  (** TODO: make it global opaque **)

  Theorem unification_smo
          msps
          (SIM: Forall ModSemPair.sim msps)
          (MIDXWF: forall n msp (NTH: nth_error msps n = Some msp),
              <<MIDX: msp.(ModSemPair.src).(ModSem.midx) = n>>)
    :
      exists SMOS,
        (<<RESPECTS: forall n msp (NTH: nth_error msps n = Some msp),
            (<<RESPECTS: respects msp.(ModSemPair.SMO) SMOS>>)>>)
        /\
        (<<INITOH: forall
            sm
            (WF: SimMem.wf sm)
          ,
            exists (smos: SimMemOhs.t (class := (SMOS))),
              (<<WF: SimMemOhs.wf smos>>) /\
              (<<SMEQ: smos.(SimMemOhs.sm) = sm>>) /\
              (<<OHSRC: smos.(SimMemOhs.ohs_src) = initial_ohs_src msps>>) /\
              (<<OHTGT: smos.(SimMemOhs.ohs_tgt) = initial_ohs_tgt msps>>)>>)
  .
  Proof.
    exists (SimMemOhs_intro msps). ss.
    split.
    { eapply respects_intro; eauto. }
    clear MIDXWF.
    ginduction msps; ii; ss.
    { unshelve eexists (@mk _ _ [] sm0 [] _ _); ss.
      { ii. destruct n; ss. }
      esplits; ss; eauto.
      - econs; ss. ii. destruct n; ss.
      - unfold ohs_src. apply func_ext1. intro n. ss. destruct n; ss.
      - unfold ohs_tgt. apply func_ext1. intro n. ss. destruct n; ss.
    }
    inv SIM. rename H1 into HD. rename H2 into TL.
    exploit IHmsps; eauto. i; des.
    des_ifs.
    bar. inv HD. move INITOH at top. clear_until_bar. exploit INITOH; eauto. i; des.
    unshelve eexists (@mk _ _ _ smos.(sm) (upcast smo :: smos.(anys)) _ _).
    { ss. erewrite LEN; eauto. }
    { ii. destruct n; ss.
      - clarify. esplits; eauto. rewrite upcast_downcast. refl.
      - eapply smos.(WTY); et.
    }
    unfold ohs_src. unfold ohs_tgt. ss.
    esplits; eauto.
    - econs; ss; eauto.
      ii. destruct n; ss.
      + clarify. rewrite upcast_downcast in *. clarify.
      + eapply WF0; eauto.
    - apply func_ext1. ii.
      destruct x0; ss.
      { rewrite upcast_downcast. ss. }
      clear - OHSRC.
      unfold initial_ohs_src in *. ss.
      unfold ohs_src in *.
      assert(TMP: forall {A B} x (f: A -> B) g, f = g -> f x = g x).
      { ii; clarify. }
      eapply (TMP _ _ x0) in OHSRC.
      erewrite <- OHSRC.
      des_ifs.
    - apply func_ext1. ii.
      destruct x0; ss.
      { rewrite upcast_downcast. ss. }
      clear - OHTGT.
      unfold initial_ohs_tgt in *. ss.
      unfold ohs_tgt in *.
      assert(TMP: forall {A B} x (f: A -> B) g, f = g -> f x = g x).
      { ii; clarify. }
      eapply (TMP _ _ x0) in OHTGT.
      erewrite <- OHTGT.
      des_ifs.
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
