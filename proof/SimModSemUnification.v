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
Require Import SimModSem.

Set Implicit Arguments.




Section SimMemOhsIntro.

  Context `{SM: SimMem.class} {SS: SimSymb.class SM}.
  Variable msps: list ModSemPair.t.

  Ltac des_let :=
    match goal with
    | [ H: context[let y := ?x in _ ] |- _ ] =>
      let name := fresh "let" in destruct x eqn:name
    end.

  Inductive SimMemOhs_t_aux: Midx.t -> Type :=
  | TyNil: SimMemOhs_t_aux 0%nat
  | TyCons
      n msp
      (MSP: List.nth_error msps n = Some msp)
      (hd: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)))
      (tl: SimMemOhs_t_aux n)
    :
      SimMemOhs_t_aux (S n)
  .

  (* TODO: change to Let *)
  Definition SimMemOhs_t: Type := SimMem.t * SimMemOhs_t_aux (length msps).

  Inductive SimMemOhs_le_aux:
    forall (midx: Midx.t) (smos0 smos1: SimMemOhs_t_aux midx), Prop :=
  | LeNil smos0 smos1: @SimMemOhs_le_aux (0%nat) smos0 smos1
  | LeCons
      n msp
      (MSP: List.nth_error msps n = Some msp)
      (hd0 hd1: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)))
      (tl0 tl1: SimMemOhs_t_aux n)
    :
      @SimMemOhs_le_aux (S n) (@TyCons n msp MSP hd0 tl0)
                        (@TyCons n msp MSP hd0 tl0)
  .

  (* TODO: change to Let *)
  Definition SimMemOhs_le: SimMemOhs_t -> SimMemOhs_t -> Prop :=
    fun smos0 smos1 =>
      SimMem.le (fst smos0) (fst smos1) /\
      @SimMemOhs_le_aux (length msps) (snd smos0) (snd smos1).

  Program Instance PreOrder_SimMemOhs_le_aux: PreOrder SimMemOhs_le.
  Next Obligation.
    ii. rr. split; try refl. abstr (snd x) y.
    induction y; ii; ss.
    - econs.
    - econs; eauto.
  Qed.
  Next Obligation.
    unfold SimMemOhs_le.
    ii. des. split; try etrans; eauto. clear H H0.
    abstr (snd x) a. abstr (snd y) b. abstr (snd z) c.
    ginduction a; ii; ss.
    - inv H2. simpl_depind. clarify. econs.
    - inv H2. simpl_depind. clarify. inv H1. simpl_depind. clarify.
      replace MSP2 with MSP.
      { econs; eauto. }
      eapply Axioms.proof_irr.
  Qed.

  Inductive SimMemOhs_wf_aux (sm: SimMem.t):
    forall (midx: Midx.t) (smos: SimMemOhs_t_aux midx), Prop :=
  | WfNil smos: @SimMemOhs_wf_aux sm 0%nat smos
  | WfCons
      n msp
      (MSP: List.nth_error msps n = Some msp)
      (hd: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)))
      (tl: @SimMemOhs_t_aux n)
      (HDEQ: hd.(SimMemOh.sm) = sm)
      (HD: SimMemOh.wf hd)
      (TL: @SimMemOhs_wf_aux sm n tl)
    :
      @SimMemOhs_wf_aux sm (S n) (@TyCons n msp MSP hd tl)
  .

  (* TODO: change to Let *)
  Definition SimMemOhs_wf: SimMemOhs_t -> Prop :=
    fun smos => SimMem.wf (fst smos)
                /\ @SimMemOhs_wf_aux (fst smos) (length msps) (snd smos).

  (* Let SimMemOhs_t: Type := *)
  (*   SimMem.t * *)
  (*   (forall midx, *)
  (*       match List.nth_error msps midx with *)
  (*       | Some msp => (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)) *)
  (*       | None => SimMemOh.t *)
  (*       end *)
  (*   ). *)
           
  Fail Inductive SimMemOhs_ohs_src_aux:
    forall (midx: Midx.t) (smos: SimMemOhs_t_aux midx), list { oh: Type & oh } :=
  | OhsSrcNil smos: @SimMemOhs_ohs_src_aux 0%nat smos
  .

  Fixpoint SimMemOhs_ohs_src_aux2 (midx: Midx.t) (smos: SimMemOhs_t_aux midx):
    list { oh: Type & oh } :=
    match smos with
    | TyNil => nil
    | TyCons n msp MSP hd tl =>
      (* (@existT Type _ _ hd) *)
      (existT id _ hd.(SimMemOh.oh_src)) :: @SimMemOhs_ohs_src_aux2 n tl
    end
  .

  (* TODO: make it Let *)
  Definition SimMemOhs_ohs_src_aux: forall midx, SimMemOhs_t_aux midx -> Sem.Ohs :=
    fun midx smos_aux n =>
      match nth_error (rev (@SimMemOhs_ohs_src_aux2 midx smos_aux)) n with
      | Some oh_src => oh_src
      | _ => (existT id _ tt)
      end
  .

  (* TODO: make it Let *)
  Definition SimMemOhs_ohs_src: SimMemOhs_t -> Sem.Ohs :=
    fun smos => @SimMemOhs_ohs_src_aux (length msps) (snd smos)
  .
  (* Let SimMemOhs_ohs_src: SimMemOhs_t -> Sem.Ohs := *)
  (*   fun smos midx => *)
  (*     match nth_error (@SimMemOhs_ohs_src_aux (length msps) (snd smos)) midx with *)
  (*     | Some oh_src => oh_src *)
  (*     | _ => (existT id _ tt) *)
  (*     end *)
  (* . *)
  Obligation Tactic := idtac.

  Ltac dep_destruct E :=
    let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
    try match goal with
        | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
        end.

Program Instance SimMemOhs_intro: SimMemOhs.class :=
{|
  (* SimMemOhs.t := SimMem.t * list SimMemOh.t; *)
  SimMemOhs.t := SimMemOhs_t;
  SimMemOhs.sm := fst;
  SimMemOhs.le := SimMemOhs_le;
  (* SimMemOhs.le_PreOrder := _; *)
|}
.
Next Obligation.
  (* SimMemOhs.ohs_src *)
  uo.
  ii. destruct X. specialize (y H).
  cbv zeta in y.
  des_ifs.
  - eexists. eapply y.
  - eexists. eapply y.
Defined.
Next Obligation.
  (* SimMemOhs.ohs_tgt *)
  uo.
  ii. destruct X. specialize (y H).
  cbv zeta in y.
  des_ifs.
  - eexists. eapply y.
  - eexists. eapply y.
Defined.
Next Obligation.
  (* SimMemOhs.wf *)
  uo.
  ii. destruct X.
  eapply and.
  { eapply t0.(SimMem.wf). }
  refine (forall midx: nat, _: Prop).
  specialize (y midx).
  cbv zeta in y. des_ifs.
  - eapply and. { eapply (y.(SimMemOh.sm) = t0). } eapply y.(SimMemOh.wf).
  - eapply True.
    (* eapply and. { eapply (y.(SimMemOh.sm) = t0). } eapply y.(SimMemOh.wf). *)
Defined.
Next Obligation.
  (* SimMemOhs.lepriv *)
  uo.
  intros X Y.
  destruct X as [X0 X1], Y as [Y0 Y1].
  eapply and.
  { eapply (SimMem.le X0 Y0). }
  refine (forall midx: nat, _: Prop).
  specialize (X1 midx). specialize (Y1 midx).
  cbv zeta in *. des_ifs.
  - eapply (SimMemOh.le X1 Y1).
  - eapply True.
Defined.
Next Obligation.
  econs.
  - ii. r. des_ifs.
    split; ss; try refl.
    i. rename y into yyy.
    Fail subst yyy.
    Fail hrewrite yyy.
    Fail rewrite yyy.
    Fail unfold yyy.
    (* dup y. specialize (y0 midx0). *)
    Fail dep_destruct (nth_error msps midx0).
    (* dependent destruction (nth_error msps midx0). *)
    (* depdes (nth_error msps midx0). *)
    generalize (yyy midx0).
    destruct (nth_error msps midx0).
    TTTTTTTTTTTTTTTTTTTTTT above two  lines !!!! 
    unfold yyy.
    revert yyy.
    generalize (nth_error msps midx0).
    destruct (nth_error msps midx0).
    pattern (nth_error msps midx0) at 2. ss.
    remember (nth_error msps midx0) as tmp.
    pattern (nth_error msps midx0) at 2. ss.
    destruct (nth_error msps midx0).
    hpattern (nth_error msps midx0).
    hresolve (nth_error msps midx0).
    destruct (nth_error msps midx0).
    hpattern
    destruct (nth_error msps midx0) eqn:T.
Qed.
Next Obligation.
  (* SimMemOhs.lepriv *)
  intros ? ? ? X Y.
  destruct X as [X0 X1], Y as [Y0 Y1].
  eapply and.
  { eapply (SimMem.le X0 Y0). }
  refine (forall midx: nat, _: Prop).
  specialize (X1 midx). specialize (Y1 midx).
  cbv zeta in *. des_ifs.
  - eapply (SimMemOh.le X1 Y1).
  - eapply True.
Defined.

    ohs_src : t -> Sem.Ohs;
    ohs_tgt : t -> Sem.Ohs;
    wf : t -> Prop;
    le : t -> t -> Prop;
    lepriv : t -> t -> Prop;
    le_PreOrder : PreOrder le;
    pub_priv : forall smo0 smo1 : t, le smo0 smo1 -> lepriv smo0 smo1;
    wf_proj : wf <1= SimMem.wf <*> sm;
    le_proj : Morphisms.respectful le SimMem.le sm sm;
    lepriv_proj : Morphisms.respectful lepriv SimMem.lepriv sm sm }

Record sm_match_tmp_aux (msp: @ModSemPair.t SM SS)
  (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) m (smos: SimMemOhs_t_aux m): Prop :=
  (* TODO: I want to remove @ *)
  {
    ohsrcty_tmp: (projT1 ((@SimMemOhs_ohs_src_aux m smos) (msp.(ModSemPair.src).(midx)))) =
             msp.(ModSemPair.src).(owned_heap);
    ohsrc_tmp: (projT2 ((@SimMemOhs_ohs_src_aux m smos) (msp.(ModSemPair.src).(midx)))
                   ~= smo.(SimMemOh.oh_src));
  }.

Definition sm_match_tmp (msp: @ModSemPair.t SM SS)
  (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))) (smos: SimMemOhs_t): Prop :=
  @sm_match_tmp_aux msp smo (length msps) (snd smos) /\ fst smos = smo.

  (* Fixpoint get_nth (midx: Midx.t) (smos: SimMemOhs_t_aux midx) *)
  (*          (n: Midx.t) msp (MSP: List.nth_error msps n = Some msp): *)
  (*   (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)) := *)
  (*   match smos with *)
  (*   | TyNil => nil *)
  (*   | TyCons n msp MSP hd tl => *)
  (*     nil *)
  (*   end *)
  (* . *)

End SimMemOhsIntro.
Arguments sm_match_tmp {_ _}.
Arguments sm_match_tmp_aux {_ _}.
Arguments SimMemOhs_t {_ _}.
Arguments SimMemOhs_wf {_ _}.
Arguments SimMemOhs_wf_aux {_ _}.
Arguments SimMemOh.t {_}.
(* Arguments sm_match_tmp: clear implicits. *)

  (* Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM} *)
  (*             (msps: list ModSemPair.t) *)
  (*             len n (LT: (len > n)%nat) msp *)
  (*             (MSP: nth_error msps n = Some msp), *)
  (*     (<<SMPROJ: forall sm (smos: SimMemOhs_t_aux msps len) *)
  (*                       (MWF0: SimMem.wf sm) *)
  (*                       (MWF1: SimMemOhs_wf_aux msps sm len smos), *)
  (*         exists (smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO))), *)
  (*           sm = smo /\ *)
  (*           (projT1 ((SimMemOhs_ohs_src_aux smos) *)
  (*                      (msp.(ModSemPair.src).(midx)))) = *)
  (*            msp.(ModSemPair.src).(owned_heap) /\ *)
  (*           (projT2 ((SimMemOhs_ohs_src_aux smos) *)
  (*                      (msp.(ModSemPair.src).(midx))) *)
  (*                  ~= smo.(SimMemOh.oh_src)) /\ *)
  (*           (* sm_match_tmp msps msp smo (sm, smos) /\ *) *)
  (*           SimMemOh.wf smo>>). *)
  (* Proof. *)
  (*   (* intros ? ? ?. *) *)
  (*   (* ginduction len; ii; ss. *) *)
  (*   ii. gen n. *)
  (*   dependent induction smos; ii; ss. *)
  (*   { omega. } *)
  (*   destruct n0; ss. *)
  (*   { destruct msps; ss. clarify. *)
  (*     exists hd. *)
  (* hd : @SimMemOh.t SM (owned_heap (@ModSemPair.src SM SS msp0)) *)
  (*        (owned_heap (@ModSemPair.tgt SM SS msp0)) msp0 *)
  (*   smo : @SimMemOh.t SM (owned_heap (@ModSemPair.src SM SS msp)) *)
  (*           (owned_heap (@ModSemPair.tgt SM SS msp)) msp, *)
  (*   } *)
  (* Qed. *)

  Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n msp
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall (smos: SimMemOhs_t_aux msps (length msps)),
          exists smo: (@SimMemOh.t _ _ _ msp.(ModSemPair.SMO)), True>>).
  Proof.
    ii.
    assert((n < length msps)%nat).
    { eapply nth_error_Some; eauto. rewrite MSP; ss. }
    abstr (length msps) m. gen n.
    dependent induction smos; ii; ss.
    { omega. }
    destruct (classic (n0 = n)).
    { clarify. }
    eapply IHsmos; eauto.
    omega.
  Qed.

  Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n msp
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos),
          exists smo, sm_match_tmp msps msp smo smos /\ SimMemOh.wf smo>>).
  Proof.
    ii.
    destruct smos as [sm smos].
    assert((n < length msps)%nat).
    { eapply nth_error_Some; eauto. rewrite MSP; ss. }
    rr in MWF. des. ss.
    (* Set Printing Implicit. *)
    pattern (length msps) in smos.
    Fail remember (length msps).
    Fail generalize (length msps).
  Abort.

  Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n msp
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos),
          exists smo, sm_match_tmp_aux msps msp smo (length msps) (snd smos)
                      /\ SimMemOh.sm smo = fst smos
                      /\ SimMemOh.wf smo>>).
  Proof.
    ii.
    assert((n < length msps)%nat).
    { eapply nth_error_Some; eauto. rewrite MSP; ss. }
    destruct smos as [sm smos]; ss.
    gen smos.
    Fail generalize (length msps).
  Abort.

  Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n msp
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall (smos: SimMemOhs_t msps), exists smo, fst smos = smo>>).
  Proof.
    ii.
    gen n.
    destruct smos as [sm smos].
    dependent induction smos; ii; ss.
    { destruct msps; ss. clarify. destruct n; ss. }
    destruct msps; ss. clarify.
    dependent destruction smos0.
    simpl_depind. clarify. simpl_depind. clarify.
    idtac "IHsmos-is-not well-formed".
  Abort.

  Lemma ohs_src_aux2_length
        `{SM: SimMem.class} {SS: SimSymb.class SM}
        (msps: list ModSemPair.t)
        m (smos: SimMemOhs_t_aux msps m)
    :
      length (SimMemOhs_ohs_src_aux2 smos) = m
  .
  Proof.
    ginduction m; ii; ss.
    { dependent destruction smos. ss. }
    { dependent destruction smos. ss.
      f_equal. eapply IHm; eauto.
    }
  Qed.

  Lemma tmp_lemma_aux: forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n m msp
              (LT: (n < m)%nat)
              (MIDXFACT: forall o msp_o,
                  nth_error msps o = Some msp_o ->
                  msp_o.(ModSemPair.src).(midx) = o)
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall smos (MWF: SimMem.wf (fst smos) /\
                                   SimMemOhs_wf_aux msps (fst smos) m (snd smos)),
          exists smo, sm_match_tmp_aux msps msp smo m (snd smos)
                      /\ SimMemOh.sm smo = fst smos
                      /\ SimMemOh.wf smo>>).
  Proof.
    ii.
    destruct smos as [sm smos]; ss. des.
    gen n.
    dependent induction smos; ii; ss.
    { omega. }
    dependent destruction MWF0.
    assert(LEN: length (rev (SimMemOhs_ohs_src_aux2 smos)) = n).
    { rewrite rev_length. eapply ohs_src_aux2_length; eauto. }
    destruct (classic (n0 = n)).
    {
      clarify.
      exists hd. esplits; eauto.
      - econs; ss.
        + unfold SimMemOhs_ohs_src_aux. ss.
          exploit (MIDXFACT n); eauto. intro T. rewrite T.
          clear_tac.
          rewrite nth_error_app2; cycle 1.
          { omega. }
          rewrite LEN. replace (n - n)%nat with 0%nat by omega.
          ss.
        + unfold SimMemOhs_ohs_src_aux. ss.
          exploit (MIDXFACT n); eauto. intro T. rewrite T.
          clear_tac.
          rewrite nth_error_app2; cycle 1.
          { omega. }
          rewrite LEN. replace (n - n)%nat with 0%nat by omega.
          ss.
    }
    exploit IHsmos; eauto.
    { omega. }
    i; des.
    clarify.
    exploit (MIDXFACT n0); eauto. intro T.
    assert(LT2: (n0 < n)%nat) by omega.
    esplits; eauto.
    {
      clear - LT2 T H0 LEN.
      clear_tac.
      inv H0.
      econs; eauto.
      - unfold SimMemOhs_ohs_src_aux in *. ss.
        rewrite nth_error_app1; try omega. ss.
      - unfold SimMemOhs_ohs_src_aux in *. ss.
        rewrite nth_error_app1; try omega. ss.
    }
  Qed.

  Goal forall `{SM: SimMem.class} {SS: SimSymb.class SM}
              (msps: list ModSemPair.t)
              n msp
              (MSP: nth_error msps n = Some msp),
      (<<SMPROJ: forall smos (MWF: SimMemOhs_wf msps smos),
          exists smo, sm_match_tmp msps msp smo smos /\ SimMemOh.wf smo>>).
  Proof.
    ii. destruct smos as [sm smos]. rr in MWF. des.
    exploit (@tmp_lemma_aux _ _ msps n (length msps)); eauto.
    { eapply nth_error_Some; eauto. rewrite MSP; ss. }
    { admit "". }
    i; des. ss.
    esplits; eauto. rr. esplits; eauto.
  Qed.




Theorem fundamental_theorem_merge
        SM (SS: SimSymb.class SM)
        (msps: list ModSemPair.t)
  :
    exists SMOS: SimMemOhs.class, Forall (good_properties SMOS) msps
.
Proof.
  eexists (SimMemOhs.Build_class _ _ _ _ _ _ _ _ _ _ _ _).
Qed.