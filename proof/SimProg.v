Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import SimSymb.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem.
Require Import SimMem SimModSemUnified SimMod.
Require Import Sound SemProps.

Set Implicit Arguments.





Module ProgPair.
Section PROGPAIR.
Context `{SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Definition t := list ModPair.t.

  Definition sim (pp: t) := List.Forall ModPair.sim pp.
  Definition simU_aux {SMOS: SimMemOhs.class} (pp: t) (begin: Midx.t) :=
    let ppi := Midx.mapi_aux (fun i x => (i, x)) begin pp in
    List.Forall (fun '(i, x) => ModPair.simU x i) ppi.
  Definition simU {SMOS: SimMemOhs.class} (pp: t) := simU_aux pp 1%nat.

  Definition src (pp: t): program := List.map ModPair.src pp.
  Definition tgt (pp: t): program := List.map ModPair.tgt pp.

  (* Definition ss_link (pp: t): option SimSymb.t := link_list (List.map ModPair.ss pp). *)
  (* ############ TODO: *)
  (* ModPair.wf mp0 /\ ModPair.wf mp1 /\ link mp0.(src) mp1.(src) = Some /\ link mp1.(tgt) mp1.(tgt) = Some *)
  (* =================> link mp0.(ss) mp1.(ss) suceeds. *)
  (* Move ModPair.wf into SimSymb and obligate its proof? *)

End PROGPAIR.
End ProgPair.

Hint Unfold ProgPair.sim ProgPair.src ProgPair.tgt.
(* Hint Unfold ProgPair.ss_link. *)






Section SIM.
Context `{SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).



  Theorem sim_link_sk
          sk_link_src
          (LOADSRC: (link_sk p_src) = Some sk_link_src)
          (WF: forall md, In md p_src -> <<WF: Sk.wf md>>):
      exists ss_link sk_link_tgt,
        <<LOADTGT: (link_sk p_tgt) = Some sk_link_tgt>>
        /\ <<SIMSK: SimSymb.wf ss_link>>
        /\ <<SKSRC: ss_link.(SimSymb.src) = sk_link_src>>
        /\ <<SKTGT: ss_link.(SimSymb.tgt) = sk_link_tgt>>
        /\ <<LE: Forall (fun mp => (SimSymb.le mp.(ModPair.ss) ss_link)) pp>>.
  Proof.
    u. subst_locals. ginduction pp; ii; ss. destruct a; ss.
    unfold ProgPair.src in *. unfold link_sk in *. ss. destruct (classic (t = [])).
    { clarify; ss. cbn in *. clarify. clear IHt. inv SIMPROG. inv H2. inv H1. ss.
      esplits; eauto. econs; eauto. ss. refl.
    }
    rename H into NNIL. eapply link_list_cons_inv in LOADSRC; cycle 1.
    { destruct t; ss. }
    des. rename sk_link_src into sk_link_link_src. rename restl into sk_link_src.
    inv SIMPROG. exploit IHt; eauto. intro IH; des.
    inv H1. ss. exploit (SimSymb.wf_link).
    3: { rewrite SKSRC. eapply HD. }
    all: eauto.
    { rewrite SKSRC. eapply WF; et. }
    { eapply link_list_preserves_wf_sk; eauto. }
    { eapply SimSymb.wf_preserves_wf; et. rewrite SKSRC. eapply WF; et. }
    { eapply SimSymb.wf_preserves_wf; et. eapply link_list_preserves_wf_sk; eauto. }
    i; des. esplits; eauto.
    - eapply link_list_cons; eauto.
      rewrite SKTGT in LINKTGT. ss.
    - econs; eauto. rewrite Forall_forall in *. ii.
      all ltac:(fun H => apply link_list_linkorder in H). des.
      rewrite Forall_forall in *. etrans; eauto.
  Qed.

End SIM.

Module WEMANYNOTNEETHIS.
Section SIM.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG:
    Forall (fun mp =>
              (<<SIMSK: SimSymb.wf mp.(ModPair.ss)>>) /\
              (<<SKSRC: mp.(ModPair.ss).(SimSymb.src) = (Mod.sk mp.(ModPair.src))>>) /\
              (<<SKTGT: mp.(ModPair.ss).(SimSymb.tgt) = (Mod.sk mp.(ModPair.tgt))>>)) pp
  .
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).


  Theorem sim_link_sk_aux_aux
          sk_link_src
          (LOADSRC: (link_sk p_src) = Some sk_link_src)
          (WF: forall md, In md p_src -> <<WF: Sk.wf md>>):
      exists ss_link sk_link_tgt,
        <<LOADTGT: (link_sk p_tgt) = Some sk_link_tgt>>
        /\ <<SIMSK: SimSymb.wf ss_link>>
        /\ <<SKSRC: ss_link.(SimSymb.src) = sk_link_src>>
        /\ <<SKTGT: ss_link.(SimSymb.tgt) = sk_link_tgt>>
        /\ <<LE: Forall (fun mp => (SimSymb.le mp.(ModPair.ss) ss_link)) pp>>.
  Proof.
    u. subst_locals. ginduction pp; ii; ss. destruct a; ss.
    unfold ProgPair.src in *. unfold link_sk in *. ss. destruct (classic (t = [])).
    { clarify; ss. cbn in *. clarify. clear IHt. inv SIMPROG. ss. inv H2. des.
      esplits; eauto. econs; eauto. ss. refl.
    }
    rename H into NNIL. eapply link_list_cons_inv in LOADSRC; cycle 1.
    { destruct t; ss. }
    des. rename sk_link_src into sk_link_link_src. rename restl into sk_link_src.
    inv SIMPROG. exploit IHt; eauto. intro IH; des.
    clarify. ss. exploit (SimSymb.wf_link).
    3: { rewrite SKSRC. eapply HD. }
    all: eauto.
    { rewrite SKSRC. eapply WF; et. }
    { eapply link_list_preserves_wf_sk; eauto. }
    { eapply SimSymb.wf_preserves_wf; et. rewrite SKSRC. eapply WF; et. }
    { eapply SimSymb.wf_preserves_wf; et. eapply link_list_preserves_wf_sk; eauto. }
    i; des. esplits; eauto.
    - eapply link_list_cons; eauto.
      rewrite SKTGT in LINKTGT. ss.
    - econs; eauto. rewrite Forall_forall in *. ii.
      all ltac:(fun H => apply link_list_linkorder in H). des.
      rewrite Forall_forall in *. etrans; eauto.
  Qed.

End SIM.


Section SIM.
Context `{SM: SimMem.class} {SMOS: SimMemOhs.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Variable pp: ProgPair.t.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).

  Theorem sim_link_sk_aux
          j
          (SIMPROG: ProgPair.simU_aux pp j)
          sk_link_src
          (LOADSRC: (link_sk p_src) = Some sk_link_src)
          (WF: forall md, In md p_src -> <<WF: Sk.wf md>>):
      exists ss_link sk_link_tgt,
        <<LOADTGT: (link_sk p_tgt) = Some sk_link_tgt>>
        /\ <<SIMSK: SimSymb.wf ss_link>>
        /\ <<SKSRC: ss_link.(SimSymb.src) = sk_link_src>>
        /\ <<SKTGT: ss_link.(SimSymb.tgt) = sk_link_tgt>>
        /\ <<LE: Forall (fun mp => (SimSymb.le mp.(ModPair.ss) ss_link)) pp>>.
  Proof.
    eapply sim_link_sk_aux_aux; eauto. rr in SIMPROG. clear - SIMPROG.
    ginduction pp; ii; ss.
    inv SIMPROG. econs; eauto.
    { inv H1. ss. }
  Qed.

  Theorem sim_link_sk
          (SIMPROG: ProgPair.simU pp)
          sk_link_src
          (LOADSRC: (link_sk p_src) = Some sk_link_src)
          (WF: forall md, In md p_src -> <<WF: Sk.wf md>>):
      exists ss_link sk_link_tgt,
        <<LOADTGT: (link_sk p_tgt) = Some sk_link_tgt>>
        /\ <<SIMSK: SimSymb.wf ss_link>>
        /\ <<SKSRC: ss_link.(SimSymb.src) = sk_link_src>>
        /\ <<SKTGT: ss_link.(SimSymb.tgt) = sk_link_tgt>>
        /\ <<LE: Forall (fun mp => (SimSymb.le mp.(ModPair.ss) ss_link)) pp>>.
  Proof.
    eapply sim_link_sk_aux; eauto.
  Qed.

End SIM.
End WEMANYNOTNEETHIS.









Theorem unification
        {SM: SimMem.class}
        {SU: Sound.class}
        {SS: SimSymb.class _}
        pp
        (SIM: ProgPair.sim pp)
  :
    exists SMOS, (<<SIM: ProgPair.simU pp (SMOS := SMOS)>>).
Proof.
  rr in SIM.
  rewrite Forall_forall in *.
  assert(RESPECTS: exists SMOS, forall n mp (NTH: nth_error pp n = Some mp),
              (<<RESPECTS: respects mp.(ModPair.SMO) (S n) SMOS>>)).
  { admit "somehow". }

  des.
  esplits; eauto.
  rr.
  rewrite Forall_forall. intros [j mp] ?.
  rewrite Midx.in_mapi_aux_iff in *. des. clarify.
  hexploit (RESPECTS idx); eauto. clear RESPECTS. intro RESPECTS; des. clarify.
  exploit nth_error_In; eauto. intro IN.
  exploit SIM; eauto. clear SIM. intro SIM.

  {
    clear - RESPECTS SIM.
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    (*********************************** TODO: Separate Lemma ***************************************)
    inv SIM.
    econs; eauto.
    ii. exploit SIMMS; eauto. intro SIM; des.
    (* Set Printing All. *)
    instantiate (1:= (S idx)) in SIM.
    remember (ModPair.to_msp (S idx) skenv_link_src skenv_link_tgt sm_init_link mp) as msp.
    assert(MIDX: S idx = (ModSem.midx (ModSemPair.src msp))).
    { clarify. ss. unfold Mod.modsem. erewrite Mod.get_modsem_midx_spec. ss. }
    rewrite MIDX in RESPECTS.
    assert(MIDX2: ModSem.midx (ModSemPair.src msp) = ModSem.midx (ModSemPair.tgt msp)).
    { clarify. ss. unfold Mod.modsem. erewrite ! Mod.get_modsem_midx_spec. ss. }
    hexploit (@fundamental_theorem SM SS SU _ SMOS _ MIDX2 RESPECTS); ss.
  }

  (* (* rewrite Forall_forall in *. *) *)
  (* ginduction pp; ii; ss. *)
  (* { unshelve esplits; eauto. *)
  (*   - admit "Make default instance for SimMemOhs. nil theroem". *)
  (*   - econs; eauto. *)
  (* } *)
  (* inv SIM. *)
  (* exploit IHpp; eauto. i; des. *)
  (* assert(exists SMOS', *)
  (*           (<<SIM: ProgPair.simU (SMOS := SMOS') pp>>) /\ *)
  (*           (<<SIM: ModPair.simU (SMOS := SMOS') a 0%nat>>) *)
  (*       ). *)
  (* { admit "cons theorem". } *)
  (* clear - H. *)
  (* admit "". *)
  (* des. *)
  (* exists SMOS'. rr. rewrite Forall_forall. intros [i x] IN. *)
  (* rewrite Midx.in_mapi_aux_iff in IN. des. clarify. destruct idx; ss; clarify. *)
  (* rr in SIM. rewrite Forall_forall in SIM. *)
  (* exploit SIM; eauto. *)
  (* { eapply Midx.in_mapi_aux_iff. esplits; eauto. } *)
  (* i; des. des_ifs. *)
  (* admit "TODO----------------------------------". *)
Qed.
(* SimModSemUnified.fundamental_theorem *)


Theorem unification_modsem
        {SM: SimMem.class}
        {SU: Sound.class}
        {SS: SimSymb.class _}
        pp
        (SIM: ProgPair.sim pp)

        p_src p_tgt sm sk_src sk_tgt ge_src ge_tgt ohs_src ohs_tgt
        (PSRC: p_src = ProgPair.src pp)
        (PTGT: p_tgt = ProgPair.tgt pp)
        (SKSRC: link_sk p_src = Some sk_src)
        (SKTGT: link_sk p_tgt = Some sk_tgt)
        (GESRC: load_genv p_src (Sk.load_skenv sk_src) = ge_src)
        (GETGT: load_genv p_tgt (Sk.load_skenv sk_tgt) = ge_tgt)
        (OHSSRC: load_owned_heaps ge_src = ohs_src)
        (OHSTGT: load_owned_heaps ge_tgt = ohs_tgt)
  :
    exists SMOS, (<<SIM: ProgPair.simU pp (SMOS := SMOS)>>) /\
                 (<<INITOH: forall
                     (WF: SimMem.wf sm)
                   ,
                     exists (smos: SimMemOhs.t (class := (SMOS))),
                       (<<WF: SimMemOhs.wf smos>>) /\
                       (<<SMEQ: smos.(SimMemOhs.sm) = sm>>) /\
                       (<<OHSRC: smos.(SimMemOhs.ohs_src) = ohs_src>>) /\
                       (<<OHTGT: smos.(SimMemOhs.ohs_tgt) = ohs_tgt>>)>>)
.
Proof.
  rr in SIM.
  rewrite Forall_forall in *.
  assert(RESPECTS: exists SMOS, forall n mp (NTH: nth_error pp n = Some mp),
              (<<RESPECTS: respects mp.(ModPair.SMO) (S n) SMOS>>)).
  { admit "somehow". }

  des.
  esplits; eauto.
  -
    rr.
    rewrite Forall_forall. intros [j mp] ?.
    rewrite Midx.in_mapi_aux_iff in *. des. clarify.
    hexploit (RESPECTS idx); eauto. clear RESPECTS. intro RESPECTS; des. clarify.
    exploit nth_error_In; eauto. intro IN.
    exploit SIM; eauto. clear SIM. intro SIM.

    {
      clear - RESPECTS SIM.
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      (*********************************** TODO: Separate Lemma ***************************************)
      inv SIM.
      econs; eauto.
      ii. exploit SIMMS; eauto. intro SIM; des.
      (* Set Printing All. *)
      instantiate (1:= (S idx)) in SIM.
      remember (ModPair.to_msp (S idx) skenv_link_src skenv_link_tgt sm_init_link mp) as msp.
      assert(MIDX: S idx = (ModSem.midx (ModSemPair.src msp))).
      { clarify. ss. unfold Mod.modsem. erewrite Mod.get_modsem_midx_spec. ss. }
      rewrite MIDX in RESPECTS.
      assert(MIDX2: ModSem.midx (ModSemPair.src msp) = ModSem.midx (ModSemPair.tgt msp)).
      { clarify. ss. unfold Mod.modsem. erewrite ! Mod.get_modsem_midx_spec. ss. }
      hexploit (@fundamental_theorem SM SS SU _ SMOS _ MIDX2 RESPECTS); ss.
    }

    (* (* rewrite Forall_forall in *. *) *)
    (* ginduction pp; ii; ss. *)
    (* { unshelve esplits; eauto. *)
    (*   - admit "Make default instance for SimMemOhs. nil theroem". *)
    (*   - econs; eauto. *)
    (* } *)
    (* inv SIM. *)
    (* exploit IHpp; eauto. i; des. *)
    (* assert(exists SMOS', *)
    (*           (<<SIM: ProgPair.simU (SMOS := SMOS') pp>>) /\ *)
    (*           (<<SIM: ModPair.simU (SMOS := SMOS') a 0%nat>>) *)
    (*       ). *)
    (* { admit "cons theorem". } *)
    (* clear - H. *)
    (* admit "". *)
    (* des. *)
    (* exists SMOS'. rr. rewrite Forall_forall. intros [i x] IN. *)
    (* rewrite Midx.in_mapi_aux_iff in IN. des. clarify. destruct idx; ss; clarify. *)
    (* rr in SIM. rewrite Forall_forall in SIM. *)
    (* exploit SIM; eauto. *)
    (* { eapply Midx.in_mapi_aux_iff. esplits; eauto. } *)
    (* i; des. des_ifs. *)
    (* admit "TODO----------------------------------". *)
  - admit "".
Qed.
