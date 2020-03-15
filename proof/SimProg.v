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
  Definition simU {SMOS: SimMemOhs.class} (pp: t) := simU_aux pp 0%nat.

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












Variable respects2: forall
    {SM: SimMem.class},
    SimMemOhs.class -> SimMemOhs.class -> Prop
.
Hypothesis respects2_theorem: forall
    {SM: SimMem.class} {SS: SimSymb.class _} {SU: Sound.class} SMOS0 SMOS1
    (RESPECT: respects2 SMOS0 SMOS1)
  ,
    forall msp, (ModSemPair.simU (SMOS := SMOS0) msp) ->
                (ModSemPair.simU (SMOS := SMOS1) msp)
.
           

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
  (* rewrite Forall_forall in *. *)
  ginduction pp; ii; ss.
  { unshelve esplits; eauto.
    - admit "Make default instance for SimMemOhs. nil theroem".
    - econs; eauto.
  }
  inv SIM.
  exploit IHpp; eauto. i; des.
  assert(exists SMOS',
            (<<SIM: ProgPair.simU (SMOS := SMOS') pp>>) /\
            (<<SIM: ModPair.simU (SMOS := SMOS') a 0%nat>>)
        ).
  { admit "cons theorem". }
  clear - H.
  des.
  exists SMOS'. rr. rewrite Forall_forall. intros [i x] IN.
  rewrite Midx.in_mapi_aux_iff in IN. des. clarify. destruct i; ss; clarify.
  rr in SIM. rewrite Forall_forall in SIM.
  exploit SIM; eauto.
  { eapply Midx.in_mapi_aux_iff. esplits; eauto. }
  i; des. des_ifs.
  econs; eauto.
  -
  econs; eauto.
Qed.
SimModSemUnified.fundamental_theorem
