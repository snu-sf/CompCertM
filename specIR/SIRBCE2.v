From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require SimMemId SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon SimSIR SIR.

Require Import Program.
Require Import Simulation.
Require Import Relation_Operators.

Set Implicit Arguments.



(*** TODO: move to CoqlibC ***)
Lemma app_inj
      X (hd0 hd1 tl: list X)
      (EQ: hd0 ++ tl = hd1 ++ tl)
  :
    <<EQ: hd0 = hd1>>
.
Proof.
  ginduction hd0; ii; ss.
  - apply (@func_app _ _ (@List.length _)) in EQ; des. rewrite app_length in *. destruct hd1; ss. xomega.
  - dup EQ.
    apply (@func_app _ _ (@List.length _)) in EQ; des. ss. rewrite ! app_length in *. destruct hd1; ss; try xomega.
    clarify. erewrite IHhd0; et.
Qed.




(*** TODO: move ***)
Lemma bind_ignore
      E R S
      (X: itree E R) (Y: itree E S)
  :
  Y = X ;; Y
.
Proof.
  f. revert_until S. ginit. gcofix CIH. ii.
  ides X.
  - irw. gstep. refl.
  - irw.
Abort.

Lemma bind_ignore
      E R S
      (X: itree E R) (Y: itree E S)
  :
  Y ≈ X ;; Y
.
Proof.
  revert_until S. ginit. gcofix CIH. ii.
  (* guclo eqit_clo_bind. *)
  ides X.
  - irw. gstep. refl.
  - irw. gstep. econs; et.
Abort.



Section WFPROJ.

  Variable idxa: Type.
  Variable orda: idxa -> idxa -> Prop.
  Hypothesis WF: well_founded orda.

  Variable idxb: Type.
  Variable f: idxb -> idxa.
  Let ordb (b0 b1: idxb): Prop := orda (f b0) (f b1).

  Theorem wf_proj: well_founded ordb.
  Proof.
    ii. rename a into b.
    remember (f b) as a. generalize dependent b.
    pattern a. eapply well_founded_ind; et. clear a; i.
    clarify. econs; et.
  Qed.

End WFPROJ.




Section LEXSTK.
  (** exponential? **)

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Definition idx_stk := list idx.
  Inductive ord_stk: idx_stk -> idx_stk -> Prop :=
  | ord_stk_hd
      hd0 hd1
      (ORD: ord hd0 hd1)
      tl
    :
      ord_stk (hd0 :: tl) (hd1 :: tl)
  | ord_stk_call
      hd0 hd1
      (ORD: ord hd0 hd1)
      tl
    :
      ord_stk (hd0 :: hd0 :: tl) (hd1 :: tl)
  | ord_stk_ret
      hd tl
    :
      ord_stk tl (hd :: tl)
  .

  Theorem ord_stk_wf: <<WF: well_founded ord_stk>>.
  Proof.
    assert(ACC: forall xs, Acc ord_stk xs).
    {
      induction 0; i; ss.
      { econs; et. ii. inv H. }

      generalize dependent xs. pattern a. eapply well_founded_ind.
      { eapply WF. }
      i. clear a.

      econs. ii. inv H0.
      - eapply H; et.
      - eapply H; et.
      - ss.
    }
    et.
  Qed.

End LEXSTK.

(*** TODO: Move to Ord.v ***)
Section LEXICO.

  Variable (idxh idxl: Type) (ordh: idxh -> idxh -> Prop) (ordl: idxl -> idxl -> Prop).

  Definition idx_lex := (idxh * idxl)%type.

  Inductive ord_lex: idx_lex -> idx_lex -> Prop :=
  | ord_lex_high
      idxh0 idxh1 idxl0 idxl1
      (ORDH: ordh idxh0 idxh1):
      ord_lex (idxh0, idxl0) (idxh1, idxl1)
  | ord_lex_low
      idxh idxl0 idxl1
      (ORDL: ordl idxl0 idxl1):
      ord_lex (idxh, idxl0) (idxh, idxl1).

  Theorem ord_lex_wf
          (WF0: well_founded ordl)
          (WF1: well_founded ordh):
      <<WF: well_founded ord_lex>>.
  Proof.
    assert(ACC: forall h, Acc ordh h -> forall l, Acc ordl l -> Acc ord_lex (h, l)).
    {
      induction 1.
      induction 1.
      econs. i. inv H3.
      - eauto.
      - eauto.
    }
    rr. i. destruct a. eapply ACC; eauto.
  Qed.

End LEXICO.
























































Local Obligation Tactic := ii; ss; eauto.

(*** TODO: move to CoqlibC ***)
Local Open Scope signature_scope.

(*** TODO: move to CoqlibC ***)
Coercion is_some_coercion {X}: (option X) -> bool := is_some.


Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.
(* Variable _pures: ident -> Prop. *)
(* Let idx := nat. *)
(* Let ord := lt. *)
Variable idx: Type.
Variable ord: idx -> idx -> Prop.
Hypothesis wf_ord: well_founded ord.
Variable manifesto: ident -> option (owned_heap -> mem -> list val -> idx).
Let sim_st := sim_st (@eq owned_heap).



Let gidx: Type := idx_stk (idx_lex idx nat).
Let gord: gidx -> gidx -> Prop := tc (ord_stk (ord_lex ord lt)).
Let wf_gord: well_founded gord.
Proof. eapply well_founded_clos_trans. eapply ord_stk_wf. eapply ord_lex_wf; et. eapply lt_wf. Qed.


Ltac tc_left := eapply t_trans; [apply t_step|].
Ltac tc_right := eapply t_trans; [|apply t_step]; cycle 1.

Let grord := rtc (ord_stk (ord_lex ord lt)).

Lemma rtc_tc
      X (r: X -> X -> Prop)
      x0 x1
      (NEQ: x0 <> x1)
      (RTC: rtc r x0 x1)
  :
    <<TC: tc r x0 x1>>
.
Proof.
  induction RTC; ss.
  destruct (classic (y = z)).
  - clarify. et.
  - tc_left; et. eapply IHRTC. ss.
Qed.

Lemma tc_rtc
      X (r: X -> X -> Prop)
      x0 x1
      (TC: tc r x0 x1)
  :
    <<RTC: rtc r x0 x1>>
.
Proof.
  induction TC; ss.
  - econs; et.
  - r. etrans; et.
Qed.

Lemma rtc_tc_trans
      X (r: X -> X -> Prop)
      x0 x1 x2
      (RTC: rtc r x0 x1)
      (TC: tc r x1 x2)
  :
    <<TC: tc r x0 x2>>
.
Proof.
  gen x2.
  induction RTC; i; ss.
  r. econs 2; et. eapply IHRTC. et.
Qed.

Lemma tc_rtc_trans
      X (r: X -> X -> Prop)
      x0 x1 x2
      (TC: tc r x0 x1)
      (RTC: rtc r x1 x2)
  :
    <<TC: tc r x0 x2>>
.
Proof.
  gen x0.
  induction RTC; i; ss.
  r. econs 2; et. eapply IHRTC. et.
Qed.

Global Instance well_founded_irreflexive X (r: X -> X -> Prop) (WF: well_founded r): Irreflexive r.
Proof.
  r in WF.
  ii. hexploit (WF x); et. intro T. induction T.
  eapply H1; et.
Qed.

Lemma grord_app_l
      hd tl
  :
    <<ORD: grord tl (hd ++ tl)>>
.
Proof.
  revert tl.
  induction hd; ii; ss.
  - rr. refl.
  - rr. etrans; cycle 1.
    { eapply rtc_once. econsr; et. }
    eapply IHhd.
Qed.

Lemma gord_app_l
      hd tl
      (NNIL: hd <> nil)
  :
    <<ORD: gord tl (hd ++ tl)>>
.
Proof.
  eapply rtc_tc; ss.
  { ii. apply (@func_app _ _ (@List.length _)) in H. destruct hd; ss.
    rewrite app_length in *. ss. des. xomega. }
  eapply grord_app_l.
Qed.

Lemma grord_postfix_aux_once
      hd0 hd1 tl
      (ORD: ord_stk (ord_lex ord lt) hd0 hd1)
  :
    <<ORD: ord_stk (ord_lex ord lt) (hd0 ++ [tl]) (hd1 ++ [tl])>>
.
Proof.
  inv ORD; econs; et.
Qed.

Lemma grord_postfix_aux
      hd0 hd1 tl
      (ORD: ord_stk (ord_lex ord lt) hd0 hd1)
  :
    <<ORD: ord_stk (ord_lex ord lt) (hd0 ++ tl) (hd1 ++ tl)>>
.
Proof.
  gen hd0 hd1.
  induction tl; ii; ss.
  { rewrite ! app_nil_r. et. }
  rewrite cons_app. rewrite ! app_assoc. eapply IHtl.
  eapply grord_postfix_aux_once; et.
Qed.

Lemma grord_postfix
      hd0 hd1 tl
      (ORD: grord hd0 hd1)
  :
    <<ORD: grord (hd0 ++ tl) (hd1 ++ tl)>>
.
Proof.
  revert tl.
  induction ORD; ii; ss.
  { rr. refl. }
  rr. etrans; cycle 1.
  { eapply IHORD. }
  eapply rtc_once.
  eapply grord_postfix_aux; et.
Qed.

Lemma gord_postfix
      hd0 hd1 tl
      (* (NNIL: hd0 <> nil) *)
      (ORD: gord hd0 hd1)
  :
    <<ORD: gord (hd0 ++ tl) (hd1 ++ tl)>>
.
Proof.
  eapply rtc_tc; ss.
  { ii.
    exploit app_inj; et. i; des; clarify.
    eapply well_founded_irreflexive in ORD; ss.
  }
  eapply grord_postfix; et.
  eapply tc_rtc; et.
Qed.

(* Lemma grord_cons_r *)
(*       hd x *)
(*   : *)
(*     <<ORD: grord hd (hd ++ [x])>> *)
(* . *)
(* Proof. *)
(*   induction hd; ii; ss. *)
(*   - econs; et. econs; et. *)
(*   - econs; et. econs; et. *)
(* Qed. *)

(* Lemma grord_app_r *)
(*       hd tl *)
(*   : *)
(*     <<ORD: grord hd (hd ++ tl)>> *)
(* . *)
(* Proof. *)
(*   revert hd. *)
(*   induction tl; ii; ss. *)
(*   - rewrite app_nil_r. rr. refl. *)
(*   - rr. etrans; cycle 1. *)
(*     { rewrite cons_app. rewrite app_assoc. eapply IHtl. } *)
(*     ss. *)
(*     { eapply rtc_once. econsr; et. } *)
(*     eapply IHhd. *)
(* Qed. *)

(* Lemma grord_cons_distr *)
(*       hd0 hd1 tl0 tl1 *)
(*       (ORDH: grord [hd0] [hd1]) *)
(*       (ORDT: grord tl0 tl1) *)
(*   : *)
(*     <<ORD: grord (hd0 :: tl0) (hd1 :: tl1)>> *)
(* . *)
(* Proof. *)
(*   gen hd0 hd1 tl1. *)
(*   induction tl0; ii; ss. *)
(*   { rr. etrans. *)
(*     { et. } *)
(*     eapply  *)
(*     etrans; cycle 1. *)
(*     { eapply rtc_once. econsr; et. } *)

(*     econs; et. rr in ORDT. inv ORDT. *)
(*   revert_until hd0. *)
(*   induction hd0; ii; ss. *)
(*   - rr. refl. *)
(*   - rr. etrans; cycle 1. *)
(*     { eapply rtc_once. econsr; et. } *)
(*     eapply IHhd. *)
(* Qed. *)

(* Lemma grord_drop *)
(*       x y z *)
(*   : *)
(*     <<ORD :grord (x ++ z) (x ++ y ++ z)>> *)
(* . *)
(* Proof. *)
(*   gen y z. *)
(*   induction x; ii; ss. *)
(*   - eapply grord_app_l; et. *)
(*   - exploit (IHx y); et. intro T. tc_right. *)
(*     { econsr; et. } *)
(*     eapply IHhd; ss. *)
(* Qed. *)

(* Lemma gord_drop *)
(*       x y z *)
(*       (NNIL: y <> nil) *)
(*   : *)
(*     <<ORD :gord (x ++ z) (x ++ y ++ z)>> *)
(* . *)
(* Proof. *)
(*   gen y z. *)
(*   induction x; ii; ss. *)
(*   - eapply gord_prefix; et. *)
(*   - exploit (IHx y); et. intro T. tc_right. *)
(*     { econsr; et. } *)
(*     eapply IHhd; ss. *)
(* Qed. *)











(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Section REL.

Context `{S: Type}.
Let itr := itree (E owned_heap) S.

Inductive _match_itr (match_itr: itr -> itr -> Prop): itr -> itr -> Prop :=
| match_ret
    s
  :
    _match_itr match_itr (Ret s) (Ret s)
| match_tau
    i_src
    i_tgt
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr (Tau i_src) (Tau i_tgt)
| match_vis
    X (e: (E owned_heap) X) k_src k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr (Vis e k_src) (Vis e k_tgt)
| match_icall_pure
    fname oh0 m0 vs0 i_src i_tgt
    (PURE: manifesto fname)
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr
               (tau;; i_src)
               (trigger (ICall fname oh0 m0 vs0) >>= (fun _ => i_tgt))
.

Definition match_itr: itr -> itr -> Prop := paco2 _match_itr bot2.
Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try (by econs; et; rr; et).
Qed.

End REL.

(* Hint Unfold pure. *)
(* Hint Resolve pure_mon: paco. *)
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.







(* Section PURE. *)

(* Variable p: program owned_heap. *)

(* Let itr := itree (E owned_heap) (owned_heap * (mem * val)). *)

(* (*** NOTE: we have idx, so we are able to define in coinductive. What could be the difference? ***) *)
(* Inductive pure (i0: idx): itr -> Prop := *)
(* | pure_ret *)
(*     s *)
(*   : *)
(*     pure i0 (Ret s) *)
(* | pure_tau *)
(*     i1 *)
(*     (ORD: ord i1 i0) *)
(*     itr *)
(*     (PURE: pure i1 itr) *)
(*   : *)
(*     pure i0 (Tau itr) *)
(* | pure_icall *)
(*     fname oh0 m0 vs0 ktr *)
(*     (K: forall ohmv, exists i1, <<ORD: ord i1 i0>> /\ <<PURE: pure i1 (ktr ohmv)>>) *)
(*     (* i1 *) *)
(*     (* (ORD: ord i1 i0) *) *)
(*     (* (CALL: pure i1 (interp_function p (ICall fname oh0 m0 vs0))) *) *)
(*     (*** NOTE: let's not obligate the user mutual induction. That is the point of manifesto ***) *)
(*     mf *)
(*     (MF: manifesto fname = Some mf) *)
(*     (CALL: ord (mf oh0 m0 vs0) i0) *)
(*   : *)
(*     pure i0 (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr) *)
(* | pure_nb *)
(*     ktr *)
(*   : *)
(*     pure i0 (Vis (subevent _ (ENB)) ktr) *)
(* . *)

(* End PURE. *)
(* Hint Constructors pure. *)



Section PURE.

Variable p: program owned_heap.

Let itr := itree (E owned_heap) (owned_heap * (mem * val)).

(*** NOTE: we have idx, so we are able to define in coinductive. What could be the difference? ***)
Inductive _pure (pure: idx -> itr -> Prop) (i0: idx): itr -> Prop :=
| pure_ret
    s
  :
    _pure pure i0 (Ret s)
| pure_tau
    i1
    (ORD: ord i1 i0)
    itr
    (PURE: pure i1 itr)
  :
    _pure pure i0 (Tau itr)
| pure_icall
    fname oh0 m0 vs0 ktr
    (K: forall ohmv, exists i1, <<ORD: ord i1 i0>> /\ <<PURE: pure i1 (ktr ohmv)>>)
    (* i1 *)
    (* (ORD: ord i1 i0) *)
    (* (CALL: pure i1 (interp_function p (ICall fname oh0 m0 vs0))) *)
    (*** NOTE: let's not obligate the user mutual induction. That is the point of manifesto ***)
    mf
    (MF: manifesto fname = Some mf)
    (CALL: ord (mf oh0 m0 vs0) i0)
  :
    _pure pure i0 (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr)
| pure_nb
    ktr
  :
    _pure pure i0 (Vis (subevent _ (ENB)) ktr)
.
Definition pure: idx -> itr -> Prop := paco2 _pure bot2.
Lemma pure_mon: monotone2 _pure.
Proof.
  ii. inv IN; try (by econs; et; rr; et).
  econs; et. ii. exploit K; et. i; des. esplits; et.
Qed.

End PURE.
Hint Unfold pure.
Hint Resolve pure_mon: paco.






Section GPURE.

Variable p: program owned_heap.

Let itr := itree (E owned_heap) (owned_heap * (mem * val)).

(*** NOTE: we have idx, so we are able to define in coinductive. What could be the difference? ***)
Inductive _gpure (gpure: gidx -> itr -> Prop): gidx -> itr -> Prop :=
| gpure_ret
    i0 s
  :
    _gpure gpure i0 (Ret s)
| gpure_tau
    i0 tl i1
    (ORD: ord i1 i0)
    itr
    (GPURE: gpure ((i1, 1%nat) :: tl) itr)
  :
    _gpure gpure ((i0, 1%nat) :: tl) (Tau itr)
| gpure_icall
    i0 tl
    fname oh0 m0 vs0 ktr
    (K: forall ohmv, exists i1, (<<ORD: (ord_lex ord lt) i1 (i0, 0%nat)>>)
                                /\ (<<GPURE: gpure (i1 :: tl) (ktr ohmv)>>))
    (* i1 *)
    (* (ORD: ord i1 i0) *)
    (* (CALL: gpure i1 (interp_function p (ICall fname oh0 m0 vs0))) *)
    (*** NOTE: let's not obligate the user mutual induction. That is the point of manifesto ***)
    mf
    (MF: manifesto fname = Some mf)
    (CALL: (ord_lex ord lt) (mf oh0 m0 vs0, 1%nat) (i0, 1%nat))
  :
    _gpure gpure ((i0, 1%nat) :: tl) (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr)
| gpure_nb
    i0 ktr
  :
    _gpure gpure i0 (Vis (subevent _ (ENB)) ktr)
| gpure_stutter
    i0 i1
    itr
    (ORD: (tc (ord_stk (ord_lex ord lt))) i1 i0)
    (GPURE: gpure i1 itr)
  :
    _gpure gpure i0 itr
.
Definition gpure: gidx -> itr -> Prop := paco2 _gpure bot2.
Lemma gpure_mon: monotone2 _gpure.
Proof.
  ii. inv IN; try (by econs; et; rr; et).
  econs; et. ii. exploit K; et. i; des. esplits; et.
Qed.

Hint Unfold gpure.
Hint Resolve gpure_mon: paco.

Lemma gpure_mon_idx
      clo r rg i0 i1 it
      (GPURE: gpaco2 _gpure clo r rg i1 it)
      (RCOMPAT: forall
          i0 i1 x
          (ORD: gord i1 i0)
          (R: r i1 x)
        ,
          (* <<R: r i0 x>>) *)
          r i0 x)
      (ORD: gord i1 i0)
  :
    <<GPURE: gpaco2 _gpure clo r rg i0 it>>
.
Proof.
  (* revert_until i0. revert i0. *)
  (* gcofix CIH. *)
  (* i. *)

  (* gunfold GPURE. *)
  (* econs. *)
  inv GPURE. econs.
  gen i0. induction IN; i; ss.
  - econs 1. des; et. left.
    punfold IN. pfold. inv IN.
    + econs 1; et.
    + unfold Basics.compose.
Abort.

Inductive gpure_ordC (r: gidx -> itr -> Prop) : gidx -> itr -> Prop :=
| gpure_ordC_intro
    i0 i1 itr
    (ORD: gord i1 i0)
    (GPURE: r i1 itr)
  :
    gpure_ordC r i0 itr
.

Hint Constructors gpure_ordC: core.

Lemma gpure_ordC_spec
      simC
  :
    gpure_ordC <3= gupaco2 (_gpure) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  gclo.
Abort.

Lemma ordC_wcompat
  :
    wcompatible2 _gpure gpure_ordC.
Proof.
  constructor.
  - intros x0 x1 r r' IN LE. induction IN; subst; eauto.
  - intros. inv PR.
Abort.

Inductive gpure_bindC (r: gidx -> itr -> Prop) : gidx -> itr -> Prop :=
| gpure_bindC_intro
    hd0 itr
    (* (NNIL: hd0 <> nil) *)
    (PURE: gpure hd0 itr)
    hd1 tl ktr
    (K: forall ohmv, exists i0, <<ORD: ord_lex ord lt i0 (hd1, 0%nat)>> /\
                                       <<PURE: r (i0 :: tl) (ktr ohmv)>>)
  :
    gpure_bindC r (hd0 ++ (hd1, 0%nat) :: tl) (ITree.bind itr ktr)
.

Hint Constructors gpure_bindC: core.

Lemma gpure_bindC_spec
      simC
  :
    gpure_bindC <3= gupaco2 (_gpure) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold PURE. inv PURE.
  - (* ret *)
    irw. spc K. des.
    gstep.
    econsr.
    { instantiate (1:= i0 :: tl). rewrite cons_app. rewrite cons_app with (xtl:=tl). rewrite app_assoc.
      eapply tc_rtc_trans; cycle 1.
      { eapply grord_postfix; et. eapply grord_app_l. }
      ss. econs; et. econs; et.
    }
    eauto with paco.
  - (* tau *)
    irw. pclearbot.
    gstep. econs; et.
    gbase. eapply CIH. rewrite cons_app. rewrite app_assoc. econs; et.
  - (* call *)
    irw. gstep. econs; et.
    i. spc K0. des. pclearbot.
    { esplits.
      - eapply ORD.
      - gbase. eapply CIH. rewrite cons_app. rewrite app_assoc. econs; et.
    }
  - (* nb *)
    irw. gstep. econs; et.
  - (* stutter *)
    irw. pclearbot.
    gstep. econsr.
    { instantiate (1:= (i1 ++ (hd1, 0%nat) :: tl)). rewrite cons_app. eapply gord_postfix; et. }
    eauto with paco.
Qed.

End GPURE.
Hint Unfold gpure.
Hint Resolve gpure_mon: paco.


Theorem pure_gpure
        i0 itr
        (PURE: pure i0 itr)
  :
    <<GPURE: gpure [(i0, 1%nat)] itr>>
.
Proof.
  revert_until i0. revert i0.
  ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  gcofix CIH. i.
  punfold PURE. inv PURE.
  - gstep. econs; et.
  - gstep. econs; et.
    pclearbot. eauto with paco.
  - gstep. econs; et.
    + ii. exploit K; et. i; des. pclearbot. esplits; et.
      { econs; et. }
      eauto with paco.
    + econs; et.
  - gstep. econs; et.
Unshelve.
  all: ss.
Qed.

Theorem gpure_bind
        hd0 hd1 itr tl ktr
        (PURE: gpure [hd0] itr)
        (K: forall ohmv, exists i0, <<ORD: ord_lex ord lt i0 (hd1, 0%nat)>> /\
                                           <<PURE: upaco2 _gpure bot2 (i0 :: tl) (ktr ohmv)>>)
  :
    <<PURE: gpure ([hd0; (hd1, 0%nat)] ++ tl) (itr >>= ktr)>>
.
Proof.
  ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  guclo gpure_bindC_spec.
  ss. rewrite cons_app. econs; et. ii. spc K. des. esplits; et. pclearbot. eauto with paco.
Qed.









Section PROG.

Definition match_fn: relation (function owned_heap) := (eq ==> eq ==> eq ==> match_itr).

Inductive match_prog (p_src p_tgt: program owned_heap): Prop :=
| match_prog_intro
    (PURES: forall
        _fn mf
        (PURE: manifesto _fn = Some mf)
      ,
        exists fn,
          (<<FN: p_tgt _fn = Some fn>>) /\
          (<<PURE: forall oh m vs, pure (mf oh m vs) (fn oh m vs)>>))
    (MATCH: (eq ==> option_rel match_fn) p_src p_tgt)
.

End PROG.



(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)

Context `{S : Type}.
Let itr := itree (E owned_heap) S.
Inductive bindC (r: itr -> itr -> Prop) : itr -> itr -> Prop :=
| bindC_intro
    U
    i_src i_tgt
    (SIM: match_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: ((@eq U) ==> r) k_src k_tgt)
  :
    bindC r (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindC: core.

Lemma bindC_spec
      simC
  :
    bindC <3= gupaco2 (_match_itr) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold SIM. inv SIM.
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. ii. clarify.
    repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. eauto with paco.
  - rewrite ! bind_bind. gstep.
    erewrite f_equal2; try eapply match_icall_pure; try refl; ss.
    { pclearbot. eauto with paco. }
    irw. ss.
Qed.

Global Instance match_itr_bind T :
  Proper ((eq ==> match_itr) ==> (match_itr) ==> (match_itr)) (ITree.bind' (T:=T) (U:=S))
.
Proof.
  red. ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  guclo bindC_spec. ii. econs; et.
  u. ii.
  exploit H0; et. i. eauto with paco.
Qed.




(* Theorem pure_bind *)
(*         manifesto *)
(*         i0 it ktr *)
(*         (PURE: pure manifesto i0 it) *)
(*         (K : forall ohmv: owned_heap * (mem * val), *)
(*             exists i1, <<ORD: ord i1 i0 >> /\ <<PURE: pure manifesto i1 (ktr ohmv)>>) *)
(*   : *)
(*     exists i1, pure manifesto i1 (it >>= ktr) *)
(* . *)
(* Proof. *)
(*   induction PURE. *)
(*   - irw. exploit K; et. i; des. esplits; et. *)
(*   - irw. exploit IHPURE; et. exploit K; et. i; des. esplits; et. *)
(* Qed. *)




End SYNTAX.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.
Hint Unfold pure.
Hint Resolve pure_mon: paco.
Hint Unfold gpure.
Hint Resolve gpure_mon: paco.









Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
  Hypothesis (SIMP: match_prog p_src p_tgt).
  (* Hypothesis (WFSRC: wf_prog p_src). *)

  Global Instance match_itr_Reflexive S: Reflexive (@match_itr S).
  Proof.
    ginit.
    { intros. eapply cpn2_wcompat; et. eauto with paco. }
    gcofix CIH. ii. ides x.
    - gstep. econs; et.
    - gstep. econs; et. eauto with paco.
    - gstep. econs; et. ii. clarify. eauto with paco.
  Qed.

  Lemma match_itr_glue
        i_src i_tgt
        (SIM: match_itr (S:=owned_heap * (mem * val)) i_src i_tgt)
    :
      (interp_mrec (interp_function p_src) i_src) ≈ (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    ginit.
    revert_until SIMP.
    gcofix CIH.
    i. punfold SIM. inv SIM; irw.
    - gstep. econs; et.
    - gstep. econs; et. pclearbot. gbase. rewrite <- ! unfold_interp_mrec. eapply CIH. et.
    - des_ifs.
      + gstep. econs; et. destruct i. irw. inv SIMP.
        specialize (MATCH0 name name eq_refl). r in MATCH0. des_ifs; cycle 1.
        { irw. gstep. econs; et. ii; ss. }
        guclo eqit_clo_bind. rr in MATCH0.
        hexploit (@MATCH0 oh oh eq_refl m m eq_refl vs vs eq_refl); et. intro T.
        unfold _interp_mrec. des_ifs.
  Abort.

  Lemma match_prog_sim_st
        i0 i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st (ord_stk ord) i0 (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    punfold SIM. inv SIM; cbn.
    - gstep. destruct s as [oh [m v]]. econs; et.
    - gstep. econs; et. gbase. pclearbot. et.
    - gstep. des_ifs.
      + econs; et. gbase.
        eapply CIH. eapply match_itr_bind; et.
        { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
        destruct i.
        inv SIMP.
        exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1.
        { pfold. econs; et. ii; ss. }
        exploit T; et.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify.
          gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot.
          eauto with paco.
        * destruct e.
          { econs; et. }
          { econs; et. }
          { econs; et. ii.
            esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot.
            gstep. econs; et.
            eauto with paco. }
    - pclearbot. inv SIMP.
      exploit PURES; et. i; des.
      exploit (MATCH0 fname); et. intro T. r in T.
      des_ifs.
      (* gstep. econs; et. *)
      (* irw. *)
      (* rr in T. hexploit (T oh0 _ eq_refl m0 _ eq_refl vs0 _ eq_refl); et. intro U. *)
      (* gbase. rewrite <- ! unfold_interp_mrec. eapply CIH. *)

      (* (*** TODO: make lemma ***) *)
      (* rewrite <- bind_bind. rewrite bind_ret_r. *)
      (* repeat spc PURE0. *)
      (* rename f into fff. *)
  Abort.




  (* Lemma match_prog_sim_st *)
  (*       i0 *)
  (*       i_src i_tgt (d_tgt: itree (E owned_heap) (owned_heap * (mem * val))) *)
  (*       (PURE: pure i0 d_tgt) *)
  (*       (SIM: match_itr i_src (d_tgt ;; i_tgt)) *)
  (*   : *)
  (*     sim_st (ord_stk ord) [i0] (interp_mrec (interp_function p_src) i_src) *)
  (*            (interp_mrec (interp_function p_tgt) i_tgt) *)
  (* . *)
  (* Proof. *)
  (*   revert_until SIMP. *)
  (*   ginit. *)
  (*   { intros. eapply cpn3_wcompat; et. eauto with paco. } *)
  (*   gcofix CIH. *)
  (*   i. rewrite ! unfold_interp_mrec. *)
  (*   punfold SIM. inv SIM; cbn. *)
  (*   - gstep. destruct s as [oh [m v]]. *)
  (*     ides d_tgt; irw in H1; clarify. econs; et. *)
  (*   - gstep. pclearbot. ides d_tgt; irw in H1; clarify. *)
  (*     + (* ret *) *)
  (*       econs; et. gbase. eapply CIH; et. irw. et. *)
  (*     + (* tau *) *)
  (*       inv PURE. *)
  (*       econs; et. *)
  (*       { gbase. rewrite <- ! unfold_interp_mrec. eapply CIH; et. } *)
  (*       econs; et. *)
  (*   - ides d_tgt; ss; irw in H1; clarify. *)
  (*     + (* ret *) *)
  (*       des_ifs. *)
  (*       * gstep. econs; et. gbase. eapply CIH; et. irw. eapply match_itr_bind; et. *)
  (*         { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. } *)
  (*         destruct i. *)
  (*         inv SIMP. *)
  (*         exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1. *)
  (*         { pfold. econs; et. ii; ss. } *)
  (*         exploit T; et. *)
  (*       * destruct s. *)
  (*         -- destruct e. gstep. econs; et. ii. rr in H. des_ifs. des; clarify. *)
  (*            gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot. *)
  (*            eauto with paco. gbase. eapply CIH; et. irw; et. *)
  (*         -- gstep. destruct e. *)
  (*            { econs; et. } *)
  (*            { econs; et. } *)
  (*            { econs; et. ii. *)
  (*              esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot. *)
  (*              gstep. econs; et. *)
  (*              gbase. eapply CIH; et. irw. *)
  (*              eauto with paco. } *)
  (*     + (* vis *) *)
  (*       csc. *)
  (* Abort. *)

  Lemma sim_st_upto_pure
        i0 tl i_src i_tgt (d_tgt: itree (E owned_heap) (owned_heap * (mem * val)))
        (PURE: pure i0 d_tgt)
        (SIM: sim_st (ord_stk ord) tl (interp_mrec (interp_function p_src) i_src)
                     (interp_mrec (interp_function p_tgt) i_tgt))
    :
      (<<SIM: sim_st (ord_stk ord) (i0 :: tl) (interp_mrec (interp_function p_src) i_src)
                     (interp_mrec (interp_function p_tgt) (d_tgt ;; i_tgt))>>)
  .
  Proof.
    revert_until manifesto.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    i. revert_until i0. revert i0. gcofix CIH.
    i.
    punfold PURE. inv PURE.
    - (* pure-ret *)
      irw. gstep. rewrite <- ! unfold_interp_mrec. econs; et.
      { rr in SIM. gfinal. right. eapply paco3_mon; eauto. ii; ss. }
      econs; et.
    - (* pure-tau *)
      irw. gstep. rewrite <- ! unfold_interp_mrec. pclearbot. econs; et.
      { eauto with paco. }
      econs; et.
    - (* pure-icall *)
      irw.
      inv SIMP. exploit PURES; et. i; des. des_ifs.
      gstep. econs; et.
      { rewrite <- ! unfold_interp_mrec.
        gbase. rewrite <- bind_bind. eapply CIH; et.
        repeat spc PURE.
        instantiate (1:= (mf oh0 m0 vs0)).
        clear - K PURE.
        admit "we should put radix".
      }
      econs; et.
    - (* pure-nb *)
      irw. gstep. econs; et.
  Unshelve.
    all: ss.
  Abort.

  Lemma sim_st_upto_gpure
        i0 tl i_src i_tgt (d_tgt: itree (E owned_heap) (owned_heap * (mem * val)))
        (PURE: gpure i0 d_tgt)
        (SIM: sim_st gord tl (interp_mrec (interp_function p_src) i_src)
                     (interp_mrec (interp_function p_tgt) i_tgt))
    :
      (<<SIM: sim_st gord (i0 ++ tl) (interp_mrec (interp_function p_src) i_src)
                     (interp_mrec (interp_function p_tgt) (d_tgt ;; i_tgt))>>)
  .
  Proof.
    revert_until i0. revert i0.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    i. revert_until i0. revert i0. gcofix CIH.
    i.
    punfold PURE. inv PURE.
    - (* pure-ret *)
      irw. destruct i0; ss.
      + rr in SIM. rewrite <- ! unfold_interp_mrec. gfinal. right. eapply paco3_mon; et. ii; ss.
      + gstep. econs; et; cycle 1.
        { instantiate (1:= tl). rewrite cons_app. rewrite app_assoc. eapply gord_app_l. ss. }
        { rewrite <- ! unfold_interp_mrec. rr in SIM. gfinal. right.
          eapply paco3_mon; et. ii; ss. }
    - (* pure-tau *)
      irw. gstep. rewrite <- ! unfold_interp_mrec. pclearbot. econs; et.
      { gbase. eapply CIH; eauto with paco. }
      econs; et. econs; et. econs; et.
    - (* pure-icall *)
      rename tl0 into mid.
      irw.
      inv SIMP. exploit PURES; et. i; des. des_ifs.
      gstep. econs; et.
      { rewrite <- ! unfold_interp_mrec.
        gbase. rewrite <- bind_bind. eapply CIH; et.
        repeat spc PURE.
        eapply pure_gpure in PURE. des.
        instantiate (1:= [(mf oh0 m0 vs0, 1%nat) ; (i1, 0%nat)] ++ mid).
        (** we should had (i0hd, 1) and we should put (i0hd, 0) **)
        eapply gpure_bind; et.
      }
      ss. r.
      tc_right.
      { eapply ord_stk_call. econs 2; et. }
      econs; et. econs; et.
      clear - CALL.
      inv CALL; ss.
      { econs; et. }
      { xomega. }
    - (* pure-nb *)
      irw. gstep. econs; et.
    - (* pure-stutter *)
      irw. pclearbot. gstep. econs; cycle 1.
      { instantiate (1:= i2 ++ tl). eapply gord_postfix; et. }
      rewrite <- ! unfold_interp_mrec. eauto with paco.
  Unshelve.
    all: ss.
  Qed.
  TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT

  Lemma match_prog_sim_st
        manifesto i0
        i_src i_tgt (d_tgt: itree (E owned_heap) (owned_heap * (mem * val)))
        (PURE: pure i0 d_tgt)
        (SIM: match_itr i_src i_tgt)
    :
      sim_st (ord_stk ord) [i0] (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) (d_tgt ;; i_tgt))
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    induction PURE; irw.
    { punfold SIM. inv SIM; cbn.
      - (* ret *) gstep. destruct s0 as [oh [m v]]. econs; et.
      - (* tau *) admit "".
      - (* vis *) admit "".
      - (* pure call *) admit "".
    }
    { }
    punfold SIM. inv SIM; cbn.
    - gstep. destruct s as [oh [m v]]. econs; et.
    - gstep. econs; et. gbase. pclearbot. et.
    - gstep. des_ifs.
      + econs; et. gbase.
        eapply CIH. eapply match_itr_bind; et.
        { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
        destruct i.
        inv SIMP.
        exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1.
        { pfold. econs; et. ii; ss. }
        exploit T; et.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify.
          gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot.
          eauto with paco.
        * destruct e.
          { econs; et. }
          { econs; et. }
          { econs; et. ii.
            esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot.
            gstep. econs; et.
            eauto with paco. }
    - pclearbot. inv SIMP.
      exploit PURES; et. i; des.
      exploit (MATCH0 fname); et. intro T. r in T.
      des_ifs.
      gstep. econs; et.
      irw.
      rr in T. hexploit (T oh0 _ eq_refl m0 _ eq_refl vs0 _ eq_refl); et. intro U.
      gbase. rewrite <- ! unfold_interp_mrec. eapply CIH.

      (*** TODO: make lemma ***)
      rewrite <- bind_bind. rewrite bind_ret_r.
      repeat spc PURE0.
      rename f into fff.
  Qed.
        * gstep. econs; et. gbase. eapply CIH; et. irw. eapply match_itr_bind; et.
          { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
          destruct i.
          inv SIMP.
          exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1.
          { pfold. econs; et. ii; ss. }
          exploit T; et.
        * destruct s.
          -- destruct e. gstep. econs; et. ii. rr in H. des_ifs. des; clarify.
             gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot.
             eauto with paco. gbase. eapply CIH; et. irw; et.
          -- gstep. destruct e.
             { econs; et. }
             { econs; et. }
             { econs; et. ii.
               esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot.
               gstep. econs; et.
               gbase. eapply CIH; et. irw.
               eauto with paco. }
        * gstep. econs; et.
          
      + (* vis *)
      gstep. des_ifs.
      + destruct i. irw. inv SIMP.
        des_ifs. econs; et.
        { gbase. irw. rewrite <- ! unfold_interp_mrec.
          eapply CIH; et. ides d_tgt; ss; irw in H1; clarify.
          - irw. eapply match_itr_bind; et.
        { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
        destruct i.
        inv SIMP.
        exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1.
        { pfold. econs; et. ii; ss. }
        exploit T; et.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify.
          gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot.
          eauto with paco.
        * destruct e.
          { econs; et. }
          { econs; et. }
          { econs; et. ii.
            esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot.
            gstep. econs; et.
            eauto with paco. }
    - pclearbot. inv SIMP.
      exploit PURES; et. i; des.
      exploit (MATCH0 fname); et. intro T. r in T.
      des_ifs.
      gstep. econs; et.
      irw.
      rr in T. hexploit (T oh0 _ eq_refl m0 _ eq_refl vs0 _ eq_refl); et. intro U.
      gbase. rewrite <- ! unfold_interp_mrec. eapply CIH.

      (*** TODO: make lemma ***)
      rewrite <- bind_bind. rewrite bind_ret_r.
      repeat spc PURE0.
      rename f into fff.


      replace (i_src0) with (i_src0 >>= (@id_ _)). refl. rewrite  f. f_equiv. ii. f. irw. ss. }
      eapply match_itr_bind.
      right.


      exploit (MATCH0 fname); et. intro T. rr in T. des_ifs. des.
      exploit PURES; et. i; des.
      gstep. econs; et.
      irw.
          eauto with paco. gbase. eapply CIH. econs; et.
    - step_guarantee. irw. step.
      rewrite <- ! unfold_interp_mrec.
      gbase. eapply CIH.
      inv SIMP.
      des_ifs_safe. inv FOCUS. rewrite TGT. irw.
      step_assume; ss. irw.
      eapply match_itr_bind; et.
      { ii. clarify. step_guaranteeK; ss.
        (*** TODO: fix step_guaranteeK ***)
        { pfold. unfold triggerNB. rewrite bind_vis. econs; et. }
        irw. step_assume; ss.
        irw. exploit MATCH; et. intro U. pclearbot. eauto.
      }
      exploit SIM; et.
    - gstep. econs; et. u in *. gstep. econs; et.
      assert(a0 = a1).
      { rr in H0. des_ifs. des. clarify. }
      clarify.
      repeat spc MATCH. hexploit1 MATCH; ss. pclearbot.
      gbase. eapply CIH. eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - irw. step. step. ii. esplits; et. step.
      exploit MATCH; et. intro T. pclearbot. eauto with paco.
  Unshelve.
    all: ss.
    all: try (by econs).
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh
    ,
      (<<SIM: sim_st lt 1%nat (interp_program p_src (ICall fname oh m vs))
                     (interp_program p_tgt (ICall fname oh m vs))
                     >>)
  .
  Proof.
    {
      ii.
      destruct (eq_block fname _fn).
      {
        clarify.
        dup SIMP. inv SIMP0.
        unfold interp_program, interp_function, mrec.
        irw. des_ifs. inv FOCUS. rewrite TGT.
        unfold fn_src. cbn.
        unfold assume. des_ifs; cycle 1.
        { irw. pfold. unfold triggerUB. irw. econs; et. }
        rewrite ! bind_ret_l.
        irw.
        pfold. econs; et. left.
        des_ifs.
        rewrite <- ! unfold_interp_mrec.
        eapply match_prog_sim_st; ss.
        eapply match_itr_bind.
        { ii. clarify. step_guaranteeK.
          - pfold. econs; et.
          - unfold guaranteeK. des_ifs. pfold. econs; et.
        }
        eapply SIM; et.
      }
      eapply match_prog_sim_st; ss.
      inv SIMP.
      destruct (eq_block fname _fn_ru).
      { des_ifs. pfold. econs; et. }
      exploit OTHERS; et. intro T. rr in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      exploit T; et.
    }
  Qed.

  Variable ioh: SkEnv.t -> owned_heap.
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh).
  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    eapply SimSIR.sim_mod with (SO:=eq); eauto.
    { eapply lt_wf. }
    ii. clarify. esplits. eapply adequacy_local_local; et.
  Qed.

  Theorem correct: rusc defaultR [md_src] [md_tgt].
  Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

End SIM.
End OWNEDHEAP.
Hint Unfold match_itr match_fn.
Hint Constructors match_fn_focus match_prog.
Hint Resolve match_itr_mon: paco.
Hint Constructors bindC: core.
