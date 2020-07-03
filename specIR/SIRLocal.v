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
Require Import SIRCommon SIR SimSIR.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.



Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap_src owned_heap_tgt: Type.
Variable SO: owned_heap_src -> owned_heap_tgt -> Prop.
Let SALL := SALL SO.
Let sim_st := sim_st SO.





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let itr_src := itree (E owned_heap_src) (owned_heap_src * (mem * val)).
Let itr_tgt := itree (E owned_heap_tgt) (owned_heap_tgt * (mem * val)).

Inductive _match_itr (match_itr: itr_src -> itr_tgt -> Prop): itr_src -> itr_tgt -> Prop :=
| match_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    _match_itr match_itr (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| match_tau
    i_src
    i_tgt
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr (Tau i_src) (Tau i_tgt)
| match_icall
    fname m vs
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (MATCH: HProper (SALL !-> match_itr) k_src k_tgt)
  :
    _match_itr match_itr
             (* (trigger (ICall fname oh_src m vs) >>= k_src) *)
             (* (trigger (ICall fname oh_tgt m vs) >>= k_tgt) *)
             (Vis (subevent _ (ICall fname oh_src m vs)) k_src)
             (Vis (subevent _ (ICall fname oh_tgt m vs)) k_tgt)
| match_ecall
    sg m vs fptr
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (MATCH: HProper (SALL !-> match_itr) k_src k_tgt)
    (* (MATCH: forall *)
    (*     mr vr *)
    (*     ohr_src ohr_tgt *)
    (*   , *)
    (*     match_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _match_itr match_itr
             (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| match_nb
    i_src k_tgt
  :
    _match_itr match_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| match_ub
    k_src i_tgt
  :
    _match_itr match_itr (Vis (subevent _ (EUB)) k_src) i_tgt
| match_choose
    X_src X_tgt
    k_src k_tgt
    (INHAB: inhabited X_tgt \/ X_src = X_tgt)
    (SIM: forall x_tgt, exists x_src, match_itr (k_src x_src) (k_tgt x_tgt))
  :
    _match_itr match_itr
               (Vis (subevent _ (EChoose X_src)) k_src)
               (Vis (subevent _ (EChoose X_tgt)) k_tgt)
| match_choose_src
    X_src
    k_src i_tgt
    (MATCH: exists x_src, match_itr (k_src x_src) i_tgt)
  :
    _match_itr match_itr
             (Vis (subevent _ (EChoose X_src)) k_src)
             (Tau (Tau i_tgt))
| match_choose_tgt
    X_tgt
    k_tgt i_src
    (MATCH: forall x_tgt, match_itr i_src (k_tgt x_tgt))
    (INHAB: inhabited X_tgt)
  :
    _match_itr match_itr
             (Tau (Tau i_src))
             (Vis (subevent _ (EChoose X_tgt)) k_tgt)
.

Definition match_itr: itr_src -> itr_tgt -> Prop := paco2 _match_itr bot2.

Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try econs; et; rr; et.
  - i. exploit SIM; et. i; des_safe. esplits; et.
  - des. esplits; et.
Unshelve.
Qed.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.



Let fn_src := function owned_heap_src.
Let fn_tgt := function owned_heap_tgt.

(*** TODO: curry "function", and we can state "SALL --> match_itr" ***)
(*** TODO: give better name than SALL ***)
Definition match_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall
    m vs
    oh_src oh_tgt
    (O: SO oh_src oh_tgt)
  ,
    <<SIM: match_itr (k_src oh_src m vs) (k_tgt oh_tgt m vs)>>
.





(*** sim prog ***)
Definition match_prog: program owned_heap_src -> program owned_heap_tgt -> Prop :=
  eq !-> option_rel match_fn
.




(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)
Inductive bindC (r: itr_src -> itr_tgt -> Prop) : itr_src -> itr_tgt -> Prop :=
| bindC_intro
    i_src i_tgt
    (SIM: match_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: HProper (SALL !-> r) k_src k_tgt)
    (* (SIMK: forall *)
    (*     oh_src oh_tgt m vs *)
    (*     (O: SO oh_src oh_tgt) *)
    (*   , *)
    (*     <<SIM: r (k_src (oh_src, (m, vs))) (k_tgt (oh_tgt, (m, vs)))>>) *)
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
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et. rr; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot. eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot.
    eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis.
    gstep. econs; eauto. ii. exploit SIM0; et. intro T; des_safe. pclearbot. eauto with paco.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. des. pclearbot. eauto with paco.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. ii. pclearbot. eauto with paco.
Qed.

Global Instance match_itr_bind :
  HProper ((SALL !-> match_itr) !-> match_itr !-> match_itr) ITree.bind' ITree.bind'
.
Proof.
  red. ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  guclo bindC_spec. ii. econs; et.
  u. ii.
  exploit H0; et.
  intro T. eauto with paco.
Qed.

End SYNTAX.
Hint Unfold match_itr match_fn match_prog.
Hint Resolve match_itr_mon: paco.









Section SIM.

  Variable p_src: program owned_heap_src.
  Variable p_tgt: program owned_heap_tgt.
  Hypothesis (SIMP: match_prog p_src p_tgt).

  Lemma match_prog_sim_st
        i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st bot2 tt (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    punfold SIM. inv SIM; cbn.
    - gstep. econs; et.
    - pclearbot. gstep. econs; et. gbase. et.
    - pclearbot. gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind.
      { u. ii. repeat spc MATCH. pclearbot. eauto. }
      exploit (@SIMP fname); et. intro T. rr in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      exploit T; et.
    - gstep. econs; et. u in *. gstep. econs; et. repeat spc MATCH. specialize (MATCH H0).
      des; ss. gbase. eapply CIH.
      eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - gstep. econs; et. ii. exploit SIM0; et. i; des_safe. pclearbot. esplits.
      gstep. econs; et. eauto with paco.
    - gstep. des. pclearbot. econs; et. esplits; et. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_tgt0)). cbn. econs; et. eauto with paco.
    - gstep. pclearbot. econs; et. ii. repeat spc SIM0. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_src0)). cbn. econs; et. eauto with paco.
  Unshelve.
    all: ss.
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      (<<SIM: sim_st bot2 tt (interp_program p_src (ICall fname oh_src m vs))
                     (interp_program p_tgt (ICall fname oh_tgt m vs))
                     >>)
  .
  Proof.
    {
      ii.
      eapply match_prog_sim_st; ss.
      hexploit (@SIMP fname); et. intro T. rr in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      repeat (spc T). des. ss.
    }
  Qed.

  Variable ioh_src: SkEnv.t -> owned_heap_src.
  Variable ioh_tgt: SkEnv.t -> owned_heap_tgt.
  Hypothesis (SIMO: forall skenv, SO (ioh_src skenv) (ioh_tgt skenv)).
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh_src).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh_tgt).
  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    eapply SimSIR.sim_mod; eauto.
    { eapply unit_ord_wf. }
    ii. clarify. esplits. eapply adequacy_local_local; et.
  Qed.

  Theorem correct: rusc defaultR [md_src] [md_tgt].
  Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold match_itr match_fn match_prog.
Hint Resolve match_itr_mon: paco.
Hint Constructors bindC: core.


Section REFL.
  Variable owned_heap: Type.
  Global Program Instance match_itr_Reflexive: Reflexive (match_itr (@eq owned_heap)).
  Next Obligation.
    rr. revert x.
    ginit.
    { intros. eapply cpn2_wcompat; eauto with paco. }
    gcofix CIH. ii. gstep.
    ides x.
    - destruct r0 as [oh [m vs]]. econs; et.
    - econs; et. eauto with paco.
    - destruct e.
      + destruct i. econs; et. ii. rr in H. des_ifs. des; clarify. eauto with paco.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify. eauto with paco.
        * destruct e; try econs; et. ii. esplits; et. eauto with paco.
  Qed.
  
  Global Program Instance match_fn_Reflexive: Reflexive (match_fn (@eq owned_heap)).
  Next Obligation.
    ii. clarify. r. refl.
  Qed.

  Global Program Instance match_prog_Reflexive: Reflexive (match_prog (@eq owned_heap)).
  Next Obligation.
    ii. clarify. r. des_ifs. r. refl.
  Qed.

End REFL.
