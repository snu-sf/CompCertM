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


(*** same as SimSIRLocal, but in inductive type *)



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

Inductive match_itr: itr_src -> itr_tgt -> Prop :=
| match_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    match_itr (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| match_tau
    i_src
    i_tgt
    (MATCH: match_itr i_src i_tgt)
  :
    match_itr (Tau i_src) (Tau i_tgt)
| match_icall
    fname m vs
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (MATCH: HProper (SALL !-> match_itr) k_src k_tgt)
  :
    match_itr (Vis (subevent _ (ICall fname oh_src m vs)) k_src)
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
    match_itr (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| match_nb
    i_src k_tgt
  :
    match_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| match_ub
    k_src i_tgt
  :
    match_itr (Vis (subevent _ (EUB)) k_src) i_tgt
| match_choose_src
    X_src
    k_src i_tgt
    (MATCH: exists x_src, match_itr (k_src x_src) i_tgt)
  :
    match_itr (Vis (subevent _ (EChoose X_src)) k_src)
              (Tau (Tau i_tgt))
| match_choose_tgt
    X_tgt
    k_tgt i_src
    (MATCH: forall x_tgt, match_itr i_src (k_tgt x_tgt))
    (INHAB: inhabited X_tgt)
  :
    match_itr (Tau (Tau i_src))
              (Vis (subevent _ (EChoose X_tgt)) k_tgt)
.

Hint Constructors match_itr.

Lemma match_itr_ind2 :
forall P : itr_src -> itr_tgt -> Prop,
(forall (oh_src : owned_heap_src) (oh_tgt : owned_heap_tgt) (m : mem) (v : val),
 SO oh_src oh_tgt -> P (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))) ->
(forall (i_src : itr_src) (i_tgt : itr_tgt), match_itr i_src i_tgt -> P i_src i_tgt -> P (tau;; i_src) (tau;; i_tgt)) ->
(forall (fname : ident) (m : mem) (vs : list val) (oh_src : owned_heap_src) (k_src : owned_heap_src * (mem * val) -> itr_src)
   (oh_tgt : owned_heap_tgt) (k_tgt : owned_heap_tgt * (mem * val) -> itr_tgt),
 SO oh_src oh_tgt ->
 HProper (SALL !-> match_itr) k_src k_tgt ->
 (forall (a0 : owned_heap_src * (mem * val)) (a1 : owned_heap_tgt * (mem * val)), SALL a0 a1 -> P (k_src a0) (k_tgt a1)) ->
 P (Vis (subevent (owned_heap_src * (mem * val)) (ICall fname oh_src m vs)) k_src)
   (Vis (subevent (owned_heap_tgt * (mem * val)) (ICall fname oh_tgt m vs)) k_tgt)) ->
(forall (sg : signature) (m : mem) (vs : list val) (fptr : val) (oh_src : owned_heap_src)
   (k_src : owned_heap_src * (mem * val) -> itr_src) (oh_tgt : owned_heap_tgt) (k_tgt : owned_heap_tgt * (mem * val) -> itr_tgt),
 SO oh_src oh_tgt ->
 HProper (SALL !-> match_itr) k_src k_tgt ->
 (forall (a0 : owned_heap_src * (mem * val)) (a1 : owned_heap_tgt * (mem * val)), SALL a0 a1 -> P (k_src a0) (k_tgt a1)) ->
 P (Vis (subevent (owned_heap_src * (mem * val)) (ECall sg fptr oh_src m vs)) k_src)
   (Vis (subevent (owned_heap_tgt * (mem * val)) (ECall sg fptr oh_tgt m vs)) k_tgt)) ->
(forall (i_src : itr_src) (k_tgt : void -> itree (E owned_heap_tgt) (owned_heap_tgt * (mem * val))),
 P i_src (Vis (subevent void ENB) k_tgt)) ->
(forall (k_src : void -> itree (E owned_heap_src) (owned_heap_src * (mem * val))) (i_tgt : itr_tgt),
 P (Vis (subevent void EUB) k_src) i_tgt) ->
(forall (X_src : Type) (k_src : X_src -> itr_src) (i_tgt : itr_tgt),
 (exists x_src : X_src, match_itr (k_src x_src) i_tgt /\ P (k_src x_src) i_tgt) -> P (Vis (subevent X_src (EChoose X_src)) k_src) (tau;; tau;; i_tgt)) ->
(forall (X_tgt : Type) (k_tgt : X_tgt -> itr_tgt) (i_src : itr_src),
 (forall x_tgt : X_tgt, match_itr i_src (k_tgt x_tgt)) ->
 (forall x_tgt : X_tgt, P i_src (k_tgt x_tgt)) ->
 inhabited X_tgt -> P (tau;; tau;; i_src) (Vis (subevent X_tgt (EChoose X_tgt)) k_tgt)) ->
forall (i : itr_src) (i0 : itr_tgt), match_itr i i0 -> P i i0.
Proof.
  intros. revert_until H6. fix IH 3.
  intros. inv H7.
  - eapply H; et.
  - eapply H0; et.
  - eapply H1; et.
  - eapply H2; et.
  - eapply H3; et.
  - eapply H4; et.
  - des. eapply H5; et. (* the only difference *)
  - eapply H6; et.
Qed.



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



Global Instance match_itr_bind :
  HProper ((SALL !-> match_itr) !-> match_itr !-> match_itr) ITree.bind' ITree.bind'
.
Proof.
  red. ii.
  gen a0 a1.
  
  induction H0 using match_itr_ind2; i; irw; try (by econs; et).
  - eapply H0; rr; et.
  - des. econs; et.
Qed.

End SYNTAX.
Hint Constructors match_itr.









Section SIM.

  Variable p_src: program owned_heap_src.
  Variable p_tgt: program owned_heap_tgt.
  Hypothesis (SIMP: match_prog p_src p_tgt).

  Lemma sim_prog_sim_st
        i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn2_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    inv SIM; cbn.
    - gstep. econs; et.
    - pclearbot. gstep. econs; et. gbase. et.
    - pclearbot. gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind.
      { u. ii. repeat spc MATCH. pclearbot. eauto. }
      exploit (@SIMP fname); et. intro T.
      inv T.
      { econs; et. }
      exploit H1; et.
    - gstep. econs; et. u in *. gstep. econs; et. repeat spc MATCH. specialize (MATCH H0).
      des; ss. gbase. eapply CIH.
      eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - gstep. des. pclearbot. econs; et. esplits; et. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_tgt0)). cbn. econs; et. eauto with paco.
    - gstep. pclearbot. econs; et. ii. repeat spc SIM0. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_src0)). cbn. econs; et. eauto with paco.
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      (<<SIM: sim_st (interp_program p_src (ICall fname oh_src m vs))
                     (interp_program p_tgt (ICall fname oh_tgt m vs))
                     >>)
  .
  Proof.
    {
      ii.
      eapply sim_prog_sim_st; ss.
      hexploit (@SIMP fname); et. intro T. inv T; ss.
      { econs; et. }
      repeat (spc H1). des. ss.
    }
  Qed.

  Variable ioh_src: SkEnv.t -> owned_heap_src.
  Variable ioh_tgt: SkEnv.t -> owned_heap_tgt.
  Hypothesis (SIMO: forall skenv, SO (ioh_src skenv) (ioh_tgt skenv)).
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh_src).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh_tgt).

  Theorem sim_mod: ModPair.sim (SimSymbId.mk_mp (SIR.module sk p_src mi ioh_src)
                                                (SIR.module sk p_tgt mi ioh_tgt)).
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem; et.
    eapply adequacy_local_local.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Constructors match_itr.
