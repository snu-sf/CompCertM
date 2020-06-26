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
Require Import SIRcommon SIRmini SimSIR.

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

Inductive _sim_itr (sim_itr: itr_src -> itr_tgt -> Prop): itr_src -> itr_tgt -> Prop :=
| sim_ret
    oh_src oh_tgt m v
    (O: SO oh_src oh_tgt)
  :
    _sim_itr sim_itr (Ret (oh_src, (m, v))) (Ret (oh_tgt, (m, v)))
| sim_tau
    i_src
    i_tgt
    (SIM: sim_itr i_src i_tgt)
  :
    _sim_itr sim_itr (Tau i_src) (Tau i_tgt)
| sim_icall
    fname m vs
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL !-> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src *)
    (*     ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (trigger (ICall fname oh_src m vs) >>= k_src)
             (trigger (ICall fname oh_tgt m vs) >>= k_tgt)
             (* (Vis (subevent _ (ICall fname oh_src m vs)) k_src) *)
             (* (Vis (subevent _ (ICall fname oh_tgt m vs)) k_tgt) *)
| sim_ecall
    sg m vs fptr
    oh_src k_src
    oh_tgt k_tgt
    (O: SO oh_src oh_tgt)
    (SIM: HProper (SALL !-> sim_itr) k_src k_tgt)
    (* (SIM: forall *)
    (*     mr vr *)
    (*     ohr_src ohr_tgt *)
    (*   , *)
    (*     sim_itr (k_src (ohr_src, (mr, vr))) (k_tgt (ohr_tgt, (mr, vr)))) *)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (ECall sg fptr oh_src m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh_tgt m vs)) k_tgt)
| sim_nb
    i_src k_tgt
  :
    _sim_itr sim_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| sim_ub
    k_src i_tgt
  :
    _sim_itr sim_itr (Vis (subevent _ (EUB)) k_src) i_tgt
| sim_choose_src
    X_src
    k_src i_tgt
    (SIM: exists x_src, sim_itr (k_src x_src) i_tgt)
  :
    _sim_itr sim_itr
             (Vis (subevent _ (EChoose X_src)) k_src)
             (Tau (Tau i_tgt))
| sim_choose_tgt
    X_tgt
    k_tgt i_src
    (SIM: forall x_tgt, sim_itr i_src (k_tgt x_tgt))
    (INHAB: inhabited X_tgt)
  :
    _sim_itr sim_itr
             (Tau (Tau i_src))
             (Vis (subevent _ (EChoose X_tgt)) k_tgt)
.

Definition sim_itr: itr_src -> itr_tgt -> Prop := paco2 _sim_itr bot2.

Lemma sim_itr_mon: monotone2 _sim_itr.
Proof.
  ii. inv IN; try econs; et; rr; et.
  des. esplits; et.
Unshelve.
Qed.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.



Let fn_src := function owned_heap_src.
Let fn_tgt := function owned_heap_tgt.

(*** TODO: curry "function", and we can state "SALL --> sim_itr" ***)
(*** TODO: give better name than SALL ***)
Definition sim_fn (k_src: fn_src) (k_tgt: fn_tgt): Prop := forall
    m vs
    oh_src oh_tgt
    (O: SO oh_src oh_tgt)
  ,
    <<SIM: sim_itr (k_src oh_src m vs) (k_tgt oh_tgt m vs)>>
.





(*** sim prog ***)
Definition sim_prog: program owned_heap_src -> program owned_heap_tgt -> Prop :=
  eq !-> option_rel sim_fn
.




(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)
Inductive bindC (r: itr_src -> itr_tgt -> Prop) : itr_src -> itr_tgt -> Prop :=
| bindC_intro
    i_src i_tgt
    (SIM: sim_itr i_src i_tgt)
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
    bindC <3= gupaco2 (_sim_itr) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold SIM. inv SIM.
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et. rr; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - rewrite ! bind_bind. gstep. econs; eauto. u. ii. repeat spc SIM0. pclearbot. eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc SIM0. pclearbot.
    eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. des. pclearbot. eauto with paco.
  - rewrite ! bind_vis. rewrite ! bind_tau.
    gstep. econs; eauto. ii. pclearbot. eauto with paco.
Qed.

Global Instance sim_itr_bind :
  HProper ((SALL !-> sim_itr) !-> sim_itr !-> sim_itr) ITree.bind' ITree.bind'
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
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.









Section SIM.

  Variable p_src: program owned_heap_src.
  Variable p_tgt: program owned_heap_tgt.
  Hypothesis (SIMP: sim_prog p_src p_tgt).

  Lemma sim_prog_sim_st
        i_src i_tgt
        (SIM: sim_itr i_src i_tgt)
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
    punfold SIM. inv SIM; cbn.
    - gstep. econs; et.
    - pclearbot. gstep. econs; et. gbase. et.
    - pclearbot. gstep. econs; et. gbase.
      eapply CIH. eapply sim_itr_bind.
      { u. ii. repeat spc SIM0. pclearbot. rewrite ! bind_ret_l. eauto. }
      exploit (@SIMP fname); et. intro T.
      inv T.
      { pfold. econs; et. }
      exploit H1; et.
    - gstep. econs; et. u in *. gstep. econs; et. repeat spc SIM0. specialize (SIM0 H0).
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
      { pfold. econs; et. }
      repeat (spc H1). des. ss.
    }
  Qed.

  Variable ioh_src: SkEnv.t -> owned_heap_src.
  Variable ioh_tgt: SkEnv.t -> owned_heap_tgt.
  Hypothesis (SIMO: forall skenv, SO (ioh_src skenv) (ioh_tgt skenv)).
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIRmini.module sk p_src mi ioh_src).
  Let md_tgt: Mod.t := (SIRmini.module sk p_tgt mi ioh_tgt).

  Theorem sim_mod: ModPair.sim (SimSymbId.mk_mp (SIRmini.module sk p_src mi ioh_src)
                                                (SIRmini.module sk p_tgt mi ioh_tgt)).
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem; et.
    eapply adequacy_local_local.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.
Hint Constructors bindC: core.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.
