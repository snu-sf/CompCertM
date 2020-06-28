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

Set Implicit Arguments.






Local Obligation Tactic := ii; ss; eauto.

Local Open Scope signature_scope.





Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.
Variable precond: owned_heap -> mem -> list val -> Prop.
Variable postcond: owned_heap -> mem -> list val -> (owned_heap * (mem * val)) -> Prop.
Let sim_st := sim_st (@eq owned_heap).




Goal forall fname (oh0: owned_heap) m0 vs0 (k: (owned_heap * (mem * val)) -> itree (E owned_heap) (owned_heap * (mem * val))),
    (trigger (ICall fname oh0 m0 vs0) >>= assumeK (postcond oh0 m0 vs0) >>= k)
    = ohmv <- trigger (ICall fname oh0 m0 vs0) ;; assume (postcond oh0 m0 vs0 ohmv) ;; k ohmv.
Proof.
  i.
  rewrite bind_bind. f. f_equiv. ii. f.
  unfold assumeK, assume. des_ifs; et.
  - rewrite ! bind_ret_l. ss.
  - unfold triggerUB. rewrite ! bind_vis. f. f_equiv. ii. ss.
Qed.

(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let itr := itree (E owned_heap) (owned_heap * (mem * val)).
Variable _fn _fn_ru: ident.

(*** TODO: We don't have to define these in coinductive manner. Try inductive style instead? SimSIRLocal also. ***)
(*** TODO: However, if we want to add loop, we may need coinductive...? Q: Why loop and recursion is treated differently? ***)
Inductive _match_itr (match_itr: itr -> itr -> Prop): itr -> itr -> Prop :=
| match_ret
    oh m v
  :
    _match_itr match_itr (Ret (oh, (m, v))) (Ret (oh, (m, v)))
| match_tau
    i_src
    i_tgt
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr (Tau i_src) (Tau i_tgt)
| match_icall
    fname oh0 m0 vs0 k_src k_tgt
    (NEQ: fname <> _fn)
    (NEQ: fname <> _fn_ru)
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr
             (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_src)
             (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_tgt)
| match_icall_fn
    oh0 m0 vs0 k_src k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr
             (* (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_src) *)
             (trigger (ICall _fn_ru oh0 m0 vs0) >>= k_src)
             (guarantee (precond oh0 m0 vs0) ;;
              ohmv <- trigger (ICall _fn oh0 m0 vs0) ;;
              assume (postcond oh0 m0 vs0 ohmv) ;;
              k_tgt ohmv
              (*** we can write in point-free style but ***)
              (* trigger (ICall fname oh0 m0 vs0) *)
              (* >>= assumeK (postcond oh0 m0 vs0) *)
              (* >>= k_tgt *)
             )
      (* guarantee (precond oh0 m0 vs0) ;; *)
      (* '(oh1, (m1, y1)) <- trigger (ICall _fib oh0 m0 vs0) ;; *)
      (* (assume (postcond oh0 m0 vs0 (oh1, (m1, y1)))) ;; *)
| match_ecall
    sg oh m vs fptr
    k_src
    k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr
             (Vis (subevent _ (ECall sg fptr oh m vs)) k_src)
             (Vis (subevent _ (ECall sg fptr oh m vs)) k_tgt)
| match_nb
    i_src k_tgt
  :
    _match_itr match_itr i_src (Vis (subevent _ (ENB)) k_tgt)
| match_ub
    k_src i_tgt
  :
    _match_itr match_itr (Vis (subevent _ (EUB)) k_src) i_tgt
| match_choose
    X
    k_src k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr
             (Vis (subevent _ (EChoose X)) k_src)
             (Vis (subevent _ (EChoose X)) k_tgt)
.

Definition match_itr: itr -> itr -> Prop := paco2 _match_itr bot2.

Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try econs; et; rr; et.
Unshelve.
Qed.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.

Section PROG.

Definition fn_src (oh0: owned_heap) (m0: mem) (vs0: list val): itree (E owned_heap) (owned_heap * (mem * val)) :=
  assume (precond oh0 m0 vs0) ;;
  _I_DONT_USE_THIS__RUDIMENT_ORGAN_ <- trigger (ICall _fn_ru oh0 m0 vs0) ;;
  trigger (EChoose { ohmv: (owned_heap * (mem * val)) | postcond oh0 m0 vs0 ohmv }) >>= (fun x => Ret (proj1_sig x))
.

Inductive match_fn (fn_ru fn_tgt: function owned_heap): Prop :=
| match_fn_intro
    fn_tgt_inner
    (SIM: (eq ==> eq ==> eq ==> match_itr) fn_ru fn_tgt_inner)
    (TGT: fn_tgt = fun oh0 m0 vs0 =>
                     assume (precond oh0 m0 vs0) ;;
                     (fn_tgt_inner oh0 m0 vs0)
                     >>= guaranteeK (postcond oh0 m0 vs0)
    )
.

Inductive match_prog (p_src p_tgt: program owned_heap): Prop :=
| match_prog_intro
    fn_ru (* rudiment *) fn_tgt
    (FNSRC: p_src _fn = Some fn_src)
    (FNTGT: p_tgt _fn = Some fn_tgt)
    (RDSRC: p_src _fn_ru = Some fn_ru)
    (RDTGT: p_tgt _fn_ru = None)
    (SIMFN: match_fn fn_ru fn_tgt)
    (OTHERS: forall _fm (NEQ: _fm <> _fn) (NEQ: _fm <> _fn_ru), p_src _fm = p_tgt _fm)
  :
    match_prog p_src p_tgt
.

End PROG.





(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)
Inductive bindC (r: itr -> itr -> Prop) : itr -> itr -> Prop :=
| bindC_intro
    i_src i_tgt
    (SIM: match_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: (eq ==> r) k_src k_tgt)
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
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - irw. gstep; econs; et. ii. clarify. exploit (MATCH y); eauto. intro R. pclearbot.
    eauto with paco.
  - rewrite ! bind_bind. gstep. erewrite f_equal2; [eapply match_icall_fn|..]; try refl; cycle 1.
    { f. f_equiv. ii. f_equiv. ii. f. instantiate (1:= k_src0 >>> k_src). irw.
      f. f_equiv. ii. f_equiv; eauto. ii.
    match_icall_fn
    econs; eauto. u. ii. clarify. exploit (MATCH y); eauto. intro T. pclearbot.
    (* gfinal. left. eapply CIH. econs. { et. } uh. ii. eapply SIMK. et. *)
    eauto with paco.

    
             (trigger (ICall _fn_ru oh0 m0 vs0) >>= k_src)
             (guarantee (precond oh0 m0 vs0) ;;
              ohmv <- trigger (ICall _fn oh0 m0 vs0) ;;
              assume (postcond oh0 m0 vs0 ohmv) ;;
              k_tgt ohmv
              (*** we can write in point-free style but ***)
              (* trigger (ICall fname oh0 m0 vs0) *)
              (* >>= assumeK (postcond oh0 m0 vs0) *)
              (* >>= k_tgt *)
             )
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
    ii. clarify. exploit (MATCH y); eauto. intro R. pclearbot. eauto with paco.
Qed.

Global Instance match_itr_bind :
  Proper ((eq ==> match_itr) ==> match_itr ==> match_itr) ITree.bind'
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
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.








Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
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
    punfold SIM. inv SIM; cbn.
    - gstep. econs; et.
    - pclearbot. gstep. econs; et. gbase. et.
    - pclearbot. gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind.
      { u. ii. repeat spc MATCH. pclearbot. eauto. }
      exploit (@SIMP fname); et. intro T.
      inv T.
      { pfold. econs; et. }
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
      { pfold. econs; et. }
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
Hint Unfold sim_itr.
Hint Resolve sim_itr_mon: paco.
Hint Constructors bindC: core.
Hint Unfold sim_st.
Hint Resolve sim_st_mon: paco.
