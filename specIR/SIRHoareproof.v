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



Inductive is_finite {E : Type -> Type} {t : Type} : itree E t -> Prop :=
| is_finite_ret {x}: is_finite (Ret x)
| is_finite_tau {tr} (TL: is_finite tr): is_finite (Tau tr)
| is_finite_vis {u e k} {x: u} (TL: is_finite (k x)): is_finite (Vis e k).

Inductive wf_prog owned_heap (p: program owned_heap): Prop :=
| wf_prog_intro
    (WF: forall
        fname fn
        (SOME: p fname = Some fn)
      ,
        <<RET: forall oh m vs, is_finite (fn oh m vs)>>)
.

Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.
Variable _fn _fn_ru: ident.
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
    _match_itr match_itr (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_src)
               (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_tgt)
| match_icall_fn
    oh0 m0 vs0 k_src k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr (trigger (ICall _fn_ru oh0 m0 vs0) >>= k_src)
               (guarantee (precond oh0 m0 vs0) ;;
                ohmv <- trigger (ICall _fn oh0 m0 vs0) ;;
                assume (postcond oh0 m0 vs0 ohmv) ;;
                k_tgt ohmv
               )
| match_ecall
    sg oh m vs fptr
    k_src
    k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr (Vis (subevent _ (ECall sg fptr oh m vs)) k_src)
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
    _match_itr match_itr (Vis (subevent _ (EChoose X)) k_src)
              (Vis (subevent _ (EChoose X)) k_tgt)
.

Definition match_itr: itr -> itr -> Prop := paco2 _match_itr bot2.
Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try econs; et; rr; et.
  des. esplits; et.
Unshelve.
Qed.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.

Hint Constructors match_itr.

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





Global Instance match_itr_bind :
  Proper ((eq ==> match_itr) ==> match_itr ==> match_itr) ITree.bind'
.
Proof.
  red. ii.
  gen x y.
  induction H0 using match_itr_ind; i; try (by irw; et; econs; et; ii; eapply H; et).
  - rewrite ! bind_bind.
    erewrite f_equal2; try eapply match_icall_fn; try reflexivity; revgoals.
    { irw. f. f_equiv. ii. f_equiv. ii. f. rewrite bind_bind. reflexivity. }
    ii. clarify. et.
Qed.

(* Global Instance match_itr_bind_strong : *)
(*   Proper ((eq ==> (match_itr \2/ eq)) ==> (match_itr \2/ eq) ==> (match_itr \2/ eq)) ITree.bind' *)
(* . *)
(* Proof. *)
(*   red. ii. *)
(*   gen x y. *)
(*   des. *)
(*   { *)
(*     induction H0 using match_itr_ind; i; try (by irw; et; econs; et; ii; eapply H; et). *)
(*     - ii. irw; et. exploit IHmatch_itr; et. intro T. des. *)
(*       + left. econs; et. *)
(*       + right. do 2 f_equal; et. *)
(*     - left. irw. econs; et. ii. clarify. exploit H; et. intro T. instantiate (1:= y0) in T. des; ss. *)
(*       ii. irw; et. exploit H; et. intro T. des. *)
(*       + left. econs; et. ii. clarify. instantiate (1:= y0) in T. eapply T. *)
(*       + right. do 2 f_equal; et. *)
(*     - *)
(*     - rewrite ! bind_bind. *)
(*       erewrite f_equal2; try eapply match_icall_fn; try reflexivity; revgoals. *)
(*       { irw. f. f_equiv. ii. f_equiv. ii. f. rewrite bind_bind. reflexivity. } *)
(*       ii. clarify. et. *)
(*   } *)
(* Qed. *)

End SYNTAX.
Hint Constructors match_itr.








Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
  Hypothesis (SIMP: match_prog p_src p_tgt).
  (* Hypothesis (WFSRC: wf_prog p_src). *)

  Lemma sim_prog_sim_st
        i_src i_tgt
        (SIM: match_itr i_src i_tgt \/ i_src = i_tgt)
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
    des; cycle 1.
    { clarify.
      gstep.
      Hint Unfold E. u. (*** <-- TODO: remove E, or use as a notation, or ... ***)
      ides i_tgt.
      (* destruct (observe i_tgt) eqn:T; u in T; rewrite T; cbn. *)
      - destruct r0; ss. destruct p; ss. econs; et.
      - econs; et. gbase. et.
      - cbn. des_ifs.
        + econs; et. gbase. eapply CIH.
          destruct i.
          destruct (eq_block name _fn).
          { clarify. unfold interp_function. inv SIMP. cbn. des_ifs_safe.
            inv SIMFN. left. eapply match_itr_bind; et.
            { ii. clarify. rename k into kk.
              admit "". }
            { admit "". }
          }
          destruct (eq_block name _fn_ru).
          {
            admit "".
          }
          right. f_equal.
    }
    inv SIM; cbn.
    - gstep. econs; et.
    - gstep. econs; et. gbase. et.
    - gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind; et.
      inv SIMP.
      exploit OTHERS; et. intro T. des_ifs; cycle 1.
      { econs; et. }
      econs; et.

      eapply CIH. eapply match_itr_bind.
      { u. ii. repeat spc MATCH. pclearbot. eauto. }

      exploit (@MATCH fname); et. intro T.
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
      (fname: ident) m vs oh
    ,
      (<<SIM: sim_st (interp_program p_src (ICall fname oh m vs))
                     (interp_program p_tgt (ICall fname oh m vs))
                     >>)
  .
  Proof.
    {
      ginit.
      { intros. eapply cpn2_wcompat; et. eauto with paco. }
      gcofix CIH.
      ii. inv SIMP.
      destruct (eq_block fname _fn).
      {
        unfold interp_program, interp_function, mrec. irw.
        clarify. des_ifs_safe.
        unfold fn_src.
        admit "".
      }
      destruct (eq_block fname _fn_ru).
      {
        unfold interp_program, interp_function, mrec. irw.
        clarify. des_ifs_safe.
        gstep. econs.
      }
      unfold interp_program, interp_function, mrec. irw.
      exploit OTHERS; et. intro T. rewrite <- T. des_ifs; irw; cycle 1.
      { gstep. econs; et. }
      gcofix CIH0.
      (*** TODO: FIXIT. Maybe by removing "E" and "eff1" // changing to notation ***)
      Check ((observe (f oh m vs)): itree' (E owned_heap) (owned_heap * (mem * val))).
      remember (@observe (sum1 (InternalCallE owned_heap) (sum1 (ExternalCallE owned_heap) EventE)) _ (f oh m vs)) as itr in *.
      u.
      remember (observe (f oh m vs)) as itr in *.
      gcofix CIH0.
      gfinal. right. clear_until CIH. pcofix CIH2.
      revert_until CIH. pcofix CIH2.
      gstep. econs.
      irw.
      des_ifs_safe. gstep.
    }
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
