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
    ohmv
  :
    _match_itr match_itr (Ret ohmv) (Ret ohmv)
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
    (INHAB: inhabited X)
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr
               (tau;; (Vis (subevent _ (EChoose X)) k_src))
               (tau;; (Vis (subevent _ (EChoose X)) k_tgt))
.

Definition match_itr: itr -> itr -> Prop := paco2 _match_itr bot2.
Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try (by econs; et; rr; et).
Qed.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.





Section PROG.

(* Definition fn_src_ignorant (oh0: owned_heap) (m0: mem) (vs0: list val): itree (E owned_heap) (owned_heap * (mem * val)) := *)
(*   assume (precond oh0 m0 vs0) ;; *)
(*   _I_DONT_USE_THIS__RUDIMENT_ORGAN_ <- trigger (ICall _fn_ru oh0 m0 vs0) ;; *)
(*   trigger (EChoose { ohmv: (owned_heap * (mem * val)) | postcond oh0 m0 vs0 ohmv }) >>= (fun x => Ret (proj1_sig x)) *)
(* . *)

Definition fn_src (oh0: owned_heap) (m0: mem) (vs0: list val): itree (E owned_heap) (owned_heap * (mem * val)) :=
  assume (precond oh0 m0 vs0) ;;
  trigger (ICall _fn_ru oh0 m0 vs0)
  >>= guaranteeK (postcond oh0 m0 vs0)
.

Inductive match_fn_focus (fn_ru fn_tgt: function owned_heap): Prop :=
| match_fn_intro
    fn_tgt_inner
    (SIM: (eq ==> eq ==> eq ==> match_itr) fn_ru fn_tgt_inner)
    (TGT: fn_tgt = fun oh0 m0 vs0 =>
                     assume (precond oh0 m0 vs0) ;;
                     (fn_tgt_inner oh0 m0 vs0)
                     >>= guaranteeK (postcond oh0 m0 vs0)
    )
.

Definition match_fn (fn_src fn_tgt: function owned_heap): Prop :=
  (eq ==> eq ==> eq ==> match_itr) fn_src fn_tgt
.

Inductive match_prog (p_src p_tgt: program owned_heap): Prop :=
| match_prog_intro
    fn_ru (* rudiment *) fn_tgt
    (FNSRC: p_src _fn = Some fn_src)
    (FNTGT: p_tgt _fn = Some fn_tgt)
    (RDSRC: p_src _fn_ru = Some fn_ru)
    (RDTGT: p_tgt _fn_ru = None)
    (FOCUS: match_fn_focus fn_ru fn_tgt)
    (OTHERS: forall _fm (NEQ: _fm <> _fn) (NEQ: _fm <> _fn_ru),
        option_rel match_fn (p_src _fm) (p_tgt _fm))
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
    erewrite f_equal2; try eapply match_icall_fn; try refl; cycle 1.
    { irw. f. f_equiv. ii. f_equiv. ii. f. irw. refl. }
    ii. clarify.
    repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. ii. clarify.
    repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto.
  - gstep. irw. econsr; ss. ii. clarify.
    repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. eauto with paco.
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





Ltac step := gstep; econs; et.
Ltac step_guarantee := match goal with
                    | |- context[guarantee ?P ;; _] =>
                      (*** I want to unfold only the "first" guarantee.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                      first[
                          unfold guarantee at 5|
                          unfold guarantee at 4|
                          unfold guarantee at 3|
                          unfold guarantee at 2|
                          unfold guarantee at 1|
                          unfold guarantee at 0
                        ];
                      let name := fresh "T" in
                      destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
                        unfold triggerNB; rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
                        try step|]
                    end
.
Ltac step_assume := match goal with
                    | |- context[assume ?P ;; _] =>
                      (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                      first[
                          unfold assume at 5|
                          unfold assume at 4|
                          unfold assume at 3|
                          unfold assume at 2|
                          unfold assume at 1|
                          unfold assume at 0
                        ];
                      let name := fresh "T" in
                      destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
                        unfold triggerUB; rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
                        try step|]
                    end
.
Ltac step_guaranteeK := match goal with
                        | |- context[guaranteeK ?P ;; _] =>
                          (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                          first[
                              unfold guaranteeK at 5|
                              unfold guaranteeK at 4|
                              unfold guaranteeK at 3|
                              unfold guaranteeK at 2|
                              unfold guaranteeK at 1|
                              unfold guaranteeK at 0
                            ];
                          destruct (ClassicalDescription.excluded_middle_informative P); cycle 1
                        | |- context[guaranteeK ?P ?Q] =>
                          (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                          first[
                              unfold guaranteeK at 5|
                              unfold guaranteeK at 4|
                              unfold guaranteeK at 3|
                              unfold guaranteeK at 2|
                              unfold guaranteeK at 1|
                              unfold guaranteeK at 0
                            ];
                          destruct (ClassicalDescription.excluded_middle_informative (P Q)); cycle 1
                        end
.



Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
  Hypothesis (SIMP: match_prog p_src p_tgt).
  (* Hypothesis (WFSRC: wf_prog p_src). *)

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
    - gstep. destruct ohmv as [oh [m v]]. econs; et.
    - gstep. econs; et. gbase. pclearbot. et.
    - gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind; et.
      { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
      inv SIMP.
      exploit OTHERS; et. intro T. inv T.
      { pfold. econs; et. }
      exploit H1; et.
    - step_guarantee. irw. step.
      rewrite <- ! unfold_interp_mrec.
      gbase. eapply CIH.
      inv SIMP.
      des_ifs_safe. inv FOCUS. irw.
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
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh
    ,
      (<<SIM: sim_st bot2 tt (interp_program p_src (ICall fname oh m vs))
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
        irw. des_ifs. inv FOCUS.
        unfold fn_src. cbn.
        unfold assume. des_ifs; cycle 1.
        { irw. pfold. unfold triggerUB. irw. econs; et. }
        rewrite ! bind_ret_l.
        irw.
        assert(tau: forall E R (a: itree E R), (tau;; a) = a).
        { admit "backdoor --- relax sim_st to allow tau* before each progress". }
        rewrite tau. des_ifs.
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
      exploit OTHERS; et. intro T.
      inv T; ss.
      { pfold. econs; et. }
      exploit H1; et.
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
    { eapply unit_ord_wf. }
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
