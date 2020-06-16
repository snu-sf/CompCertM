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
Require Import LinkingC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton SimMod SimModSem.
Require Import Sound SoundTop SimMem SimMemId SimSymb.
Require Import SIRCommon2.
Require Import SIRmini.
Require Import SIRmini_stack.
Require Import MatchSimModSemExcl.

Require Import Program.
Require Import SmallstepC.

Set Implicit Arguments.












Import CatNotations.
Open Scope cat_scope.








Section OWNEDHEAP.

Variable owned_heap: Type.
Variable initial_owned_heap: SkEnv.t -> owned_heap.
Variable mi: string.
Variable prog: program owned_heap.





Section SMO.

  Record t: Type :=
    mk {
      sm :> SimMem.t;
      oh_src: Any;
      oh_tgt: Any;
    }
  .

  Inductive wf (smo: t): Prop :=
  | wf_intro
      (oh: owned_heap)
      (MWF: SimMem.wf smo)
      (OHSRC: smo.(oh_src) = upcast oh)
      (OHTGT: smo.(oh_tgt) = upcast oh)
  .

  Local Obligation Tactic := try (by ii; des; ss).

  Program Instance SimMemOh: (SimMemOh.class) :=
    {|
      SimMemOh.t := t;
      SimMemOh.sm := sm;
      SimMemOh.oh_src := oh_src;
      SimMemOh.oh_tgt := oh_tgt;
      SimMemOh.wf := wf;
      SimMemOh.le := SimMem.le;
      SimMemOh.lepriv := SimMem.lepriv;
      SimMemOh.midx := Some mi;
      SimMemOh.set_sm := fun smo sm => mk sm smo.(oh_src) smo.(oh_tgt);
    |}
  .
  Next Obligation.
    ii. eapply PR.
  Qed.
  Next Obligation.
    ii. inv WF.
    econs; ss; et.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.


Section SIMMODSEM.

Variable sk: Sk.t.
Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (SIRmini.module sk prog mi initial_owned_heap).
Let md_tgt: Mod.t := (SIRmini_stack.module sk prog mi initial_owned_heap).
Let ms_src: ModSem.t := (Mod.modsem md_src skenv_link).
Let ms_tgt: ModSem.t := (Mod.modsem md_tgt skenv_link).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).

Local Existing Instance SimMemOh.
Local Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].

Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link)
                                              (SimSymbId.mk md_src md_tgt) sm_link.

Notation ktr :=
  (ktree (eff1 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
.
Notation itr := (itree (eff1 owned_heap) (owned_heap * (mem * val))).

Definition fold_cont (cont: list ktr): ktr :=
  (* List.fold_left (fun s i => s >>> i) cont (id_ _) *)
  List.fold_right (fun i s => i >>> s) (id_ _) cont
.
Hint Unfold fold_cont.

(* Definition merge_events E R (itr: itree (E +' E) R): itree E R := *)
(*   interp ((fun _ e => match e with *)
(*                       | inl1 e => trigger e *)
(*                       | inr1 e => trigger e *)
(*                       end): ((E +' E) ~> itree E)) itr *)
(* . *)
(* Hint Unfold merge_events. *)

(* Definition my_fix (itr1: (itree (eff1 owned_heap) (owned_heap * (mem * val)))): *)
(*   (itree (eff0 owned_heap) (owned_heap * (mem * val))) := *)
(*   merge_events (interp (bimap (interp_program0 prog) (id_ _)) itr1) *)
(* . *)
(* Hint Unfold my_fix. *)

(* Definition my_fix (itr1: (itree (eff1 owned_heap) (owned_heap * (mem * val)))): *)
(*   (itree (eff0 owned_heap) (owned_heap * (mem * val))) := *)
(*   interp_mrec (interp_function prog) itr1 *)
(* . *)
(* Hint Unfold my_fix. *)




Lemma eq_is_bisim: forall E R (t1 t2 : itree E R), t1 = t2 -> t1 ≅ t2.
Proof. ii. clarify. reflexivity. Qed.
Lemma bisim_is_eq: forall E R (t1 t2 : itree E R), t1 ≅ t2 -> t1 = t2.
Proof. ii. eapply bisimulation_is_eq; eauto. Qed.

Inductive match_states (idx: unit): SIRmini.state owned_heap ->
          SIRmini_stack.state owned_heap -> SimMemOh.t -> Prop :=
| match_states_intro
    itr0 cur cont smo0
    itr1
    (FOLD: itr1 = (rvs <- cur ;; (fold_cont cont) rvs))
    (SIM: itr0 = interp_mrec (interp_function prog) itr1)
    (MWF: SimMemOh.wf smo0)
    (SYNC: forall
        oh0 m0 v0
        (RET: itr0 = Ret (oh0, (m0, v0))),
        <<OH: upcast oh0 = smo0.(SimMemOh.oh_src)>> /\ <<MEM: m0 = smo0.(SimMem.src)>>)
  :
    match_states idx itr0 (SIRmini_stack.mk cur cont) smo0
.

Ltac brewrite H := eapply bisim_is_eq; erewrite H; [eapply eq_is_bisim|..].
(* Tactic Notation "sym" "in" hyp(H) := symmetry in H. *)

Ltac f := first [eapply bisim_is_eq|eapply eq_is_bisim].
Tactic Notation "f" "in" hyp(H) := first [eapply bisim_is_eq in H|eapply eq_is_bisim in H].
Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  sym in T; apply simpobs in T; apply bisim_is_eq in T; rewrite T in *; clarify.





Inductive cont_calls sg fptr oh m0 vs (r0: owned_heap * (mem * val)): list ktr -> nat -> Prop :=
| cont_calls_now
    kcall cont_r
    k_tgt
    (KCALL: kcall r0 = Vis ((subevent (owned_heap * (mem * val))) (ECall sg fptr oh m0 vs)) k_tgt)
  :
    cont_calls sg fptr oh m0 vs r0 (kcall :: cont_r) (0%nat)
| cont_calls_later
    kret cont_r r1 n
    (KRET: kret r0 = Ret r1)
    (TL: cont_calls sg fptr oh m0 vs r1 cont_r n)
  :
    cont_calls sg fptr oh m0 vs r0 (kret :: cont_r) (S n) 
.

Lemma unfold_cont_call
      oh sg fptr vs m0
      (k: ktree (eff0 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
      (cont: list ktr)
      (r0: owned_heap * (mem * val))
      (SIM: Vis (subevent (owned_heap * (mem * val)) (ECall sg fptr oh m0 vs)) k
                ≅ interp_mrec (interp_function prog) (fold_cont cont r0))
  :
    exists n, <<CALLS: cont_calls sg fptr oh m0 vs r0 cont n>>
.
Proof.
  clear - SIM.
  { ginduction cont; ii; ss.
    { cbn in SIM. rewrite unfold_interp_mrec in SIM. ss. f in SIM. clarify. }
    cbn in SIM.
    (* unfold id_, Id_Kleisli, lift_ktree_ in *. cbn in SIM. ss. *)
    ides (a r0); autorewrite with itree in SIM.
    + (* RET *)
      exploit IHcont; eauto. i; des.
      exists (S n).
      econs; eauto.
    + (* TAU *)
      rewrite unfold_interp_mrec in SIM. cbn in SIM. f in SIM. clarify.
    + (* VIS *)
      rewrite unfold_interp_mrec in SIM. cbn in SIM. f in SIM.
      des_ifs; clarify; simpl_depind; clarify.
      esplits; eauto.
      econs; eauto.
  }
Qed.





Lemma match_states_lxsim
      idx st_src0 st_tgt0 smo0
      (MATCH: match_states idx st_src0 st_tgt0 smo0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun _ => () -> exists (_ : ()) (_ : mem), True)
                  (Ord.lift_idx unit_ord_wf idx) st_src0 st_tgt0 smo0>>
.
Proof.
  revert_until idx. revert idx.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.


  destruct (classic (ModSem.is_call ms_tgt st_tgt0)).
  { (*** tgt extcall ***)
    rr in H. des. ss. inv H. inv MATCH. ss. clarify.
    econs 3; ss; eauto.
    { rr. esplits; eauto. ss. econs; eauto.
      f.
      rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      f.
      reflexivity.
    }
    ii. clear_tac. inv ATSRC.
    f in VIS.
    rewrite interp_mrec_bind in VIS. rewrite unfold_interp_mrec in VIS.
    cbn in VIS. autorewrite with itree in VIS.
    f in VIS.
    clarify; simpl_depind; clarify.
    inv MWF. ss. destruct smo0; ss. destruct sm0; ss. clarify.
    eexists _, (Args.mk _ _ _), (mk (SimMemId.mk _ _) _ _); ss. esplits; eauto.
    { rr. esplits; ss; eauto. econs; ss; eauto. }
    { econs; ss. }
    { econs; ss. }
    ii. clear_tac.
    inv AFTERSRC. inv GETK. rr in SIMRETV; des; ss.
    inv SIMRETV0; ss. clarify.

    f in VIS.
    rewrite interp_mrec_bind in VIS. rewrite unfold_interp_mrec in VIS.
    cbn in VIS. autorewrite with itree in VIS.
    f in VIS.
    clarify; simpl_depind; clarify.

    assert(RMT: forall E R (t: itree E R), Tau t = t).
    { admit "remove later". }

    esplits; eauto.
    { econs; eauto. econs; eauto. ss. }
    right. eapply CIH. econs; ss; eauto.
    -
      destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify.
      f.
      autorewrite with itree.
      rewrite RMT.
      rewrite RMT.
      rewrite interp_mrec_bind.
      f.
      ss.
    - ii.
      f in RET. autorewrite with itree in RET. f in RET. clarify.
  }
  rename H into NCALLTGT.



  destruct (classic (ModSem.is_return ms_tgt st_tgt0)).
  { (*** tgt return ***)
    rr in H. des. ss. inv H. inv MATCH. ss. clarify.
    econs 4; ss; eauto.
    { econs; eauto.
      f.
      rewrite unfold_interp_mrec. cbn.
      f.
      reflexivity.
    }
    cbn in SYNC. exploit SYNC; et.
    { f. rewrite unfold_interp_mrec. cbn. f. reflexivity. }
    i; des. clarify.
    inv MWF. rewrite <- OH in *. clarify. destruct smo0; ss. destruct sm0; ss. clarify.
    rr; ss. esplits; ss; eauto.
    { econs; ss; eauto. }
  }
  rename H into NRETTGT.



  destruct (classic (ModSem.is_call ms_src st_src0)).
  {
    rr in H. des. ss. inv H. inv MATCH. ss.
    f in SIM.
    rewrite interp_mrec_bind in SIM. rewrite unfold_interp_mrec in SIM.
    ides (cur: itree (InternalCallE owned_heap +' EventE owned_heap) _);
      cbn in SIM; autorewrite with itree in SIM.
    { (* RET *)
      exploit unfold_cont_call; eauto. i; des.
      admit "gogogo with index".
    }
    { (* TAU *)
      f in SIM.
      clarify.
    }
    { (* CALL *)
      des_ifs.
      { autorewrite with itree in SIM. f in SIM. clarify. }
      autorewrite with itree in SIM. f in SIM. clarify; simpl_depind; clarify.
      econs 3; ss; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      ii. clear_tac. inv ATSRC; ss.
      clarify; simpl_depind; clarify.
      inv MWF. ss. destruct smo0; ss. destruct sm0; ss. clarify.
      eexists _, (Args.mk _ _ _), (mk (SimMemId.mk _ _) _ _); ss. esplits; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      { econs; ss. }
      { econs; ss. }
      ii. clear_tac.
      inv AFTERSRC. inv GETK. rr in SIMRETV; des; ss.
      inv SIMRETV0; ss. clarify; simpl_depind; clarify.
      assert(RMT: forall E R (t: itree E R), Tau t = t).
      { admit "remove later". }

      esplits; eauto.
      { econs; eauto. econs; eauto. ss. }
      right. eapply CIH. econs; ss; eauto.
      -
        destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify.
        f.
        autorewrite with itree.
        rewrite RMT.
        rewrite RMT.
        rewrite interp_mrec_bind.
        f.
        ss.
      - ii.
        f in RET. autorewrite with itree in RET. f in RET. clarify.
    }
  }
  rename H into NCALLSRC.



  destruct (classic (ModSem.is_return ms_src st_src0)).
  {
    rr in H. des. ss. inv H. inv MATCH. ss.
    f in SIM.
    rewrite interp_mrec_bind in SIM. rewrite unfold_interp_mrec in SIM.
    ides (cur: itree (InternalCallE owned_heap +' EventE owned_heap) _);
      cbn in SIM; autorewrite with itree in SIM.
    { (* RET *)
      exploit SYNC; eauto. i ;des. clarify.
      
    }
    { (* TAU *)
      f in SIM.
      clarify.
    }
    { (* CALL *)
      des_ifs.
      { autorewrite with itree in SIM. f in SIM. clarify. }
      autorewrite with itree in SIM. f in SIM. clarify; simpl_depind; clarify.
      econs 3; ss; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      ii. clear_tac. inv ATSRC; ss.
      clarify; simpl_depind; clarify.
      inv MWF. ss. destruct smo0; ss. destruct sm0; ss. clarify.
      eexists _, (Args.mk _ _ _), (mk (SimMemId.mk _ _) _ _); ss. esplits; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      { econs; ss. }
      { econs; ss. }
      ii. clear_tac.
      inv AFTERSRC. inv GETK. rr in SIMRETV; des; ss.
      inv SIMRETV0; ss. clarify; simpl_depind; clarify.
      assert(RMT: forall E R (t: itree E R), Tau t = t).
      { admit "remove later". }

      esplits; eauto.
      { econs; eauto. econs; eauto. ss. }
      right. eapply CIH. econs; ss; eauto.
      -
        destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify.
        f.
        autorewrite with itree.
        rewrite RMT.
        rewrite RMT.
        rewrite interp_mrec_bind.
        f.
        ss.
      - ii.
        f in RET. autorewrite with itree in RET. f in RET. clarify.
    }
  }

  assert(NCALLSRC: ~ModSem.is_call ms_src st_src0).
  {
    ii. rr in H. des. ss. inv H. inv MATCH. ss.
    f in SIM.
    rewrite interp_mrec_bind in SIM. rewrite unfold_interp_mrec in SIM.
    ides (cur: itree (InternalCallE owned_heap +' EventE owned_heap) _);
      cbn in SIM; autorewrite with itree in SIM.
    - contradict NCALLTGT. rr. esplits; ss; et. econs; ss; et.
  }



  econs 2; eauto. ii. clear_tac.
  econs 1; eauto; cycle 1.
  { ss. exploit SAFESRC; ss; try eapply star_refl; ss. i. des.
  }
  - ii. ss. inv STEPTGT; ss.
Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  econstructor 1 with (sidx := unit) (sound_states := top4); eauto;
    try apply sound_state_local_preservation; et; try (by ii; ss).
  { ii. eapply Preservation.local_preservation_noguarantee_weak.
    apply sound_state_local_preservation; et.
  }
  { ii. ss. eexists (mk _ _ _); ss. esplits; eauto. econs; ss; eauto. }
  ii. ss. esplits; eauto.
  - ii. des. esplits; eauto. eapply match_states_lxsim; eauto.
    admit "".
  - admit "".
Qed.









Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with
      (match_states := match_states) (match_states_at := top4)
      (has_footprint := top3) (mle_excl := fun _ _ => SimMemOh.le) (sidx := unit)
      (order:= bot2);
    eauto; ii; ss; folder.
  - eapply SoundTop.sound_state_local_preservation; et.
  - des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
    rr in SIMARGS. des. ss.  inv SIMARGS0; ss. clarify.
    assert(fid = fid0).
    { apply_all_once Genv.find_invert_symbol. clarify. }
    clarify.
    esplits; eauto.
    { econs; eauto. ss. }
    ss.
    econs; eauto.
    + cbn. unfold interp_program0, mrec. cbn.
      Fail brewrite bind_ret_r. (*** <---- TODO: fix this !!!!!!!!! ***)
      eapply bisim_is_eq; erewrite bind_ret_r; [eapply eq_is_bisim|..].
      inv MWF. destruct sm_arg; ss. destruct sm0; ss.
      rewrite OHSRC0 in *. rewrite OHTGT0 in *. clarify.
  - des. inv SAFESRC. ss. des_ifs.
    rr in SIMARGS. des. ss.  inv SIMARGS0; ss. clarify. inv MWF. destruct sm_arg; ss.
    esplits; eauto.
    econs; ss; eauto.
  - inv MATCH. ss.
  - inv MATCH. ss. inv CALLSRC.
    eapply eq_is_bisim in VIS; erewrite interp_mrec_bind in VIS; eapply bisim_is_eq in VIS.

    (********* TGT SHOULD TAKE SOME TAU STEPS *********)
    destruct (observe cur) eqn:T; sym in T; apply simpobs in T; apply bisim_is_eq in T; clarify.
    { cbn in *.
      eapply eq_is_bisim in VIS.
      rewrite unfold_interp_mrec in VIS. cbn in VIS.
      autorewrite with itree in VIS.
    }
      unfold interp_mrec in VIS at 2. cbn in VIS.
      Erewrite  in VIS; eapply bisim_is_eq in VIS.
    esplits; eauto.
    + econs; ss; eauto.
    
    exploit eq_itree_inv_vis; eauto.
    { }
    destruct (observe (interp_mrec (interp_function prog) cur)) eqn:T.
    + rewrite itree_eta_ in VIS at 1. cbn in VIS.
      unfold_bind
        simpobs
      rewrite itree_eta in VIS.
      Set Printing All. rewrite T in VIS.
    esplits; eauto.
    + econs; ss; eauto.
Qed.

End SIMMODSEM.





Section SIMMOD.

(* Variable prog: program owned_heap. *)
(* Variable mi: string. *)

(* Definition mp: ModPair.t := SimSymbId.mk_mp (SIR0.module prog mi initial_owned_heap) *)
(*                                             (SIR2.module prog mi initial_owned_heap). *)

(* Theorem sim_mod: ModPair.sim mp. *)
(* Proof. *)
(*   econs; ss. *)
(*   - ii. inv SIMSKENVLINK. eexists. eapply sim_modsem; eauto. *)
(* Qed. *)

End SIMMOD.

End OWNEDHEAP.
