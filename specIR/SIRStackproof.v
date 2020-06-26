From Coq Require Import
     Arith.PeanoNat
     (* Strings.String *)
     Lists.List
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
Require Import SIRCommon.
Require Import SIR.
Require Import SIRStack.

Require Import Program.
Require Import SmallstepC.

Set Implicit Arguments.







Section OWNEDHEAP.

Variable owned_heap: Type.
Variable initial_owned_heap: SkEnv.t -> owned_heap.
Variable sk: Sk.t.
Variable prog: program owned_heap.
Variable mi: string.





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

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (SIR.module sk prog mi initial_owned_heap).
Let md_tgt: Mod.t := (SIRStack.module sk prog mi initial_owned_heap).
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




Inductive match_states (idx: nat): SIR.state owned_heap ->
          SIRStack.state owned_heap -> SimMemOh.t -> Prop :=
| match_states_intro
    itr0 cur cont smo0
    itr1
    (FOLD: itr1 = (rvs <- cur ;; (fold_cont cont) rvs))
    (SIM: itr0 = interp_mrec (interp_function prog) itr1)
    (MWF: SimMemOh.wf smo0)
    (IDX: (idx >= 2 + List.length cont)%nat)
  :
    match_states idx itr0 (SIRStack.mk cur cont) smo0
.





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
      des_ifs; csc.
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
                  (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 smo0>>
.
Proof.
  revert_until idx. revert idx.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.



  destruct (classic (ModSem.is_call ms_src st_src0)).
  { (*** src extcall ***)
    rr in H. des. ss. inv H. inv MATCH. ss.
    f in SIM.
    rewrite interp_mrec_bind in SIM. rewrite unfold_interp_mrec in SIM.
    ides cur; cbn in SIM; autorewrite with itree in SIM.
    { (* RET *)
      destruct cont; ss.
      { cbn in SIM. rewrite unfold_interp_mrec in SIM. cbn in SIM. f in SIM. clarify. }
      destruct r0 as [oh0 [m v]]; ss.
      econs 1. ii. clear_tac. econs 2; try refl; eauto.
      { esplits; eauto.
        - eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { split; ss.
            { eapply modsem_determinate; ss; et. }
            instantiate (1:= SIRStack.mk _ _).
            eapply step_return; ss; et.
          }
          apply star_refl.
        - eapply Ord.lift_idx_spec; et.
      }

      right. eapply CIH. econs; ss; eauto.
      f. rewrite SIM. cbn. f. ss.
    }
    (* { (* RET *) *)
    (*   exploit unfold_cont_call; eauto. i; des. *)
    (*   ginduction CALLS; ii; ss. *)
    (*   { cbn in *. rewrite interp_mrec_bind in SIM. rewrite KCALL in *. *)
    (*     rewrite unfold_interp_mrec in SIM. cbn in SIM. *)
    (*     autorewrite with itree in SIM. *)
    (*     f in SIM. csc. *)
    (*     (* assert(pair_eta: forall X Y (xy: X * Y), xy = (fst xy, snd xy)). *) *)
    (*     (* { i. destruct xy; ss. } *) *)
    (*     (* assert(ETA: r0 = (fst r0, (fst (snd r0), (snd (snd r0))))). *) *)
    (*     (* { rewrite <- ! pair_eta. ss. } *) *)
    (*     destruct r0 as [oh0 [m v]]; ss. *)
    (*     econs 1. ii. clear_tac. econs 2; try refl; eauto. *)
    (*     { esplits; eauto. *)
    (*       - eapply plus_left with (t1 := E0) (t2 := E0); ss. *)
    (*         { split; ss. *)
    (*           { eapply modsem_determinate; ss; et. } *)
    (*           instantiate (1:= SIRStack.mk _ _). *)
    (*           eapply step_return; ss; et. *)
    (*         } *)
    (*         apply star_refl. *)
    (*       - eapply Ord.lift_idx_spec; et. *)
    (*     } *)

    (*     right. eapply CIH. econs; ss; eauto. *)
    (*     - rewrite KCALL. f. *)
    (*       autorewrite with itree. rewrite unfold_interp_mrec. cbn. *)
    (*       (* rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. *) *)
    (*       Ltac f_equiv := *)
    (*         first [eapply eutt_eq_bind|eapply eqit_VisF|eapply eqit_bind'|Morphisms.f_equiv]. *)
    (*       f_equiv. *)
    (*       ii. *)
    (*       autorewrite with itree. *)
    (*       f_equiv. f_equiv. *)
    (*       rewrite interp_mrec_bind. *)
    (*       f. ss. *)
    (*   } *)
    (*   move IHCALLS at top. *)

    (*   cbn in SIM. rewrite interp_mrec_bind in SIM. rewrite KRET in SIM. *)
    (*   rewrite unfold_interp_mrec in SIM. cbn in SIM. *)
    (*   autorewrite with itree in SIM. *)
    (*   exploit IHCALLS; eauto. i; des. *)

    (*       econs. *)
    (*       autorewrite with itree. *)
    (*       destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify. *)
    (*       f. *)
    (*       autorewrite with itree. *)
    (*       rewrite interp_mrec_bind. *)
    (*       f. *)
    (*       ss. *)


    (*     econs 3; eauto. *)
    (*     { rr. esplits; ss; eauto. econs; ss; eauto. } *)
    (*     ii; ss. clear_tac. inv ATSRC. csc. *)

    (*     eexists _, (Args.mk _ _ _), (mk (SimMemId.mk _ _) _ _); ss. esplits; eauto. *)
    (*     { rr. esplits; ss; eauto. econs; ss; eauto. } *)
    (*     { econs; ss. } *)
    (*     { econs; ss. } *)
    (*     ii. clear_tac. *)
    (*     inv AFTERSRC. inv GETK. rr in SIMRETV; des; ss. *)
    (*     inv SIMRETV0; ss. csc. *)

    (*     eexists _, _, (Ord.lift_idx lt_wf (S idx)); ss. *)
    (*     esplits; eauto. *)
    (*     { econs; eauto. econs; eauto. ss. } *)
    (*     left. pfold. ii. clear SUSTAR. econs 2. ii. clear_tac. econs 2; try refl; eauto. *)
    (*     { esplits; eauto. *)
    (*       - apply star_one. econs; ss; eauto. *)
    (*         f. autorewrite with itree. f. eauto. *)
    (*       - eapply Ord.lift_idx_spec; et. *)
    (*     } *)
    (*     right. eapply CIH. econs; ss; eauto. *)
    (*     - *)
    (*       destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify. *)
    (*       f. *)
    (*       autorewrite with itree. *)
    (*       rewrite interp_mrec_bind. *)
    (*       f. *)
    (*       ss. *)


    (*     esplits; eauto. *)
    (*     { rr. esplits; eauto. *)
    (*     autorewrite with itree in SIM. cbn in *. *)
    (*   } *)
    (*   admit "gogogo with index". *)
    (* } *)
    { (* TAU *)
      f in SIM.
      clarify.
    }
    { (* CALL *)
      des_ifs.
      { autorewrite with itree in SIM. f in SIM. clarify. }
      autorewrite with itree in SIM. f in SIM. csc.
      econs 3; ss; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      ii. clear_tac. inv ATSRC; ss.
      csc.
      inv MWF. ss. destruct smo0; ss. destruct sm0; ss. clarify.
      eexists _, (Args.mk _ _ _), (mk (SimMemId.mk _ _) _ _); ss. esplits; eauto.
      { rr. esplits; ss; eauto. econs; ss; eauto. }
      { econs; ss. }
      { econs; ss. }
      ii. clear_tac.
      inv AFTERSRC. inv GETK. rr in SIMRETV; des; ss.
      inv SIMRETV0; ss. csc.

      eexists _, _, (Ord.lift_idx lt_wf (S idx)); ss.
      esplits; eauto.
      { econs; eauto. econs; eauto. ss. }
      left. pfold. ii. clear SUSTAR. econs 2. ii. clear_tac. econs 2; try refl; eauto.
      { esplits; eauto.
        - apply star_one. econs; ss; eauto.
          f. autorewrite with itree. f. eauto.
        - eapply Ord.lift_idx_spec; et.
      }
      right. eapply CIH. econs; ss; eauto.
      -
        destruct smo_ret; ss. inv MWF; ss. clarify. destruct sm0; ss. clarify.
        f.
        autorewrite with itree.
        rewrite interp_mrec_bind.
        f.
        ss.
    }
  }
  rename H into NCALLSRC.


  destruct (classic (ModSem.is_return ms_src st_src0)).
  { (*** src return ***)
    rr in H. des. ss. inv H. inv MATCH. ss.
    f in SIM.
    rewrite interp_mrec_bind in SIM. rewrite unfold_interp_mrec in SIM.
    ides cur; cbn in SIM; autorewrite with itree in SIM.
    { (* RET *)
      destruct r0 as [oh0 [m v]]; ss. unfold id in *. clarify.
      inv MWF. inv MWF0. destruct smo0; ss. destruct sm0; ss. clarify.

      destruct cont; ss.
      { cbn in SIM. rewrite unfold_interp_mrec in SIM. cbn in SIM. f in SIM. clarify.
        econstructor 4 with (smo_ret := mk (SimMemId.mk m m) (upcast oh0) (upcast oh0)); ss; eauto.
        { econs; ss; et. }
        { econs; ss; et. }
        { rr; ss. esplits; ss; et. econs; ss; et. }
      }

      econs 1. ii. clear_tac. econs 2; try refl; eauto.
      { esplits; eauto.
        - eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { split; ss.
            { eapply modsem_determinate; ss; et. }
            instantiate (1:= SIRStack.mk _ _).
            eapply step_return; ss; et.
          }
          apply star_refl.
        - eapply Ord.lift_idx_spec; et.
      }

      right. eapply CIH. econs; ss; eauto.
      { f. rewrite SIM. cbn. f. ss. }
      { econs; ss; et. }
    }
    { (* TAU *)
      f in SIM. clarify.
    }
    { (* VIS *)
      des_ifs; autorewrite with itree in SIM; f in SIM; clarify.
    }
  }
  rename H into NRETSRC.



  econs 2; eauto. ii. clear_tac.
  econs 1; eauto; cycle 1.
  { (* bsim progress *)
    ss. exploit SAFESRC; ss; try eapply star_refl; ss. i; des; ModSem.tac.
    inv MATCH. ss.
    ides cur.
    - (* RET *)
      destruct r0 as [oh0 [m v]]; ss.
      destruct cont; ss.
      { contradict NRETSRC. rr; ss. esplits; et. econs; et.
        f. autorewrite with itree. rewrite unfold_interp_mrec. cbn. f. ss. }
      esplits; et.
      eapply step_return; ss; et.
    - (* TAU *)
      esplits; et. esplits; et. econs; ss; et.
    - (* VIS *)
      (* remember (interp_mrec (interp_function prog) *)
      (*           (` rvs : owned_heap * (mem * val) <- Vis e k;; fold_cont cont rvs)) as st0. *)
      (* depdes EVSTEP; ss; clarify. *)
      inv EVSTEP; ss.
      + (* SRCTAU *)
        f in TAU. autorewrite with itree in TAU. rewrite unfold_interp_mrec in TAU. cbn in TAU.
        f in TAU. des_ifs; simpl_depind.
        destruct i; ss.
        esplits; et. eapply step_call; ss; et.
      + (* SRCNB *)
        f in VIS. rewrite interp_mrec_bind in VIS. rewrite unfold_interp_mrec in VIS. cbn in VIS.
        des_ifs; autorewrite with itree in VIS; f in VIS; csc.
        esplits; eauto. eapply step_nb; ss; et.
      + (* SRCCHOOSE *)
        f in VIS. rewrite interp_mrec_bind in VIS. rewrite unfold_interp_mrec in VIS. cbn in VIS.
        des_ifs; autorewrite with itree in VIS; f in VIS; csc.
        esplits; eauto. eapply step_choose; ss; et.
  }
  inv MATCH; ss. ii; ss.
  inv STEPTGT.
  - (* TGTTAU *)
    ss; clarify.
    esplits; ss; et.
    + left. apply plus_one. eapply SIR.step_tau; ss; et. f.
      rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      f. ss.
    + right. eapply CIH. econs; ss; et.
      f. rewrite interp_mrec_bind. f. ss.
  - (* TGTNB *)
    ss; clarify.
    esplits; ss; et.
    + left. apply plus_one. eapply SIR.step_nb; ss; et. f.
      rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      f. ss.
    + right. eapply CIH. econs; ss; et.
  - (* TGTCHOOSE *)
    ss; clarify.
    exists (Ord.lift_idx lt_wf (S idx)). esplits; ss; et.
    + left. apply plus_one. eapply SIR.step_choose; ss; et. f.
      rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      f. ss.
    + left. pfold. ii. clear SUSTAR. econs 2. ii. clear_tac. econs 2; try refl; eauto.
      { esplits; eauto.
        - apply star_one. econs; ss; eauto.
          f. autorewrite with itree. f. eauto.
        - eapply (Ord.lift_idx_spec lt_wf); et.
      }
      right. eapply CIH. econs; ss; et.
      f. rewrite interp_mrec_bind. autorewrite with itree. f. ss.
  - (* TGTCALL *)
    ss; clarify.
    esplits; ss; et.
    + left. apply plus_one. eapply SIR.step_tau; ss; et. f.
      rewrite interp_mrec_bind. rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      f. ss.
    + right. eapply CIH. econs; ss; et.
      f. rewrite interp_mrec_bind. autorewrite with itree. cbn.
      rewrite interp_mrec_bind.
      f_equiv. ii. ss.
      rewrite interp_mrec_bind. f. ss.
  - (* TGTRET *)
    ss; clarify.
    esplits; ss; et.
    + right. esplits; et.
      { apply star_refl. }
      { eapply Ord.lift_idx_spec; et. }
    + right. eapply CIH. econs; ss; et. cbn.
      f. rewrite interp_mrec_bind. rewrite interp_mrec_bind.
      rewrite unfold_interp_mrec. cbn. autorewrite with itree.
      rewrite interp_mrec_bind. f. ss.
  Unshelve.
    all: ss.
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
  - ii. des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
    esplits; eauto.
    { econs; ss; et. }
    eapply match_states_lxsim; eauto.
    econs; ss; et.
    f. unfold interp_program. unfold mrec. cbn. autorewrite with itree. f.
    rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. destruct sm0; ss. clarify.
    inv MWF; ss. clarify.
    apply_all_once Genv.find_invert_symbol. clarify.
  - i; des. inv SAFESRC. ss. des_ifs.
    rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. destruct sm0; ss. clarify.
    esplits; et. econs; ss; et.
Qed.

End SIMMODSEM.

Section SIMMOD.

Definition mp: ModPair.t := SimSymbId.mk_mp (SIR.module sk prog mi initial_owned_heap)
                                            (SIRStack.module sk prog mi initial_owned_heap).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. eexists. eapply sim_modsem; eauto.
Qed.

End SIMMOD.

End OWNEDHEAP.
