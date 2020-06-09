Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSemExcl.
Require SoundTop.
Require SimMemId.
Require Import Clightdefs.
Require Import CtypesC.
Require Import Any.
Require Import SIRmini_eutt.
Require Import IterSource.
Require Import IterTarget.
Require Import ModSemProps.

Set Implicit Arguments.

Local Existing Instance SimMemOh_default.
Local Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].



(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)
(********* TODO: try the same proof with extension ***************)

Inductive taus E R: itree E R -> nat -> Prop :=
| taus_tau
    itr0 n
    (TL: taus itr0 n)
  :
    taus (Tau itr0) (1 + n)
| taus_ret
    r
  :
    taus (Ret r) 0
| taus_vis
    X (e: E X) k
  :
    taus (Vis e k) 0
.

Definition mtaus E R (itr: itree E R) (n: nat): Prop :=
  taus itr n /\ ~taus itr (S n)
.

Theorem case_analysis
        E R
        (itr: itree E R)
  :
    (<<TAUS: exists (m: nat), (m > 0)%nat /\ mtaus itr m>>)
    \/ (<<DIVERGE: forall m, ~mtaus itr m>>)
    \/ (<<CALL: exists X (e: E X) k, itr = Vis e k>>)
    \/ (<<RET: exists r, itr = Ret r>>)
.
Proof.
  destruct (classic (exists m, (m > 0)%nat /\ mtaus itr m)); et.
  destruct (classic (mtaus itr 0)); et.
  - destruct (observe itr) eqn:T; ss; et.
    + sym in T. apply simpobs in T. apply bisimulation_is_eq in T.
      subst. right. right. right. et.
    + sym in T. apply simpobs in T. apply bisimulation_is_eq in T.
      subst. inv H0. inv H1.
    + sym in T. apply simpobs in T. apply bisimulation_is_eq in T.
      subst. right. right. left. et.
  - right. left.
    ii. 
    eapply Classical_Pred_Type.not_ex_all_not with (n:=m) in H. Psimpl.
    des; et. destruct m; ss. xomega.
Qed.

Lemma eq_eutt
      E R
      (a b: itree E R)
      (EQ: a = b)
  :
    eutt eq a b
.
Proof. i. clarify. refl. Qed.

Lemma vis_not_ret
      E R (r: R) X (e: E X) k
      (EUTT: Vis e k ≈ Ret r)
  :
    False
.
Proof. ii. punfold EUTT. inv EUTT. Qed.






Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (IterSource.module).
Let md_tgt: Mod.t := (IterTarget.module).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Let INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt).
Proof. ss. Qed.
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Let sk_same: (CSk.of_program signature_of_function IterTarget.prog) =
             (Sk.of_program (fn_sig (owned_heap:=owned_heap)) IterSource.prog).
Proof.
  (*** TODO: generalize lemma and replace CshmgenproofC? ***)
  unfold CSk.of_program, Sk.of_program. ss.
Qed.

Lemma unsymb
      fid fblk
      (FID: Genv.find_symbol ge fid = Some fblk)
  :
    <<FID: fid = _iter>>
.
Proof.
  subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs.
  unfold defs in *. des_sumbool. ss. des; ss.
  (*** TODO: strengthen "spec" !!!!!!!!!!! ***)
  (*** TODO: strengthen "spec" !!!!!!!!!!! ***)
  (*** TODO: strengthen "spec" !!!!!!!!!!! ***)
  (* exploit (SkEnv.project_impl_spec); et. intro SPEC. *)
  (* inv SPEC. *)
  (* exploit (SYMBKEEP _iter); et. intro T. ss. folder. rewrite <- T in *. *)
  (* exploit DEFKEEP; et. *)
  (* assert(defs (md_src: Sk.t) _iter). *)
  (* { ss. } *)
  (* ss. *)
Qed.

Lemma symb_def
      fblk
      (SYMB: Genv.find_symbol ge _iter = Some fblk)
  :
    <<DEF: Genv.find_funct tge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal f_iter)>>
.
Proof.
  exploit (SkEnv.project_impl_spec); try apply INCLSRC. intro SPECSRC.
  exploit (SkEnv.project_impl_spec); try apply INCLTGT. intro SPECTGT.
  des.
  exploit SkEnv.project_revive_precise; et.
  { unfold md_tgt in SPECTGT. ss. rewrite sk_same in *.
    (* instantiate (1:= (SkEnv.project skenv_link *)
    (*              (Sk.of_program (fn_sig (owned_heap:=owned_heap)) IterSource.prog))). *)
    (* instantiate (3:= skenv_link). *)
    (* instantiate (2:= (fn_sig (owned_heap:=owned_heap))). *)
    (* instantiate (1:= IterSource.prog). *)
    Fail eapply SPECTGT.
    admit "universe".
  }
  { unfold md_tgt in INCLTGT. ss. rewrite sk_same in *. Fail eapply INCLTGT. admit "universe". }
  i. inv H.
  assert((prog_defmap IterTarget.prog) ! _iter = Some (Gfun (Internal f_iter))).
  { ss. }
  exploit P2GE; et.
  { Fail eapply H.
    admit "maybe universe". }
  admit "giveup".
Unshelve.
  all: admit "giveup".
Qed.

Inductive match_states_internal: SIRmini_eutt.state owned_heap -> Clight.state -> Prop :=
| match_initial
    itr0 ty m0 vs
    fid fblk fptr_tgt
    (SYMB: Genv.find_symbol ge fid = Some fblk)
    (FPTR: fptr_tgt = (Vptr fblk Ptrofs.zero))
    (ITR: itr0 = interp_program0 IterSource.prog (ICall fid tt m0 vs))
    (TY: ty = Clight.type_of_fundef (Internal f_iter))
  :
    match_states_internal (SIRmini_eutt.State itr0)
                          (Clight.Callstate fptr_tgt ty vs Kstop m0)
| match_final
    itr0 m0 v
    (RET: itr0 = Ret (tt, (m0, v)))
  :
    match_states_internal (SIRmini_eutt.State itr0) (Clight.Returnstate v Kstop m0)
.

Inductive match_states
          (i: nat) (st_src0: state owned_heap) (st_tgt0: Clight.state) (smo0: SimMemOh.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (IDX: (i >= 100)%nat)
.

Lemma match_states_lxsim
      idx st_src0 st_tgt0 sm0
      (MATCH: match_states idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsimL (md_src skenv_link) (md_tgt skenv_link)
                   (fun st => unit -> exists su m_init, SoundTop.sound_state su m_init st)
                   top3 (fun _ _ => SimMemOh.le)
                   (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until idx. revert idx.
  pcofix CIH.
  i.
  pfold.
  inv MATCH. subst; ss. ii. clear SUSTAR. inv MATCHST; ss; clarify.
  - econs 1; eauto. ii. clear SU.
    exploit unsymb; et. intro T. des; clarify.
    exploit symb_def; et. intro DEF; des. ss. des_ifs.
    +
      remember (interp_program0 IterSource.prog (ICall _iter tt m0 vs)) as itr0 in *.
      rename Heqitr0 into V.
      Ltac des_itr itr :=
        let name := fresh "V" in
        destruct (observe itr) eqn:name; sym in name; eapply simpobs in name;
        eapply bisimulation_is_eq in name; subst itr
      .
      unfold interp_program0 in *. rewrite sk_same in *. folder.
      apply eq_eutt in V.
      rewrite mrec_as_interp in V. cbn in V. des_ifs. cbn in V.
      unfold c_iter in V.
      econs 1; eauto; swap 2 3.
      { esplits; intro T; rr in T; des; inv T; ss. rewrite RET in *.
        des_ifs;
          try (by unfold triggerUB, triggerDone in *; autorewrite with itree in V; cbn in V;
               rewrite bind_trigger in V; sym in V; eapply vis_not_ret in V; ss).
      }
      { eapply modsem_receptive; et. }
      ii. ss. des_ifs.
      inv STEPSRC.

      rewrite mrec_as_interp in V.
      rewrite itree_eta_ in V. ss. des_itr itr0; ss. rename V0 into V.
      rewrite <- itree_eta_ in V. symmetry in V.

      econs 2; try refl; eauto.
      { esplits; et; cycle 1.
        { apply Ord.lift_idx_spec. instantiate (1 := Nat.pred idx). xomega. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        ss. unfold interp_program0. ss.
        rewrite itree_eta'. f_equal.
        unfold interp_OwnedHeapE, interp_MemE, interp_LocalE, interp_GlobalE, ITree.map.
        unfold interp_state.
        }
        econs; eauto.
      }

      rewrite itree_eta_ in V. ss. des_itr itr0; ss. rename V0 into V.
      rewrite <- itree_eta_ in V. symmetry in V.

      unfold interp_program0 in V. ss.
      apply eq_eutt in V.
      unfold interp_OwnedHeapE, interp_MemE, interp_LocalE, interp_GlobalE, ITree.map in V.
      rewrite mrec_as_interp in V. ss.
      autorewrite with itree in V. cbn in V.
      rewrite interp_state_trigger in V.
      
      unfold interp_state.
      rewrite itree_eta_ in V. ss. des_itr itr0; ss. rewrite <- itree_eta_ in V. symmetry in V.
      rewrite itree_eta_ in V. ss. des_itr t; ss.
      { rewrite itree_eta_ in V. unfold observe in V. ss. }
      rewrite <- itree_eta_ in V.
      rewrite itree_eta_ in I. ss. des_itr itr0; ss.
      rewrite itree_eta_ in I. ss.
      exploit SAFESRC. { apply star_refl. } intro U; des; ss.
      { rr in EVCALL. des. ss. inv EVCALL. ss.
        rewrite itree_eta_ in VIS at 1. ss.
      }
      { rr in EVRET. des. ss. inv EVRET. ss.
        rewrite itree_eta_ in RET at 1. ss.
      }
      inv EVSTEP; ss. clarify.

      exploit SAFESRC. { apply star_one. econs; eauto. } intro U; des; ss.
      { rr in EVCALL. des. ss. inv EVCALL. ss.
        sym in VIS. apply simpobs in VIS. apply bisimulation_is_eq in VIS.
        clarify.
      }

      econs 2; try refl; eauto.
      { esplits; et; cycle 1.
        { apply Ord.lift_idx_spec. instantiate (1 := Nat.pred idx). xomega. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        ss. unfold interp_program0. ss.
        rewrite itree_eta'. f_equal.
        unfold interp_OwnedHeapE, interp_MemE, interp_LocalE, interp_GlobalE, ITree.map.
        unfold interp_state.
        }
        econs; eauto.
      }
  - econs 1; eauto. ii. clear SU.
    exploit unsymb; et. intro T. des; clarify.
    exploit symb_def; et. intro DEF; des. ss. des_ifs.
    +
      econs 1; eauto; swap 2 3.
      { esplits; intro T; rr in T; des; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. ss. inv STEPSRC; ss; clarify; try rewrite TAU in *; clarify.
      unfold interp_program0 in *. ss.



      sym in TAU. apply simpobs in TAU. apply eq_sub_eutt in TAU.
      unfold interp_OwnedHeapE, interp_MemE, interp_LocalE, interp_GlobalE, ITree.map in TAU.
      



      (* set (LocalE +' stateE Mem.mem' +' stateE owned_heap +' *)
      (*        ExternalCallE owned_heap +' DoneE owned_heap +' EventE) as E in *. *)
      (* { *)
      (*   rewrite mrec_as_interp in TAU. ss. *)
      (*   rewrite interp_state_bind in TAU. *)
      (*   rewrite interp_state_bind in TAU. *)
      (*   autorewrite with itree in TAU. *)
      (*   setoid_rewrite interp_bind in TAU. *)
      (* } *)
      esplits; et; try refl.
      { right. esplits; try apply star_refl; eauto.
        apply Ord.lift_idx_spec. instantiate (1 := Nat.pred idx). xomega.
      }










      (** need to get some informatino about itr1 *)
      set (mrec (interp_function IterSource.prog) (ICall _iter vs)) as itr0 in *.
      destruct (observe itr0) eqn:T; sym in T; apply simpobs in T; apply bisimulation_is_eq in T.
      { rewrite T in *.
        autorewrite with itree in TAU.
        rewrite interp_state_ret in TAU.
        autorewrite with itree in TAU.
        rewrite interp_state_ret in TAU.
        rewrite interp_state_ret in TAU. ss.
        subst itr0.
        apply eq_eutt in T.
        rewrite mrec_as_interp in T. ss.
        autorewrite with itree in T. ss.
        rewrite bind_trigger in T. ss.
        exfalso. eapply vis_not_ret; eauto.
      }
      {
        rewrite T in *.
        rewrite interp_tau in TAU.
        rewrite interp_state_tau in TAU.
        autorewrite with itree in TAU.
        rewrite interp_state_tau in TAU.
        rewrite interp_state_tau in TAU.
        rewrite tau_eutt in TAU.
        rewrite tau_eutt in TAU.





        rewrite bind_tau in TAU.
        autorewrite with itree in TAU.
        subst itr0.
        eapply U in T.
        rewrite mrec_as_interp in T. ss.
        rewrite interp_bind in T.
        rewrite interp_trigger in T. ss.
        rewrite bind_trigger in T.
        rewrite interp_interp in T.
      }
      { rewrite T in *.
        rewrite interp_vis in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite bind_bind in TAU.
        unfold interp_state in *.
        rewrite interp_interp in TAU.
        rewrite interp_state_ret in TAU.
        rewrite bind_ret_l in TAU.
        rewrite interp_state_ret in TAU.
        rewrite interp_state_ret in TAU. ss.
        rewrite tau_eutt in TAU.
        subst itr0.
        assert(U: forall E R (a b: itree E R), a = b -> eutt eq a b).
        { i. clarify. refl. }
        apply U in T.
        rewrite mrec_as_interp in T. ss.
        rewrite interp_bind in T.
        rewrite interp_trigger in T. ss.
        rewrite bind_trigger in T.
        exfalso. clear - T.
        assert(V: forall E R (r: R) X (e: E X) k, Vis e k ≈ Ret r -> False).
        { clear - vs. clear vs.
          ii. punfold H. inv H.
        }
        eauto.
      }





      left. pfold.
      ii. clear SUSTAR. econs 1; eauto. ii. clear SU.
      econs 1; eauto; swap 2 3.
      { esplits; intro T; rr in T; des; inv T; ss. }
      { eapply modsem_receptive; et. }













      destruct (observe itr0) eqn:T; sym in T; apply simpobs in T; apply bisimulation_is_eq in T.
      { rewrite T in *.
        rewrite interp_ret in TAU.
        rewrite interp_state_ret in TAU.
        rewrite bind_ret_l in TAU.
        rewrite interp_state_ret in TAU.
        rewrite interp_state_ret in TAU. ss.
        rewrite tau_eutt in TAU.
        subst itr0.
        apply U in T.
        rewrite mrec_as_interp in T. ss.
        rewrite interp_bind in T.
        rewrite interp_trigger in T. ss.
        rewrite bind_trigger in T.
        exfalso. eauto.
      }
      {
        rewrite T in *.
        subst itr0.
        eapply U in T.
        rewrite mrec_as_interp in T. ss.
        rewrite interp_bind in T.
        rewrite interp_trigger in T. ss.
        rewrite bind_trigger in T.
        rewrite interp_interp in T.
      }
      { rewrite T in *.
        rewrite interp_vis in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite interp_state_bind in TAU.
        rewrite bind_bind in TAU.
        unfold interp_state in *.
        rewrite interp_interp in TAU.
        rewrite interp_state_ret in TAU.
        rewrite bind_ret_l in TAU.
        rewrite interp_state_ret in TAU.
        rewrite interp_state_ret in TAU. ss.
        rewrite tau_eutt in TAU.
        subst itr0.
        assert(U: forall E R (a b: itree E R), a = b -> eutt eq a b).
        { i. clarify. refl. }
        apply U in T.
        rewrite mrec_as_interp in T. ss.
        rewrite interp_bind in T.
        rewrite interp_trigger in T. ss.
        rewrite bind_trigger in T.
        exfalso. clear - T.
        assert(V: forall E R (r: R) X (e: E X) k, Vis e k ≈ Ret r -> False).
        { clear - vs. clear vs.
          ii. punfold H. inv H.
        }
        eauto.
      }
      { rewrite T in *.
      }
      rewrite interp_state_bind in TAU.
      rewrite interp_state_bind in TAU.
      setoid_rewrite unfold_interp_state in TAU.
      rewrite mrec_as_interp in TAU. ss.
      repeat (try rewrite interp_bind in TAU; try setoid_rewrite interp_bind in TAU).
      setoid_rewrite interp_bind in TAU.
      setoid_rewrite interp_bind in TAU.
      rewrite interp_mrecursive.
      rewrite interp_mrec in *.

mrec_as_interp :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (T : Type) (d : D T),
(mrec ctx d ≈ interp (mrecursive ctx) (ctx T d))%itree
interp_mrecursive :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (T : Type) (d : D T),
(interp (mrecursive ctx) (trigger_inl1 d) ≈ mrec ctx d)%itree


itree_eta: forall (E : Type -> Type) (R : Type) (t : itree E R), t ≅ {| _observe := observe t |}
itree_eta':
  forall (E : Type -> Type) (R : Type) (ot : itree' E R), ot = observe {| _observe := ot |}
simpobs:
  forall (E : Type -> Type) (R : Type) (ot : itree' E R) (t : itree E R),
  ot = observe t -> t ≅ {| _observe := ot |}
unfold_interp:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
  interp f t ≅ _interp f (observe t)
unfold_interp_state:
  forall (E F : Type -> Type) (S R : Type) (h : forall T : Type, E T -> stateT S (itree F) T)
    (t : itree E R) (s : S), interp_state h t s ≅ _interp_state h (observe t) s


      unfold interp_function in *. ss.
      rewrite unfold_interp_state in *.
      esplits; et; try refl.
      * left. eapply spread_dplus. { eapply modsem2_mi_determinate; et. } eapply plus_one.
        econs; eauto.
        { repeat (econs; ss; eauto; ii; ss; des; clarify).
      left.
  -
Qed.

