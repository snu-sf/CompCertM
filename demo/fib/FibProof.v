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
Require Import SIRmini_quotient.
Require Import FibSource.
Require Import FibTarget.
Require Import ModSemProps.
Require Import Program.

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
Let md_src: Mod.t := (FibSource.module).
Let md_tgt: Mod.t := (FibTarget.module).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Let INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt).
Proof. ss. Qed.
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Let sk_same: __GUARD__ ((CSk.of_program signature_of_function FibTarget.prog) =
                        (Sk.of_program (fn_sig (owned_heap:=owned_heap)) FibSource.prog)).
Proof.
  (*** TODO: generalize lemma and replace CshmgenproofC? ***)
  unfold CSk.of_program, Sk.of_program. ss.
Qed.

Lemma unsymb
      fid fblk
      (FID: Genv.find_symbol ge fid = Some fblk)
  :
    <<FID: fid = _fib>>
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

Lemma symb
  :
    exists fblk, <<FID: Genv.find_symbol tge _fib = Some fblk>>
.
Proof.
  Local Opaque _fib.
  inv INCLSRC. ss.
  exploit (DEFS _fib); et.
  { unfold prog_defmap. ss. }
  i; des. ss. rewrite sk_same. folder.
  clear - SYMB.
  subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. et.
Qed.

Lemma symb_def
      fblk
      (SYMB: Genv.find_symbol ge _fib = Some fblk)
  :
    <<DEF: Genv.find_funct tge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal f_fib)>>
.
Proof.
  exploit (SkEnv.project_impl_spec); try apply INCLSRC. intro SPECSRC.
  exploit (SkEnv.project_impl_spec); try apply INCLTGT. intro SPECTGT.
  des.
  exploit SkEnv.project_revive_precise; et.
  { unfold md_tgt in SPECTGT. ss. rewrite sk_same in *.
    (* instantiate (1:= (SkEnv.project skenv_link *)
    (*              (Sk.of_program (fn_sig (owned_heap:=owned_heap)) FibSource.prog))). *)
    (* instantiate (3:= skenv_link). *)
    (* instantiate (2:= (fn_sig (owned_heap:=owned_heap))). *)
    (* instantiate (1:= FibSource.prog). *)
    Fail eapply SPECTGT.
    admit "universe".
  }
  { unfold md_tgt in INCLTGT. ss. rewrite sk_same in *. Fail eapply INCLTGT. admit "universe". }
  i. inv H.
  assert((prog_defmap FibTarget.prog) ! _fib = Some (Gfun (Internal f_fib))).
  { ss. }
  exploit P2GE; et.
  { Fail eapply H.
    admit "maybe universe". }
  admit "giveup".
Unshelve.
  all: admit "giveup".
Qed.





Notation "'_'" := PTree.Leaf (at level 150).
Notation "a % x % b" := (PTree.Node a x b) (at level 150).
Notation "a %% b" := (PTree.Node a None b) (at level 150).

Let te nn: temp_env := (@PTree.Node val
             (@PTree.Node val (@PTree.Leaf val) (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val))))
                   (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val)))) (@None val)
             (@PTree.Node val
                (@PTree.Node val (@PTree.Leaf val) (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val (Vint nn)) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val))) (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val))))
                   (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val))))).

Let k1 (nn: int) (k_tgt: cont): cont :=
  (Kcall (Some _t'1) f_fib empty_env (te nn)
          (Kseq (Sset _y1 (Etempvar _t'1 tint))
             (Kseq
                (Clight.Ssequence
                   (Clight.Ssequence
                      (Scall (Some _t'2)
                         (Clight.Evar _fib (Tfunction (Tcons tint Tnil) tint cc_default))
                         [Clight.Ebinop Cop.Osub (Etempvar _n tint) (Econst_int (Int.repr 2) tint)
                            tint]) (Sset _y2 (Etempvar _t'2 tint)))
                   (Clight.Sreturn
                      (Some (Clight.Ebinop Cop.Oadd (Etempvar _y1 tint) (Etempvar _y2 tint) tint))))
                k_tgt))).

Let k2 (nn: int) (k_tgt: cont): cont := (admit "").




From ITree Require Export
     KTree
     KTreeFacts
     Basics.CategoryOps
     Basics.CategoryKleisli
.

(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
Lemma eutt_eq_bind : forall E R U (t1 t2: itree E U) (k1 k2: U -> itree E R), t1 ≈ t2 -> (forall u, k1 u ≈ k2 u) -> ITree.bind t1 k1 ≈ ITree.bind t2 k2.
Proof.
  intros.
  eapply eutt_clo_bind with (UU := Logic.eq); [eauto |].
  intros ? ? ->. apply H0.
Qed.





Import CatNotations.
Open Scope cat_scope.
Notation ktr := (ktree (EventE owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val))).

Definition is_call_cont_strong (k0: cont): Prop :=
  match k0 with
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(***
fib(n) calls fib(n-1) or fib(n-2).
- match_stacks 0 n k_src k_tgt: if fib(n-2) is returned, it can go continuation and return fib(n).
- match_stacks 1 n k_src k_tgt: if fib(n-1) is returned, it can go continuation and return fib(n).

- match_stacks e n k_src k_tgt: if fib(e) is returned, it can go continuation and return fib(n).
 ***)
Inductive match_stacks (e: int) (n: int): ktr -> cont -> Prop :=
| match_stacks_nil
  :
    match_stacks e n (fun r => Ret r) Kstop
| match_stacks_cons1
    (hd_src tl_src: ktr)
    (tl_tgt: cont)
    m
    (TL: match_stacks n m tl_src tl_tgt)
    k_src k_tgt
    (KSRC: k_src = (hd_src >>> tl_src))
    (KTGT: k_tgt = k1 n tl_tgt)
    (EXPECT: e = Int.sub n (Int.repr 1))
  :
    match_stacks e n k_src k_tgt
| match_stacks_cons2
    (hd_src tl_src: ktr)
    (tl_tgt: cont)
    m
    (TL: match_stacks n m tl_src tl_tgt)
    k_src k_tgt
    (KSRC: k_src = (hd_src >>> tl_src))
    (KTGT: k_tgt = k2 n tl_tgt)
    (EXPECT: e = Int.sub n (Int.repr 2))
  :
    match_stacks e n k_src k_tgt
.
    (* n *)
    (* (HDSRC: hd_src = *)
    (*         (fun '(oh1, (m1, y1)) => *)
    (*            '(oh2, (m2, y2)) <- trigger (ICall _sum oh1 m1 [Vint (Int.sub n (Int.repr 1))]) ;; *)
    (*            Ret (oh2, (m2, Val.add y1 y2)))) *)




Inductive match_states_internal (i: nat): SIRmini_quotient.state owned_heap -> Clight.state ->
                                          SimMem.t -> Prop :=
| match_call
    itr0 ty m0 vs n
    fid fblk fptr_tgt k_src k_tgt par
    (VS: vs = [Vint n])
    (* (ITR: itr0 ≈ interp_program0 IterSource.prog (ICall fid tt m0 vs)) *)
    (STKS: match_stacks n par k_src k_tgt)
    (ITR: itr0 ≈ 'r <- (mrec (interp_function FibSource.prog) (ICall fid tt m0 vs)) ;; (k_src r))
    (TY: ty = Clight.type_of_fundef (Internal f_fib))
    (SYMB: Genv.find_symbol ge fid = Some fblk)
    (FPTR: fptr_tgt = (Vptr fblk Ptrofs.zero))
    (IDX: (i >= 100)%nat)
  :
    match_states_internal i (Eqv.lift itr0)
                          (Clight.Callstate fptr_tgt ty vs k_tgt m0) (SimMemId.mk m0 m0)
| match_return
    itr0 m0 v k_src k_tgt n par
    (STKS: match_stacks n par k_src k_tgt)
    (RET: itr0 ≈ r <- Ret (tt, (m0, v)) ;; (k_src r))
  :
    match_states_internal i (Eqv.lift itr0) (Clight.Returnstate v k_tgt m0)
                          (SimMemId.mk m0 m0)
.

Inductive match_states
          (i: nat) (st_src0: state owned_heap) (st_tgt0: Clight.state) (smo0: SimMemOh.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal i st_src0 st_tgt0 smo0)
    (MWF: SimMemOh.wf smo0)
.

Lemma bind_ret_map {E R1 R2} (u : itree E R1) (f : R1 -> R2) :
  (r <- u ;; Ret (f r)) ≅ f <$> u.
Proof.
  rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_Ret. auto.
  - rewrite bind_ret_r. reflexivity.
Qed.

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) ≅ Vis e (fun x => f <$> (k x)).
Proof.
  cbn.
  unfold ITree.map.
  autorewrite with itree. refl.
Qed.






(*** TODO: IDK why but (1) ?UNUSNED is needed (2) "fold" tactic does not work. WHY????? ***)
Ltac fold_eutt :=
  repeat multimatch goal with
         | [ H: eqit eq true true ?A ?B |- ?UNUSED ] =>
           let name := fresh "tmp" in
           assert(tmp: eutt eq A B) by apply H; clear H; rename tmp into H
         end
.

Ltac des_itr itr :=
  let name := fresh "V" in
  destruct (observe itr) eqn:name; sym in name; eapply simpobs in name;
  eapply bisimulation_is_eq in name; subst itr
.

Ltac vvt H := clear - H; exfalso; punfold H; inv H; simpl_depind; subst; simpl_depind.
Ltac f_equiv := first [eapply eutt_eq_bind|eapply eqit_VisF|eapply eqit_bind'|Morphisms.f_equiv].

Hint Rewrite @bind_trigger : itree.
Hint Rewrite @tau_eutt : itree.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree; cbn).








Lemma init_fsim
      args st_src0
      (INIT: ModSem.initial_frame (md_src skenv_link) tt args st_src0)
  :
    exists i st_tgt0 smo0,
      (<<INIT: ModSem.initial_frame (md_tgt skenv_link) tt args st_tgt0>>)
      /\ (<<MATCH: match_states i st_src0 st_tgt0 smo0>>)
.
Proof.
  inv INIT. ss. des_ifs. folder.
  unfold interp_program0 in *.
  exploit unsymb; et. i; des. clarify.
  assert(SIG: fd = signature_of_function f_fib).
  { admit "ez - findf sig". }
  clarify. destruct args; ss. inv TYP. ss. destruct vs; ss. destruct vs; ss.
  inv DEF. clear H2. unfold typify_list, typify in *; ss. des_ifs. destruct v; ss.
  revert sk_same. revert INCLTGT. clear_tac. i.
  eexists _, _, (SimMemId.mk _ _). esplits; eauto.
  - econs; ss; eauto.
    { rewrite sk_same. folder. exploit symb_def; et. }
    { ss. }
  - econs; ss; eauto. econs; ss; eauto.
    + unfold typify_list. ss. unfold typify. des_ifs; ss.
    + econs; ss.
    + cbn. irw. rewrite ITR. unfold typify. des_ifs; ss. refl.
Unshelve.
  all: ss.
Qed.

(* Lemma final_fsim *)
(*       i st_src0 st_tgt0 smo0 retv *)
(*       (MATCH: match_states i st_src0 st_tgt0 smo0) *)
(*       (FIN: ModSem.final_frame (md_src skenv_link) st_src0 tt retv) *)
(*   : *)
(*     exists smo_ret, *)
(*       (<<FIN: ModSem.final_frame (md_tgt skenv_link)  st_tgt0 tt retv>>) /\ *)
(*       (<<SIMRET: SimMem.sim_retv retv retv smo_ret>>) /\ *)
(*       (<<MWF: SimMem.wf smo_ret>>) *)
(* . *)
(* Proof. *)
(*   inv FIN. ss. *)
(*   inv MATCH. ss. inv MATCHST; ss. *)
(*   { rewrite RET in *. rewrite ITR in *. clear - IN. exfalso. *)
(*     rewrite mrec_as_interp in IN. irw in IN. des_ifs; vvt IN. } *)
(*   eexists (SimMemId.mk m0 m0). *)
(*   esplits; ss; eauto; cycle 1. *)
(*   { econs; eauto. ss. } *)
(*   inv STKS; cycle 1. *)
(*   { rewrite RET in *. rewrite RET0 in *. clear - IN. exfalso. *)
(*     vvt IN. *)
(* Qed. *)

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

    rename ITR into V.
    unfold interp_program0 in V. rewrite sk_same in *. folder.
    rewrite mrec_as_interp in V. cbn in V. des_ifs. cbn in V.
    (* unfold c_iter in V. *)


    econs 1; et; swap 2 3.
    { esplits; intro T; rr in T; des; inv T; ss; rewrite V in *; ss.
      - rewrite VIS in IN. irw in IN. vvt IN.
      - rewrite RET in IN. irw in IN. vvt IN.
    }
    { eapply modsem_receptive; et. }
    ii. ss. inv STEPSRC; ss; rewrite V in IN; swap 3 4.
    { rewrite VIS in IN. irw in IN. vvt IN. }
    { rewrite VIS in IN. irw in IN. vvt IN. }
    { rewrite VIS in IN. irw in IN. vvt IN. }
    rewrite VIS in IN. autorewrite with itree in IN. cbn in IN. rewrite bind_trigger in IN.
    apply eqit_inv_vis in IN. des. specialize (IN0 tt). fold_eutt.
    rename k into itr2.

    eexists _, _, (SimMemId.mk _ _). esplits; eauto.
    { right. esplits; try apply star_refl.
      apply Ord.lift_idx_spec. instantiate (1 := Nat.pred idx). xomega. }
    left. pfold.

    econs 1; et. intro T. revert sk_same. clear_tac. clear SUSTAR. i.
    sym in IN0. unfold c_fib in IN0. unfold unwrapU in IN0.
    clears itr0. clear itr0.
    clears itr1. clear itr1.
    rename IN0 into V.
    (* destruct (classic (exists n, vs = [Vint n])); cycle 1. *)
    (* { assert(UB: exists k, itr2 () ≈ Vis (EUB _) k). *)
    (*   { des_ifs; try (unfold triggerUB in V; irw in V; eauto); *)
    (*       try (by contradict H; esplits; et). *)
    (*   } *)
    (*   des. *)
    (*   econs 1; et; swap 2 3. *)
    (*   { esplits; intro T; rr in T; des; inv T; ss; rewrite V in *; ss. *)
    (*     - rewrite VIS in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (*     - rewrite RET in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (*   } *)
    (*   { eapply modsem_receptive; et. } *)
    (*   ii. ss. inv STEPSRC; ss. *)
    (*   - rewrite VIS in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (*   - rewrite VIS in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (*   - rewrite VIS in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (*   - rewrite VIS in IN. rewrite UB in IN. irw in IN. vvt IN. *)
    (* } *)
    des. clarify. ss. irw in V. des_ifs_safe.
    des_ifs.
    { apply_all_once Int.same_if_eq. subst.
      irw in V.
      econs 2; try refl; eauto.
      { esplits; eauto; cycle 1.
        { apply Ord.lift_idx_spec. instantiate (1 := Nat.pred (Nat.pred idx)). xomega. }
        eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_refl.
      }
      right. eapply CIH. econs; eauto.
      - ss. econs; eauto; cycle 1.
        { rewrite V. instantiate (1:= k_src). irw. refl. }
        { inv STKS.
          - econs; eauto.
          - econs; eauto.
          - }
      - ss.
    }
    { apply_all_once Int.same_if_eq. subst.
      irw in V.
      econs 2; try refl; eauto.
      { esplits; eauto; cycle 1.
        { apply Ord.lift_idx_spec. instantiate (1 := Nat.pred (Nat.pred idx)). xomega. }
        eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_refl.
      }
      right. eapply CIH. econs; eauto.
      - ss. econs; eauto; cycle 1.
        { rewrite V. instantiate (1:= k_src). irw. refl. }
        { inv STKS.
          - econs; eauto.
          - econs; eauto. }
      - ss.
    }
    { irw in V. rewrite mrec_as_interp in V. irw in V. des_ifs.
      unfold triggerNB in *.
      econs 2; try refl; eauto.
      { esplits; eauto; cycle 1.
        { apply Ord.lift_idx_spec. instantiate (1 := Nat.pred (Nat.pred idx)). xomega. }
        eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify).
          fold Int.zero. rewrite Heq. ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify).
          fold Int.one. rewrite Heq0. ss. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econsr; ss; et.
          - econsr; ss; et.
            + econsr; ss; et.
            + econs 2; ss; et.
          - repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        apply star_refl.
      }
      fold (te n). right. eapply CIH.
      econs; ss.
      econs; ss; eauto.
      - unfold Cop.cast_int_int.
        assert(L: Int.add (Int.sub n (Int.repr 1)) Int.one = n).
        { rewrite Int.sub_add_opp.
          rewrite Int.add_assoc. rewrite Int.neg_repr.
          unfold Int.one. rewrite Int.Ptrofs_add_repr. simpl.
          rewrite Int.add_zero. eauto.
        }
        econs; eauto; try refl.
        * rewrite L. eauto.
        * unfold k1. repeat f_equal. rewrite L. eauto.
      - rewrite V. f_equiv.
        { rewrite mrec_as_interp.
          f_equiv. irw. des_ifs_safe. cbn. rewrite <- bind_trigger.
          f_equiv; try refl. admit "".
        }
        eapply eutt_eq_bind.  eutt_eq_bind. eqit_bind'. admit "".
      - admit "idx".
      - ss.
    }
  - econs 3; eauto.
    { rr. esplits; et. econs; et.
      - refl.
      - admit "change is_call to NSTEP NRET".
      - admit "change is_call to NSTEP NRET -- or put in match_states && exploit 'safe'". }
    ii. ss. inv ATSRC. ss.
    rewrite ITR in *. rewrite VIS in *. eapply eqit_inv_vis in IN. des. clarify.
    eexists _, _, (SimMemId.mk _ _). ss. esplits; et.
    { rr. ss. esplits; et. econs; ss; et. }
    { econs; ss; et.
      - rewrite sk_same. folder. admit "ez - FINDF".
      - esplits; et. unfold sg in *. rewrite H4. unfold signature_of_type in *.
        unfold Sk.get_sig in *. des_ifs. ss. rewrite <- H4. ss. }
    ii.
    inv AFTERSRC. inv GETK. ss.
    rewrite ITR in *. rewrite VIS0 in *.
    apply eqit_inv_vis in IN. des. clarify.
    rr in SIMRETV. des. ss. clarify. revert sk_same. clear_tac. i. (*** TODO: update claer_tac ***)
    inv SIMRETV0; ss. clarify.
    unfold Retv.mk in *. clarify. destruct sm_ret ;ss. clarify.
    rename tgt into m0. rename v_tgt into rv.
    specialize (IN1 (tt, (m0, rv))). specialize (IN0 (tt, (m0, rv))). fold_eutt. des_ifs.
    rewrite IN0 in *.
    eexists _, (SimMemId.mk m0 m0). esplits; et.
    { econs; et. }
    left.
    pfold.
    econs 1; eauto. clear SUSTAR.
    ii. clear SU.
    econs 1; et; swap 2 3.
    { esplits; intro T; rr in T; des; inv T; ss; rewrite <- IN in *; ss.
      - rewrite <- IN1 in VIS1. rewrite <- IN0 in VIS1. rewrite interp_trigger in VIS1.
        cbn in VIS1. rewrite mrec_as_interp in VIS1.
        cbn in VIS1. des_ifs.
        cbn in VIS1. autorewrite with itree in VIS1.
        cbn in VIS1. rewrite bind_trigger in VIS1. vvt VIS1.
      - rewrite <- IN1 in RET. rewrite <- IN0 in RET. rewrite interp_trigger in RET.
        cbn in RET. rewrite mrec_as_interp in RET.
        cbn in RET. des_ifs.
        cbn in RET. autorewrite with itree in RET.
        cbn in RET. rewrite bind_trigger in RET. vvt RET.
    }
    { eapply modsem_receptive; et. }
    ii. ss. inv STEPSRC; ss; swap 3 4.
    { rewrite <- IN in VIS1. rewrite <- IN1 in VIS1. rewrite <- IN0 in VIS1.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite mrec_as_interp in VIS1.
      cbn in VIS1. des_ifs.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite bind_trigger in VIS1. vvt VIS1. }
    { rewrite <- IN in VIS1. rewrite <- IN1 in VIS1. rewrite <- IN0 in VIS1.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite mrec_as_interp in VIS1.
      cbn in VIS1. des_ifs.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite bind_trigger in VIS1. vvt VIS1. }
    { rewrite <- IN in VIS1. rewrite <- IN1 in VIS1. rewrite <- IN0 in VIS1.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite mrec_as_interp in VIS1.
      cbn in VIS1. des_ifs.
      cbn in VIS1. autorewrite with itree in VIS1.
      cbn in VIS1. rewrite bind_trigger in VIS1. vvt VIS1. }
    hexploit symb; et. i; des.
    eexists _, _, (SimMemId.mk _ _). esplits; eauto.
    { left.
      eapply spread_dplus; et.
      { eapply modsem2_mi_determinate; et. }
      eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { econs; ss; et.
        { econs; ss; et.
          - repeat (econsr; ss; et).
          - econs 2; ss; et.
        }
        repeat (econs; ss; et); ii; repeat (des; ss; clarify).
        - destruct _fptr; ss.
        - admit "---------------------------type".
      }
      apply star_refl.
    }
    right. eapply CIH. econs; ss; et. econs; ss; et.
    {
    { rewrite VIS in IN. autorewrite with itree in IN. cbn in IN. rewrite bind_trigger in IN.
      vvt IN. }
    { rewrite VIS in IN. autorewrite with itree in IN. cbn in IN. rewrite bind_trigger in IN.
      vvt IN. }
    { }
    eapply CIH. econs; ss; et. econs; et.

      destruct vs; ss.
      { unfold triggerUB in V. (*** TODO: use notation instead ***)
        rewrite interp_vis in V. cbn in V. rewrite bind_trigger in V.
        econs 1; et; swap 2 3.
        { esplits; intro T; rr in T; des; inv T; ss; rewrite V in *; ss.
          - vvt VIS.
          - apply vis_not_ret in RET. ss.
        }
        { eapply modsem_receptive; et. }
        ii. ss. inv STEPSRC; rewrite V in *; try (vvt VIS).
      }
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

