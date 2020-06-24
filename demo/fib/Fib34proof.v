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
Require Import Any.
Require Import SIRmini.
Require Import SIRmini_stack.
Require Import Fib4.
Require Import Fib3.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.









Lemma bind_unwrapU
      E `{EventE -< E} R S
      (r: option R) r'
      (k: R -> itree E S)
      (SOME: r = Some r')
  :
    ` x : _ <- unwrapU r;; k x = k r'.
Proof.
  rewrite SOME. cbn. eapply bind_ret_l.
Qed.

Lemma bind_unwrapN
      E `{EventE -< E} R S
      (r: option R) r'
      (k: R -> itree E S)
      (SOME: r = Some r')
  :
    ` x : _ <- unwrapN r;; k x = k r'.
Proof.
  rewrite SOME. cbn. eapply bind_ret_l.
Qed.

Lemma bind_bind : forall (E : Type -> Type) (R S T : Type) (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ` x : _ <- (` x : _ <- s;; k x);; h x = ` r : R <- s;; ` x : _ <- k r;; h x.
Proof.
  i. f. eapply bind_bind.
Qed.

Lemma bind_assume
      E `{EventE -< E} R
      (P: Prop)
      (prf: P)
      (k: itree E R)
  :
    assume P ;; k = k.
Proof.
  unfold assume. des_ifs. rewrite bind_ret_l. ss.
Qed.

Lemma bind_guarantee
      E `{EventE -< E} R
      (P: Prop)
      (prf: P)
      (k: itree E R)
  :
    guarantee P ;; k = k.
Proof.
  unfold guarantee. des_ifs. rewrite bind_ret_l. ss.
Qed.

Lemma interp_mrec_bind :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U T : Type) (t : itree (D +' E) U)
  (k : U -> itree (D +' E) T), interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x).
Proof. i. f. eapply interp_mrec_bind. Qed.











Lemma eta
      i j
      (EQ: i.(Int.intval) = j.(Int.intval))
  :
    <<EQ: i = j>>
.
Proof.
  r. destruct i, j; ss. clarify. f_equal. eapply Axioms.proof_irr.
Qed.

(* Lemma signed_inj *)
(*       i j *)
(*       (EQ: Int.signed i = Int.signed j) *)
(*   : *)
(*     <<EQ: i = j>> *)
(* . *)
(* Proof. *)
(*   unfold Int.signed in *. des_ifs. *)
(*   - r. eapply eta. ss. *)
(*   - r. eapply eta. ss. *)
(* Qed. *)

Lemma Int_add_repr: forall x y,
    <<EQ: (Int.add (Int.repr x) (Int.repr y)) = Int.repr (x + y)>>.
Proof.
  i. apply Int.eqm_repr_eq. eapply Int.eqm_sym. eapply Int.eqm_trans.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_add; apply Int.eqm_unsigned_repr.
Qed.

Lemma Int_sub_repr: forall x y,
    <<EQ: (Int.sub (Int.repr x) (Int.repr y)) = Int.repr (x - y)>>.
Proof.
  i. apply Int.eqm_repr_eq. eapply Int.eqm_sym. eapply Int.eqm_trans.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_sub; apply Int.eqm_unsigned_repr.
Qed.

Lemma bind_trigger: forall (E : Type -> Type) (R U : Type) (e : E U) (k : U -> itree E R),
    ` x : _ <- ITree.trigger e;; k x = Vis e (fun x : U => k x).
Proof. i. f. eapply bind_trigger. Qed.

Local Opaque ident_eq.
Local Opaque Z.of_nat.

Ltac step := gstep; econs; et.
Definition mp: ModPair.t := SimSymbId.mk_mp (Fib4.module) (Fib3.module).

(* Hint Unfold assume guarantee assumeK guaranteeK triggerUB triggerNB unwrapU unwrapN. *)
Hint Unfold of_nat to_nat of_nat_opt to_nat_opt.

Lemma fib_nat_0: (fib_nat 0 = 0)%nat. Proof. ss. Qed.
Lemma fib_nat_1: (fib_nat 1 = 1)%nat. Proof. ss. Qed.
Lemma fib_nat_recurse: forall n, ((fib_nat (S (S n))) = (fib_nat n) + fib_nat (S n))%nat.
Proof. reflexivity. Qed.
Local Opaque fib_nat.

Theorem sim_mod: ModPair.sim mp.
Proof.
  assert(tau: forall E R (a: itree E R), (tau;; a) = a).
  { admit "backdoor". }
  assert(forall fname oh0 m0 vs0, sim_st eq (interp_program0 Fib4.prog (ICall fname oh0 m0 vs0))
                                         (interp_program0 prog (ICall fname oh0 m0 vs0))).
  {
    ginit.
    { i. eapply cpn2_wcompat; eauto with paco. }
    ii.
    unfold interp_program0, mrec. ss.
    destruct(ident_eq fname Fib0._fib); cycle 1.
    {
      unfold Fib4.prog, prog. ss. des_ifs.
      unfold sim_st. unfold triggerNB.
      rewrite ! unfold_interp_mrec. cbn. step.
    }
    des_ifs.
    set (interp_function Fib4.prog) as X.
    set (interp_function prog) as Y.
    unfold Fib4.prog, prog in *. ss. des_ifs.
    unfold Fib4.f_fib, f_fib. ss.
    replace Fib4.precond with precond; ss.
    replace Fib4.fib_nat with fib_nat; ss.
    destruct (precond vs0) eqn:T; cycle 1.
    { rewrite ! unfold_interp_mrec. cbn. step.
      rewrite ! unfold_interp_mrec. cbn. step.
    }
    clear T vs0.
    (* https://coq-club.inria.narkive.com/VWS50VZQ/adding-strong-induction-to-the-standard-library *)
    induction n as [ n IHn ] using (well_founded_induction lt_wf); ii; ss.
    destruct n eqn:U0.
    { rewrite ! unfold_interp_mrec. cbn. step.
      rewrite ! bind_ret_l.
      unfold guaranteeK. des_ifs; cycle 1.
      { unfold NW in *. repeat (Psimpl; des; ss). }
      des; clarify. ss. rewrite V. clear_tac.
      rewrite ! unfold_interp_mrec. cbn. rewrite tau. unfold Fib4.of_nat.
      rewrite ! unfold_interp_mrec. cbn. rewrite tau.
      rewrite ! unfold_interp_mrec. cbn.
      step.
    }
    destruct n0 eqn:U1.
    { rewrite ! unfold_interp_mrec. cbn. step.
      rewrite ! bind_ret_l.
      unfold guaranteeK. des_ifs; cycle 1.
      { unfold NW in *. repeat (Psimpl; des; ss). }
      des; clarify. ss. rewrite V. clear_tac.
      rewrite ! unfold_interp_mrec. cbn. rewrite tau. unfold Fib4.of_nat.
      rewrite ! unfold_interp_mrec. cbn. rewrite tau.
      rewrite ! unfold_interp_mrec. cbn.
      step.
    }
    rewrite ! unfold_interp_mrec. cbn. step.
    rewrite ! bind_ret_l.
    rewrite ! tau.
    Ltac step_unwrapN := match goal with
                         | |- context[unwrapN ?ox ;; _] =>
                           (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                           first[
                               unfold unwrapN at 5|
                               unfold unwrapN at 4|
                               unfold unwrapN at 3|
                               unfold unwrapN at 2|
                               unfold unwrapN at 1|
                               unfold unwrapN at 0
                             ];
                           let name := fresh "T" in
                           destruct ox eqn:name; cycle 1
                         end
    .
    step_unwrapN.
    { rewrite ! unfold_interp_mrec. cbn. step. }
    cbn. rewrite bind_ret_l.
    rewrite bind_bind.
    rewrite ! unfold_interp_mrec. cbn. rewrite ! tau.
    exploit (IHn n0); eauto.
    { xomega. }
    intro V. repeat (rewrite ! tau in *; rewrite bind_ret_l in *).
    rewrite interp_mrec_trigger.
    step.

    rewrite ! unfold_interp_mrec. cbn. step.
    unfold guaranteeK. des_ifs; cycle 1.
    { unfold NW in *. repeat (Psimpl; des; ss). }
    des; clarify. ss. rewrite V. clear_tac.
    rewrite ! unfold_interp_mrec. cbn. rewrite tau. unfold Fib4.of_nat.
    rewrite ! unfold_interp_mrec. cbn. rewrite tau.
    rewrite ! unfold_interp_mrec. cbn.
    step.
    
    {
      rewrite ! unfold_interp_mrec.
    }
    assert(precond vs0 = Some n).
    unfold Fib4.f_fib, f_fib.
    rewrite ! unfold_interp_mrec. ss. cbn. step.
    rewrite 
    cbn.
      cecons; et.
        eapply sim_st_nb. econs; et.
        rewrite <- ! bind_trigger. rewrite ! interp_mrec_bind.
      eapply sim_st_nb. econs; et.
      step.
      econs; et.
    }
    unfold interp_program0. ss.
  }
  assert(Fib4.module = Fib3.module).
  {
    unfold Fib4.module. unfold module. f_equal.
    unfold Fib4.prog. unfold prog. f_equal.
    apply func_ext3. intros oh0 m0 vs0.
                                           (Fib4.f_fib oh0 m0 vs0) (f_fib oh0 m0 vs0)).
    unfold Fib4.f_fib. unfold f_fib.
    f.
    do 2 f_equiv. replace Fib4.precond with precond; ss.
    f_equiv. ii.
    f.
    assert(tau: forall (a: itree (E owned_heap) (owned_heap * (mem * val))), (tau;; a) = a).
    { admit "backdoor". }
    induction a; ii; ss.
    - rewrite ! tau.
      rewrite bind_ret_l. unfold guaranteeK. des_ifs.
    do 2 f_equiv. ii.
    econs; et.
    f_equal.
  }
  eapply SimSIR.sim_mod with (SO := eq); ss.
  ii. clarify. unfold Fib3.prog, prog. ss. des_ifs; econs; et.
  ii. clarify. unfold Fib3.owned_heap in *. des_u. ss.
  revert m vs.
  ginit.
  { i. eapply cpn2_wcompat; eauto with paco. }
  gcofix CIH. ii.
  step.
  destruct (precond vs) eqn:T; cycle 1.
  { cbn. unfold triggerUB. rewrite bind_vis. step. }
  cbn. rewrite bind_ret_l. unfold precond in *. des_ifs_safe. unfold to_nat_opt in T. set n as x. des_ifs_safe.
  destruct x eqn:T.
  { rewrite bind_ret_l. u. rewrite fib_nat_0. unfold guaranteeK. cbn.
    rewrite Nat2Z.inj_0. fold Int.zero.
    assert(i = Int.zero).
    { subst x.
      assert((Int.signed i) = 0).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify.
    rewrite Int.eq_true. des_ifs; repeat (Psimpl; des; ss; et).
    step.
  }
  destruct n eqn:U.
  { rewrite bind_ret_l. u. rewrite fib_nat_1. unfold guaranteeK. cbn.
    rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_0. cbn. fold Int.one.
    assert(i = Int.one).
    { subst x.
      assert((Int.signed i) = 1).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify.
    rewrite Int.eq_true. des_ifs; repeat (Psimpl; des; ss; et).
    step.
  }
  Fail rewrite bind_unwrapN. (*** <---------- TODO: FIXIT ***)
  destruct (to_nat_opt (of_nat n0)) eqn:W; cbn; cycle 1.
  { exfalso. unfold to_nat_opt in *. des_ifs. psimpl. unfold of_nat in *. rewrite Int.signed_repr in *; ss.
    - xomega.
    - generalize (Nat2Z.is_nonneg n0); i. generalize Int.min_signed_neg; i.
      generalize (Int.signed_range i); i. subst x.
      split; try xomega.
      assert(Z.of_nat (S (S n0)) <= Int.max_signed).
      { rewrite <- T. rewrite Z2Nat.id; ss. xomega. }
      xomega.
  }
  assert(~Int.eq i Int.zero).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  assert(~Int.eq i Int.one).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  des_ifs_safe.
  rewrite bind_ret_l.
  rewrite bind_bind. rewrite ! bind_trigger.
  (*** TODO: make lemma ***)
  assert(SUCPRED: forall x y, x = S y <-> ((x - 1)%nat = y /\ (1 <= x)%nat)).
  { clear - r. clear r.
    split.
    - ginduction x; ii; ss. clarify. split; try xomega. clear - y. ginduction y; ii; ss. et.
    - ginduction x; ii; des; clarify; ss; try xomega. f_equal. rewrite Nat.sub_0_r. ss.
  }
  assert(U: of_nat n0 = Int.sub i (Int.repr 2)).
  { unfold of_nat. subst x.
    eapply SUCPRED in T; des.
    eapply SUCPRED in T; des. ss. clarify.
    (* rewrite <- Nat.sub_add_distr. ss. *)
    rewrite Nat2Z.inj_sub; ss. rewrite Nat2Z.inj_sub; ss. rewrite <- Z.sub_add_distr; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  rewrite <- U. step.
  sii S. r in S. des_ifs_safe. des. clarify.
  rewrite bind_bind.
  (* unfold assume at 2. *)
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
                        destruct (ClassicalDescription.excluded_middle_informative P); [
                        |unfold triggerUB; rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
                         step]
                      end
  .
  step_assume. des. clarify.
  rewrite bind_ret_l.
  rewrite bind_bind.
  Ltac step_unwrapN := match goal with
                       | |- context[unwrapN ?ox ;; _] =>
                         (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                         first[
                             unfold unwrapN at 5|
                             unfold unwrapN at 4|
                             unfold unwrapN at 3|
                             unfold unwrapN at 2|
                             unfold unwrapN at 1|
                             unfold unwrapN at 0
                           ];
                         let name := fresh "T" in
                         destruct ox eqn:name; cycle 1
                       end
  .
  assert(V: of_nat (S n0) = Int.sub i (Int.repr 1)).
  { unfold of_nat. subst x.
    eapply SUCPRED in T; des.
    eapply SUCPRED in T; des. ss. clarify.
    rewrite Nat.sub_1_r. rewrite Nat.succ_pred; ss; cycle 1.
    { intro X. rewrite X in *. inv T1. }
    (* rewrite <- Nat.sub_add_distr. ss. *)
    rewrite Nat2Z.inj_sub; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  rewrite V.
  step_unwrapN.
  { exfalso. unfold to_nat_opt in *. des_ifs.
    rewrite Int.signed_eq in *. des_sumbool. ss.
    rewrite <- (@Int.repr_signed i) in g.
    rewrite Int_sub_repr in *.
    rewrite Int.signed_repr in *; ss.
    - assert(Int.signed i = 0).
      { xomega. }
      ss.
    - generalize (Int.signed_range i); i.
      generalize Int.min_signed_neg; i. split; i; try lia.
  }
  cbn. rewrite bind_ret_l. rewrite ! bind_bind. rewrite ! bind_trigger. step.
  sii S. r in S. des_ifs_safe; des; clarify.
  rewrite bind_bind.
  step_assume.
  des; des_ifs_safe. rewrite bind_ret_l. rewrite bind_ret_l.
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
                       end
  .
  unfold guaranteeK. des_ifs; cycle 1.
  { unfold NW in *. repeat (Psimpl; des; ss; et). }
  des; clarify.
  rewrite fib_nat_recurse.
  unfold of_nat. rewrite Int_add_repr. rewrite Nat2Z.inj_add. step.
Qed.
