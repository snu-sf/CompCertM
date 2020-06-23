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
Require Import Fib3.
Require Import Fib2.
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
Definition mp: ModPair.t := SimSymbId.mk_mp (Fib3.module) (Fib2.module).

(* Hint Unfold assume guarantee assumeK guaranteeK triggerUB triggerNB unwrapU unwrapN. *)
Hint Unfold of_nat to_nat of_nat_opt to_nat_opt.

Lemma fib_nat_0: (fib_nat 0 = 0)%nat. Proof. ss. Qed.
Lemma fib_nat_1: (fib_nat 1 = 1)%nat. Proof. ss. Qed.
Lemma fib_nat_recurse: forall n, ((fib_nat (S (S n))) = (fib_nat n) + fib_nat (S n))%nat.
Proof. reflexivity. Qed.
Local Opaque fib_nat.

Theorem sim_mod: ModPair.sim mp.
Proof.
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
