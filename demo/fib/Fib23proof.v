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
Require Import SIR.
Require Import SIRStack.
Require Import FibHeader.
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







Ltac step := gstep; econs; et.
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




(* Hint Unfold assume guarantee assumeK guaranteeK triggerUB triggerNB unwrapU unwrapN. *)
Theorem correct: rusc defaultR [Fib3.module] [Fib2.module].
Proof.
  assert(AA := range_to_nat).
  assert(SUCPRED := succ_pred).

  eapply SIRLocal.correct with (SO := eq); ss.
  ii. clarify. unfold Fib3.prog, prog. ss. des_ifs; econs; et.
  ii. clarify. unfold owned_heap in *. des_u.
  revert m vs.
  ginit.
  { i. eapply cpn2_wcompat; eauto with paco. }
  gcofix CIH. ii.
  step.
  step_assume.
  unfold precond, parse_arg in *. des. des_ifs_safe. irw. rewrite T. irw.
  destruct n eqn:U.
  { rewrite bind_ret_l. clarify.
    assert(i = Int.zero).
    { unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 0).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify. rewrite Int.eq_true. step_guaranteeK.
    { unfold postcond, NW in *. des_ifs; repeat (Psimpl; des; ss; et). clarify. }
    step.
  }
  destruct n0 eqn:V.
  { rewrite bind_ret_l. u.
    assert(i = Int.one).
    { unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 1).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify. rewrite Int.eq_true. step_guaranteeK.
    { des_ifs; repeat (Psimpl; des; ss; et). }
    step.
  }
  Fail rewrite bind_unwrapN. (*** <---------- TODO: FIXIT ***)
  assert(R: Int.min_signed <= Z.of_nat n0 <= Int.max_signed).
  { unfold to_nat_opt in *. des_ifs.
    generalize (Nat2Z.is_nonneg (S n1)); i. generalize Int.min_signed_neg; i.
    generalize (Int.signed_range i); i.
    split; try xomega.
    assert(Z.of_nat (S (S n1)) <= Int.max_signed).
    { rewrite <- H0. rewrite Z2Nat.id; ss. xomega. }
    xomega.
  }
  assert(R0: Int.min_signed <= Z.of_nat n <= Int.max_signed).
  { unfold to_nat_opt in *. des_ifs.
    generalize (Nat2Z.is_nonneg (S n1)); i. generalize Int.min_signed_neg; i.
    generalize (Int.signed_range i); i.
    split; try xomega.
    assert(Z.of_nat (S (S n1)) <= Int.max_signed).
    { rewrite <- H0. rewrite Z2Nat.id; ss. xomega. }
    xomega.
  }
  (* destruct (to_nat_opt (of_nat n0)) eqn:W; cbn; cycle 1. *)
  (* { exfalso. unfold to_nat_opt in *. des_ifs. psimpl. unfold of_nat in *. rewrite Int.signed_repr in *; ss. xomega. } *)
  assert(~Int.eq i Int.zero).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  assert(~Int.eq i Int.one).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  des_ifs_safe.
  rewrite ! AA; try lia. cbn.
  step_guarantee.
  { Psimpl. (*** TODO: fixit ***)
    eapply Classical_Pred_Type.not_ex_all_not in T0. contradict T0; eauto.
  }
  clear_tac. clear T0.
  rewrite bind_ret_l.
  rewrite bind_bind.
  assert(U: of_nat n1 = Int.sub i (Int.repr 2)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply SUCPRED in H0; des.
    eapply SUCPRED in H0; des. ss. clarify.
    (* rewrite <- Nat.sub_add_distr. ss. *)
    rewrite Nat2Z.inj_sub; ss. rewrite Nat2Z.inj_sub; ss. rewrite <- Z.sub_add_distr; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  rewrite <- U. rewrite ! bind_trigger. step.
  sii S. r in S. des_ifs_safe. des. clarify.
  rewrite bind_bind.
  (* unfold assume at 2. *)
  step_assume. des. clarify.
  rewrite bind_ret_l.
  rewrite bind_bind.
  assert(V: of_nat (S n1) = Int.sub i (Int.repr 1)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply SUCPRED in H0; des.
    eapply SUCPRED in H0; des. ss. clarify.
    rewrite Nat.sub_1_r. rewrite Nat.succ_pred; ss; cycle 1.
    { intro X. rewrite X in *. inv H2. }
    rewrite Nat2Z.inj_sub; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  cbn.
  step_guarantee.
  { eapply Classical_Pred_Type.not_ex_all_not in T0. contradict T0; eauto. }
  rewrite bind_ret_l. rewrite ! bind_trigger. rewrite bind_vis. rewrite V. step.
  sii S. r in S. des_ifs_safe; des; clarify.
  rewrite bind_bind.
  step_assume.
  des; des_ifs_safe. rewrite bind_ret_l. rewrite bind_ret_l.
  step_guaranteeK.
  { unfold postcond, parse_arg in *. unfold NW in *. des_ifs. repeat (Psimpl; des; ss; et). }
  rewrite fib_nat_recurse.
  unfold of_nat. rewrite Int_add_repr. rewrite Nat2Z.inj_add. clear_tac. step.
Qed.
