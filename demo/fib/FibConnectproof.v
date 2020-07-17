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
Require Import FibHeader.
Require Import Fib3_old.
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




Ltac hide_left name :=
  match goal with
  | [ |- SIRLocal.match_itr eq ?LHS _ ] => remember LHS as name
  end
.
Ltac unhide_left name := subst name.

Ltac hide_right name :=
  match goal with
  | [ |- SIRLocal.match_itr eq _ ?RHS ] => remember RHS as name
  end
.
Ltac unhide_right name := subst name.



Ltac step :=
  match goal with
  | [ |- SIRLocal.match_itr eq (assume ?P ;; _) (assume ?Q ;; _) ] =>
    check_equal P Q;
    let name0 := fresh "HIDE" in
    hide_right name0; unfoldr assume; unhide_right name0;
    hide_left name0; unfoldr assume; unhide_left name0;
    let name := fresh "_ASSUME" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      des_ifs_safe; unfold triggerUB; irw;
      pfold; by (econs; eauto)
     |irw]
    (* eapply match_itr_bind_assume; irw *)
  | [ |- SIRLocal.match_itr eq (guarantee ?P ;; _) (guarantee ?Q ;; _) ] =>
    check_equal P Q;
    let name0 := fresh "HIDE" in
    hide_right name0; unfoldr guarantee; unhide_right name0;
    hide_left name0; unfoldr guarantee; unhide_left name0;
    let name := fresh "_GUARANTEE" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      des_ifs_safe; unfold triggerUB; irw;
      pfold; by (econs; eauto)
     |irw]
    (* eapply match_itr_bind_guarantee; irw *)
  | [ |- SIRLocal.match_itr eq (unwrapN ?x >>= _) _ ] =>
    let name := fresh "_UNWRAPN" in
    destruct x eqn:name; [irw|exfalso]; cycle 1

  (*** assume src ***)
  | [ |- SIRLocal.match_itr eq (assume ?P ;; _) _ ] =>
    let name0 := fresh "HIDE" in
    hide_right name0; unfoldr assume; unhide_right name0;
    let name := fresh "_ASSUME" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      unfold triggerUB;
      rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
      pfold; by (econs; eauto)|irw]

  (*** guarantee src ***)
  | [ |- SIRLocal.match_itr eq (guarantee ?P ;; _) _ ] =>
    let name0 := fresh "HIDE" in
    hide_right name0; unfoldr guarantee; unhide_right name0;
    let name := fresh "_GUARANTEE" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      contradict name|irw]

  (*** guarantee tgt ***)
  | [ |- SIRLocal.match_itr eq _ (guarantee ?P ;; _) ] =>
    let name0 := fresh "HIDE" in
    hide_left name0; unfoldr guarantee; unhide_left name0;
    let name := fresh "_GUARANTEE" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      unfold triggerNB;
      rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
      pfold; by (econs; eauto)|irw]

  (*** assume tgt ***)
  | [ |- SIRLocal.match_itr eq _ (assume ?P ;; _) ] =>
    let name0 := fresh "HIDE" in
    hide_left name0; unfoldr assume; unhide_left name0;
    let name := fresh "_ASSUME" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      contradict name|irw]



  | [ |- SIRLocal.match_itr eq ((match ?x with _ => _ end) >>= guaranteeK _)
                            (match ?y with _ => _ end) ] =>
    tryif (check_equal x y)
    then let name := fresh "_DES" in
         destruct x eqn:name; clarify; irw
    else fail
  | [ |- SIRLocal.match_itr eq (triggerUB >>= _) _ ] =>
    unfold triggerUB; irw;
    pfold; by (econs; eauto)
  | [ |- SIRLocal.match_itr eq _ (triggerNB >>= _) ] =>
    unfold triggerNB; irw;
    pfold; by (econs; eauto)
  | [ |- SIRLocal.match_itr eq (guaranteeK ?P ?x) _ ] =>
    unfold guaranteeK;
    let name := fresh "_GUARANTEEK" in
    destruct (ClassicalDescription.excluded_middle_informative (P x)) as [name|name]; cycle 1; [
      contradict name|irw]
  | [ |- SIRLocal.match_itr eq (Ret _) (Ret _) ] =>
    pfold; (by econs; eauto)
  | [ |- SIRLocal.match_itr eq (Vis (subevent _ (ICall _ _ _ _)) _)
                            (Vis (subevent _ (ICall _ _ _ _)) _) ] =>
    pfold; eapply match_icall; ss; et
  | [ |- HProper _ _ _ ] => ii
  | [ H: SALL _ _ _ |- _ ] => r in H; des_ifs_safe; des; clarify
  | [ |- upaco2 (_match_itr ?SO) bot2 _ _ ] =>
    left;
    replace (paco2 (_match_itr SO) bot2) with (SIRLocal.match_itr SO) by ss;
    irw
  end
.





Theorem correct: rusc defaultR [Fib3_old.module: Mod.t] [Fib3.module: Mod.t].
Proof.
  eapply SIRLocal.correct with (SO := eq); ss.
  prog_tac.
  (* replace (f_fib oh_tgt m vs) with (f_fib oh_tgt m vs >>= (fun x => Ret x)); cycle 1. *)
  (* { irw. ss. } *)
  unfold Fib3_old.f_fib, f_fib.
  repeat step.
  { r in _ASSUME. des. clarify. }
  eapply match_itr_bind.
  { ii. rr in H. des_ifs. des; clarify. unfold guaranteeK. des_ifs; refl. }
  progress des_ifs_safe. unfold parse_arg in _UNWRAPN.
  destruct n eqn:U.
  { assert(i = Int.zero).
    { unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 0).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify. rewrite Int.eq_true. step.
  }
  destruct n0 eqn:V.
  { assert(i = Int.one).
    { unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 1).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    clarify. rewrite Int.eq_true. des_ifs. step.
  }
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
  assert(~Int.eq i Int.zero).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  assert(~Int.eq i Int.one).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  des_ifs_safe.
  rewrite ! range_to_nat; try lia; cbn.
  clear_tac.
  assert(U: of_nat n1 = Int.sub i (Int.repr 2)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply succ_pred in H0; des.
    eapply succ_pred in H0; des. ss. clarify.
    (* rewrite <- Nat.sub_add_distr. ss. *)
    rewrite Nat2Z.inj_sub; ss. rewrite Nat2Z.inj_sub; ss. rewrite <- Z.sub_add_distr; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  assert(V: of_nat (S n1) = Int.sub i (Int.repr 1)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply succ_pred in H0; des.
    eapply succ_pred in H0; des. ss. clarify.
    rewrite Nat.sub_1_r. rewrite Nat.succ_pred; ss; cycle 1.
    { intro X. rewrite X in *. inv H2. }
    rewrite Nat2Z.inj_sub; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }

  repeat step.
  { u in *. des_ifs. lia. }
  { r. unfold parse_arg. rewrite ! range_to_nat; try lia; cbn. et. }
  rewrite <- U.
  repeat step.
  { des; clarify. u. des_ifs. }
  { des; clarify. r. unfold parse_arg. rewrite ! range_to_nat; try lia; cbn. et. }
  { des; clarify. rewrite ! range_to_nat; try lia; cbn. esplits; et. }
  des; clarify. rewrite ! range_to_nat in *; try lia; cbn. des; clarify. clear_tac.
  rewrite <- V.
  repeat step.
  { des; clarify. rewrite ! range_to_nat in *; try lia; cbn. esplits; et. }
  des; clarify. des_ifs. des. clear_tac. rewrite fib_nat_recurse.
  unfold of_nat. rewrite Int_add_repr. rewrite Nat2Z.inj_add. step.
Qed.
