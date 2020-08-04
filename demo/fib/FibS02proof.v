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
Require Import FibS0.
Require Import FibS2.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.


Let sim_st: nat -> state owned_heap -> state owned_heap -> Prop := (sim_st (@eq owned_heap) lt).


(* Axiom sim_st_trans: Transitive (sim_st 0%nat). *)
Require Import Morphisms.
Local Open Scope signature_scope.

Ltac my_tac := 
  repeat match goal with
         | [ |- context[interp_function ?H] ] =>
           let name := fresh "x" in set (name := (interp_function H)) in *
         end
.

Lemma interp_mrec_bind: forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
                               (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof.
  ii. f. eapply interp_mrec_bind.
Qed.














Lemma unfold_fib3: forall oh0 m0 vs0,
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
    =
    (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      guarantee (parse_arg oh0 m0 vs0) ;;
      tau;;
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      guarantee (parse_arg oh1 m1 vs1) ;;
      tau;;
      '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh1 m1 vs1)) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
    end
      )
.
Proof.
  {
    i. irw.
    unfold FibS0.f_fib at 2. irw.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. irw. f_equiv. f_equiv. apply func_ext1. ii; ss. }
    irw. destruct n.
    { irw. refl. }
    destruct n.
    { irw. refl. }
    destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1.
    { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw.
      f_equiv. f_equiv. apply func_ext1. ii; ss. }
    unfold guarantee. des_ifs_safe. irw.
    f_equiv. f_equiv. des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. f_equiv. apply func_ext1.
    ii. des_ifs; cycle 1.
    { irw. unfold triggerNB. irw. f_equiv. f_equiv. apply func_ext1. ii; ss. }
    rewrite ! bind_ret_l.
    rewrite interp_mrec_bind. irw. f_equiv. f_equiv. f_equiv. apply func_ext1. ii. des_ifs. irw. refl.
  }
Qed.




Lemma to_nat_opt_id: forall n, to_nat_opt (of_nat n) = Some n.
Proof.
  i. unfold to_nat_opt, of_nat. des_ifs.
  - rewrite Int.signed_repr; cycle 1.
    { generalize Int.min_signed_neg; i. split; try xomega.
      abstr (Z.of_nat n) x.
      admit "Need more condition".
    }
    rewrite Nat2Z.id. ss.
  - admit "Need more condition".
Abort.






Definition rclo: (state owned_heap) -> (state owned_heap) -> Prop :=
  rtc ((sim_st 0%nat) \2/ eutt eq).

Global Instance sim_st_refl n: Reflexive (sim_st n).
Proof.
  admit "redundant -- see FibS01proof".
Qed.

Global Instance rclo_bind: Proper ((eq ==> rclo) ==> rclo ==> rclo) (ITree.bind').
Proof.
  admit "".
Qed.

Theorem lemma_aux
        m vs oh n
        (T: parse_arg oh m vs = Some n)
  :
    rclo (interp_mrec (interp_function prog) (f_fib oh m vs))
         (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh m vs))
.
Proof.
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  rewrite unfold_fib3.
  unfold f_fib. ss.

  Local Opaque prog FibS0.prog.

  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss. irw. apply rtc_once; left. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss. irw. apply rtc_once; left. refl. }

  unfold parse_arg in T. des_ifs.
  ss. rewrite ! T. ss. irw.
  unfold guarantee.
  destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. apply rtc_once; left. pfold. econs; et. }
  ss. des_ifs_safe. irw.
  eapply rtc_n1; cycle 1.
  { right. rewrite tau_eutt. refl. }
  assert(n = n0).
  { admit "math!!". }
  subst.
  fold rclo.
  rewrite <- bind_ret_r at 1. eapply rclo_bind; cycle 1.
  { rewrite <- unfold_interp_mrec.
    etrans; cycle 1.
    - eapply (H n0); ss. xomega.
    - irw. unfold f_fib. irw. unfold unwrapU. des_ifs. irw. refl.
    exploit (H n); eauto.
    {
  }
  rewrite <- unfold_interp_mrec. rewrite interp_mrec_bind.
Qed.

Global Instance rclo_bind: Proper ((eq ==> rclo) ==> rclo ==> rclo) (ITree.bind').
Proof.
  admit "".
Qed.

Theorem lemma_aux
        m vs oh n
        (T: parse_arg oh m vs = Some n)
  :
    rclo (interp_mrec (interp_function prog) (f_fib oh m vs))
         (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh m vs))
.
Proof.
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  rewrite unfold_fib3.
  unfold f_fib. ss.

  Local Opaque prog FibS0.prog.

  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss. irw. pfold.
    rewrite <- BDOOR.
    eapply sim_st_choose_src. exists 0%nat. ss. left. pfold. econs; et.
    irw. Fail refl. left. pfold. econs; et. }
  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss.  irw. pfold.
    rewrite <- BDOOR.
    eapply sim_st_choose_src. exists 0%nat. ss. left. pfold. econs; et.
    irw. Fail refl. left. pfold. econs; et. }

  unfold parse_arg in T. des_ifs.
  ss. rewrite ! T. ss. irw.
  unfold guarantee.
  destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  ss. des_ifs_safe. irw.
Abort.
  ------------------------------------
  pfold.
  irw.
  ss.
  destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  
  unfold guarantee. des_ifs.
  unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  unfold guarantee. destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  ss. des_ifs_safe. rewrite bind_ret_l.
  assert(n = n0).
  { unfold to_nat_opt, of_nat in U. des_ifs. rewrite Int.signed_repr.
    - rewrite Nat2Z.id. ss.
    - admit "more integer reasoning from below facts needed".
  }
  subst.
  rewrite fib_nat_recurse.
  eapply rtc_n1; cycle 1.
  { right. rewrite ! tau_eutt. refl. }
  fold rel_trans.


  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs_safe. rewrite ! bind_ret_l. ss.
  rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs. repeat (rewrite bind_ret_l; ss).
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. unfold unwrapU. des_ifs. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l.
  refl.





  unfold f_fib. unfold unwrapU. des_ifs.rewrite unfold_interp_mrec. ss. des_ifs; cycle 1.
  { irw. eapply rtc_once. left. unfold triggerNB. irw. pfold. econs; et. }
  rewrite ! bind_ret_l. ss.
  rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs. repeat (rewrite bind_ret_l; ss).
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. unfold unwrapU. des_ifs. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l.
  refl.
  econs.
  pfold.
Qed.

Theorem lemma
        m vs oh
  :
    sim_st 0%nat
           (* (match parse_arg oh m vs with *)
           (*  | Some n => fib_nat n *)
           (*  | _ => 0%nat *)
           (*  end) *)
           (interp_program prog (ICall Fib0._fib oh m vs))
           (interp_program FibS0.prog (ICall Fib0._fib oh m vs))
.
Proof.
  destruct (parse_arg oh m vs) eqn:T; cycle 1.
  { unfold interp_program, mrec. irw. des_ifs.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    unfold unwrapU. des_ifs. irw. pfold; econs; et.
  }
  clear_tac.
  eapply lemma_aux; et.

  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  destruct n.
  { unfold parse_arg in *. des_ifs.
    unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
    rewrite ! unfold_interp_mrec.
    unfold f_fib, FibS0.f_fib. ss. rewrite T. ss. irw. Fail refl. pfold. econs; et. }
  destruct n.
  { unfold parse_arg in *. des_ifs.
    unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
    rewrite ! unfold_interp_mrec.
    unfold f_fib, FibS0.f_fib. ss. rewrite T. ss. irw. Fail refl. pfold. econs; et. }

  unfold parse_arg in T. des_ifs.
  unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
  rewrite unfold_fib3. unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  unfold guarantee. destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  ss. des_ifs_safe. rewrite bind_ret_l.
  assert(n = n0).
  { unfold to_nat_opt, of_nat in U. des_ifs. rewrite Int.signed_repr.
    - rewrite Nat2Z.id. ss.
    - admit "more integer reasoning from below facts needed".
  }
  subst.
  rewrite fib_nat_recurse.
  eapply rtc_n1; cycle 1.
  { right. rewrite ! tau_eutt. refl. }
  fold rel_trans.


  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs_safe. rewrite ! bind_ret_l. ss.
  rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs. repeat (rewrite bind_ret_l; ss).
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. unfold unwrapU. des_ifs. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l.
  refl.





  unfold f_fib. unfold unwrapU. des_ifs.rewrite unfold_interp_mrec. ss. des_ifs; cycle 1.
  { irw. eapply rtc_once. left. unfold triggerNB. irw. pfold. econs; et. }
  rewrite ! bind_ret_l. ss.
  rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs. repeat (rewrite bind_ret_l; ss).
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. unfold unwrapU. des_ifs. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l.
  refl.
  econs.
  pfold.
Qed.

Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SimSIR.correct; ss.
  econs; try apply unit_ord_wf; ss.
  ii. clarify. exists tt.
  r.
  destruct (ident_eq fname Fib0._fib); cycle 1.
  { unfold interp_program, mrec. irw. des_ifs. irw. pfold. econs; et. }
  clarify.
  destruct (parse_arg oh_tgt m vs) eqn:T; cycle 1.
  { unfold interp_program, mrec. irw. des_ifs.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    unfold unwrapU. des_ifs. irw. pfold; econs; et.
  }
  clear_tac.

  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  destruct n.
  { unfold parse_arg in *. des_ifs.
    unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
    rewrite ! unfold_interp_mrec.
    unfold f_fib, FibS0.f_fib. ss. rewrite T. ss. irw. pfold. econs; et. }
  destruct n.
  { unfold parse_arg in *. des_ifs.
    unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
    rewrite ! unfold_interp_mrec.
    unfold f_fib, FibS0.f_fib. ss. rewrite T. ss. irw. pfold. econs; et. }

  unfold parse_arg in T. des_ifs.
  unfold interp_program, mrec. ss. des_ifs. cbn in Heq, Heq0. des_ifs. clear_tac.
  rewrite unfold_fib3. unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  unfold guarantee. destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  ss. des_ifs_safe. rewrite bind_ret_l.
  assert(n = n0).
  { unfold to_nat_opt, of_nat in U. des_ifs. rewrite Int.signed_repr.
    - rewrite Nat2Z.id. ss.
    - admit "more integer reasoning from below facts needed".
  }
  subst. irw. pfold.

  rewrite U.
  assert(U: to_nat_opt (of_nat n) = Some n).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. rewrite U. ss. des_ifs_safe. rewrite bind_ret_l.
  assert(V: to_nat_opt (of_nat (S n)) = Some (S n)).
  { admit "should be derived from guarantee". }
  des_ifs. unfold guarantee. rewrite V. ss. des_ifs.
  setoid_rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs.
  rewrite ! bind_ret_l. ss.
  rewrite unfold_interp_mrec. ss. rewrite ! bind_ret_l.
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. rewrite V. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l. refl.


  { irw. unfold interp_program, mrec. irw. des_ifs. unfold f_fib, FibS0.f_fib. irw.

  ginduction n; ii; ss.
  { unfold parse_arg in *. des_ifs. irw.
    unfold interp_program, mrec. irw. des_ifs.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    irw. unfold to_nat_opt in *. des_ifs. irw. des_ifs. irw. pfold. econs; et. }
  unfold parse_arg in T. des_ifs_safe.
  unfold interp_program, mrec. irw. des_ifs.
  unfold f_fib at 2. unfold FibS0.f_fib at 2. irw.
  my_tac. unfold unwrapU. des_ifs. irw.
  des_ifs.
  { pfold. econs; et. }
  rewrite ! range_to_nat; cycle 1.
  { admit "int reasoning". }
  { admit "int reasoning". }
  unfold guarantee. des_ifs; cycle 1. clear_tac.
  irw.
  assert(BDOOR: forall E R (it: itree E R), (tau;; it) = it).
  { admit "". }
  rewrite BDOOR.
  des_ifs.
  rewrite <- unfold_interp_mrec.
Abort.



Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SimSIR.correct; ss.
  econs; try apply unit_ord_wf; ss.
  ii. clarify. exists tt.
  r. unfold interp_program, mrec. irw.
  destruct (ident_eq fname Fib0._fib); cycle 1.
  { des_ifs. irw. pfold. econs; et. }
  clarify. des_ifs. clear_tac.
  repeat match goal with
  | [ |- context[interp_function ?H] ] =>
    let name := fresh "x" in set (name := (interp_function H)) in *
  end
  .
  unfold f_fib. irw.
  unfold FibS0.f_fib. irw.
  unfold unwrapU. des_ifs; cycle 1.
  { irw. pfold. econs; et. }
  rename Heq into T.
  irw.
  revert T.
  revert oh_tgt.
  revert vs.
  revert m.
  induction n; ii; ss.
  { unfold parse_arg in *. des_ifs. irw. pfold. econs; et. }
  unfold parse_arg in *. des_ifs_safe.
  destruct n.
  { irw. pfold. econs; et. }
  eapply sim_st_trans; cycle 1.
  {
Abort.
