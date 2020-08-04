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


Lemma interp_mrec_bind: forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
                               (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof.
  ii. f. eapply interp_mrec_bind.
Qed.



Lemma unfold_fib: forall oh0 m0 vs0,
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
      ≈
      (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      guarantee (parse_arg oh0 m0 vs0) ;;
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      guarantee (parse_arg oh1 m1 vs1) ;;
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
    { unfold triggerUB. irw. ITreelib.f_equiv. ii. ss. }
    irw. destruct n.
    { irw. refl. }
    destruct n.
    { irw. refl. }
    destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1.
    { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw. ITreelib.f_equiv. ii; ss. }
    unfold guarantee. des_ifs_safe. irw. rewrite tau_eutt.
    des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    (*** TODO: I just want to use "f_equiv". The problem here is that I added
`Require Import Morphisms.` after importing `ITreelib`.
Solution is to import `Morphisms` inside ITreelib.
***)
    { refl. }
    ii. des_ifs; cycle 1.
    { irw. unfold triggerNB. irw. ITreelib.f_equiv. ii; ss. }
    rewrite ! bind_ret_l.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    { irw. rewrite tau_eutt. des_ifs. refl. }
    { ii. des_ifs. irw. refl. }
  }
Qed.



Goal forall oh0 m0 vs0,
    (interp_mrec (interp_function prog) (f_fib oh0 m0 vs0)) ≈
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
.
Proof.
  ii.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS0.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.
  destruct n; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  rewrite unfold_fib. unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  assert(U: to_nat_opt (of_nat n) = Some n).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. rewrite U. ss. des_ifs_safe. rewrite bind_ret_l.
  assert(V: to_nat_opt (of_nat (S n)) = Some (S n)).
  { admit "should be derived from guarantee". }
  des_ifs. unfold guarantee. rewrite V. ss. des_ifs.


  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs. rewrite ! bind_ret_l. ss.
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
Qed.

Theorem correct: rusc defaultR [FibS2.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SIREutt.correct; ss.
  ii. clarify. rr.
  unfold FibS0.prog in *. ss. des_ifs.
  ii. clarify.
  rename y into oh0. rename y0 into m0. rename y1 into vs0.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS0.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  ginduction n; ii; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw.
  assert(U: to_nat_opt (of_nat n)).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. des_ifs_safe. irw.
Abort.
