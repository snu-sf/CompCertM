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
Require Import FibS3.
Require Import FibS4.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.


(*** TODO: move to CoqlibC ***)
Lemma interp_mrec_bind: forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
                               (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof.
  ii. f. eapply interp_mrec_bind.
Qed.



Lemma unfold_fib: forall oh0 m0 vs0,
    (interp_mrec (interp_function FibS3.prog) (FibS3.f_fib oh0 m0 vs0))
      ≈
      (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS3.prog) (FibS3.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS3.prog) (FibS3.f_fib oh1 m1 vs1)) ;;

      Ret (oh2, (m2, Val.add y1 y2))
    end
      )
.
Proof.
  {
    i. irw.
    unfold FibS3.f_fib at 2. irw.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. irw. ITreelib.f_equiv. ii. ss. }
    irw. destruct n.
    { irw. refl. }
    destruct n.
    { irw. refl. }
    irw. rewrite tau_eutt.
    des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    (*** TODO: I just want to use "f_equiv". The problem here is that I added
`Require Import Morphisms.` after importing `ITreelib`.
Solution is to import `Morphisms` inside ITreelib.
***)
    { refl. }
    ii. des_ifs.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    { irw. rewrite tau_eutt. des_ifs. refl. }
    { ii. des_ifs. irw. refl. }
  }
Qed.

Theorem match_itr
        oh0 m0 vs0
  :
    (interp_mrec (interp_function prog) (f_fib oh0 m0 vs0)) ≈
    (interp_mrec (interp_function FibS3.prog) (FibS3.f_fib oh0 m0 vs0))
.
Proof.
  ii.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS3.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.
  destruct n; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS3.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS3.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  rewrite unfold_fib. unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  assert(W: Z.of_nat (S (S n)) <= Int.max_signed).
  { unfold to_nat_opt in *. des_ifs. rewrite <- H1. rewrite Z2Nat.id; ss. apply Int.signed_range. }
  assert(U: to_nat_opt (of_nat n) = Some n).
  { rewrite range_to_nat; ss. xomega. (*** "should be derived from guarantee". ***) }
  assert(V: to_nat_opt (of_nat (S n)) = Some (S n)).
  { rewrite range_to_nat; ss. xomega. (*** "should be derived from guarantee". ***) }


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
  rewrite fib_nat_recurse. unfold of_nat. rewrite Int_add_repr. rewrite Nat2Z.inj_add. refl.
Qed.

Theorem correct: rusc defaultR [FibS4.module: Mod.t] [FibS3.module: Mod.t].
Proof.
  eapply SIREuttGlobal.correct; ss.
  ii. destruct icall; ss. unfold interp_program, mrec. ss.
  cbn. des_ifs.
  - eapply match_itr; et.
  - irw. f_equiv. ii; ss.
Qed.
