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
Theorem correct: rusc defaultR [FibS3.module: Mod.t] [Fib2.module: Mod.t].
Proof.
  assert(AA := range_to_nat).
  assert(SUCPRED := succ_pred).

  eapply SIRLocal.correct with (SO := eq); ss.
  prog_tac.
  ginit. { i. eapply cpn2_wcompat; eauto with paco. }
  unfold FibS3.f_fib, f_fib.
  unfold unwrapU.
  destruct (parse_arg oh_tgt m vs) eqn:T; cycle 1.
  { unfold triggerUB. irw. gstep. econs; ss; et. }
  irw. unfold parse_arg in T. des_ifs_safe.
  destruct n.
  { irw.
    (*** TODO: make lemma ***)
    assert(i = Int.zero).
    { clear - T.
      unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 0).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    des_ifs_safe. gstep. econs; ss; et.
  }
  destruct n.
  { irw.
    (*** TODO: make lemma ***)
    assert(i = Int.one).
    { clear - T.
      unfold to_nat_opt in *. des_ifs.
      assert((Int.signed i) = 1).
      { apply Z2Nat.inj; ss. }
      apply func_app with (f:=Int.repr) in H. rewrite Int.repr_signed in H. ss.
    }
    des_ifs_safe. gstep. econs; ss; et.
  }
  assert(~Int.eq i Int.zero).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  assert(~Int.eq i Int.one).
  { ii. apply_all_once Int.same_if_eq. clarify. }
  des_ifs_safe.
  irw.
  assert(U: of_nat n = Int.sub i (Int.repr 2)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply SUCPRED in H2; des.
    eapply SUCPRED in H2; des. ss. clarify.
    (* rewrite <- Nat.sub_add_distr. ss. *)
    rewrite Nat2Z.inj_sub; ss. rewrite Nat2Z.inj_sub; ss. rewrite <- Z.sub_add_distr; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  assert(V: of_nat (S n) = Int.sub i (Int.repr 1)).
  { unfold to_nat_opt in *. des_ifs. unfold of_nat.
    eapply SUCPRED in H2; des.
    eapply SUCPRED in H2; des. ss. clarify.
    rewrite Nat.sub_1_r. rewrite Nat.succ_pred; ss; cycle 1.
    { intro X. rewrite X in *. inv H3. }
    rewrite Nat2Z.inj_sub; ss.
    rewrite <- Int_sub_repr. f_equal. rewrite Z2Nat.id; ss. rewrite Int.repr_signed; ss.
  }
  rewrite <- U.
  rewrite <- V.
  gstep. econs; ss; et. ii. rr in H1. des_ifs. des; clarify. irw.
  gstep. econs; ss; et. ii. rr in H1. des_ifs. des; clarify. irw.
  gstep. econs; ss; et.
Qed.
