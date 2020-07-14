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
Require Import Fib3_new.
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






Ltac unfoldr term :=
  first[
      unfold term at 10|
      unfold term at 9|
      unfold term at 8|
      unfold term at 7|
      unfold term at 6|
      unfold term at 5|
      unfold term at 4|
      unfold term at 3|
      unfold term at 2|
      unfold term at 1|
      unfold term at 0
    ]
.

Ltac step :=
  match goal with
  | [ |- SIRLocal.match_itr eq (assume _ ;; _) (assume _ ;; _) ] =>
    fail "implement it. unfoldr assume; remember LHS as tmp; unfoldr assume; subst tmp"
  | [ |- SIRLocal.match_itr eq (guarantee _ ;; _) (guarantee _ ;; _) ] =>
    fail "implement it. unfoldr guarantee; remember LHS as tmp; unfoldr guarantee; subst tmp"
  | [ |- SIRLocal.match_itr eq (assume ?P ;; _) _ ] =>
    unfoldr assume;
    let name := fresh "_ASSUME" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      unfold triggerUB;
      rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
      pfold; by (econs; eauto)|irw]
  | [ |- SIRLocal.match_itr eq (guarantee ?P ;; _) _ ] =>
    unfoldr guarantee;
    let name := fresh "_GUARANTEE" in
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
    pfold; try (by econs; eauto)
  | [ |- SIRLocal.match_itr eq (Vis (subevent _ (ICall _ _ _ _)) _)
                            (Vis (subevent _ (ICall _ _ _ _)) _) ] =>
    pfold; eapply match_icall; ss; et
  | [ |- HProper _ _ _ ] => ii
  | [ H: SALL _ _ _ |- _ ] => r in H; des_ifs_safe; des; clarify
  | [ |- upaco2 (_match_itr ?SO) bot2 _ _ ] =>
    left;
    replace (paco2 (_match_itr SO) bot2) with (SIRLocal.match_itr (@eq owned_heap)) by ss;
    irw
  end
.

(*** TODO: make setoid rewrite under "Int.repr" or "Int.eqm" ***)
Lemma Int_repr_signed_repr
      x
  :
    Int.repr (Int.signed (Int.repr x)) = Int.repr x
.
Proof.
  eapply Int.eqm_samerepr.
  eapply Int.eqm_trans.
  { eapply Int.eqm_signed_unsigned. }
  eapply Int.eqm_sym.
  eapply Int.eqm_unsigned_repr.
Qed.

(*** NOTE: Current automation has some drawbacks.
Consider the following scenario.
```
guarantee P;;
guarantee Q;;
```
In the course of proving "P", we may prove some knowledge "R".
However, such knowledge is lost when it comes to prove "Q".

Possible solutions:
(1) For each intermediate knowledge "R", put explicit "guarantee".
(2) Make tactic to stop before each "guarantee".
(3) User manuallys controls "step" tactic (not just "repeat"ing it)
 ***)
Theorem correct: rusc defaultR [Fib3_new.module: Mod.t] [Fib2.module: Mod.t].
Proof.
  eapply SIRLocal.correct with (SO := eq); ss.
  prog_tac.
  (* replace (f_fib oh_tgt m vs) with (f_fib oh_tgt m vs >>= (fun x => Ret x)); cycle 1. *)
  (* { irw. ss. } *)
  unfold Fib3_new.f_fib, f_fib.
  repeat step.
  { r in _ASSUME. r. des. des_ifs. esplits; et.
    apply_all_once Int.same_if_eq. clarify. ss. u in *. des_ifs. }
  { r in _ASSUME. r. des. des_ifs. esplits; et.
    apply_all_once Int.same_if_eq. clarify. ss. u in *. des_ifs. }
  { r in _ASSUME. r. des. ss. u in *. des_ifs; et. exfalso.
    (*** TODO: automate integer reasoning ***)
    rewrite Int.eq_signed in *. des_ifs. clear_tac.
    rewrite Int.signed_zero in *. rewrite Int.signed_one in *; ss.
    rewrite Int.sub_signed in *; rewrite (Int.signed_repr 2) in *; ss.
    rewrite Int.signed_repr in *; cycle 1.
    { generalize (Int.signed_range i); i. generalize Int.min_signed_neg; i. split; try xomega. }
    xomega.
  }
  { des_ifs. des. clarify. r in _ASSUME. r in _GUARANTEE. r. des. u in *. des_ifs; et. exfalso.
    (*** TODO: automate integer reasoning ***)
    rewrite Int.eq_signed in *. des_ifs. clear_tac.
    rewrite Int.signed_zero in *. rewrite Int.signed_one in *; ss.
    rewrite Int.sub_signed in *.
    generalize (Int.signed_range i); i. generalize Int.min_signed_neg; i.
    rewrite (Int.signed_repr 1) in *; ss; try (by xomega).
    rewrite (Int.signed_repr 2) in *; ss; try (by xomega).
    rewrite (Int.signed_repr) in *; ss; try (by xomega).
  }
  { des_ifs_safe. des; clarify. ss. unfold precond, postcond in *.
    u in *. des. des_ifs_safe. clear_tac. esplits; et.
    f_equal. rewrite Int.add_signed.
    (*** TODO: automate integer reasoning ***)
    rewrite Int.eq_signed in *. des_ifs. clear_tac.
    rewrite Int.signed_zero in *. rewrite Int.signed_one in *; ss.
    rewrite ! Int.sub_signed in *.
    generalize (Int.signed_range i); i. generalize Int.min_signed_neg; i.
    rewrite (Int.signed_repr 1) in *; ss; try (by xomega).
    rewrite (Int.signed_repr 2) in *; ss; try (by xomega).
    rewrite (Int.signed_repr (Int.signed i - 2)) in *; ss; try (by xomega).
    rewrite (Int.signed_repr (Int.signed i - 1)) in *; ss; try (by xomega).

    assert(T: exists m,
              Z.to_nat (Int.signed i - 2) = m /\
              Z.to_nat (Int.signed i - 1) = S m /\
              Z.to_nat (Int.signed i) = S (S m)
          ).
    { destruct (Z.to_nat (Int.signed i)) eqn:T; ss.
      { rewrite <- Nat2Z.id in T. eapply Z2Nat.inj in T; ss. }
      destruct n1 eqn:U; ss.
      { rewrite <- Nat2Z.id in T. eapply Z2Nat.inj in T; ss. }
      esplits; eauto.
      - rewrite ! Z2Nat.inj_sub; ss. xomega.
      - rewrite ! Z2Nat.inj_sub; ss. xomega.
    }
    des. rewrite T. rewrite T0. rewrite T1. rewrite fib_nat_recurse.
    rewrite Nat2Z.inj_add. rewrite <- ! Int_add_repr. rewrite ! Int_repr_signed_repr. ss.
  }
Qed.
