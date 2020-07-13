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
Require Import Fib4.
Require Import Fib3.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.
Require Import ITreelib.
From Coq Require Import
     Morphisms RelationClasses.
(*** TODO: export in in SIRCommon or somewhere ***)

Set Implicit Arguments.

(* Ltac step := gstep; econs; et. *)
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

Hint Rewrite unfold_interp_mrec : itree_axiom2.
Hint Rewrite bind_ret_l : itree_axiom2.
Hint Rewrite bind_ret_r : itree_axiom2.
Hint Rewrite bind_tau : itree_axiom2.
Hint Rewrite bind_vis : itree_axiom2.
(* Hint Rewrite bind_trigger : itree_axiom2. *) (********* <---------removed this ***********)
Hint Rewrite bind_bind : itree_axiom2.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom2 in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom2; cbn).


Ltac iby TAC :=
  first [
      instantiate (1:= fun _ _ _ => _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- _ ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- _ ;; _) ;; _); irw; TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); irw; TAC|
      fail
    ]
.

Theorem correct: rusc defaultR [Fib4.module: Mod.t] [Fib3.module: Mod.t].
Proof.
  eapply SIRHoare.correct with (_fn:=Fib0._fib) (_fn_ru:=_fib_ru)
                               (precond:=precond) (postcond:=postcond); et.
  econs; ss; et.
  - econs; ss; cycle 1.
    + ii. iby refl.
    (* + ii. rewrite bind_bind. refl. *)
    + ii. clarify. unfold f_fib_ru.
      f_equiv; cycle 1.
      { pfold. unfold unwrapN. des_ifs; econs; et. }
      ii; clarify.
      des_ifs.
      { pfold. irw. econs; ss; et. }
      { pfold. irw. econs; ss; et. }
      cbn.
      f_equiv; cycle 1.
      { unfold guarantee, triggerNB. pfold. des_ifs; econs; et. }
      ii. clarify.
      pfold.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }
      ii. des_ifs_safe. left.
      f_equiv; cycle 1.
      { unfold guarantee, triggerNB. pfold. des_ifs; econs; et. }
      ii. clarify.
      pfold.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }
      ii. des_ifs_safe. left.
      pfold.
      econs; et.
  - ii. r. unfold Fib4.prog, prog. ss. des_ifs; ss.
Qed.
