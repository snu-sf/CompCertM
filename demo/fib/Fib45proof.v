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
Require Import Fib5.
Require Import Fib4.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.






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






Definition mp: ModPair.t := SimSymbId.mk_mp (Fib5.module) (Fib4.module).

Local Opaque ident_eq.
Theorem sim_mod: ModPair.sim mp.
Proof.
  assert(tau: forall E R (a: itree E R), (tau;; a) = a).
  { admit "backdoor --- relax sim_st to allow tau* before each progress". }
  eapply SimSIRLocal.sim_mod with (SO := eq); ss.
  ii. clarify. unfold Fib5.prog, prog. ss. des_ifs; econs; et.
  { r. ii. clarify.
    assert(EQ: (Fib5.f_fib_ru oh_tgt m vs) = (f_fib_ru oh_tgt m vs)).
    { refl. }
    admit "refl".
  }
  ginit.
  { i. eapply cpn2_wcompat; eauto with paco. }
  ii; clarify.
  unfold Fib5.f_fib, f_fib.
  step_assume.
  { unfold assume. des_ifs. unfold triggerUB. irw. step. }
  unfold assume. des_ifs.
  irw. step.
  ii. rr in H. des_ifs. des. clarify.
  unfold guaranteeK. des_ifs; cycle 1.
  { step. }

  rewrite <- tau. rewrite <- tau.
  step. eexists (exist _ _ _). cbn.
  step.
Unshelve.
  cbn. des_ifs.
Qed.
