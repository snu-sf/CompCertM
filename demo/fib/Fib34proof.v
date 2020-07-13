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



Ltac iby1 TAC :=
  first [
      instantiate (1:= fun '(_, (_, _)) => _); irw; TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- _ ;; _); irw; TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- _ ;; _) ;; _); irw; TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); irw; TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); irw; TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); irw; TAC|
      fail
    ]
.

Ltac step :=
  repeat match goal with
         | [ |- (_ ==> _)%signature _ _ ] => ii; clarify
         | [ |- SIRHoare.match_itr _ _ _ _ (_ <- _ ;; _) (_ <- _ ;; _) ] => f_equiv; cycle 1
         | [ |- SIRHoare.match_itr _ _ _ _ (unwrapN _) (unwrapN _) ] => 
           pfold; unfold unwrapN; des_ifs; try (by econs; et)
         | [ |- SIRHoare.match_itr _ _ _ _
                                   (match _ with _ => _ end)
                                   (match _ with _ => _ end) ] => des_ifs
         | [ |- SIRHoare.match_itr _ _ _ _ (Ret _) (Ret _) ] =>
           pfold; try (by econs; et)
         | [ |- SIRHoare.match_itr _ _ _ _ (guarantee _) (guarantee _) ] => 
           pfold; unfold guarantee; des_ifs; try (by econs; et)
         end
.
(*** TODO: change unwrapU/unwrapN/assume/guarantee into notation? ***)
(*** TODO: generalize "Hoare" like "BCE" --> put manifesto ***)

Theorem correct: rusc defaultR [Fib4.module: Mod.t] [Fib3.module: Mod.t].
Proof.
  eapply SIRHoare.correct with (_fn:=Fib0._fib) (_fn_ru:=_fib_ru)
                               (precond:=precond) (postcond:=postcond); et.
  econs; ss; et.
  - econs; ss; cycle 1.
    + ii. iby refl.
    (* + ii. rewrite bind_bind. refl. *)
    + unfold f_fib_ru.

      repeat step.

      pfold.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }

      ii. clarify. des_ifs_safe. left.
      f_equiv; cycle 1.
      { unfold guarantee, triggerNB. pfold. des_ifs; econs; et. }

      ii. clarify. pfold.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }

      ii. clarify. des_ifs_safe. left.

      pfold. econs; et.
  - prog_tac.
Qed.
