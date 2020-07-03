From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Open Scope signature_scope.

Set Implicit Arguments.


Variable A B: Type.
Variable sim_A: A -> A -> Prop.
Variable sim_B: B -> B -> Prop.
Variable ctx: B -> A.

Global Instance sim_A_PreOrder: PreOrder sim_A.
Proof.
Admitted.

Global Instance sim_B_PreOrder: PreOrder sim_B.
Proof.
Admitted.

Global Instance ctx_good: Proper (sim_B ==> sim_A) ctx.
Admitted.

Variable b0 b1 b2: B.
(* Hypothesis SIM0: sim_A (ctx b0) (ctx b1). *)
(* Hypothesis SIM1: sim_A (ctx b1) (ctx b2). *)
Hypothesis SIM0: sim_B b0 b1.
Hypothesis SIM1: sim_B b1 b2.
Goal sim_A (ctx b0) (ctx b2).
Proof.
  etransitivity.
  { eapply ctx_good. eapply SIM0. }
  { eapply ctx_good. eapply SIM1. }
Qed.

Goal sim_A (ctx b0) (ctx b2).
Proof.
  erewrite SIM0.
  erewrite SIM1.
  reflexivity.
Qed.











Require Import CoqlibC.
Require Import Relation_Operators.

Inductive itree: Type :=
| Tau: itree -> itree
| Ret: nat -> itree
| Vis: itree -> itree
.

Inductive eutt: itree -> itree -> Prop :=
| eutt_ret
    n
  :
    eutt (Ret n) (Ret n)
| eutt_vis
    itr0 itr1
    (TL: eutt itr0 itr1)
  :
    eutt (Vis itr0) (Vis itr1)
| eutt_taul
    itr0 itr1
    (TL: eutt itr0 itr1)
  :
    eutt (Tau itr0) itr1
| eutt_taur
    itr0 itr1
    (TL: eutt itr0 itr1)
  :
    eutt itr0 (Tau itr1)
.

Program Instance eutt_Reflexive: Reflexive eutt.
Next Obligation.
  induction x; ii; ss; try (econsby et).
  econs. econs. et.
Qed.

Inductive eqv (r: nat -> nat -> Prop): itree -> itree -> Prop :=
| eqv_tau
    itr0 itr1
    (TL: eqv r itr0 itr1)
  :
    eqv r (Tau itr0) (Tau itr1)
| eqv_ret
    n m
    (REL: r n m)
  :
    eqv r (Ret n) (Ret m)
| eqv_vis
    itr0 itr1
    (TL: eqv r itr0 itr1)
  :
    eqv r (Vis itr0) (Vis itr1)
.

Program Instance eqv_Reflexive r `{Reflexive _ r}: Reflexive (eqv r).
Next Obligation.
  induction x; ii; ss; try (econsby et).
Qed.

Definition my_rel: itree -> itree -> Prop := rtc (eutt \2/ eqv le).


Module TEST0.
  Definition i0 := Tau (Vis (Ret 5)).
  Definition i1 := Vis (Tau (Ret 6)).

  Goal my_rel i0 i1.
  Proof.
    unfold i0, i1. r.
    econs.
    { left.
      eapply eutt_taul. refl.
    }
    (* econs. *)
    (* { right. *)
    (*   eapply eqv_vis. refl. *)
    (* } *)

    (*** I know "i1" so I can do this. ***)
    eapply rtc_n1; cycle 1.
    { left. econs; et. econsr; et. econs; et. }
    eapply rtc_once.
    { right. econs; et. econs; et. }
  Qed.
End TEST0.


Module TEST1.
  Definition i0 := Tau (Tau (Vis (Tau (Ret 5)))).
  Definition i1 := Tau (Vis (Tau (Tau (Ret 6)))).

  Goal my_rel i0 i1.
  Proof.
    unfold i0, i1. r.
    econs.
    { left.
      repeat (econs; eauto).
    }

    econs.
    { right. econs; eauto. instantiate (1:= Ret 6). econs; eauto. }

    econs.
    { left.
      eapply eutt_taur.
      econs; eauto.
      eapply eutt_taur.
      eapply eutt_taur.
      refl.
    }
    refl.
  Qed.
End TEST1.







































(*** refugee ***)
Require Import RUSC AdequacyLocal IdSimExtra.

Let rel_default := (mkPR SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
Theorem eutt_proof
        owned_heap
        (p_src p_tgt: program owned_heap)
        (SIM: (eq ==> (option_rel (eq ==> eq ==> eq ==> eutt eq)))%signature p_src p_tgt)
        sk mi init_oh
  :
    rusc (eq rel_default) [SIR.module sk p_src mi init_oh]
         [SIR.module sk p_tgt mi init_oh]
.
Proof.
Admitted.

Theorem rusc_format
  :
    rusc (eq rel_default) [Fib4.module] [Fib3.module]
.
Proof.
  unfold Fib4.module, Fib3.module.
  rewrite eutt_proof; cycle 1.
  { ii. clarify. unfold Fib4.prog.
    instantiate (1:= (add _fib_ru (fun _ _ _ => _) (add Fib0._fib (fun _ _ _ => _) empty))).
    ss. des_ifs.
    - ii. clarify. unfold f_fib_ru. rewrite tau_eutt. refl.
    - ii. clarify. refl.
  }
  eapply (@relate_single_rusc (eq rel_default) SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
  - ii. exists mp. esplits; ss; et. eapply sim_mod.
  - ss.
Qed.
