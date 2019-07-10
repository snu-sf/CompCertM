(** Libraries. *)
Require Import String.
Require Import CoqlibC Errors ErrorsC.
Require Import AST Linking Smallstep.
(** Command-line flags. *)
Require Import Compopts.
(** newly added **)
Require Import BehaviorsC.
Require Export Compiler.
Require Import Simulation.
Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import SemProps AdequacyLocal.

Require SimMemInjInvC.

Require Import RUSC.

Require Import MutrecHeader.
Require Import MutrecAspec MutrecBspec MutrecABspec MutrecA MutrecB.
Require Import MutrecABproof MutrecAproof MutrecBproof.

Require IdSimAsmIdInv.
Require IdSimClightIdInv.


Definition mutrec_relations :=
  fun r => exists P, r = mkPR (SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P)
                              (SimMemInjInvC.SimSymbIdInv P)
                              SoundTop.Top.

Lemma asm_self_related (asm: Asm.program)
  :
    self_related mutrec_relations [asm.(AsmC.module)].
Proof.
  intros r RELIN. unfold mutrec_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  exploit IdSimAsmIdInv.asm_inj_inv_id; ss; eauto.
Qed.

Lemma clight_self_related (cls: Clight.program)
  :
    self_related mutrec_relations [cls.(ClightC.module2)].
Proof.
  intros r RELIN. unfold mutrec_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  exploit IdSimClightIdInv.clight_inj_inv_id; ss; eauto.
Qed.

Lemma asms_self_related (asms: list Asm.program)
  :
    self_related mutrec_relations (map AsmC.module asms).
Proof.
  induction asms; ss; ii.
  exploit IHasms; ss; eauto. i.
  eapply (@program_relation.horizontal _ [a.(AsmC.module)] _ [a.(AsmC.module)]); eauto.
  eapply asm_self_related; eauto.
Qed.

Lemma clights_self_related (cls: list Clight.program)
  :
    self_related mutrec_relations (map ClightC.module2 cls).
Proof.
  induction cls; ss; ii.
  exploit IHcls; ss; eauto. i.
  eapply (@program_relation.horizontal _ [a.(ClightC.module2)] _ [a.(ClightC.module2)]); eauto.
  eapply clight_self_related; eauto.
Qed.


Require IdSimMutrecAIdInv.

Lemma specA_self_related
  :
    self_related mutrec_relations [MutrecAspec.module].
Proof.
  intros r RELIN. unfold mutrec_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  exploit IdSimMutrecAIdInv.a_inj_inv_id; ss; eauto.
Qed.

Require IdSimMutrecBIdInv.

Lemma specB_self_related
  :
    self_related mutrec_relations [MutrecBspec.module].
Proof.
  intros r RELIN. unfold mutrec_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  exploit IdSimMutrecBIdInv.b_inj_inv_id; ss; eauto.
Qed.

Lemma MutrecA_rusc
  :
    rusc mutrec_relations [MutrecAspec.module] [MutrecA.prog.(ClightC.module2)].
Proof.
  eapply (@relate_single_rusc
            _
            (SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv MutrecAproof.memoized_inv)
            (SimMemInjInvC.SimSymbIdInv MutrecAproof.memoized_inv)
            SoundTop.Top).
  - set MutrecAproof.sim_mod. unfold relate_single. i. esplits; ss; eauto.
  - unfold mutrec_relations. eauto.
Qed.

Lemma MutrecB_rusc
  :
    rusc mutrec_relations [MutrecBspec.module] [MutrecB.prog.(AsmC.module)].
Proof.
  eapply (@relate_single_rusc
            _
            (SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv MutrecBproof.memoized_inv)
            (SimMemInjInvC.SimSymbIdInv MutrecBproof.memoized_inv)
            SoundTop.Top).
  - set MutrecBproof.sim_mod. unfold relate_single. i. esplits; ss; eauto.
  - unfold mutrec_relations. eauto.
Qed.

Theorem MutrecAB_AB_rusc
  :
    rusc bot1 [(MutrecABspec.module)] [(MutrecAspec.module) ; (MutrecBspec.module)]
.
Proof.
  unfold rusc. i. eapply mutrecABcorrect.
Qed.

Lemma MutrecAB_impl_rusc
 :
   rusc mutrec_relations
        [MutrecABspec.module]
        [MutrecA.prog.(ClightC.module2); MutrecB.prog.(AsmC.module)].
Proof.
 etrans.
 - eapply rusc_mon; [|eapply MutrecAB_AB_rusc]; ss.
 - hexploit rusc_horizontal.
   + eapply MutrecA_rusc.
   + eapply MutrecB_rusc.
   + eapply specA_self_related.
   + eapply specB_self_related.
   + eapply clight_self_related.
   + eapply asm_self_related.
   + i. eauto.
Qed.

Theorem Mutrec_correct
        (srcs: list Clight.program)
        (hands: list Asm.program)
  :
    improves (sem ((map ClightC.module2 srcs) ++ (map AsmC.module hands) ++ [MutrecABspec.module]))
             (sem ((map ClightC.module2 srcs) ++ (map AsmC.module hands) ++ [MutrecA.prog.(ClightC.module2); MutrecB.prog.(AsmC.module)])).
Proof.
  replace (map ClightC.module2 srcs ++ map AsmC.module hands ++ [MutrecABspec.module]) with
      ((map ClightC.module2 srcs ++ map AsmC.module hands) ++ [MutrecABspec.module]); cycle 1.
  { rewrite app_assoc. auto. }
  replace (map ClightC.module2 srcs ++ map AsmC.module hands
               ++ [ClightC.module2 MutrecA.prog; AsmC.module prog]) with
      ((map ClightC.module2 srcs ++ map AsmC.module hands) ++ [ClightC.module2 MutrecA.prog; AsmC.module prog]); cycle 1.
  { rewrite app_assoc. auto. }
  eapply rusc_adequacy_left_ctx.
  - eapply MutrecAB_impl_rusc.
  - eapply self_related_horizontal.
    + eapply clights_self_related.
    + eapply asms_self_related.
Qed.
