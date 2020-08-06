From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require SimMemId SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon SIR SimSIR.

Require Import Program.
Require Import Simulation.
Require Import SIREuttGlobal.

Set Implicit Arguments.

Local Open Scope signature_scope.




Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let itr := itree (E owned_heap) (owned_heap * (mem * val)).

Definition match_itr: relation itr := fun i_src i_tgt => i_src ≈ i_tgt.

Let fn := function owned_heap.

Definition match_fn: relation (function owned_heap) := (eq ==> eq ==> eq ==> match_itr).

Definition match_prog: relation (program owned_heap) := (eq ==> option_rel match_fn).

End SYNTAX.
Hint Unfold match_itr match_fn match_prog.

Lemma match_prog_local_global_aux
      p_src p_tgt
      (SIMP: match_prog p_src p_tgt)
  :
    Relation.i_pointwise (fun _ => eutt eq) (interp_function p_src) (interp_function p_tgt)
.
Proof.
  ii.
  destruct a; ss.
  r in SIMP. exploit (SIMP name); et. intro U. rr in U. des_ifs; et.
  - eapply U; et.
  - refl.
Qed.

Theorem match_prog_local_global
        (p_src p_tgt: program owned_heap)
        (SIMP: match_prog p_src p_tgt)
  :
    (<<SIMP: SIREuttGlobal.match_prog p_src p_tgt>>)
.
Proof.
  ii.
  eapply Proper_interp_mrec; et.
  - eapply match_prog_local_global_aux; et.
  - eapply match_prog_local_global_aux; et.
Qed.





Section SIM.

  Variable md_src: SMod.t owned_heap.
  Variable md_tgt: SMod.t owned_heap.
  Let p_src := md_src.(SMod.prog).
  Let p_tgt := md_tgt.(SMod.prog).
  Let mi_src := md_src.(SMod.midx).
  Let mi_tgt := md_tgt.(SMod.midx).
  Hypothesis (SIMP: match_prog p_src p_tgt).
  Hypothesis (SIMMI: mi_src = mi_tgt).
  Hypothesis (SIMO: forall skenv, (md_src.(SMod.initial_owned_heap) skenv)
                                  = (md_tgt.(SMod.initial_owned_heap) skenv)).
  Hypothesis (SIMSK: md_src.(SMod.sk) = md_tgt.(SMod.sk)).
  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).
  Let SIMPG: SIREuttGlobal.match_prog p_src p_tgt. eapply match_prog_local_global; et. Qed.

  Theorem sim_mod: ModPair.sim mp.
  Proof. eapply SIREuttGlobal.sim_mod; et. Qed.

  Theorem correct: rusc defaultR [md_src: Mod.t] [md_tgt: Mod.t].
  Proof. eapply SIREuttGlobal.correct; et. Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold match_itr match_fn match_prog.
