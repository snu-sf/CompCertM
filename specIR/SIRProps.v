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
Require Import Mod ModSem Any Skeleton SimMod SimModSem.
Require Import Sound SoundTop SimMem SimMemId SimSymb.
Require Import SIRCommon SIR2 SIR3.

Require Import Program.

Set Implicit Arguments.



Local Existing Instance SimMemOh_default.
Global Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].

Section OWNEDHEAP.

Variable owned_heap: Type.
Variable initial_owned_heap: SkEnv.t -> owned_heap.





Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: program owned_heap.
Variable mi: string.
Let md_src: Mod.t := (SIR2.module prog mi initial_owned_heap).
Let md_tgt: Mod.t := (SIR3.module prog mi initial_owned_heap).
Hypothesis (INCLSRC: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt)).
Hypothesis (WF: SkEnv.wf skenv_link).

Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link)
                                              (SimSymbId.mk md_src md_tgt) sm_link.

Print SIR2.state.
Print SIR3.state.

(* Theorem sim_modsem: ModSemPair.sim msp. *)
(* Proof. *)
(*   econs; eauto. *)
(* Qed. *)

End SIMMODSEM.





Section SIMMOD.

(* Variable prog: program owned_heap. *)
(* Variable mi: string. *)

(* Definition mp: ModPair.t := SimSymbId.mk_mp (SIR0.module prog mi initial_owned_heap) *)
(*                                             (SIR2.module prog mi initial_owned_heap). *)

(* Theorem sim_mod: ModPair.sim mp. *)
(* Proof. *)
(*   econs; ss. *)
(*   - ii. inv SIMSKENVLINK. eexists. eapply sim_modsem; eauto. *)
(* Qed. *)

End SIMMOD.

End OWNEDHEAP.