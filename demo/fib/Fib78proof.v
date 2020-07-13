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
Require Import Fib8.
Require Import Fib7.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.
Require Import MatchSimModSemExcl.

Set Implicit Arguments.


Let mp: ModPair.t := (SimSymbId.mk_mp Fib8.module Fib7.module).
Theorem correct: rusc defaultR [Fib8.module: Mod.t] [Fib7.module: Mod.t].
Proof.
  eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto.
  econs; ss; et. ii. exists (SimMemOh_default_aux _ (Some "fib")).
  econs; ss; et.
  { apply SoundTop.sound_state_local_preservation; et. }
  { ii. eapply Preservation.local_preservation_noguarantee_weak.
    apply SoundTop.sound_state_local_preservation; et.
  }
  { ii. esplits; et. }
  { ii. ss. esplits; et.
    - ii. inv INITTGT. ss. des_ifs. inv SIMSKENV; ss. r in SIMSKE. r in SIMSKELINK. clarify.
      rr in SIMARGS; des. ss. clarify. inv SIMARGS0; ss. clarify. clear_tac.
      assert(fid = Fib0._fib).
      { admit "ez - UNSYMB". }
      clarify. inv SAFESRC. ss. clarify.
      esplits; et.
      { econs; ss; et. }
      pfold. econs 4; try refl; ss; et.
      { econs; ss. unfold interp_program, mrec. irw. des_ifs. unfold f_fib. irw.
        unfold unwrapU. des_ifs. }
      econs; ss; et. econs; ss; et.
    - i; des. inv SAFESRC. ss. destruct args_src; ss. clarify.
      rr in SIMARGS; des. ss. clarify. inv SIMARGS0; ss. clarify. ss. des_ifs. clear_tac.
      inv SIMSKENV. ss. r in SIMSKE. r in SIMSKELINK. clarify.
      esplits; ss; et.
      econs; ss; et.
      + assert(sg_init_src = signature_of_function Fib0.f_fib).
        { admit "ez - sig". }
        clarify. unfold signature_of_function. ss. econs; ss; et.
        unfold typify_list. cbn. unfold typify. des_ifs; ss.
      + econs; ss; et.
  }
Unshelve.
- apply unit.
- apply (Ord.lift_idx unit_ord_wf tt).
Qed.
