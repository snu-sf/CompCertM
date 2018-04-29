Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Asmregs.
Require Import Integers.

Require Import Skeleton.
Require Import Mod.
Require Import ModSem.
Require Import SimSymb.
Require Import SimSymbId.
Require Import SimMem.

Set Implicit Arguments.




Record t' := mkrelation {
  src_mem: mem;
  tgt_mem: mem;
}.

Program Instance MemRelId : SimMem.class SimSymbId :=
{
  t := t';
  src_mem := src_mem;
  tgt_mem := tgt_mem;
  wf := fun (rel: t') => rel.(src_mem) = rel.(tgt_mem);
  le := fun (mrel0 mrel1: t') => True;
  lift := id;
  unlift := fun _ => id;
  sim_val := fun (_: t') => eq;
}.
Next Obligation.
  ss.
Qed.
(* Next Obligation. *)
(*   eexists (mkrelation _ _). *)
(*   esplits; ss; eauto. *)
(*   inv WF. ss. *)
(*   clear_tac. *)
(*   assert(NOCOVER0: forall id, <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>). *)
(*   { i. eapply NOCOVER. eauto. } *)
(*   clear NOCOVER. *)
(*   clear_tac. *)
(*   econs; eauto. *)
(*   - admit "This should hold; Maybe ""Genv.init_mem_match"" and ""Genv.init_mem_genv_next"" might help". *)
(*   - admit "This should hold;". *)
(* Qed. *)

