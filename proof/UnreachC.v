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
Require Import Integers.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require SimSymbId.
Require Import SimMem.

Require Import Sound.
Require Unreach.
Include Unreach.

Set Implicit Arguments.


Definition val' (su: Unreach.t) (v: val): Prop :=
  forall blk ofs (PTR: v = Vptr blk ofs true), ~su blk
.

Definition memval' (su: Unreach.t) (mv: memval): Prop :=
  forall v q n (PTR: mv = Fragment v q n), su.(val') v
.

Inductive mem': Unreach.t -> Memory.mem -> Prop :=
| mem'_intro
    (su: Unreach.t) m0
    (SOUND: forall
        blk ofs
        (PUB: ~ su blk)
        (PERM: Mem.perm m0 blk ofs Cur Readable) (* <------------ Cur? *)
      ,
        su.(memval') (ZMap.get ofs (Mem.mem_contents m0) !! blk))
    (BOUND: su <1= m0.(Mem.valid_block))
    (* (BOUND: Ple su.(Unreach.nb) m0.(Mem.nextblock)) *)
  :
    mem' su m0
.

Hint Unfold val' memval'.

Definition le' (x y: Unreach.t): Prop :=
  (<<PRIV: x <1= y>>)
.

Global Program Instance Unreach: Sound.class := {
  t := Unreach.t;
  le := le';
  val := val';
  mem := mem';
  val_list := fun (su0: Unreach.t) => List.Forall su0.(val');
  get_greatest := admit "tttttttttttttt"
}
.
Next Obligation.
  eapply mle_monotone; eauto.
Qed.
Next Obligation.
Qed.

