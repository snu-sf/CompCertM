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

(* Require Import IntegersC LinkingC. *)
(* Require Import SimSymb Skeleton Mod ModSem. *)
Require Import ModSem.
(* Require SimSymbId. *)
(* Require Import SimMem. *)

Require Import Sound.
Require Unreach.
Include Unreach.
Require Import SemiLattice.
Require Import FinFun.

Set Implicit Arguments.


Local Open Scope nat.

(* Let cons_sig *)
(*     X (P: X -> Prop) (Q: X -> Prop) (R: X -> Prop) *)
(*     (PR: P <1= R) *)
(*     (QR: Q <1= R) *)
(*     (x: { x: X | P x }) *)
(*     (xs: list { x: X | Q x}) *)
(*   : *)
(*     exists (xxs: list { x: X | R x}), *)
(*       exists hd tl, xxs = hd :: tl /\ <<HD: hd$ = x$>> /\ <<TL: List.map (@proj1_sig _ _) tl = List.map (@proj1_sig _ _) xs>> *)
(* . *)
(* Proof. *)
(*   admit "". *)
(*   (* ginduction xs; ii; ss. *) *)
(* Qed. *)

(* Lemma Finite_sig *)
(*       X (P: X -> Prop) *)
(*       (FIN: exists l, forall x (PROP: P x), In x l) *)
(*   : *)
(*     <<FIN: FinFun.Finite { x: X | P x }>> *)
(* . *)
(* Proof. *)
(*   des. rr. ginduction l; ii; ss. *)
(*   - exists []. rr. i. destruct a. eauto. *)
(*   - destruct (classic (P a)); cycle 1. *)
(*     { exploit IHl; eauto. i. exploit FIN; eauto. i; des; clarify; eauto. } *)
(*     specialize (IHl (fun x => P x /\ a <> x)). *)
(*     exploit IHl; eauto. *)
(*     { ii. des. exploit FIN; eauto. i; des; clarify. } *)
(*     i; des. *)
(*     unfold FinFun.Full. *)
(*     assert(exists (hd: {x: X | , hd $ = a). *)
(*     exploit (cons_sig _ _ a l0); eauto. *)
(*     exists (a :: l0). *)
(*               exploit IHl; eauto. i. *)
(*   exists l. *)
(*   econs; eauto. *)
(* Qed. *)

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

(* TODO: I really don't want to define this. It is redundant with `Sound.args`, but it seems there is no other way *)
Definition args' (su: Unreach.t) (args0: Args.t) :=
  (<<VAL: val' su (Args.fptr args0)>>)
  /\ (<<VALS: List.Forall su.(val') (Args.vs args0)>>)
  /\ (<<MEM: mem' su (Args.m args0)>>)
.

Let lub (x y: t): t := x \1/ y.
Hint Unfold lub.

(* Inductive flatten_list: block -> list t -> Prop := *)
(* | flatten_list_nil *)
(*   : *)
(*     flatten_list 1%positive [] *)
(* | flatten_list_cons *)
(*     nb xs *)
(*     (LIST: flatten_list nb xs) *)
(*   : *)
(*     flatten_list (nb + 1)%positive (xs ++ xs) *)
(* . *)
Lemma not_ex_all_not
      U (P: U -> Prop)
      (NEX: ~ (exists n : U, P n))
  :
    <<NALL: forall n : U, ~ P n>>
.
Proof. eauto. Qed.

Lemma finite_map
      X (P: X -> Prop) Y
      (j: X -> Y)
      (INJ: Injective j)
      (FIN: exists ly, forall x, P x -> In (j x) ly)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  rr in FIN. des.
  ginduction ly; ii; ss.
  { exists []. ii. exploit FIN; eauto. }
  rename a into y0.
  specialize (IHly X (fun x => P x /\ j x <> y0) j INJ).
  exploit IHly; eauto.
  { ii. des. exploit FIN; eauto. i; des; ss; clarify. }
  i; des.
  destruct (classic (exists x0, j x0 = y0)); cycle 1.
  { eapply not_ex_all_not in H0. exists lx. i. eapply H. esplits; eauto. }
  des.
  exists (x0 :: lx).
  i. ss.
  destruct (classic (x0 = x)); eauto.
  right. eapply H; eauto. esplits; eauto. ii.
  assert(x0 = x).
  { eapply INJ. congruence. }
  clarify.
Qed.

Fixpoint range (n: nat): list nat :=
  match n with
  | 0%nat => [0]
  | S n => (S n) :: range n
  end
.

Lemma range_0
      bound
  :
    In 0 (range bound)
.
Proof.
  ginduction bound; ii; ss; try tauto.
Qed.

Lemma range_spec
      x bound
      (BDD: (x <= bound))
  :
    In x (range bound)
.
Proof.
  admit "ez".
Qed.

Lemma finite_nat
      X (P: X -> Prop)
      (j: positive -> X -> option nat)
      (fuel: positive)
      (INJ: Injective (j fuel))
      (FIN: exists bound, forall x, P x -> exists n, j fuel x = Some n /\ (n <= bound))
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  eapply finite_map with (j := j fuel); eauto. des.
  exists (map Some (range bound)). ii. exploit FIN; eauto. i.
  des; ss. rewrite H0.
  rewrite in_map_iff. esplits; eauto. eapply range_spec; eauto.
Qed.

Global Program Instance Unreach: Sound.class := {
  t := Unreach.t;
  le := le';
  val := val';
  mem := mem';
  val_list := fun (su0: Unreach.t) => List.Forall su0.(val');
  get_greatest (args: Args.t) := greatest le' (fun su => su.(args') args);
  top := bot1;
}
.
Next Obligation.
  eapply mle_monotone; eauto.
Qed.
Next Obligation.
  rr in GR0. rr in GR1. des.
  assert(le' su0 su1).
  { eauto. }
  assert(le' su1 su0).
  { eauto. }
  rr in H. rr in H0.
  apply func_ext1; i.
  apply prop_ext1. split; i; eauto.
Qed.
Next Obligation.
  rr in GR. des. eapply MAX; eauto. econs; eauto.
Qed.
Next Obligation.
  eapply find_greatest with (lub:= lub); eauto.
  - econs; ii; eauto.
  - ii. esplits; rr; eauto.
  - rr. destruct args0.
    eapply finite_nat; eauto.
  - ii. inv PX. inv PY. des. u in *.
    rewrite Forall_forall in *.
    econs; esplits; u; ii; ss; des; eauto.
    { rewrite Forall_forall in *. ii; ss; des; eauto. }
    inv MEM0. inv MEM.
    econs; ss.
    + ii; clarify. Nsimpl. des_safe; eauto.
      unfold memval', val' in *.
      hexpl SOUND; hexpl SOUND0; eauto.
    + ii. des; eauto.
  - exists bot1. rr. esplits; ii; ss; eauto.
    + rewrite Forall_forall. ii; ss.
    + econs; eauto. ii; ss.
Qed.
Next Obligation.
  rr in GR. des. eauto.
Qed.
Next Obligation.
  admit "---------------------------------------------".
Qed.
Next Obligation.
  esplits; ii; ss; eauto. econs; ii; ss; eauto.
Qed.

