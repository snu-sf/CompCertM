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
Require Import Fib6.
Require Import Fib5.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.






(*** TODO: update Ord.v ***)
Section WFMAP.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Variable idx_map: Type.
  Variable f: idx_map -> idx.
  Definition ord_map (b0 b1: idx_map): Prop := ord (f b0) (f b1).

  Theorem wf_map: well_founded ord_map.
  Proof.
    ii. rename a into b.
    remember (f b) as a. generalize dependent b.
    pattern a. eapply well_founded_ind; et. clear a; i.
    clarify. econs; et.
  Qed.

End WFMAP.

Section WFOPTION.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Let idx_option: Type := option idx.
  Inductive ord_option: idx_option -> idx_option -> Prop :=
  | ord_option_some
      i0 i1
      (ORD: ord i0 i1)
    :
      ord_option (Some i0) (Some i1)
  .

  Theorem wf_option: well_founded ord_option.
  Proof.
    ii.
    induction a; ii; ss.
    { pattern a. eapply well_founded_ind; et. clear a; i.
      econs; et. ii. inv H0. eapply H; et. }
    { econs. ii. inv H. }
  Qed.

End WFOPTION.

Section WFPMAP.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Variable idx_pmap: Type.
  Variable f: idx_pmap -> option idx.
  Definition ord_pmap (b0 b1: idx_pmap): Prop := (ord_map (ord_option ord) f) b0 b1.

  Theorem wf_pmap: well_founded ord_pmap.
  Proof.
    eapply wf_map. eapply wf_option. assumption.
  Qed.

End WFPMAP.




















Theorem Int_ltu_wf: well_founded Int.ltu.
Proof.
  assert(ACC0: forall x: Z, 0 <= x < Int.modulus -> (Acc Int.ltu (Int.repr x))).
  {
    intro x. pattern x. eapply well_founded_ind. { eapply Z.lt_wf. } clear x. i. ss.
    instantiate (1:= 0) in H.
    econs. ii.
    generalize (Int.unsigned_range y); i.
    destruct (classic (x = 0)).
    - clarify. exfalso.
      unfold Int.ltu in *. des_ifs. ss. rewrite Int.unsigned_repr in *; ss.
      lia.
    - exploit (H (Int.unsigned y)); et.
      { unfold Int.ltu in H1. des_ifs.
        split; try lia.
        rewrite Int.unsigned_repr in *; try lia. unfold Int.max_unsigned. lia.
      }
      intro T. rewrite Int.repr_unsigned in *. ss.
  }
  assert(ACC1: forall x: Int.int, 0 <= (Int.unsigned x) < Int.modulus -> (Acc Int.ltu x)).
  {
    i. exploit ACC0; et. intro T. rp; et. rewrite Int.repr_unsigned; ss.
  }
  ii.
  eapply ACC1; et. generalize (Int.unsigned_range a). i. xomega.
Qed.












Definition mp: ModPair.t := SimSymbId.mk_mp (Fib6.module) (Fib5.module).

Require Import SIRBCE. (*** TODO: export in SIRProps ***)
Local Opaque ident_eq.

(*** TODO: use prop instead of option ***)
Let idx := option (Int.int * nat).
Definition manifesto (fname: ident): option (owned_heap -> mem -> list val -> idx) :=
  if ident_eq fname _fib_ru
  then Some (fun oh m vs => match vs with | [Vint n] => Some (n, 1%nat) | _ => None end)
  else None
.

Theorem correct: rusc defaultR [Fib6.module: Mod.t] [Fib5.module: Mod.t].
Proof.
  etrans.
  { mimic. eapply SIREutt.correct; ss.
    prog_tac.
    unfold Fib6.f_fib. setoid_rewrite <- tau_eutt at 2. refl.
  }
  eapply SIRBCE.correct with (manifesto:=manifesto); et.
  { eapply wf_option. eapply ord_lex_wf; try apply lt_wf; try apply Int_ltu_wf. }
  econs; et; cycle 1.
  { prog_tac.
    - unfold Fib6.f_fib, f_fib. irw.
      f_equiv; cycle 1.
      { pfold. unfold assume. des_ifs; econs; et. }
      ii. clarify. rewrite <- ! bind_trigger. pfold. eapply match_icall_pure; et.
      left. pfold. irw. econs; et. ii; ss. clarify.
      left. pfold. irw. econs; et.
  }
  { ii. unfold manifesto in PURE. des_ifs.
    esplits; et.
    { unfold prog. ss. }
    ii. unfold f_fib_ru.
    des_ifs; try (by pfold; unfold triggerNB; irw; econs; et).
    irw. unfoldr guarantee. des_ifs; [irw|pfold; unfold triggerNB; irw; econs; et].
    pfold. econs; et.
    irw.
    {
      assert(0 <= (Int.signed i)).
      { admit "". }
      assert(0 <= (Int.signed (Int.sub i (Int.repr 2)))).
      { admit "". }
      unfold to_nat_opt.
      des_ifs.
      econs; et. econs; et.
      cbn. rewrite range_to_nat; cycle 1.
      { u in T. des_ifs. }
      cbn. econs; et. econs; et.
    }
    {
    des_ifs_safe.
    des_ifs; irw; cycle 1.
    { unfold triggerNB. irw. econs; et. }
    des_ifs; try econs; et. irw.
    step_guarantee.
    { econs; et. }
    irw.
    econs; ss; et; cycle 1.
    { cbn. rewrite range_to_nat; cycle 1.
      { u in T. des_ifs. }
      cbn. econs; et. econs; et.
    }
    ii. esplits; et.
    { econs; et. econs 2; et. }
    left. pfold. des_ifs. irw.
    step_guarantee.
    { econs; et. }
    irw.
    econs; ss; et; cycle 1.
    { cbn. rewrite range_to_nat; cycle 1.
      { u in T0. des_ifs. }
      econs; et. econs; et.
    }
    ii. esplits; et.
    { econs; et. econs; et. }
    left. pfold. des_ifs. econs; et.
  }
Unshelve.
  all: ss.
  all: try (by sk_incl_tac).
Qed.

Theorem lt_wf: well_founded Int.lt.
Proof.
  (* replace (fun x y => is_true (Int.lt x y)) with (fun x y => Z.lt (Int.signed x) (Int.signed y)); cycle 1. *)
  (* { unfold Int.lt. apply func_ext2. ii. des_ifs. *)
  (*   - apply AxiomsC.prop_ext. split; i; ss. *)
  (*   - apply AxiomsC.prop_ext. split; i; ss. *)
  (* } *)
  (* replace (fun x y => Z.lt (Int.signed x) (Int.signed y)) with (ord_map Z.lt Int.signed); cycle 1. *)
  (* { ss. } *)
  (* eapply wf_map with (f:=Int.signed). *)
  (* eapply Z.lt_wf. *)
  assert(ACC: forall x: Z, 0 <= x < Int.modulus -> (Acc Int.lt (Int.repr x))).
  {
    intro x. pattern x.
    eapply well_founded_ind.
    { eapply Z.lt_wf. }
    clear x.
    i. ss.
    econs; et. ii.
    destruct (classic (x = 0)).
    - exfalso. clarify. unfold Int.lt in H1. des_ifs.
      rewrite Int.signed_repr in *; ss.
      destruct y; ss. unfold Int.signed in *. ss. des_ifs; try xomega.
      xomega.
      xomega.
    eapply H.
  }
  assert(ACC: forall x: Z, 0 <= x -> (forall i, Int.signed i = x -> Acc Int.lt i)).
  { i. eapply Z_lt_induction; et. ii.
    destruct (classic (0 < x0 )).
    { eapply H1. instantiate (1:= x0 - 1). xomega. }
    
  }
  ii. destruct a.
  pattern (Int.signed a).
  eapply well_founded_ind.
  { eapply Z.lt_wf. }
  i.
Z_lt_abs_induction:
  forall P : Z -> Prop,
  (forall n : Z, (forall m : Z, Z.abs m < Z.abs n -> P m) -> P n) -> forall n : Z, P n
Z_lt_induction:
  forall P : Z -> Prop,
  (forall x : Z, (forall y : Z, 0 <= y < x -> P y) -> P x) -> forall x : Z, 0 <= x -> P x
Z.bi_induction:
  forall P : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful Z.eq iff) P ->
  P 0 -> (forall x : Z, P x <-> P (Z.succ x)) -> forall z : Z, P z
Z.central_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z, A z -> (forall n : Z, A n <-> A (Z.succ n)) -> forall n : Z, A n
Z.right_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z, A z -> (forall n : Z, z <= n -> A n -> A (Z.succ n)) -> forall n : Z, z <= n -> A n
Z.right_induction':
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, n <= z -> A n) -> (forall n : Z, z <= n -> A n -> A (Z.succ n)) -> forall n : Z, A n
Z.left_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z, A z -> (forall n : Z, n < z -> A (Z.succ n) -> A n) -> forall n : Z, n <= z -> A n
Z.left_induction':
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, z <= n -> A n) -> (forall n : Z, n < z -> A (Z.succ n) -> A n) -> forall n : Z, A n
Z.strong_right_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, z <= n -> (fun n0 : Z => forall m : Z, z <= m -> m < n0 -> A m) n -> A n) ->
  forall n : Z, z <= n -> A n
Z.strong_left_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, n <= z -> (fun n0 : Z => forall m : Z, m <= z -> n0 <= m -> A m) (Z.succ n) -> A n) ->
  forall n : Z, n <= z -> A n
Z.order_induction:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  A z ->
  (forall n : Z, z <= n -> A n -> A (Z.succ n)) ->
  (forall n : Z, n < z -> A (Z.succ n) -> A n) -> forall n : Z, A n
Z.order_induction':
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  A z ->
  (forall n : Z, z <= n -> A n -> A (Z.succ n)) ->
  (forall n : Z, n <= z -> A n -> A (Z.pred n)) -> forall n : Z, A n
Z.order_induction'_0:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  A 0 ->
  (forall n : Z, 0 <= n -> A n -> A (Z.succ n)) ->
  (forall n : Z, n <= 0 -> A n -> A (Z.pred n)) -> forall n : Z, A n
Z.strong_right_induction':
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, n <= z -> A n) ->
  (forall n : Z, z <= n -> (fun n0 : Z => forall m : Z, z <= m -> m < n0 -> A m) n -> A n) ->
  forall n : Z, A n
Z.order_induction_0:
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  A 0 ->
  (forall n : Z, 0 <= n -> A n -> A (Z.succ n)) ->
  (forall n : Z, n < 0 -> A (Z.succ n) -> A n) -> forall n : Z, A n
Z.strong_left_induction':
  forall A : Z -> Prop,
  Morphisms.Proper (Morphisms.respectful eq iff) A ->
  forall z : Z,
  (forall n : Z, z <= n -> A n) ->
  (forall n : Z, n <= z -> (fun n0 : Z => forall m : Z, m <= z -> n0 <= m -> A m) (Z.succ n) -> A n) ->
  forall n : Z, A n
Qed.
