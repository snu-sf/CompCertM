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
    pfold. econs; ss; et; cycle 1.
    { econs; et. econs; et. }
    ii. esplits; et.
    { econs; et. econs 2; et. }
    left. des_ifs_safe.
    irw. unfoldr guarantee. des_ifs; [irw|pfold; unfold triggerNB; irw; econs; et].
    pfold. econs; ss; et; cycle 1.
    { econs; et. econs; et. }
    ii. esplits; et.
    { econs; et. instantiate (1:= (_, 0%nat)). econs 1; et. }
    left. pfold. des_ifs. (*** WHY LONG? ***)
    econs; et.
  }
Unshelve.
  all: ss.
  all: try (by sk_incl_tac).
Qed.
