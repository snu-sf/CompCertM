Require Import CoqlibC.

Set Implicit Arguments.


(* Naming: Do not use order; 1) "ord" is shorter. 2) "orer_link" will be confusing with "link_order" *)
Section LINK_WFO.

  Variable (idx0 idx1: Type) (ord0: idx0 -> idx0 -> Prop) (ord1: idx1 -> idx1 -> Prop).

  Inductive embedded A B (ordA: A -> A -> Prop) (ordB: B -> B -> Prop): Prop :=
  | embedded_intro
      f
      (PRESERVING: forall a0 a1
          (ORDA: ordA a0 a1),
          <<ORDB: ordB (f a0) (f a1)>>).

  Definition idx_link := (idx0 + idx1)%type.

  Inductive ord_link: idx_link -> idx_link -> Prop :=
  | ord_link_introl
      idx0a idx0b
      (ORD0: ord0 idx0a idx0b):
      ord_link (inl idx0a) (inl idx0b)
  | ord_link_intror
      idx1a idx1b
      (ORD1: ord1 idx1a idx1b):
      ord_link (inr idx1a) (inr idx1b).

  Theorem ord_link_embedded:
      <<EMBED0: embedded ord0 (ord_link)>> /\ <<EMBED1: embedded ord1 (ord_link)>>.
  Proof.
    esplits; eauto.
    - eapply embedded_intro with (f := inl). econs; eauto.
    - eapply embedded_intro with (f := inr). econs; eauto.
  Qed.

  Theorem ord_link_wf
          (WF0: well_founded ord0)
          (WF1: well_founded ord1):
      <<WF: well_founded ord_link>>.
  Proof.
    - econs; eauto. i. inv H.
      + generalize dependent idx0a. pattern idx0b. eapply well_founded_ind; eauto. clear idx0b; i.
        econs; eauto. i. inv H0; eapply H; eauto.
      + generalize dependent idx1a. pattern idx1b. eapply well_founded_ind; eauto. clear idx1b. i.
        econs; eauto. i. inv H0. eapply H; eauto.
  Qed.

  Theorem ord_link_spec
          (WF0: well_founded ord0)
          (WF1: well_founded ord1):
      exists (idx: Type) (ord: idx -> idx -> Prop),
        <<EMBED0: embedded ord0 ord>> /\ <<EMBED1: embedded ord1 ord>> /\ <<WF: well_founded ord>>.
  Proof.
    exists idx_link, ord_link. generalize ord_link_embedded; i.
    hexploit ord_link_wf; eauto. i; des. esplits; eauto.
  Qed.

End LINK_WFO.




























Require Import Program.
Require Import Axioms.


Record idx := mk { local_idx: Type;
                   local_ord: local_idx -> local_idx -> Prop;
                   wf_local_ord: well_founded local_ord;
                   elem: local_idx;
                }.

(* Require Import Coq.Logic.ClassicalFacts. *)
(* Require Import Coq.Logic.ClassicalDescription. *)
(* Require Import Coq.Logic.ChoiceFacts. *)

(* About constructive_definite_description. *)
(* Program Definition ord (x0 x1: idx): Prop := *)
(*   match classic (x0.(local_idx) = x1.(local_idx)) with *)
(*   | or_introl _ => False *)
(*   | or_intror _ => False *)
(*   end *)
(* . *)
(*     (<<EQLOCAL_IDX: x0.(local_idx) = x1.(local_idx)>>) *)
(*     /\ *)
(*     (<<EQORD: x0.(local_ord) ~= x1.(local_ord)>>) *)
(*     /\ *)
(*     (<<ORD: _>>) *)
(* . *)
(* Next Obligation. *)
(*   destruct x0, x1; ss. *)
(* Defined. *)
(* Defined. *)
(* | ord_intro *)
(*     (EQLOCAL_IDX: x0.(local_idx) = x1.(local_idx)) *)
(*     (EQORD: x0.(local_ord) ~= x1.(local_ord)) *)
(*     (ORD: x0.(local_ord) x0.(elem) x1.(elem)) *)
(* . *)

Section TMP.
  Variable X Y: Type.
  Hypothesis EQ: X = Y.
  Hypothesis ORDX: X -> X -> Prop.
  Hypothesis ORDY: Y -> Y -> Prop.
  Definition my_funcX (x: X) (y: Y): Prop.
    rewrite <- EQ in y. specialize (ORDX x y). apply ORDX.
  Defined.

  Definition my_funcY (x: X) (y: Y): Prop.
    rewrite EQ in x. specialize (ORDY x y). apply ORDY.
  Defined.

  About eq_rect.
  (* eq_rect : forall (A : Local_Idxpe) (x : A) (P : A -> Local_Idxpe), P x -> forall y : A, x = y -> P y *)
  About eq_rect_r.
(* eq_rect_r : forall (A : Local_Idxpe) (x : A) (P : A -> Local_Idxpe), P x -> forall y : A, y = x -> P y *)

End TMP.

(* I wish I had a program inductive local_idxpe *)
Inductive ord (x0 x1: idx): Prop :=
| ord_intro
    (EQLOCAL_IDX: x0.(local_idx) = x1.(local_idx))
    (EQORD: x0.(local_ord) ~= x1.(local_ord))
    (ORD: x1.(local_ord) (eq_rect x0.(local_idx) id x0.(elem) x1.(local_idx) EQLOCAL_IDX) x1.(elem)).

Theorem wf_ord: well_founded ord.
Proof.
  econs; eauto. ii. inv H. destruct a, y; ss. clarify.
  apply JMeq_eq in EQORD. clarify. clear_tac. unfold eq_rect in *.
  swapname elem1 elem0. clear ORD. clear_tac.
  { pattern elem0. eapply well_founded_ind; try eassumption. ii. clear_tac.
    econs; eauto. ii. destruct y; ss. inv H0. ss. clarify.
    (* eapply H. Undo 1. (* IDK why but apply acts in weird way. *) *)
    specialize (H elem0). unfold eq_rect in *. specialize (H ORD).
    apply JMeq_eq in EQORD. clarify. clear_tac.
    generalize proof_irr. intro IRR. unfold ClassicalFacts.proof_irrelevance in *.
    specialize (IRR _ wf_local_ord0 wf_local_ord1). clarify.
  }
Qed.

Theorem idx_greatest
        (local_idx: Type) (local_ord: local_idx -> local_idx -> Prop)
        (WF: well_founded local_ord):
    embedded local_ord ord.
Proof.
  apply embedded_intro with (f:= fun local_elem => mk WF local_elem).
  ii. econs; eauto. ss. instantiate (1:= eq_refl). ss.
Qed.

Program Definition idx_bot: idx := @mk unit bot2 _ tt.
Next Obligation. econs; eauto. ii; ss. Qed.

Lemma idx_bot_spec
      i0
      (ORD: ord i0 idx_bot):
    False.
Proof. inv ORD. ss. Qed.


Section LIFT.

  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis WFORD: well_founded order.

  Definition lift_idx (i0: index): idx := (mk WFORD i0).

  Lemma lift_idx_spec
        i0 i1
        (ORD: order i0 i1):
      <<ORD: ord (lift_idx i0) (lift_idx i1)>>.
  Proof. econs; eauto. cbn. instantiate (1:= eq_refl). cbn. ss. Qed.

  Hint Unfold lift_idx.

End LIFT.

