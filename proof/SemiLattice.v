Require Import CoqlibC.
Require Import MapsC.
Require Import FinFun.

Set Implicit Arguments.

Local Open Scope nat_scope.



Definition greatest A (le: A -> A -> Prop) (P: A -> Prop) (max: A): Prop :=
  <<PROP: P max>> /\ <<MAX: forall a (PROP: P a), le a max>>
.

Module TRIAL1.

(* Finite Semi-Lattice *)
Class FSL: Type := {
  t: Type;
  finite: Finite t;
  le: t -> t -> Prop;
  le_PreOrder :> PreOrder le;
  lub: t -> t -> t;
  lub_spec: forall x y ,
      (<<LE: le x (lub x y)>>) /\ (<<LE: le y (lub x y)>>);
  greatest P := greatest le P;
}.

Section SemiLatticeProps.

  Context `{FSL}.
  Variable P: t -> Prop.
  Hypothesis CLOSED: forall x y
      (PX: P x)
      (PY: P y),
      <<PXY: P (lub x y)>>.

  Let find_greatest_aux: forall l
      (INHAB: exists inhab, P inhab),
      exists max,
        (<<PROP: P max>>) /\
        (<<LE: forall x
            (PROP: P x)
            (IN: List.In x l),
            <<LE: le x max>>>>).
  Proof.
    intros. induction l; ii; ss.
    { des. esplits; eauto. ii. ss. }
    des. destruct (classic (P a)); cycle 1.
    { esplits; eauto. ii. des; clarify. eapply LE; eauto. }
    exists (lub max a). esplits; eauto.
    { eapply CLOSED; eauto. }
    ii. des; clarify.
    { eapply lub_spec; eauto. }
    etrans; try eapply LE; eauto. eapply lub_spec; eauto.
  Qed.
  Lemma find_greatest
        (INHAB: exists inhab, P inhab):
      exists max, <<MAX: greatest P max>>.
  Proof.
    hexpl finite FIN. rr in FIN. des.
    exploit (@find_greatest_aux l); eauto. i; des.
    esplits; eauto. rr. esplits; eauto. ii. eapply LE; eauto.
  Qed.

End SemiLatticeProps.

End TRIAL1.
















Module FSL.


(* Finite Semi-Lattice *)
Class class (t: Type) (le: t -> t -> Prop) (lub: t -> t -> t): Type := {
  (* finite: Finite t; *)
  le_PreOrder :> PreOrder le;
  lub_spec: forall x y,
      (<<LE: le x (lub x y)>>) /\ (<<LE: le y (lub x y)>>);
  greatest P := greatest le P;
}.
Section SemiLatticeProps.

  Variable t: Type.
  Variable le: t -> t -> Prop.
  Variable lub: t -> t -> t.
  Context `{class t le lub}.
  Variable P: t -> Prop.
  Hypothesis FIN: Finite t. (* or, finite P t only *)
  Hypothesis CLOSED: forall x y
      (PX: P x)
      (PY: P y),
      <<PXY: P (lub x y)>>.
  Let find_greatest_aux: forall l
      (INHAB: exists inhab, P inhab),
      exists max,
        (<<PROP: P max>>) /\
        (<<LE: forall x
            (PROP: P x)
            (IN: List.In x l),
            <<LE: le x max>>>>).
  Proof.
    intros. induction l; ii; ss.
    { des. esplits; eauto. ii. ss. }
    des. destruct (classic (P a)); cycle 1.
    { esplits; eauto. ii. des; clarify. eapply LE; eauto. }
    exists (lub max a). esplits; eauto.
    { eapply CLOSED; eauto. }
    ii. des; clarify.
    { eapply lub_spec; eauto. }
    etrans; try eapply LE; eauto. eapply lub_spec; eauto.
  Qed.

  Lemma find_greatest
        (INHAB: exists inhab, P inhab):
      exists max, <<MAX: greatest P max>>.
  Proof.
    rr in FIN. destruct FIN as [l ?].
    exploit (@find_greatest_aux l); eauto. i; des.
    esplits; eauto. rr. esplits; eauto. ii. eapply LE; eauto.
  Qed.

End SemiLatticeProps.

End FSL.














Section SemiLatticeProps.

  Variable t: Type.
  Variable le: t -> t -> Prop.
  Variable lub: t -> t -> option t.
  Variable P: t -> Prop.
  Hypothesis LEORD: PreOrder le.
  Hypothesis LUBSUCC: forall x y
      (PX: P x)
      (PY: P y),
      exists z, lub x y = Some z.
  Hypothesis LUBSPEC: forall x y z
      (LUB: lub x y = Some z),
      (<<LE: le x z>>) /\ (<<LE: le y z>>).
  (* Hypothesis FIN: Finite { x: t | P x }. *) (* <-- this is pain in the ass *)
  Hypothesis FIN: exists l, forall x (PROP: P x), In x l.
  Hypothesis CLOSED: forall x y z
      (PX: P x)
      (PY: P y)
      (LUB: lub x y = Some z),
      <<PXY: P z>>.
  Let find_greatest_aux: forall l
      (INHAB: exists inhab, P inhab) ,
      exists max,
        (<<PROP: P max>>) /\
        (<<LE: forall x
            (PROP: P x)
            (IN: List.In x l),
            <<LE: le x max>>>>).
  Proof.
    intros. induction l; ii; ss.
    { des. esplits; eauto. ii. ss. }
    des. destruct (classic (P a)); cycle 1.
    { esplits; eauto. ii. des; clarify. eapply LE; eauto. }
    exploit (@LUBSUCC max a); eauto. i; des.
    exploit (@CLOSED max a); eauto. i; des.
    exists z. esplits; eauto. ii. exploit LUBSPEC; eauto. i; des_safe.
    etrans; try eapply LE; eauto.
  Qed.

  Lemma find_greatest
        (INHAB: exists inhab, P inhab):
      exists max, <<MAX: greatest le P max>>.
  Proof.
    rr in FIN. destruct FIN as [l ?]. des.
    (* set (l' := map (@proj1_sig _ P) l). *)
    exploit (@find_greatest_aux l); eauto. i; des.
    esplits; eauto. rr. esplits; eauto. ii. eapply LE; eauto.
    (* eapply in_map_iff. unshelve eexists (exist _ _ _); ss. *)
  Qed.

End SemiLatticeProps.



Section GRLE.

  Variable t: Type.
  Variable le: t -> t -> Prop.
  Variable lub: t -> t -> option t.
  Variable P: t -> Prop.
  Hypothesis LEORD: PreOrder le.
  Hypothesis LUBSUCC: forall su0 x y
      (PX: le su0 x /\ P x)
      (PY: le su0 y /\ P y),
      exists z, lub x y = Some z.
  Hypothesis LUBSPEC: forall x y z
      (LUB: lub x y = Some z),
      (<<LE: le x z>>) /\ (<<LE: le y z>>).
  (* Hypothesis FIN: Finite { x: t | P x }. *) (* <-- this is pain in the ass *)
  Hypothesis FIN: exists l, forall x (PROP: P x), In x l.
  Hypothesis CLOSED: forall su0 x y z
      (PX: le su0 x /\ P x)
      (PY: le su0 y /\ P y)
      (LUB: lub x y = Some z),
      <<PXY: P z>>.

  Lemma greatest_le_irr (* better name!!! *)
        a0 a1 max
        (LE: le a0 a1)
        (P1: P a1)
        (GR: greatest le (fun a => le a1 a /\ P a) max):
      <<GR: greatest le (fun a => le a0 a /\ P a) max>>.
  Proof.
    r in GR. rr. des. esplits; eauto.
    { etrans; eauto. }
    ii. des. exploit LUBSUCC.
    { esplits; cycle 1. eapply P1. eauto. }
    { esplits; cycle 1. eapply PROP2. eauto. }
    intro LUB; des. exploit LUBSPEC; eauto. i; des. exploit CLOSED; try apply LUB; eauto. i; des.
    specialize (MAX z). exploit MAX; eauto. i; des. etrans; eauto.
  Qed.

End GRLE.
