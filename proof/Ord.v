Require Import CoqlibC.

Set Implicit Arguments.



Section LINK_WFO.

  Variable (idx0 idx1: Type) (ord0: idx0 -> idx0 -> Prop) (ord1: idx1 -> idx1 -> Prop).

  Inductive embedded A B (ordA: A -> A -> Prop) (ordB: B -> B -> Prop): Prop :=
  | embedded_intro
      f
      (PRESERVING: forall
          a0 a1
          (ORDA: ordA a0 a1)
        ,
          <<ORDB: ordB (f a0) (f a1)>>)
  .

  Let idx := (idx0 + idx1)%type.

  Inductive ord: idx -> idx -> Prop :=
  | ord_introl
      idx0a idx0b
      (ORD0: ord0 idx0a idx0b)
    :
      ord (inl idx0a) (inl idx0b)
  | ord_intror
      idx1a idx1b
      (ORD1: ord1 idx1a idx1b)
    :
      ord (inr idx1a) (inr idx1b)
  .

  Theorem link_wfo
          
          (WF0: well_founded ord0)
          (WF1: well_founded ord1)
    :
      exists (idx: Type) (ord: idx -> idx -> Prop),
        <<EMBED0: embedded ord0 ord>> /\ <<EMBED1: embedded ord1 ord>> /\ <<WF: well_founded ord>>
  .
  Proof.
    exists idx, ord.
    esplits; eauto.
    - eapply embedded_intro with (f := inl). econs; eauto.
    - eapply embedded_intro with (f := inr). econs; eauto.
    - econs; eauto. i. inv H.
      + generalize dependent idx0a. pattern idx0b. eapply well_founded_ind; eauto. clear idx0b. i.
        econs; eauto. i. inv H0.
        eapply H; eauto.
      + generalize dependent idx1a. pattern idx1b. eapply well_founded_ind; eauto. clear idx1b. i.
        econs; eauto. i. inv H0.
        eapply H; eauto.
  Qed.

End LINK_WFO.
