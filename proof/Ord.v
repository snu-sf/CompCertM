Require Import CoqlibC.

Set Implicit Arguments.


(* Naming: Do not use order; 1) "ord" is shorter. 2) "orer_link" will be confusing with "link_order" *)
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

  Definition idx_link := (idx0 + idx1)%type.

  Inductive ord_link: idx_link -> idx_link -> Prop :=
  | ord_link_introl
      idx0a idx0b
      (ORD0: ord0 idx0a idx0b)
    :
      ord_link (inl idx0a) (inl idx0b)
  | ord_link_intror
      idx1a idx1b
      (ORD1: ord1 idx1a idx1b)
    :
      ord_link (inr idx1a) (inr idx1b)
  .

  Theorem ord_link_embedded
    :
      <<EMBED0: embedded ord0 (ord_link)>> /\ <<EMBED1: embedded ord1 (ord_link)>>
  .
  Proof.
    esplits; eauto.
    - eapply embedded_intro with (f := inl). econs; eauto.
    - eapply embedded_intro with (f := inr). econs; eauto.
  Qed.

  Theorem ord_link_wf
          
          (WF0: well_founded ord0)
          (WF1: well_founded ord1)
    :
      <<WF: well_founded ord_link>>
  .
  Proof.
    - econs; eauto. i. inv H.
      + generalize dependent idx0a. pattern idx0b. eapply well_founded_ind; eauto. clear idx0b. i.
        econs; eauto. i. inv H0.
        eapply H; eauto.
      + generalize dependent idx1a. pattern idx1b. eapply well_founded_ind; eauto. clear idx1b. i.
        econs; eauto. i. inv H0.
        eapply H; eauto.
  Qed.

  Theorem ord_link_spec
          
          (WF0: well_founded ord0)
          (WF1: well_founded ord1)
    :
      exists (idx: Type) (ord: idx -> idx -> Prop),
        <<EMBED0: embedded ord0 ord>> /\ <<EMBED1: embedded ord1 ord>> /\ <<WF: well_founded ord>>
  .
  Proof.
    exists idx_link, ord_link.
    generalize ord_link_embedded; i.
    hexploit ord_link_wf; eauto. i; des.
    esplits; eauto.
  Qed.

End LINK_WFO.

