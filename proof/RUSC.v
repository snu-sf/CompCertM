(** Libraries. *)
Require Import String.
From compcertr Require Import Errors.
Require Import CoqlibC ErrorsC.
From compcertr Require Import AST Linking Smallstep.
(** newly added **)
Require Import BehaviorsC Sem.


Module program_relation.

  Record t :=
    mk
      { rel :> program -> program -> Prop;
        horizontal : forall
            p0_src p1_src p0_tgt p1_tgt
            (REL0: rel p0_src p0_tgt)
            (REL1: rel p1_src p1_tgt),
            rel (p0_src ++ p1_src) (p0_tgt ++ p1_tgt);
        adequacy : forall p_src p_tgt (REL: rel p_src p_tgt),
            improves (sem p_src) (sem p_tgt);
        empty : rel [] [];
      }.

End program_relation.
Hint Resolve program_relation.horizontal.
Hint Resolve program_relation.adequacy.
Hint Resolve program_relation.empty.
Coercion program_relation.rel : program_relation.t >-> Funclass.

Section RUSC.

  Variable R : program_relation.t -> Prop.

  Definition relate_R (p_src p_tgt: program) :=
    forall r (RELIN: R r), r p_src p_tgt.

  Definition self_related (p: program) := relate_R p p.

  Lemma empty_self_related: self_related [].
  Proof. ii. eauto. Qed.

  Lemma self_related_horizontal (p0 p1: program)
        (SELF0: self_related p0)
        (SELF1: self_related p1):
      self_related (p0 ++ p1).
  Proof. ii. eauto. Qed.

  Definition rusc (p_src p_tgt: program):=
    forall (ctx0 ctx1: program)
           (SELF0: self_related ctx0)
           (SELF1: self_related ctx1),
      improves (sem (ctx0 ++ p_src ++ ctx1))
               (sem (ctx0 ++ p_tgt ++ ctx1)).

  Global Program Instance rusc_PreOrder: RelationClasses.PreOrder rusc.
  Next Obligation. unfold rusc, Reflexive. i. refl. Qed.
  (* Vertical Compositionality *)
  Next Obligation. unfold rusc, Transitive. i. etrans; eauto. Qed.

  Lemma rusc_incl (p_src p_tgt: program) (r: program_relation.t)
        (REL: r p_src p_tgt)
        (RELIN: R r):
      rusc p_src p_tgt.
  Proof. unfold rusc. i. eapply program_relation.adequacy. eauto. Qed.

  Lemma rusc_adequacy_left_ctx ctx (p_src p_tgt: program)
        (RUSC: rusc p_src p_tgt)
        (SELF: self_related ctx):
      improves (sem (ctx ++ p_src))
               (sem (ctx ++ p_tgt)).
  Proof.
    specialize (RUSC ctx []).
    rewrite app_nil_r in *. rewrite app_nil_r in *.
    eapply RUSC; eauto. eapply empty_self_related.
  Qed.

  Lemma rusc_adequacy_right_ctx ctx (p_src p_tgt: program)
        (RUSC: rusc p_src p_tgt)
        (SELF: self_related ctx):
      improves (sem (p_src ++ ctx))
               (sem (p_tgt ++ ctx)).
  Proof.
    specialize (RUSC [] ctx).
    eapply RUSC; eauto. eapply empty_self_related.
  Qed.

  Lemma rusc_adequacy (p_src p_tgt: program)
        (RUSC: rusc p_src p_tgt):
      improves (sem p_src) (sem p_tgt).
  Proof.
    specialize (RUSC [] []). ss.
    rewrite app_nil_r in *. rewrite app_nil_r in *.
    eapply RUSC; eapply empty_self_related.
  Qed.

  Lemma rusc_horizontal (p0_src p1_src p0_tgt p1_tgt: program)
        (RUSC0: rusc p0_src p0_tgt)
        (RUSC1: rusc p1_src p1_tgt)
        (SELFSRC0: self_related p0_src)
        (SELFSRC1: self_related p1_src)
        (SELFTGT0: self_related p0_tgt)
        (SELFTGT1: self_related p1_tgt):
      rusc (p0_src ++ p1_src) (p0_tgt ++ p1_tgt).
  Proof.
    unfold rusc in *. i. erewrite <- app_assoc. erewrite <- app_assoc.
    transitivity (sem (ctx0 ++ p0_tgt ++ p1_src ++ ctx1)); eauto.
    { eapply RUSC0; eauto. eapply self_related_horizontal; eauto. }
    rewrite app_assoc. replace (ctx0 ++ p0_tgt ++ p1_tgt ++ ctx1)
                         with ((ctx0 ++ p0_tgt) ++ p1_tgt ++ ctx1); eauto.
    { eapply RUSC1; eauto. eapply self_related_horizontal; eauto. }
    rewrite <- app_assoc; auto.
  Qed.

  Lemma rusc_vertical (p0 p1 p2: program)
        (RUSC0: rusc p0 p1)
        (RUSC1: rusc p1 p2):
      rusc p0 p2.
  Proof. unfold rusc in *. i. etrans; eauto. Qed.

End RUSC.
Hint Resolve self_related_horizontal.
Hint Resolve empty_self_related.

Lemma self_related_mon R0 R1
      (LE: R0 <1= R1):
    self_related R1 <1= self_related R0.
Proof. ii. eauto. Qed.
Hint Resolve self_related_mon.

Lemma rusc_mon R0 R1
      (LE: R0 <1= R1):
    rusc R0 <2= rusc R1.
Proof.
  intros p_src p_tgt RU ctx0 ctx1. i.
  eapply RU; eauto; eapply self_related_mon; eauto.
Qed.
Hint Resolve rusc_mon.
