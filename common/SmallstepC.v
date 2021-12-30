Require Import Relations.
Require Import Wellfounded.
Require Import CoqlibC.
From compcertr Require Import Events.
From compcertr Require Import Globalenvs.
From compcertr Require Import Integers.
Require Import AxiomsC.
(** newly added **)
From compcertr Require Export Smallstep.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Definition PStep (L: semantics) (P: L.(state) -> Prop) :=
  (fun s1 t s2 =>  P s1 /\ Step L s1 t s2).

Definition PStar (L: semantics) (P: L.(state) -> Prop) :=
  (star (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv).

Definition PStarN (L: semantics) (P: L.(state) -> Prop) :=
  (starN (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv).

Definition PPlus (L: semantics) (P: L.(state) -> Prop) :=
  (plus (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv).

Lemma PStep_iff
      L P Q
      (IFF: all1 (P <1> Q)):
    PStep L P = PStep L Q.
Proof.
  repeat (eapply functional_extensionality; i). eapply prop_ext. split; i; inv H; econs; eauto; eapply IFF; eauto.
Qed.

Lemma star_inv
      G ST
      (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se (ge: G) st0 tr st1
      (STAR: star step se ge st0 tr st1):
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step se ge st0 tr st1>>.
Proof. inv STAR; eauto. right. econs; eauto. Qed.

Lemma plus_or_star_inv
      G ST
      (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se (ge: G) st0 tr st1
      (STAR: plus step se ge st0 tr st1 \/ star step se ge st0 tr st1):
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step se ge st0 tr st1>>.
Proof. des; eauto. eapply star_inv; eauto. Qed.

Lemma Pstar_non_E0_split'_strong
      L P st0 tr st1
      (SINGLE: single_events L)
      (STAR: PStar L P st0 tr st1):
    match tr with
    | [] => True
    | ev :: tr' => exists st0x, PPlus L P st0 [ev] st0x /\
                                ((tr' <> E0 /\ PPlus L P st0x tr' st1) \/ (tr' = E0 /\ st0x = st1))
    end.
Proof.
  ginduction STAR; ii; ss. des_ifs.
  { destruct t1; ss. clarify. rr in H. des. exploit SINGLE; eauto. i; des. ss. destruct t1; ss; try extlia.
    esplits; try (right; ss).
    { eapply plus_star_trans; eauto; traceEq. apply plus_one. rr. eauto. }
  }
  exploit IHSTAR; eauto. i; des_safe. destruct t1; ss; clarify.
  - esplits; eauto.
    + eapply star_plus_trans; eauto. apply star_one; eauto. traceEq.
  - rr in H. des_safe. exploit SINGLE; eauto. i. ss. destruct t1; ss; try extlia. esplits; eauto.
    + eapply plus_one; eauto. rr. eauto.
    + des.
      * left. split; ss. eapply plus_star_trans; eauto. eapply plus_star; eauto. ss.
      * clarify. left. split; ss.
Qed.

Lemma PStar_top_Star: forall L,
    Star L = PStar L top1.
Proof.
  i. repeat (apply func_ext1; i). apply prop_ext. split; intro STAR.
  - ginduction STAR; ii; ss.
    { econs; eauto. }
    clarify. eapply star_trans; try eapply star_refl; traceEq.
    eapply star_left; eauto. rr. esplits; eauto.
  - ginduction STAR; ii; ss.
    { econs; eauto. }
    clarify. eapply star_trans; try eapply star_refl; traceEq.
    eapply star_left; eauto. rr in H. des; eauto.
Qed.

Lemma PPlus_top_Plus: forall L,
    Plus L = PPlus L top1.
Proof.
  i. repeat (apply func_ext1; i). apply prop_ext. split; intro PLUS.
  - inv PLUS; ss. econs; eauto.
    { rr. eauto. }
    rewrite PStar_top_Star in H0; eauto.
  - inv PLUS; ss. rr in H. des. econs; eauto. rewrite PStar_top_Star; eauto.
Qed.



Lemma star_non_E0_split'_strong
      L st0 tr st1
      (SINGLE: single_events L)
      (STAR: Star L st0 tr st1):
    match tr with
    | [] => True
    | ev :: tr' => exists st0x, Plus L st0 [ev] st0x /\
                                ((tr' <> E0 /\ Plus L st0x tr' st1) \/ (tr' = E0 /\ st0x = st1))
    end.
Proof.
  exploit (@Pstar_non_E0_split'_strong L top1); eauto.
  { erewrite <- PStar_top_Star; eauto. }
  i; des. des_ifs. des_safe. erewrite <- PPlus_top_Plus in *; eauto.
Qed.


Lemma starN_plus_iff
      G ST (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se ge st0 tr st1:
    (exists n, starN step se ge n st0 tr st1 /\ (n > 0)%nat) <-> plus step se ge st0 tr st1.
Proof.
  split; i; des.
  - destruct n; ss; try extlia. ginduction H; ii; ss; try extlia. clarify. inv H0.
    + eapply plus_star_trans; et; try eapply star_refl. apply plus_one; et.
    + eapply plus_trans; et.
      { apply plus_one; et. }
      eapply IHstarN; et. extlia.
  - inv H. apply star_starN in H1. des. exists (Datatypes.S n). esplits; et; try extlia. econs; et.
Qed.

