Require Import Relations.
Require Import Wellfounded.
Require Import CoqlibC.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import AxiomsC.
(** newly added **)
Require Export Smallstep.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Definition PStep (L: semantics) (P: L.(state) -> Prop) :=
  (fun s1 t s2 => step L (symbolenv L) (globalenv L) s1 t s2 /\ P s1)
.

Definition PStar (L: semantics) (P: L.(state) -> Prop) :=
  (star (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv)
.

Definition PStarN (L: semantics) (P: L.(state) -> Prop) :=
  (starN (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv)
.

Definition PPlus (L: semantics) (P: L.(state) -> Prop) :=
  (plus (fun _ _ => PStep L P)) L.(symbolenv) L.(globalenv)
.

Lemma PStep_iff
      L P Q
      (IFF: all1 (P <1> Q))
  :
    PStep L P = PStep L Q
.
Proof.
  repeat (eapply functional_extensionality; i).
  eapply prop_ext.
  split; i.
  - inv H. econs; eauto. eapply IFF; eauto.
  - inv H. econs; eauto. eapply IFF; eauto.
Qed.

Lemma star_inv
      G ST
      (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se (ge: G) st0 tr st1
      (STAR: star step se ge st0 tr st1)
  :
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step se ge st0 tr st1>>
.
Proof.
  inv STAR; eauto.
  right. econs; eauto.
Qed.

Lemma plus_or_star_inv
      G ST
      (step: Senv.t -> G -> ST -> trace -> ST -> Prop) se (ge: G) st0 tr st1
      (STAR: plus step se ge st0 tr st1 \/ star step se ge st0 tr st1)
  :
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step se ge st0 tr st1>>
.
Proof.
  des; eauto. eapply star_inv; eauto.
Qed.

Lemma star_non_E0_split'_strong
      L
      (SINGLE: single_events L)
      st0 tr st1
      (STAR: Star L st0 tr st1)
  :
    match tr with
    | [] => True
    | ev :: tr' => exists st0x, Plus L st0 [ev] st0x /\
                                ((tr' <> E0 /\ Plus L st0x tr' st1) \/ (tr' = E0 /\ st0x = st1))
    end
.
Proof.
  ginduction STAR; ii; ss.
  des_ifs.
  { destruct t1; ss. clarify. exploit SINGLE; eauto. i; des. ss. destruct t1; ss; try xomega.
    esplits.
    { eapply plus_star_trans; eauto.
      - apply plus_one. eauto.
      - ss.
    }
    right; ss.
  }
  exploit IHSTAR; eauto. i; des_safe.
  destruct t1; ss; clarify.
  - esplits; eauto.
    + eapply star_plus_trans; eauto.
      * apply star_one; eauto.
      * ss.
  - exploit SINGLE; eauto. i. ss. destruct t1; ss; try xomega.
    esplits; eauto.
    + eapply plus_one; eauto.
    + des.
      * left. split; ss.
        eapply plus_star_trans; eauto.
        { eapply plus_star; eauto. }
        ss.
      * clarify.
        left. split; ss.
Qed.
