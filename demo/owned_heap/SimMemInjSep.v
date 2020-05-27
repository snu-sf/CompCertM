Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMemLift.
Require Import AxiomsC.
Require Import Conventions1.
(* Require Import SimMemInj. *)

Set Implicit Arguments.



Lemma iff_eta
      (P Q: Prop)
      (EQ: P = Q)
  :
    <<EQ: P <-> Q>>
.
Proof. clarify. Qed.

Lemma and_eta
      (P0 P1 Q0 Q1: Prop)
      (EQ0: P0 = P1)
      (EQ1: Q0 = Q1)
  :
    <<EQ: (P0 /\ Q0) = (P1 /\ Q1)>>
.
Proof. clarify. Qed.

Ltac smart_intro T :=
  intro;
  let x := match goal with
           | [ H: _ |- _ ] => H
           end
  in
  (* idtac x; *)
  on_last_hyp ltac:(fun id => revert id);

  let name := fresh "H" in
  intro name;
  let y := match goal with
           | [ H: _ |- _ ] => H
           end
  in
  (* idtac y; *)
  on_last_hyp ltac:(fun id => revert id);

  tryif (check_equal x y)
  then
    let name := fresh T in intro name
    (* (tryif check_hyp T *)
    (*   then (tryif check_hyp "U" *)
    (*          then (tryif (check_hyp "V") *)
    (*                 then (let name := (fresh "W") in intro name) *)
    (*                 else (let name := (fresh "V") in intro name)) *)
    (*          else (let name := (fresh "U") in intro name)) *)
    (*   else (let name := (fresh "T") in intro name)) *)

    (* (tryif check_hyp string:("T") *)
    (*   then (tryif check_hyp string:("U") *)
    (*          then (tryif (check_hyp string:("V")) *)
    (*                 then (intro W) *)
    (*                 else (intro V)) *)
    (*          else (intro U)) *)
    (*   else (intro T)) *)

    (* let T := fresh "T" in *)
    (* let U := fresh "U" in *)
    (* let V := fresh "V" in *)
    (* let W := fresh "W" in *)
    (* (tryif check_hyp T *)
    (*   then (tryif check_hyp U *)
    (*          then (tryif (check_hyp V) *)
    (*                 then (intro W) *)
    (*                 else (intro V)) *)
    (*          else (intro U)) *)
    (*   else (intro T)) *)
  else intro x

  (* match x with *)
  (* | y => let name := fresh T in *)
  (*        intro name *)
  (* | _ => intro x *)
  (* end *)
.

Tactic Notation "ii" "as" ident(a) := repeat (let name := fresh a in intro name).
(* Ltac sii := repeat (smart_intro "X"). *)
Tactic Notation "sii" ident(X) := repeat (smart_intro X).
Goal forall (t: True), True -> forall (u: True), True -> False.
Proof.
  sii T.
  clear t. clear T. clear u. clear T0.
Abort.
Hint Unfold privmod_others.



Require Import Classical_Pred_Type.

Lemma not_and_or_strong
      P Q
      (H: (~ (P /\ Q)))
  :
    ((Q /\ ~ P) \/  ~Q)
.
Proof.
  apply not_and_or in H.
  destruct (classic Q); et.
  des; clarify; et.
Qed.

Lemma NNPP_rev
      (P: Prop)
      (p: P)
  :
    ~ ~ P
.
Proof. ii. eauto. Qed.

Ltac Psimpl_ :=
  match goal with
  | [ H: ~ ~ ?P |- _ ] => apply NNPP in H
  | [ H: ~ (NW (fun _ => ~ ?P)) |- _ ] => apply NNPP in H
  | [ |- ~ ~ ?P ] => apply NNPP_rev
  | [ H: (~?P -> ?P) |- _ ] => apply Peirce in H
  | [ H: ~ (?P -> ?Q) |- _ ] => apply imply_to_and in H
  | [ |- ~?P \/ ~?Q ] => apply imply_to_or
  (* Parameter or_to_imply : forall P Q : Prop, ~ P \/ Q -> P -> Q. *)
  | [ H: ~(?P /\ ?Q) |- _ ] => apply not_and_or_strong in H
  | [ |- ~(?P /\ ?Q) ] => apply or_not_and
  | [ H: ~(?P \/ ?Q) |- _ ] => apply not_or_and in H
  | [ |- ~(?P \/ ?Q) ] => apply and_not_or
  | [ H: ~(forall n, ~?P n) |- _ ] => apply not_all_not_ex in H
  | [ H: ~(forall n, ?P n) |- _ ] => apply not_all_ex_not in H
  | [ H: ~(exists n, ?P n) |- _ ] => apply not_ex_all_not in H
  | [ H: ~(exists n, ~?P n) |- _ ] => apply not_ex_not_all in H
  | [ |- ~(forall n, ?P n) ] => apply ex_not_not_all
  | [ |- ~(exists n, ?P n) ] => apply all_not_not_ex
  end
.

Ltac Psimpl := repeat Psimpl_.









Definition loc_unmapped (f: meminj) (m: mem): block -> Z -> Prop :=
  fun b ofs => <<NONE: f b = None>> \/ <<NOPERM: ~Mem.perm m b ofs Max Nonempty>>
.
Hint Unfold loc_unmapped.



Section FROZEN.

Inductive frozen (f_old f_new: meminj) (bound_src bound_tgt: block): Prop :=
| frozen_intro
    (NEW_IMPLIES_OUTSIDE:
       forall b_src b_tgt delta
              (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
         <<OUTSIDE_SRC: (bound_src <= b_src)%positive>> /\ <<OUTSIDE_TGT: (bound_tgt <= b_tgt)%positive>>).

Remark inject_separated_frozen: forall f_old f_new m_src m_tgt,
    Events.inject_separated f_old f_new m_src m_tgt <->
    frozen f_old f_new m_src.(Mem.nextblock) m_tgt.(Mem.nextblock).
Proof.
  unfold Events.inject_separated, Mem.valid_block in *. split; i.
  - econs; eauto. i. des. hexploit H; eauto. i; des. splits; xomega.
  - inv H. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. split; xomega.
Qed.

Lemma frozen_preserves_src
      f_old f_new bound_src bound_tgt b_src
      (INJECT: inject_incr f_old f_new)
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      (INSIDE: (b_src < bound_src)%positive):
    <<PRESERVED: f_old b_src = f_new b_src>>.
Proof.
  inv FROZEN. destruct (f_old b_src) eqn:T0; ss; destruct (f_new b_src) eqn:T1; ss.
  - destruct p, p0; ss. exploit INJECT; eauto; []; i; des. clarify.
  - destruct p; ss. exploit INJECT; eauto; []; i; des. clarify.
  - destruct p; ss. exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. exfalso. xomega.
Qed.

Lemma frozen_preserves_tgt
      f_old f_new bound_src bound_tgt b_tgt
      (INJECT: inject_incr f_old f_new)
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      (INSIDE: (b_tgt < bound_tgt)%positive):
    <<PRESERVED: forall b_src delta (NOW: f_new b_src = Some (b_tgt, delta)),
      <<OLD: f_old b_src = Some (b_tgt, delta)>> >>.
Proof.
  inv FROZEN. ii. destruct (f_old b_src) eqn:T; ss.
  - destruct p; ss. exploit INJECT; eauto; []; i; des. clarify.
  - exfalso. exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. xomega.
Qed.

Lemma frozen_shortened
      f_old f_new bd_src0 bd_tgt0 bd_src1 bd_tgt1
      (FROZEN: frozen f_old f_new bd_src0 bd_tgt0)
      (SHORT_SRC: (bd_src1 <= bd_src0)%positive)
      (SHORT_TGT: (bd_tgt1 <= bd_tgt0)%positive):
    <<FROZEN: frozen f_old f_new bd_src1 bd_tgt1>>.
Proof.
  inv FROZEN. econs; eauto. ii. des.
  hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
  split; ss; red; etransitivity; eauto.
Qed.

Lemma frozen_refl: forall f bound_src bound_tgt,
    <<FROZEN: frozen f f bound_src bound_tgt>>.
Proof. econs; eauto. i; des. clarify. Qed.

Lemma loc_unmapped_frozen
      F F' fbound_src fbound_tgt b ofs m0 m1
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      (BOUND: Plt b fbound_src)
      (UNMAPPED: loc_unmapped F m0 b ofs)
      (MAXPERM: forall b ofs, Plt b fbound_src -> Mem.perm m1 b ofs Max Nonempty ->
                              Mem.perm m0 b ofs Max Nonempty)
  :
    loc_unmapped F' m1 b ofs.
Proof.
  unfold loc_unmapped in *.
  des.
  - destruct (F' b) eqn:T; ss; et. destruct p; ss.
    inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. xomega.
  - right. ii. et.
Qed.

Lemma loc_out_of_reach_frozen
      F F' fbound_src fbound_tgt b ofs m0 m1
      (INCR: inject_incr F F')
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      (BOUND: Plt b fbound_tgt)
      (UNMAPPED: loc_out_of_reach F m0 b ofs)
      (MAXPERM: forall b0 delta (MAPPED: F b0 = Some (b, delta)),
          Mem.perm m1 b0 (ofs - delta) Max Nonempty -> Mem.perm m0 b0 (ofs - delta) Max Nonempty):
    loc_out_of_reach F' m1 b ofs.
Proof.
  unfold loc_out_of_reach in *. i. exploit frozen_preserves_tgt; eauto. i. des. hexploit UNMAPPED; eauto.
Qed.

End FROZEN.

Inductive frozen_incr (bound_src bound_tgt: block) (f_old f_new: meminj): Prop :=
| frozen_incr_intro
    (FROZEN: frozen f_old f_new bound_src bound_tgt)
    (INCR: inject_incr f_old f_new)
.

Global Program Instance frozen_incr_PreOrder (bound_src bound_tgt: block):
  PreOrder (frozen_incr bound_src bound_tgt).
Next Obligation.
  econs; eauto. econs; eauto. i; des. clarify.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; eauto; cycle 1.
  { eapply inject_incr_trans; et. }
  econs; eauto. inv FROZEN. inv FROZEN0. i; des.
  destruct (y b_src) eqn:T.
  - destruct p; ss. exploit NEW_IMPLIES_OUTSIDE; et. i; des. esplits; et; try xomega.
    exploit INCR0; et. i; des. clarify.
  - exploit NEW_IMPLIES_OUTSIDE0; et.
Qed.





Inductive ownership: Type :=
| privmod (mi: string)
| external
| priv
| pub
.

Definition ownership_dec (ons0 ons1: ownership): {ons0 = ons1} + {ons0 <> ons1}.
  decide equality.
  - apply string_dec.
Defined.

Definition is_privmod (ons: ownership) (mi: Midx.t): bool :=
  match mi with
  | Some mi =>
    match ons with
    | privmod mj => string_dec mi mj
    | _ => false
    end
  | _ => false
  end
.

Definition ownership_to_ownership (ons: ownership): SimMem.ownership :=
  match ons with
  | privmod mi => SimMem.privmod mi
  | _ => SimMem.etc
  end
.

Coercion ownership_to_ownership: ownership >-> SimMem.ownership.

Notation partition := (block -> Z -> ownership).

Definition ownership_mem_bool (ptt: partition) (ons: ownership): block -> Z -> bool :=
  fun b ofs => ownership_dec (ptt b ofs) ons
.

Definition ons_mem (ptt: partition) (ons: ownership): block -> Z -> Prop :=
  fun b ofs => (ptt b ofs) = ons
.
Hint Unfold ons_mem.


Section MEMINJ.

(* Local Existing Instance Val.mi_normal. *)
(* Variable gbound_src gbound_tgt: block. *)

Record t' := mk {
  src: mem;
  tgt: mem;
  inj: meminj;
  ge_nb_src: block;
  ge_nb_tgt: block;
  ptt_src: partition;
  ptt_tgt: partition;
}.

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => (Mem.valid_block m) b.
Hint Unfold valid_blocks.

Definition private_src (sm: t'): block -> Z -> Prop :=
  loc_unmapped sm.(inj) sm.(src) /2\ (valid_blocks sm.(src)).

Definition private_tgt (sm: t'): block -> Z -> Prop :=
  loc_out_of_reach sm.(inj) sm.(src) /2\ (valid_blocks sm.(tgt)).

Definition public_src (sm: t'): block -> Z -> Prop := ~2 (private_src sm).

Definition public_tgt (sm: t'): block -> Z -> Prop := ~2 (private_tgt sm).

Goal forall X Y (P Q: X -> Y -> Prop), (P = Q) <-> all2 (P <2> Q).
Proof.
  ii. split; i; clarify. eapply func_ext2. ii. eapply prop_ext. et.
Qed.

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (PUBLIC: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
    (GENBSRC: (sm0.(ge_nb_src) <= sm0.(src).(Mem.nextblock))%positive)
    (GENBTGT: (sm0.(ge_nb_tgt) <= sm0.(tgt).(Mem.nextblock))%positive)
    (* (PTTSRC: (public_src sm0) = (ownership_mem sm0.(ptt_src) pub)) *)
    (* (PTTTGT: (public_tgt sm0) = (ownership_mem sm0.(ptt_tgt) pub)) *)
    (* (PTTSRC: all2 ((public_src sm0) <2> (ownership_mem sm0.(ptt_src) pub))) *)
    (* (PTTTGT: all2 ((public_tgt sm0) <2> (ownership_mem sm0.(ptt_tgt) pub))) *)
    (PTTSRC: (public_src sm0) <2= (ons_mem sm0.(ptt_src) pub))
    (PTTTGT: (public_tgt sm0) <2= (ons_mem sm0.(ptt_tgt) pub))
.

Inductive le' (sm0 sm1: t'): Prop :=
| le_intro
    (GENBSRC: sm0.(ge_nb_src) = sm1.(ge_nb_src))
    (GENBTGT: sm0.(ge_nb_tgt) = sm1.(ge_nb_tgt))
    (FINCR: frozen_incr (sm0.(ge_nb_src)) (sm0.(ge_nb_tgt)) sm0.(inj) sm1.(inj))
    (* (INCR: inject_incr sm0.(inj) sm1.(inj)) *)
    (UNCHSRC: Mem.unchanged_on (ons_mem sm0.(ptt_src) external) sm0.(src) sm1.(src))
    (UNCHTGT: Mem.unchanged_on (ons_mem sm0.(ptt_tgt) external) sm0.(tgt) sm1.(tgt))
    (* (PUBSRC: (ons_mem sm0.(ptt_src) pub) <2= (ons_mem sm1.(ptt_src) pub)) *)
    (* (PUBTGT: (ons_mem sm0.(ptt_tgt) pub) <2= (ons_mem sm1.(ptt_tgt) pub)) *)
    (EXTSRC: (ons_mem sm0.(ptt_src) external) <2= (ons_mem sm1.(ptt_src) external))
    (EXTTGT: (ons_mem sm0.(ptt_tgt) external) <2= (ons_mem sm1.(ptt_tgt) external))
    (PMSRC: forall mi, (ons_mem sm0.(ptt_src) (privmod mi)) <2= (ons_mem sm1.(ptt_src) (privmod mi)))
    (PMTGT: forall mi, (ons_mem sm0.(ptt_tgt) (privmod mi)) <2= (ons_mem sm1.(ptt_tgt) (privmod mi)))
    (* (MAXSRC: forall b ofs *)
    (*     (VALID: Mem.valid_block sm0.(src) b), *)
    (*     <<MAX: Mem.perm sm1.(src) b ofs Max <1= Mem.perm sm0.(src) b ofs Max>>) *)
    (* (MAXTGT: forall b ofs *)
    (*     (VALID: Mem.valid_block sm0.(tgt) b), *)
    (*     <<MAX: Mem.perm sm1.(tgt) b ofs Max <1= Mem.perm sm0.(tgt) b ofs Max>>) *)
    (** tried to minimize it (don't require FROZEN),
but because of volatile condiiton in symbols_inject, I think we need it **)
.

Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
Next Obligation.
  econs; eauto; try reflexivity; try apply Mem.unchanged_on_refl; eauto.
Qed.
Next Obligation.
  ii. inv H; inv H0. des; clarify.
  econs; eauto with mem congruence.
  + etrans; et. eauto with congruence.
  + eapply Mem.unchanged_on_trans.
    { eauto with congruence. }
    eapply Mem.unchanged_on_implies; eauto.
  + eapply Mem.unchanged_on_trans.
    { eauto with congruence. }
    eapply Mem.unchanged_on_implies; eauto.
  + etrans; et.
  + etrans; et.
  (* + i. r. etransitivity. *)
  (*   { eapply MAXSRC0; eauto. eapply Plt_Ple_trans; eauto with mem. } *)
  (*   eapply MAXSRC; eauto. *)
  (* + i. r. etransitivity. *)
  (*   { eapply MAXTGT0; eauto. eapply Plt_Ple_trans; eauto with mem. } *)
  (*   eapply MAXTGT; eauto. *)
Qed.

Definition lift_ptt (ptt: partition): partition :=
  fun b ofs =>
    match ptt b ofs with
    | privmod mi => privmod mi
    | external => external
    | priv => external
    | pub => pub
    end
.

Definition lift' (mrel0: t'): t' :=
  (mk (mrel0.(src)) (mrel0.(tgt)) (mrel0.(inj))
      (mrel0.(ge_nb_src)) (mrel0.(ge_nb_tgt))
      (lift_ptt (ptt_src mrel0)) (lift_ptt (ptt_tgt mrel0))
  ).

Definition unlift_ptt (ptt0 ptt1: partition): partition :=
  fun b ofs =>
    match ptt1 b ofs with
    | privmod mi => privmod mi
    | external =>
      match ptt0 b ofs with
      | external => external
      | _ => priv (** _ should be "priv". other cases should not happen **)
      end
    | priv => external (** ? **)
    | pub => pub
    end
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mk mrel1.(src) mrel1.(tgt) mrel1.(inj)
      (mrel0.(ge_nb_src)) (mrel0.(ge_nb_tgt))
      (unlift_ptt (ptt_src mrel0) (ptt_src mrel1)) (unlift_ptt (ptt_tgt mrel0) (ptt_tgt mrel1))
  ).

Hint Unfold lift_ptt unlift_ptt lift' unlift'.

Lemma unlift_spec : forall mrel0 mrel1 : t',
                  le' (lift' mrel0) mrel1 -> wf' mrel0 -> le' mrel0 (unlift' mrel0 mrel1).
Proof.
  i. inv H; ss. econs; ss; eauto; ii; des; ss.
  - eapply Mem.unchanged_on_implies; eauto. ii. unfold ons_mem in *. ss. unfold lift_ptt. des_ifs.
  - eapply Mem.unchanged_on_implies; eauto. ii. unfold ons_mem in *. ss. unfold lift_ptt. des_ifs.
  (* - clear - PUBSRC PR. unfold ons_mem in *. ss. unfold lift_ptt, unlift_ptt in *. *)
  (*   specialize (PUBSRC x0 x1). ss. rewrite PR in *. rewrite PUBSRC; ss. *)
  (* - clear - PUBTGT PR. unfold ons_mem in *. ss. unfold lift_ptt, unlift_ptt in *. *)
  (*   specialize (PUBTGT x0 x1). ss. rewrite PR in *. rewrite PUBTGT; ss. *)
  - clear - EXTSRC PR. unfold ons_mem in *. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (EXTSRC x0 x1). ss. rewrite PR in *. rewrite EXTSRC; ss.
  - clear - EXTTGT PR. unfold ons_mem in *. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (EXTTGT x0 x1). ss. rewrite PR in *. rewrite EXTTGT; ss.
  - clear - PMSRC PR. unfold ons_mem in *. des_sumbool. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (PMSRC mi x0 x1). ss. rewrite PR in *.
    hexploit1 PMSRC. { des_sumbool; ss. } des_sumbool. des_ifs.
  - clear - PMTGT PR. unfold ons_mem in *. des_sumbool. ss. unfold lift_ptt, unlift_ptt in *.
    specialize (PMTGT mi x0 x1). ss. rewrite PR in *.
    hexploit1 PMTGT. { des_sumbool; ss. } des_sumbool. des_ifs.
Qed.

Lemma unlift_wf : forall mrel0 mrel1 : t',
                wf' mrel0 ->
                wf' mrel1 -> le' (lift' mrel0) mrel1 -> wf' (unlift' mrel0 mrel1).
Proof.
  i. inv H. inv H0. inv H1. des; clarify.
  econs; ss.
  - etrans; et. eapply Mem.unchanged_on_nextblock; et.
  - etrans; et. eapply Mem.unchanged_on_nextblock; et.
  -
    intros b ofs.
    unfold public_src, private_src. unfold ons_mem in *. ss. i.
    + unfold unlift_ptt.
      specialize (PTTSRC0 b ofs).
      apply not_and_or in PR. des.
      * unfold loc_unmapped in *.
        exploit PTTSRC0.
        { unfold public_src. ii. eapply PR. unfold private_src in *. des; ss. }
        intro T. rewrite T. ss.
      * exploit PTTSRC0.
        { unfold public_src. ii. eapply PR. unfold private_src in *. des; ss. }
        intro T. rewrite T. ss.
  -
    intros b ofs.
    unfold public_tgt, private_tgt. unfold ons_mem in *. ss. i.
    + unfold unlift_ptt.
      specialize (PTTTGT0 b ofs).
      apply not_and_or in PR. des.
      * unfold loc_unmapped in *.
        exploit PTTTGT0.
        { unfold public_tgt. ii. eapply PR. unfold private_tgt in *. des; ss. }
        intro T. rewrite T. ss.
      * exploit PTTTGT0.
        { unfold public_tgt. ii. eapply PR. unfold private_tgt in *. des; ss. }
        intro T. rewrite T. ss.
Qed.

(* Lemma after_private_src *)
(*       sm0 sm1 *)
(*       (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock)) *)
(*       (MLE: le' (lift' sm0) sm1): *)
(*     (src_private sm0) <2= (src_private sm1). *)
(* Proof. *)
(*   inv MLE. inv SRCUNCHANGED. ss. *)
(*   unfold src_private, valid_blocks; ii; des; esplits; eauto. *)
(*   - eapply loc_unmapped_frozen; eauto. *)
(*   - unfold Mem.valid_block in *. xomega. *)
(* Qed. *)

(* Lemma after_private_tgt *)
(*       sm0 sm1 *)
(*       (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock)) *)
(*       (MWF: wf' sm0) *)
(*       (MLE: le' (lift' sm0) sm1): *)
(*     (tgt_private sm0) <2= (tgt_private sm1). *)
(* Proof. *)
(*   inv MLE. inv TGTUNCHANGED. ss. *)
(*   unfold tgt_private, valid_blocks; ii; des; esplits; eauto. *)
(*   - eapply loc_out_of_reach_frozen; eauto. ii. *)
(*     assert(VALID: Mem.valid_block (src sm0) b0). *)
(*     { apply Classical_Prop.NNPP. ii. exploit Mem.mi_freeblocks; try apply MWF; eauto. ii. clarify. } *)
(*     eapply MAXSRC; eauto. *)
(*   - unfold Mem.valid_block in *. xomega. *)
(* Qed. *)

End MEMINJ.

Hint Unfold private_src private_tgt.
Hint Unfold public_src public_tgt.



Section MEMINJ.

Definition update (sm0: t') (src tgt: mem) (inj: meminj): t' :=
  mk src tgt inj sm0.(ge_nb_src) sm0.(ge_nb_tgt) (sm0.(ptt_src)) (sm0.(ptt_tgt))
.
Hint Unfold update.
(* Notation "sm0 '.(update_tgt)' tgt" := (sm0.(update) sm0.(src) tgt sm0.(inj)) (at level 50). *)
(* Definition update_tgt (sm0: t') (tgt: mem) := (sm0.(update) sm0.(src) tgt sm0.(inj)). *)
(* Definition update_src (sm0: t') (src: mem) := (sm0.(update) src sm0.(tgt) sm0.(inj)). *)
(* Hint Unfold update_src update_tgt. *)

Hint Unfold private_src private_tgt valid_blocks.

Inductive lepriv (sm0 sm1: t'): Prop :=
| lepriv_intro
    (FINCR: frozen_incr (sm0.(ge_nb_src)) (sm0.(ge_nb_tgt)) sm0.(inj) sm1.(inj))
    (GENBSRC: sm0.(ge_nb_src) = sm1.(ge_nb_src))
    (GENBTGT: sm0.(ge_nb_tgt) = sm1.(ge_nb_tgt))
    (* (PUBSRC: (public_src sm0) <2= (public_src sm1)) *)
    (* (PUBTGT: (public_tgt sm0) <2= (public_tgt sm1)) *)
    (* (PUBSRC: (ons_mem sm0.(ptt_src) pub) <2= (ons_mem sm1.(ptt_src) pub)) *)
    (* (PUBTGT: (ons_mem sm0.(ptt_tgt) pub) <2= (ons_mem sm1.(ptt_tgt) pub)) *)
    (PMSRC: forall mi, (ons_mem sm0.(ptt_src) (privmod mi)) <2= (ons_mem sm1.(ptt_src) (privmod mi)))
    (PMTGT: forall mi, (ons_mem sm0.(ptt_tgt) (privmod mi)) <2= (ons_mem sm1.(ptt_tgt) (privmod mi)))
.

Global Program Instance lepriv_PreOrder: RelationClasses.PreOrder lepriv.
Next Obligation.
  ii. econs; eauto.
  refl.
Qed.
Next Obligation.
  ii. inv H; inv H0. des; clarify. econs; eauto with mem congruence.
  + etrans; et. rp; et.
  + etrans; et.
  + etrans; et.
Qed.

Global Program Instance SimMemInjSep : SimMem.class :=
{ t := t';
  src := src;
  tgt := tgt;
  ptt_src := ptt_src;
  ptt_tgt := ptt_tgt;
  wf := wf';
  le := le';
  (* lift := lift'; *)
  (* unlift := unlift'; *)
  lepriv := lepriv;
  sim_val := fun (mrel: t') => Val.inject mrel.(inj);
  sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
  unchanged_on := Mem.unchanged_on;
}.
Next Obligation. rename H into LE. inv LE. econs; et. Qed.
(* Next Obligation. *)
(*   rename H into VALID. *)
(*   inv VALID. econs; ss; eauto; ii; des; ss; eauto. *)
(*   - eapply Pos.compare_gt_iff in H. xomega. *)
(*   - eapply Pos.compare_gt_iff in H. xomega. *)
(* Qed. *)
(* Next Obligation. *)
(*   eapply unlift_spec; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   eapply unlift_wf; eauto. *)
(* Qed. *)
Next Obligation. ii. inv MLE. eapply val_inject_incr; try apply FINCR; eauto. Qed.
Next Obligation.
  do 2 (apply Axioms.functional_extensionality; i). apply prop_ext1. split; i; ss; clarify.
  - ginduction x; ii; inv H; ss. econs; eauto.
  - ginduction x1; ii; inv H; ss. econs; eauto.
Qed.
Next Obligation. inv H. ss. Qed.
Next Obligation. ii. eapply Mem.unchanged_on_implies; et. Qed.






Global Program Instance SimMemInjSepLift : SimMemLift.class SimMemInjSep :=
{ lift := lift';
  unlift := unlift';
}.
Next Obligation.
  inv H. econs; et.
  - etrans; et. unfold lift', ons_mem. ss. unfold lift_ptt; ss. ii. des_ifs.
  - etrans; et. unfold lift', ons_mem. ss. unfold lift_ptt; ss. ii. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold lift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold lift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold unlift_ptt. des_ifs.
Qed.
Next Obligation.
  eapply func_ext2. intros b ofs. unfold unlift_ptt. des_ifs.
Qed.
Next Obligation. eapply unlift_spec; et. Qed.
Next Obligation. eapply unlift_wf; eauto. Qed.
Next Obligation.
  inv MWF. destruct sm0; ss. econs; ss; et.
  - refl.
  - ii. unfold ons_mem in *. unfold lift_ptt. des_ifs.
  - ii. unfold ons_mem in *. unfold lift_ptt. des_ifs.
  (* - ii. unfold ons_mem in *. unfold lift_ptt. des_ifs. *)
  (* - ii. unfold ons_mem in *. unfold lift_ptt. des_ifs. *)
Qed.
Next Obligation.
  inv MWF. inv MLE. inv MLIFT. econs; ss; et; try congruence.
  - refl.
  - ii. unfold ons_mem in *. unfold unlift_ptt. des_ifs.
  - ii. unfold ons_mem in *. unfold unlift_ptt. des_ifs.
  (* - ii. unfold ons_mem in *. unfold unlift_ptt. des_ifs. *)
  (* - ii. unfold ons_mem in *. unfold unlift_ptt. des_ifs. *)
Qed.

Global Program Instance SimMemInjOhLift: SimMemOhLift.class (@SimMemOh_default SimMemInjSep)
  := SimMemOhLift.SimMemOhLift_transform.

Section ORIGINALS.

Lemma store_mapped
      sm0 chunk v_src v_tgt blk_src ofs blk_tgt delta m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.store chunk sm0.(src) blk_src ofs v_src = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
:
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.store chunk sm0.(tgt) blk_tgt (ofs + delta) v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.store_mapped_inject; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTSRC. unfold ons_mem. rewrite PTTSRC. ss.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold ons_mem. rewrite PTTTGT. ss.
    (* + unfold public_src, private_src. ss. ii; des; eauto with mem. *)
    (* + unfold public_tgt, private_tgt. ss. ii; des; eauto with mem. *)
  - des. econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTSRC. unfold privmod_others. rewrite PTTSRC. ss.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold privmod_others. rewrite PTTTGT. ss.
  - econs; ss; eauto.
    + etrans; et. erewrite <- Mem.nextblock_store; et. xomega.
    + etrans; et. erewrite <- Mem.nextblock_store; et. xomega.
    + etrans; try apply PTTSRC; et. unfold public_src, private_src. ss.
      unfold valid_blocks. ii. des. Psimpl. des; eauto with mem.
      unfold loc_unmapped in *. Psimpl. des; ss. Psimpl.
      eauto with mem.
    + etrans; try apply PTTTGT; et. unfold public_tgt, private_tgt. ss.
      unfold valid_blocks. ii. des. eapply PR. esplits; eauto with mem.
      { ii. exploit H1; et. eauto with mem. }
Unshelve.
  all: try apply sm0.
Qed.

Lemma storev_mapped
      sm0 chunk v_src v_tgt addr_src addr_tgt m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.storev chunk sm0.(src) addr_src v_src = Some m_src0)
      (SIMADDR: Val.inject sm0.(inj) addr_src addr_tgt)
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.storev chunk sm0.(tgt) addr_tgt v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.storev_mapped_inject; try apply MWF; eauto. i; des.
  unfold Mem.storev in STRSRC. des_ifs. inv SIMADDR. exploit store_mapped; eauto. i; des.
  exists sm1. esplits; eauto. unfold Mem.storev.
  hexploit (size_chunk_pos chunk); eauto. intro SZ.
  assert(Ptrofs.unsigned i + delta = Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))).
  { rewrite <- Ptrofs.repr_unsigned with (i := i). rewrite Ptrofs.Ptrofs_add_repr.
    rewrite Ptrofs.unsigned_repr; [|eapply Ptrofs.unsigned_range_2]. rewrite Ptrofs.unsigned_repr; eauto.
    eapply Mem.mi_representable; eauto.
    left. eapply Mem.perm_store_1; eauto. eapply Mem.perm_implies; [|eauto with mem]. eapply Mem.perm_cur_max.
    eapply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eapply H1. omega.
  }
  rewrite <- H1. eauto.
Qed.

Lemma store_right_prv
      sm0 chunk v_tgt ofs blk_tgt m_tgt0
      (MWF: wf' sm0)
      (PRVTGT: brange blk_tgt (ofs) (ofs + size_chunk chunk) <2=
              (ons_mem sm0.(ptt_tgt) priv))
      (STRTGT: Mem.store chunk sm0.(tgt) blk_tgt (ofs) v_tgt = Some m_tgt0)
:
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.store_outside_inject; try apply MWF; eauto.
  { ii. unfold brange in *. exploit PRVTGT; et.
    intro T.
    inv MWF.
    exploit PTTTGT; et.
    { unfold public_tgt, private_tgt. Psimpl. sii X. eapply X; et.
      instantiate (1:= ofs' + delta). zsimpl. eauto with mem. }
    intro U. rr in U. rr in T. rewrite U in T. ss. }
  intro U; des.
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + refl.
    + inv MWF.
      eapply Mem.store_unchanged_on; eauto. sii X.
      exploit PRVTGT; et. intro T. rr in T. rr in X0. rewrite T in X0. ss.
    (* + unfold public_src, private_src. ss. ii; des; eauto with mem. *)
  - des. econs; ss; eauto.
    + refl.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PRVTGT blk_tgt i). hexploit1 PRVTGT; et. rr in PRVTGT.
      { ii. unfold privmods, privmod_others in *. des_ifs. rewrite PRVTGT in *. ss. }
  - econs; ss; eauto; try apply MWF.
    + inv MWF. etrans; et. erewrite <- Mem.nextblock_store; et. refl.
    + inv MWF. etrans; try apply PTTTGT; et.
      unfold public_tgt, private_tgt; ss. ii; des. Psimpl. des; et.
      eapply PR. u in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma store_right_pm
      mi sm0 chunk v_tgt ofs blk_tgt m_tgt0
      (MWF: wf' sm0)
      (PMTGT: brange blk_tgt (ofs) (ofs + size_chunk chunk) <2=
              (privmods mi sm0.(ptt_tgt)))
      (STRTGT: Mem.store chunk sm0.(tgt) blk_tgt (ofs) v_tgt = Some m_tgt0)
:
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch mi sm0 sm1>>)
.
Proof.
  exploit Mem.store_outside_inject; try apply MWF; eauto.
  { ii. unfold brange in *. exploit PMTGT; et.
    intro T.
    inv MWF.
    exploit PTTTGT; et.
    { unfold public_tgt, private_tgt. Psimpl. sii X. eapply X; et.
      instantiate (1:= ofs' + delta). zsimpl. eauto with mem. }
    intro U. rr in U. des. unfold privmods in T. des_ifs. rewrite U in *. ss. }
  intro U; des.
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + refl.
    + inv MWF.
      eapply Mem.store_unchanged_on; eauto. sii X.
      exploit PMTGT; et. intro T. unfold privmods in *. des_ifs. rewrite X0 in *. ss.
    (* + unfold public_src, private_src. ss. ii; des; eauto with mem. *)
  - des. econs; ss; eauto.
    + refl.
    + eapply Mem.store_unchanged_on; eauto. i.
      specialize (PMTGT blk_tgt i). hexploit1 PTTTGT; et.
      { ii. unfold privmods, privmod_others in *. des_ifs. }
  - econs; ss; eauto; try apply MWF.
    + inv MWF. etrans; et. erewrite <- Mem.nextblock_store; et. refl.
    + inv MWF. etrans; try apply PTTTGT; et.
      unfold public_tgt, private_tgt; ss. ii; des. Psimpl. des; et.
      eapply PR. u in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_parallel
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<FREETGT: Mem.free sm0.(tgt) blk_tgt (lo + delta) (hi + delta) = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.free_parallel_inject; try apply MWF; eauto. i; des. inv MWF.
  (* assert(exists ptt_tgt: partition, <<U: True>>). *)
  (* { esplits; et. exact (fun _ _ => pub). } *)
  (* des. *)
  (* eexists (mk _ _ _ sm0.(ptt_src) ptt_tgt0). dsplits; ss; eauto; cycle 1. *)
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        eapply Mem.free_range_perm in FREESRC. eauto with mem xomega.
      }
      rr in PTTSRC. unfold ons_mem. rewrite PTTSRC. ss.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.free_range_perm in FREESRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold ons_mem. rewrite PTTTGT. ss.
    (* + ii. eapply Mem.perm_free_3; eauto. *)
    (* + ii. eapply Mem.perm_free_3; eauto. *)
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        eapply Mem.free_range_perm in FREESRC. eauto with mem xomega. }
      rr in PTTSRC. unfold privmod_others. rewrite PTTSRC. ss.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTTGT blk_tgt i). hexploit1 PTTTGT; et.
      { unfold public_tgt, private_tgt. eapply or_not_and. left.
        unfold loc_out_of_reach. intro T. eapply T; et.
        apply Mem.free_range_perm in FREESRC. eauto with mem xomega.
      }
      rr in PTTTGT. unfold privmod_others. rewrite PTTTGT. ss.
  - econs; ss; eauto.
    + etrans; et. erewrite <- Mem.nextblock_free; et. xomega.
    + etrans; et. erewrite <- Mem.nextblock_free; et. xomega.
    + etrans; try apply PTTSRC. unfold public_src, private_src; ss.
      ii; des. Psimpl. des.
      * unfold loc_unmapped in *. Psimpl. des; ss. Psimpl. eauto with mem.
      * eapply PR; esplits; et. unfold valid_blocks in *. eauto with mem.
    + etrans; try apply PTTTGT. unfold public_tgt, private_tgt; ss.
      ii; des. eapply PR; esplits; et.
      { unfold loc_out_of_reach in *. ii. eapply H1; et. eauto with mem. }
      { unfold valid_blocks in *. eauto with mem. }
Unshelve.
  all: try apply sm0.
Qed.

Ltac fold_not :=
  repeat
    multimatch goal with
    | H: context [?P -> False] |- _ => fold (~ P) in H
    | |- context [?P -> False] => fold (~ P)
    end
.
Goal (True -> False) -> (True -> False -> False) -> (True -> False).
  intros T U. fold_not.
Abort.

Lemma free_left
      ons_src ons_tgt sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
      /\ (<<PMSRC: (brange blk_src lo hi) <2= ons_mem sm1.(ptt_src) ons_src>>)
      /\ (<<PMTGT: (brange blk_tgt (lo + delta) (hi + delta)) <2= ons_mem sm1.(ptt_tgt) ons_tgt>>)
.
Proof.
  exploit Mem.free_left_inject; try apply MWF; eauto. i; des. inv MWF.
  eexists (mk _ _ _ _ _
              (fun b ofs => if (eq_block b blk_src) && (lo <=? ofs) && (ofs <? hi)
                            then ons_src
                            else sm0.(ptt_src) b ofs)
              (fun b ofs => if (eq_block b blk_tgt) && ((lo + delta) <=? ofs) && (ofs <? (hi + delta))
                            then ons_tgt
                            else sm0.(ptt_tgt) b ofs)
          ).
  dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        eapply Mem.free_range_perm in FREESRC. eauto with mem xomega. }
      rr in PTTSRC. unfold ons_mem. rewrite PTTSRC. ss.
    + refl.
    + u. ii. des_ifs. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTSRC; et.
      { unfold public_src, private_src. u. ii. rewrite SIMBLK in *. des; ss; eauto. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. i; congruence.
    + u. ii. des_ifs. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt. ii. des. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. i; congruence.
    + u. ii. des_ifs. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTSRC; et.
      { unfold public_src, private_src. u. ii. rewrite SIMBLK in *. des; ss; eauto. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. i; congruence.
    + u. ii. des_ifs. exfalso. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt. ii. des. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. i; congruence.
    (* + ii. eapply Mem.perm_free_3; eauto. *)
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto. i.
      specialize (PTTSRC blk_src i). hexploit1 PTTSRC; et.
      { unfold public_src, private_src. eapply or_not_and. left.
        unfold loc_unmapped. rewrite SIMBLK; ss. Psimpl. esplits; ss; et. Psimpl.
        eapply Mem.free_range_perm in FREESRC. eauto with mem xomega. }
      rr in PTTSRC. unfold privmod_others. rewrite PTTSRC. ss.
    + refl.
    +  u. ii. unfold privmods in *. des_ifs_safe; ss. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTSRC; et.
      { unfold public_src, private_src. u. ii. rewrite SIMBLK in *. des; ss; eauto. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. intro T. rewrite T in *. ss.
    + u. ii. unfold privmods in *. des_ifs_safe; ss. bsimpl. des. des_sumbool. clarify.
      rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt. ii. des. eapply H0; et.
        instantiate (1:= x1). eapply Mem.perm_max; et.
        eapply Mem.perm_implies with Freeable; [|eauto with mem].
        eapply Mem.free_range_perm in FREESRC. eapply FREESRC. xomega.
      }
      u. intro T. rewrite T in *. ss.
  - u. ii. des. clarify. rewrite <- Z.leb_le in *. rewrite <- Z.ltb_lt in *. des_ifs.
    bsimpl. des_sumbool; congruence.
  - u. ii. des. clarify. des_ifs. bsimpl. rewrite <- Z.leb_le in *. rewrite <- Z.ltb_lt in *.
    des; des_sumbool; congruence.
  - econs; ss; eauto.
    + etrans; et. erewrite <- Mem.nextblock_free; et. xomega.
    + u. ii. fold_not. repeat (Psimpl; des).
      * des_ifs.
        { bsimpl. des. des_sumbool. clarify. rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
          exploit Mem_free_noperm; et. intro T. ss.
        }
        { exploit PTTSRC; et.
          u. fold_not. Psimpl. ii. des; ss. eauto with mem. }
      * des_ifs.
        { bsimpl. des. des_sumbool. clarify. rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
          exploit Mem.mi_freeblocks; try apply PR; eauto. intro T; clarify.
        }
        { exploit PTTSRC; et.
          u. fold_not. Psimpl. ii. des; ss; eauto with mem. }
    + u. ii. des_ifs.
      * exfalso. bsimpl. des. des_sumbool. clarify.
        rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
        eapply PR. esplits; eauto.
        { ii. destruct (classic (b0 = blk_src)).
          { clarify. eapply Mem_free_noperm; et. xomega. }
          exploit (Mem.mi_no_overlap); try apply H2; et.
          { eauto with mem. }
          { eapply Mem.free_range_perm in FREESRC; et.
            eapply Mem.perm_max. eapply Mem.perm_implies with Freeable; [|eauto with mem].
            eapply FREESRC; et. instantiate (1:= x1 - delta). xomega.
          }
          ii. des; clarify. zsimpl. ss.
        }
        eapply Mem.mi_mappedblocks; et.
      * etrans; try apply PTTTGT; ss. u.
        ii; des. eapply PR; esplits; et.
        { unfold loc_out_of_reach in *. ii. eapply H0; et. eauto with mem. }
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_right_prv
      sm0 lo hi blk_tgt m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk_tgt lo hi = Some m_tgt0)
      (PRVTGT: brange blk_tgt lo hi <2= (ons_mem sm0.(ptt_tgt) priv))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
      /\ (<<PRVSRC: (ons_mem sm0.(ptt_src) priv) = (ons_mem sm1.(ptt_src) priv)>>)
      /\ (<<PRVTGT: (ons_mem sm0.(ptt_tgt) priv) = (ons_mem sm1.(ptt_tgt) priv)>>)
.
Proof.
  exploit Mem.free_right_inject; try apply MWF; eauto.
  {
    ii.
    exploit PRVTGT; et. intro T. r in T.
    inv MWF.
    exploit PTTTGT; et.
    { unfold public_tgt, private_tgt. sii X; des.
      eapply X; et. instantiate (1:= ofs + delta). zsimpl. eauto with mem.
    }
    intro U. r in U. congruence.
  }
  intro U; des. inv MWF.
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + refl.
    + eapply Mem.free_unchanged_on; eauto. ii. exploit PRVTGT; et. intro V. u in *; congruence.
    (* + ii. eapply Mem.perm_free_3; eauto. *)
  - econs; ss; eauto.
    + refl.
    + eapply Mem.free_unchanged_on; et.
      sii X.
      exploit PRVTGT; et. intro Y. u in *; des_ifs. rewrite Y in *; ss.
  - econs; ss; eauto.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; try apply PTTTGT; eauto.
      unfold public_tgt, private_tgt; ss. ii. Psimpl. des; et. eapply PR; et. u in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_right_pm
      mi sm0 lo hi blk_tgt m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk_tgt lo hi = Some m_tgt0)
      (PRVTGT: brange blk_tgt lo hi <2= (ons_mem sm0.(ptt_tgt) (privmod mi)))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch (Some mi) sm0 sm1>>)
      /\ (<<PRVSRC: (ons_mem sm0.(ptt_src) priv) = (ons_mem sm1.(ptt_src) priv)>>)
      /\ (<<PRVTGT: (ons_mem sm0.(ptt_tgt) priv) = (ons_mem sm1.(ptt_tgt) priv)>>)
.
Proof.
  exploit Mem.free_right_inject; try apply MWF; eauto.
  {
    ii.
    exploit PRVTGT; et. intro T. r in T.
    inv MWF.
    exploit PTTTGT; et.
    { unfold public_tgt, private_tgt. sii X; des.
      eapply X; et. instantiate (1:= ofs + delta). zsimpl. eauto with mem.
    }
    intro U. r in U. congruence.
  }
  intro U; des. inv MWF.
  eexists (mk _ _ _ _ _ sm0.(ptt_src) sm0.(ptt_tgt)). dsplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + refl.
    + refl.
    + eapply Mem.free_unchanged_on; eauto. ii. exploit PRVTGT; et. intro V. u in *; congruence.
    (* + ii. eapply Mem.perm_free_3; eauto. *)
  - econs; ss; eauto.
    + refl.
    + eapply Mem.free_unchanged_on; et.
      sii X.
      exploit PRVTGT; et. intro Y. u in *; des_ifs. rewrite Y in *; ss. bsimpl. des_sumbool. clarify.
  - econs; ss; eauto.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; try apply PTTTGT; eauto.
      unfold public_tgt, private_tgt; ss. ii. Psimpl. des; et. eapply PR; et. u in *. eauto with mem.
Unshelve.
  all: try apply sm0.
Qed.

Lemma free_list_right_prv
      sm0 rngs m_tgt0 m_tgt1
      (MTGT: m_tgt0 = sm0.(tgt))
      (MWF: wf' sm0)
      (FREETGT: Mem.free_list m_tgt0 rngs = Some m_tgt1)
      (PRVTGT: forall b lo hi, In (b, lo, hi) rngs -> brange b lo hi <2= (ons_mem sm0.(ptt_tgt) priv))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt1>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
      /\ (<<PRVSRC: (ons_mem sm0.(ptt_src) priv) = (ons_mem sm1.(ptt_src) priv)>>)
      /\ (<<PRVTGT: (ons_mem sm0.(ptt_tgt) priv) = (ons_mem sm1.(ptt_tgt) priv)>>)
.
Proof.
  ginduction rngs; ii; ss.
  { clarify. esplits; et; try refl. }
  des_ifs.
  exploit free_right_prv; et. i; des. clarify.
  exploit (IHrngs sm1); try apply FREETGT; et.
  { ii. exploit PRVTGT; et. i. rewrite <- PRVTGT0. ss. }
  i; des.
  exists sm2.
  esplits; ss; et; try congruence.
  { etrans; et. }
  { etrans; et. }
Qed.

Lemma alloc_parallel
      sm0 lo_src hi_src lo_tgt hi_tgt blk_src m_src0
      (MWF: wf' sm0)
      (ALCSRC: Mem.alloc sm0.(src) lo_src hi_src = (m_src0, blk_src))
      (LO: lo_tgt <= lo_src)
      (HI: hi_src <= hi_tgt):
    exists sm1 blk_tgt ,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<ALCTGT: Mem.alloc sm0.(tgt) lo_tgt hi_tgt = (sm1.(tgt), blk_tgt)>>)
      /\ (<<INJ: sm1.(inj) blk_src = Some (blk_tgt, 0) /\ forall b, b <> blk_src -> sm1.(inj) b = sm0.(inj) b>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  exploit Mem.alloc_parallel_inject; try apply MWF; eauto. i; des. inv MWF.
  (* assert(FROZEN: frozen (inj sm0) f' (src_parent_nb sm0) (tgt_parent_nb sm0)). *)
  (* { *)
  (*   + econs. ii. des. destruct (eq_block b_src blk_src). *)
  (*     * subst. rewrite H2 in NEW0. clarify. eapply Mem.alloc_result in ALCSRC. rewrite ALCSRC. *)
  (*       eapply Mem.alloc_result in H. rewrite H. esplits; eauto. *)
  (*     * rewrite H3 in NEW0; eauto. clarify. *)
  (* } *)
  eexists (mk _ _ f' _ _
              (fun b ofs => if eq_block b blk_src
                                   then pub
                                   else sm0.(ptt_src) b ofs)
              (fun b ofs => if eq_block b b2
                            then pub
                            else sm0.(ptt_tgt) b ofs)). exists b2.
  dsplits; ss; eauto; cycle 1.
  -
    econs; ss; eauto.
    + econs; eauto. econs; eauto. ii; des.
      destruct (eq_block b_src blk_src).
      * clarify. esplits; etrans; eauto with mem.
        { exploit Mem.alloc_result; try apply ALCSRC. i; des. clarify. xomega. }
        { exploit Mem.alloc_result; try apply H. i; des. clarify. xomega. }
      * erewrite H3 in NEW0; et. clarify.
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    (* + unfold ons_mem. ii. des_ifs. *)
    (* + unfold ons_mem. ii. des_ifs. *)
    + unfold ons_mem. ii. des_ifs.
      exploit (PTTSRC blk_src x1).
      { unfold public_src, private_src. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto. }
      unfold ons_mem. intro T. congruence.
    + unfold ons_mem. ii. des_ifs.
      exploit (PTTTGT b2 x1).
      { unfold public_tgt, private_tgt. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply H; eauto. }
      unfold ons_mem. intro T. congruence.
    + unfold ons_mem. ii. des_ifs.
      exploit (PTTSRC blk_src x1).
      { unfold public_src, private_src. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto. }
      unfold ons_mem. intro T. congruence.
    + unfold ons_mem. ii. des_ifs.
      exploit (PTTTGT b2 x1).
      { unfold public_tgt, private_tgt. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply H; eauto. }
      unfold ons_mem. intro T. congruence.
    (* + ii. eapply Mem.perm_alloc_4; eauto. *)
    (*   ii. subst b. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto. *)
    (* + ii. eapply Mem.perm_alloc_4; eauto. *)
    (*   ii. subst b. eapply Mem.fresh_block_alloc; eauto. *)
  - econs; ss; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + unfold privmods. ii. des_ifs. des_sumbool. clarify.
      exploit (PTTSRC blk_src x1).
      { unfold public_src, private_src. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto. }
      unfold ons_mem. intro T. congruence.
    + unfold privmods. ii. des_ifs. des_sumbool. clarify.
      exploit (PTTTGT b2 x1).
      { unfold public_tgt, private_tgt. apply or_not_and. right. ii. unfold valid_blocks in *.
        eapply Mem.fresh_block_alloc; try eapply ALCTGT; eauto. }
      unfold ons_mem. intro T. congruence.
  - econs; ss; eauto.
    + etrans; et. exploit Mem.nextblock_alloc; try apply ALCSRC. intro T; des. rewrite T. xomega.
    + etrans; et. exploit Mem.nextblock_alloc; try apply H. intro T; des. rewrite T. xomega.
    + unfold public_src, private_src in *. ss. ii. unfold ons_mem. des_ifs.
      rewrite PTTSRC; ss. eapply not_and_or in PR. eapply or_not_and.
      unfold valid_blocks in *.
      des.
      { left. ii. eapply PR. rr. rr in H4. erewrite H3; et. des; et. right.
        ii. eauto with mem.
      }
      { right. ii. eapply PR. eauto with mem. }
    + unfold public_tgt, private_tgt in *. ss. ii. unfold ons_mem. des_ifs.
      rewrite PTTTGT; ss. eapply not_and_or in PR. eapply or_not_and.
      unfold valid_blocks in *.
      des.
      { left. ii. eapply PR. rr. rr in H4. ii.
        destruct (classic (b0 = blk_src)).
        { clarify. }
        erewrite H3 in H5; ss. eapply H4; et. eapply Mem.perm_alloc_4; et. }
      { right. ii. eapply PR. eauto with mem. }
Unshelve.
  all: try apply sm0.
Qed.

Program Instance or_Symmetric: Symmetric or.
Next Obligation.
  tauto.
Qed.

Program Instance and_Symmetric: Symmetric and.

Lemma external_call
      sm0 ef se vargs t vres m_src0 tse vargs' vres' m_tgt0 f'
      (MWF: wf' sm0)
      (EXTCALLSRC: Events.external_call ef se vargs sm0.(src) t vres m_src0)
      (EXTCALLTGT: Events.external_call ef tse vargs' sm0.(tgt) t vres' m_tgt0)
      (MEMINJ: Mem.inject f' m_src0 m_tgt0)
      (UNCHANGSRC: Mem.unchanged_on (loc_unmapped sm0.(inj) sm0.(src)) sm0.(src) m_src0)
      (UNCHANGTGT: Mem.unchanged_on (loc_out_of_reach sm0.(inj) sm0.(src)) sm0.(tgt) m_tgt0)
      (INJINCR: inject_incr sm0.(inj) f')
      (INJSEP: inject_separated sm0.(inj) f' sm0.(src) sm0.(tgt))
      (PERMSRC: forall b ofs p, Mem.valid_block sm0.(src) b -> Mem.perm m_src0 b ofs Max p
                                -> Mem.perm sm0.(src) b ofs Max p)
      (PERMTGT: forall b ofs p, Mem.valid_block sm0.(tgt) b -> Mem.perm m_tgt0 b ofs Max p
                                -> Mem.perm sm0.(tgt) b ofs Max p)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = f'>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
      /\ (<<UNCH: SimMem.unch None sm0 sm1>>)
.
Proof.
  inv MWF.
  eexists (mk _ _ _ sm0.(ge_nb_src) sm0.(ge_nb_tgt) sm0.(ptt_src) sm0.(ptt_tgt)); ss.
  esplits; et.
  - econs; et.
    + ss. etrans; et. eapply Mem.unchanged_on_nextblock; et.
    + ss. etrans; et. eapply Mem.unchanged_on_nextblock; et.
    + unfold ons_mem. ss.
      unfold public_src, private_src. ss.
      ii. exploit PTTSRC; et. Psimpl. des.
      * unfold public_src, private_src. Psimpl. ii. apply PR0. rr. rr in H.
        des.
        {
          destruct (f' x0) eqn:T; ss; et. destruct p; ss. exfalso.
          exploit INJSEP; et. i; des. unfold valid_blocks in *. ss.
        }
        {
          right. ii. eapply external_call_max_perm in H; eauto.
        }
      *
        unfold public_src, private_src. Psimpl. ii. apply PR. unfold valid_blocks in *.
        eapply Mem.valid_block_unchanged_on; et.
    + unfold ons_mem. ss.
      unfold public_tgt, private_tgt. ss.
      ii. exploit PTTTGT; et. Psimpl. des.
      * unfold public_tgt, private_tgt. Psimpl. ii. apply PR0. rr. rr in H. ii.
        destruct (sm0.(inj) b0) eqn:T; ss.
        { destruct p; ss. exploit INJINCR; et. i; clarify.
          eapply H; et. eapply PERMSRC; et.
          eapply NNPP. intro U. eapply Mem.mi_freeblocks in U; et. clarify. }
        exploit INJSEP; et. i; des. unfold valid_blocks in *. ss.
      *
        unfold public_tgt, private_tgt. Psimpl. ii. apply PR. unfold valid_blocks in *.
        eapply Mem.valid_block_unchanged_on; et.
  - econs; ss; et.
    + econs; et. eapply inject_separated_frozen in INJSEP. eapply frozen_shortened; et.
    + eapply Mem.unchanged_on_implies; et.
      ii. rr. destruct (sm0.(inj) b) eqn:T; ss; et. right. ii. destruct p; ss.
      exploit PTTSRC; et.
      { unfold public_src, private_src. unfold loc_unmapped. rewrite T. Psimpl. ii; clarify.
        des; clarify. eauto with mem.
      }
      i. unfold ons_mem in *. rewrite H in *. clarify.
    + eapply Mem.unchanged_on_implies; et.
      ii. rr. (* destruct (sm0.(inj) b) eqn:T; ss. exfalso. destruct p; ss. *)
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt. unfold loc_out_of_reach. Psimpl. ii; clarify.
        eapply H3; et. }
      i. unfold ons_mem in *. rewrite H in *. clarify.
  - econs; ss; et.
    + eapply Mem.unchanged_on_implies; et.
      ii. rr. destruct (sm0.(inj) b) eqn:T; ss; et. right. ii. destruct p; ss.
      exploit PTTSRC; et.
      { unfold public_src, private_src. unfold loc_unmapped. rewrite T. Psimpl. ii; clarify.
        des; clarify. eauto with mem.
      }
      i. unfold ons_mem, privmod_others in *. rewrite H2 in *. clarify.
    + eapply Mem.unchanged_on_implies; et.
      ii. rr. (* destruct (sm0.(inj) b) eqn:T; ss. exfalso. destruct p; ss. *)
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt. unfold loc_out_of_reach. Psimpl. ii; clarify.
        eapply H3; et. }
      i. unfold ons_mem, privmod_others in *. rewrite H3 in *. clarify.
Unshelve.
  all: by (try eapply inject_separated_frozen; eauto).
Qed.

(* Lemma free_list *)
(*       sm0 l m_src0 l' m_tgt0 *)
(*       (MWF : wf' sm0) *)
(*       (FREESRC: Mem.free_list sm0.(src) l = Some m_src0) *)
(*       (FREETGT: Mem.free_list sm0.(tgt) l' = Some m_tgt0) *)
(*       (MEMINJ: Mem.inject sm0.(inj) m_src0 m_tgt0) *)
(*       (EXTSRC: forall b lo hi i, In (b, lo, hi) l -> lo <= i < hi -> ~ sm0.(src_external) b i) *)
(*       (EXTTGT: forall b lo hi i, In (b, lo, hi) l' -> lo <= i < hi -> ~ sm0.(tgt_external) b i): *)
(*     exists sm1, *)
(*       (<<MSRC: sm1.(src) = m_src0>>) *)
(*       /\ (<<MTGT: sm1.(tgt) = m_tgt0>>) *)
(*       /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>) *)
(*       /\ (<<MWF: wf' sm1>>) *)
(*       /\ (<<MLE: le' sm0 sm1>>) *)
(*       /\ (<<UNCH: SimMem.unch None sm0 sm1>>) *)
(* . *)
(* Proof. *)
(*   inv MWF. eexists (mk _ _ _ _ _ _ _ _ _ _ _). dsplits; ss; eauto; cycle 1. *)
(*   - econs; ss; eauto. *)
(*     + eapply Mem.free_list_unchanged_on; eauto. *)
(*     + eapply Mem.free_list_unchanged_on; eauto. *)
(*     + eapply frozen_refl. + eapply frozen_refl. *)
(*     + ii. eapply Mem.perm_free_list; eauto. *)
(*     + ii. eapply Mem.perm_free_list; eauto.       *)
(*   - econs; ss; eauto. *)
(*     + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et. *)
(*     + eapply Mem.unchanged_on_implies; try apply Mem_unchanged_on_bot; ss. eapply SPLITHINT3; et. *)
(*   - econs; ss; eauto. *)
(*     + etransitivity; eauto. unfold src_private. ii. ss. des. esplits; eauto. *)
(*       red. red. erewrite Mem.free_list_nextblock; eauto. *)
(*     + etransitivity; eauto. unfold tgt_private. ii. ss. des. esplits; eauto. *)
(*       red. ii. eapply PR; eauto. *)
(*       exploit Mem.perm_free_list; try eapply FREESRC; eauto. i; des. ss. *)
(*       red. red. erewrite Mem.free_list_nextblock; eauto. *)
(*     + erewrite Mem.free_list_nextblock; eauto. *)
(*     + erewrite Mem.free_list_nextblock; eauto. *)
(*     + etransitivity; eauto. unfold src_private. ii. ss. des. esplits; eauto. *)
(*       red. red. erewrite Mem.free_list_nextblock; eauto. *)
(*     + etransitivity; try apply PTTTGT; eauto. unfold tgt_private. ii. ss. des. esplits; eauto. *)
(*       red. ii. eapply PR; eauto. *)
(*       exploit Mem.perm_free_list; try eapply FREESRC; eauto. i; des. ss. *)
(*       red. red. erewrite Mem.free_list_nextblock; eauto. *)
(* Unshelve. *)
(*   all: try apply sm0. *)
(* Qed. *)

End ORIGINALS.

Record mcompat (sm0: t') (m_src0 m_tgt0: mem) (F: meminj): Prop := mkmcompat {
  mcompat_src: sm0.(src) = m_src0;
  mcompat_tgt: sm0.(tgt) = m_tgt0;
  mcompat_inj: sm0.(inj) = F;
}.

End MEMINJ.

Hint Unfold ons_mem.
Hint Unfold valid_blocks.
Hint Unfold lift_ptt unlift_ptt lift' unlift'.
Hint Unfold private_src private_tgt.
Hint Unfold public_src public_tgt.

Ltac compat_tac := ss; econs; eauto; try congruence.






Require SimSymbId.

Section SIMSYMB.

Lemma skenv_inject_meminj_preserves_globals
      F V (skenv: Genv.t F V) j
      (INJECT: skenv_inject skenv j):
    <<INJECT: meminj_preserves_globals skenv j>>.
Proof.
  inv INJECT. rr. esplits; ii; ss; eauto.
  - eapply DOMAIN; eauto. eapply Genv.genv_symb_range; eauto.
  - eapply DOMAIN; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
  - symmetry. eapply IMAGE; eauto. unfold Genv.find_var_info in *. des_ifs. eapply Genv.genv_defs_range; eauto.
Qed.

Inductive sim_skenv_inj (sm: SimMem.t) (__noname__: SimSymbId.t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INJECT: skenv_inject skenv_src sm.(inj))
    (* NOW BELOW IS DERIVABLE FROM WF *)
    (* (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_parent_nb)) *)
    (* (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_parent_nb)) *)
    (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
    (* (PTTSRC: forall b ofs (LE: Plt b skenv_src.(Genv.genv_next)), sm.(ptt_src) b ofs = pub) *)
    (* (PTTTGT: forall b ofs (LE: Plt b skenv_tgt.(Genv.genv_next)), sm.(ptt_tgt) b ofs = pub) *)
    (NBSRC: skenv_src.(Genv.genv_next) = sm.(ge_nb_src))
    (NBTGT: skenv_tgt.(Genv.genv_next) = sm.(ge_nb_tgt))
.

Section REVIVE.

  Context {F1 V1: Type} {LF: Linker F1} {LV: Linker V1}.
  Context `{HasExternal F1}.
  Variables (p_src: AST.program F1 V1).

  Lemma skenv_inject_revive
        skenv_proj_src ge_src j
        (REVIVESRC: ge_src = SkEnv.revive skenv_proj_src p_src)
        (SIMSKENV: skenv_inject skenv_proj_src j):
      <<SIMSKENV: skenv_inject ge_src j>>.
  Proof. clarify. inv SIMSKENV. econs; eauto. Qed.

End REVIVE.



Lemma Mem_unchanged_on_or
      P Q m0 m1
      (UNCH0: Mem.unchanged_on P m0 m1)
      (UNCH1: Mem.unchanged_on Q m0 m1)
  :
    <<UNCH: Mem.unchanged_on (P \2/ Q) m0 m1>>
.
Proof.
  inv UNCH0. inv UNCH1.
  econs; et.
  - ii; des; et.
  - ii; des; et.
Qed.

Global Program Instance SimSymbId: SimSymb.class SimMemInjSep := {
  t := SimSymbId.t';
  src := SimSymbId.src;
  tgt := SimSymbId.tgt;
  le := SimSymbId.le;
  wf := SimSymbId.wf;
  sim_skenv := sim_skenv_inj;
}.
Next Obligation. rr in SIMSK. r. congruence. Qed.
Next Obligation. eapply SimSymbId.wf_link; eauto. Qed.
Next Obligation. inv SIMSKE. inv SIMSKENV. ss. Qed.
Next Obligation.
  exploit SimSymbId.wf_load_sim_skenv; eauto. i; des.
  eexists.
  eexists (mk m_src m_src (Mem.flat_inj m_src.(Mem.nextblock))
              m_src.(Mem.nextblock)
              m_src.(Mem.nextblock)
              (fun _ _ => pub) (fun _ _ => pub)); ss.
  esplits; ss; eauto.
  - econs; ss; eauto.
    + econs; eauto; ii; ss.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto.
  - econs; ss; try xomega; ii; des; ss; eauto.
    + eapply Genv.initmem_inject; eauto; (u in *; eauto).
    (* + unfold privmods in *. des_ifs. *)
    (* + unfold privmods in *. des_ifs. *)
  - rewrite MAINSIM. unfold Genv.symbol_address. des_ifs. unfold Mem.flat_inj. econs; eauto.
    + des_ifs. exfalso. apply n. eapply Plt_Ple_trans.
      { eapply Genv.genv_symb_range; et. }
      erewrite Genv.init_mem_genv_next; eauto. refl.
    + psimpl. ss.
Qed.
Next Obligation.
  inv SIMSKENV. inv INJECT. econs; eauto. econs; eauto.
  - ii. exploit DOMAIN; eauto. i. eapply MLE; eauto.
  - ii. inv MLE. inv FINCR. eapply IMAGE; eauto. erewrite frozen_preserves_tgt; eauto.
    eapply Plt_Ple_trans; eauto. rewrite <- NBTGT. rr in SIMSKENV0. clarify. refl.
  (* - inv MLE. ii. eapply PUBSRC. r. et. *)
  (* - inv MLE. ii. eapply PUBTGT. r. et. *)
  - inv MLE. eauto with congruence.
  - inv MLE. eauto with congruence.
Qed.
(* Next Obligation. *)
(*   inv MWF. inv SIMSKENV. *)
(*   econs; eauto. *)
(*   - etransitivity; try apply SRCLE; eauto. *)
(*   - etransitivity; try apply TGTLE; eauto. *)
(* Qed. *)
Next Obligation.
  set (SkEnv.project skenv_link_src ss.(SimSymbId.src)) as skenv_proj_src.
  generalize (SkEnv.project_impl_spec INCLSRC); intro LESRC.
  set (SkEnv.project skenv_link_tgt ss.(SimSymbId.tgt)) as skenv_proj_tgt.
  generalize (SkEnv.project_impl_spec INCLTGT); intro LETGT.
  exploit SimSymbId.sim_skenv_monotone; try apply SIMSKENV; eauto. i; des.
  inv SIMSKENV. inv LESRC. inv LETGT. econs; eauto. inv INJECT. econs; ii; eauto.
Qed.
Next Obligation.
  exploit SimSymbId.sim_skenv_func_bisim; eauto. { eapply SIMSKENV. } i; des.
  inv H. inv SIMSKENV. inv INJECT. inv SIMSKENV0. econs; eauto.
  ii; ss. eapply FUNCFSIM; eauto. rpapply FUNCSRC. f_equal.
  { inv SIMFPTR; ss. des_ifs. rewrite Ptrofs.add_zero_l.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    exploit DOMAIN; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify. }
Qed.
Next Obligation.
  inv SIMSKENV. econs; eauto.
  - inv INJECT. econs; eauto.
  - eapply SimSymbId.system_sim_skenv; eauto.
Qed.
Next Obligation.
  destruct sm0, args_src, args_tgt; ss; inv ARGS; ss. inv MWF; ss. clarify.
  (* Note: It may be easier && more natural to use
"external_call_mem_inject" with "external_call_symbols_preserved", instead of "external_call_mem_inject_gen" *)
  (* exploit external_call_mem_inject_gen; eauto. *)
  exploit external_call_mem_inject; eauto.
  { eapply skenv_inject_meminj_preserves_globals; eauto. inv SIMSKENV; ss. }
  i; des.
  assert(UNCHSRC: Mem.unchanged_on (loc_unmapped inj0 src0) src0 (Retv.m retv_src)).
  { unfold loc_unmapped. eapply Mem_unchanged_on_or; et.
    econs; et.
    - eapply H2.
    - ii. split; i.
      { r in H6. contradict H6. eapply Mem.perm_max; eauto with mem. }
      { eapply Mem.perm_max in H8. eapply external_call_max_perm in H8; eauto.
        des. eapply Mem.perm_implies with (p2 := Nonempty) in H8; ss. eauto with mem. }
    - ii.
      exploit external_call_readonly; try apply SYSSRC; et. intro RO. inv RO.
      erewrite unchanged_on_contents; et. rr. ii. eauto with mem.
  }
  do 2 eexists. dsplits; eauto; ss.
  - instantiate (1:= Retv.mk _ _); ss. eapply external_call_symbols_preserved; eauto.
    eapply SimSymbId.sim_skenv_equiv; eauto. eapply SIMSKENV.
  - destruct retv_src; ss. instantiate (1:= mk _ _ _ _ _ ptt_src0 ptt_tgt0). econs 1; ss; eauto.
    instantiate (1:= (Retv.m retv_src)). ss.
  - assert(FROZEN: frozen inj0 f' ge_nb_src0 ge_nb_tgt0).
    { eapply inject_separated_frozen in H5. eapply frozen_shortened; eauto. }
    econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
      destruct (inj0 b) eqn:T; ss; et. destruct p; ss. right. ii.
      exploit PTTSRC; et.
      { unfold public_src, private_src; ss. intro U. des. r in U. rewrite T in U; ss.
        des; ss. eauto. }
      intro U. r in U. rewrite U in *. ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. r.
      ii as T.
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt; ss. intro U. des. r in U. exploit U; et. }
      intro U. r in U. rewrite U in *. ss.
    (* + ii. eapply external_call_max_perm; eauto. *)
    (* + ii. eapply external_call_max_perm; eauto. *)
  - econs; ii; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
      destruct (inj0 b) eqn:T; ss; et. destruct p; ss. right. ii.
      exploit PTTSRC; et.
      { unfold public_src, private_src; ss. intro U. des. r in U. rewrite T in U; ss.
        des; ss. eauto. }
      intro U. r in U. rewrite U in *. ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss. r.
      ii as T.
      exploit PTTTGT; et.
      { unfold public_tgt, private_tgt; ss. intro U. des. r in U. exploit U; et. }
      intro U. r in U. rewrite U in *. ss.
  - apply inject_separated_frozen in H5. econs; ss.
    + inv H2. xomega.
    + inv H3. xomega.
    + unfold public_src, private_src; ss. sii T.
      exploit PTTSRC; et.
      unfold public_src, private_src; ss. sii T; des.
      eapply PR. esplits; et.
      * eapply loc_unmapped_frozen; et.
        sii U. eapply external_call_max_perm; et.
      * unfold valid_blocks in *.
        eapply Plt_Ple_trans; et.
        eapply Mem.unchanged_on_nextblock; et.
    + unfold public_tgt, private_tgt; ss. sii T.
      exploit PTTTGT; et.
      unfold public_tgt, private_tgt; ss. sii T; des.
      eapply PR. esplits; et.
      * eapply loc_out_of_reach_frozen; et.
        sii U. eapply external_call_max_perm; et. eapply Mem.valid_block_inject_1; et.
      * unfold valid_blocks in *.
        eapply Plt_Ple_trans; et.
        eapply Mem.unchanged_on_nextblock; et.
Unshelve.
  all: ss.
Qed.

Local Existing Instance SimMemInjSep.
Local Existing Instance SimSymbId.

Lemma sim_skenv_symbols_inject
      sm0 ss0 skenv_src skenv_tgt
      (SIMSKE: SimSymb.sim_skenv sm0 ss0 skenv_src skenv_tgt):
    symbols_inject sm0.(inj) skenv_src skenv_tgt.
Proof.
  inv SIMSKE. inv SIMSKENV. inv INJECT. rr. esplits; ss.
  + i. exploit Genv.genv_symb_range; eauto. intro NB. exploit DOMAIN; eauto. i ;des. clarify.
  + i. exploit Genv.genv_symb_range; eauto.
  + i. unfold Genv.block_is_volatile, Genv.find_var_info. destruct (Genv.find_def skenv_tgt b1) eqn:T.
    * exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des. clarify. des_ifs.
    * des_ifs. exploit Genv.genv_defs_range; eauto. intro NB. exploit DOMAIN; eauto. i; des.
      exploit (IMAGE b1 b2); eauto. i; clarify.
Qed.

End SIMSYMB.

Arguments skenv_inject_revive [_ _ _].
