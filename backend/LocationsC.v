Require Import OrderedType.
Require Import CoqlibC.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Export Machregs.
(** newly added **)
Require Export Locations.
Require Import Conventions Integers Memory.
Require Import List.

Set Implicit Arguments.



Lemma Loc_not_in_notin_R
      r locs
      (NOTIN: ~ In (R r) locs):
    <<NOTIN: Loc.notin (R r) locs>>.
Proof. red. ginduction locs; ii; ss. esplits; eauto. destruct a; ss. ii; clarify. eauto. Qed.

Lemma typealign_divide_8: forall ty,
    <<DIV: (4 * typealign ty | 8)>>.
Proof.
  i. red. change 8 with (4 * 2). eapply Z.mul_divide_mono_l.
  destruct ty; ss; try reflexivity; try apply Z.divide_1_l.
Qed.

Definition locset := Locmap.t.

Local Opaque Z.mul Z.add.
Local Opaque list_nth_z.

Definition is_one A (ap: rpair A): bool :=
  match ap with
  | One _ => true
  | Twolong _ _ => false
  end.

(* Note: this is hacking for 64bit. It just simplifies proof, we don't exploit anything weird *)
Lemma loc_arguments_one:
  forall sg lp (IN: In lp (loc_arguments sg)), <<ONE: is_one lp>>.
Proof.
  destruct sg; ss. unfold loc_arguments in *. ss. des_ifs. clear_tac.
  generalize 0 at 1 as ir. generalize 0 at 1 as fr. generalize 0 at 1 as ofs.
  ginduction sig_args; ii; ss.
  - des_ifs; repeat (des; ss; clarify); eapply IHsig_args; eauto.
Qed.

Lemma loc_result_one: forall sg, exists mr_res, <<ONE: loc_result sg = One mr_res>>.

Lemma Loc_cons_right_disjoint
      xs0 xs1 x
      (DISJ: Loc.disjoint xs0 xs1)
      (NOTIN: Loc.notin x xs0):
    <<DISJ: Loc.disjoint xs0 (x :: xs1)>>.
Proof.
  ii; ss. des; ss; clarify; eauto.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto.
Qed.


Lemma disjoint_concat l1 l2 x:
    Loc.disjoint (l1++[x]) l2 -> Loc.disjoint l1 l2.
Proof. unfold Loc.disjoint. i. eapply H; eauto. eapply in_or_app. left. eauto. Qed.

Lemma norepet_nth_notin l n m
      (NOREPET: Loc.norepet l)
      (NTH: list_nth_z l (Z.of_nat n) = Some m):
    Loc.notin m (firstn n l).
Proof.
  ginduction l; i; ss. inv NOREPET. destruct n.
  { inv NTH. ss. }
  Local Transparent list_nth_z. unfold list_nth_z in NTH. fold list_nth_z in NTH. Local Opaque list_nth_z. des_ifs.
  replace (Z.pred (Z.of_nat (Datatypes.S n))) with (Z.of_nat n) in *; try nia.
  rewrite firstn_cons. ss. esplits; et. eapply Loc.diff_sym. eapply Loc.in_notin_diff; et. eapply list_nth_z_in; et.
Qed.

Lemma disjoint_app_inv: forall l1 l2 l3,
    Loc.disjoint l1 (l2 ++ l3) -> Loc.disjoint l1 l2 /\ Loc.disjoint l1 l3.
Proof.
  i. ginduction l2; ii; ss.
  { esplits; et. ss. }
  split.
  - ii. ss. eapply H; et. ss. des; clarify; et. right. rewrite in_app_iff. et.
  - apply Loc.disjoint_cons_right in H. eapply IHl2; et.
Qed.

Lemma notin_regs_of_rpairs
      ofs tys ir fr ofs2 T
      (LT:ofs + 2 <= ofs2):
    Loc.notin (S Outgoing ofs T) (regs_of_rpairs (loc_arguments_64 tys ir fr ofs2)).
Proof.
  ginduction tys; ss; i.
  des_ifs; destruct T; econs; ss; et; try nia; eapply IHtys; try nia.
Qed.

Lemma loc_arguments_norepet_aux
      tys (ir fr ofs: Z) locs
      (LOCS: (regs_of_rpairs (loc_arguments_64 tys ir fr ofs)) = locs):
    (<<NOREP: Loc.norepet locs>>)
    /\ (<<NOTINIR: Loc.disjoint (map R (List.firstn ir.(Z.to_nat) int_param_regs)) locs>>)
    /\ (<<NOTINFR: Loc.disjoint (map R (List.firstn fr.(Z.to_nat) float_param_regs)) locs>>).
Proof.
  ginduction tys; ii; clarify.
  { esplits; ii; ss; econs. }
  assert(TTT: Loc.disjoint (map R int_param_regs) (map R float_param_regs)).
  { ii; ss. des; subst; ss. }
  destruct (classic (a = Tfloat \/ a = Tsingle)).
  { assert(loc_arguments_64 (a :: tys) ir fr ofs =
           match list_nth_z float_param_regs fr with
           | Some freg => One (R freg) :: loc_arguments_64 tys ir (fr + 1) ofs
           | None => One (S Outgoing ofs a) :: loc_arguments_64 tys ir fr (ofs + 2)
           end).
    { desH H; subst; ss. }
    rewrite H0. clear H H0. des_ifs.
    - specialize (IHtys ir (fr + 1) ofs _ eq_refl); des; ss.
      esplits; eauto.
      + econs; eauto. eapply Loc.disjoint_notin; try apply NOTINFR. eapply in_map.
        eapply list_nth_z_in. eapply list_nth_z_firstn; et.
      + eapply Loc_cons_right_disjoint; eauto.
        { clear - Heq TTT. eapply Loc.disjoint_notin; cycle 1.
          - eapply list_nth_z_in. eapply list_nth_z_map; et.
          - eapply Loc.disjoint_sym in TTT. rewrite map_firstn.
            erewrite <- firstn_skipn in TTT. eapply disjoint_app_inv in TTT. des; et.
        }
      + eapply Loc_cons_right_disjoint; eauto.
        { exploit list_nth_z_range; et. intro RANGE.
          destruct fr; try xomega; ss.
          exploit (firstn_S float_param_regs). i; desH H.
          - rewrite <- H0. replace (Pos.to_nat p + 1)%nat with (Pos.to_nat (p + 1)); try nia. eauto.
          - replace (Z.to_nat (Z.pos p + 1)) with (Pos.to_nat p + 1)%nat in *; cycle 1.
            { clear. rewrite Z2Nat.inj_add; try nia. ss. }
            rewrite H0 in NOTINFR. rewrite list_append_map in NOTINFR; ss. eapply disjoint_concat; et.
        }
        { clear - Heq. rewrite map_firstn. eapply norepet_nth_notin; try do 9 (econs; ss).
          eapply list_nth_z_map; et. rewrite Z2Nat.id; et. eapply list_nth_z_range; et.
        }
    - specialize (IHtys ir fr (ofs + 2) _ eq_refl); des; ss.
      esplits; eauto;
        try (eapply Loc_cons_right_disjoint; eauto;
             eapply Loc.disjoint_notin with (l1 := [_]); ss; et; ii; rewrite in_map_iff in *; ss; des; clarify).
      econs; eauto. eapply notin_regs_of_rpairs. nia.
  }
  { assert(a = Tint \/ a = Tlong \/ a = Tany32 \/ a = Tany64).
    { eapply not_or_and in H. des. destruct a; des_ifs; et. }
    assert(loc_arguments_64 (a :: tys) ir fr ofs =
           match list_nth_z int_param_regs ir with
           | Some ireg => One (R ireg) :: loc_arguments_64 tys (ir + 1) fr ofs
           | None => One (S Outgoing ofs a) :: loc_arguments_64 tys ir fr (ofs + 2)
           end).
    { desH H0; subst; ss. }
    rewrite H1. clear H H0 H1. des_ifs.
    - specialize (IHtys (ir + 1) fr ofs _ eq_refl); des; ss.
      esplits; eauto.
      + econs; eauto. eapply Loc.disjoint_notin; try apply NOTINIR. eapply in_map.
        eapply list_nth_z_in. eapply list_nth_z_firstn; et.
      + eapply Loc_cons_right_disjoint; eauto.
        { exploit list_nth_z_range; et. intro RANGE.
          destruct ir; try xomega; ss.
          exploit (firstn_S int_param_regs). i; desH H.
          - rewrite <- H0. replace (Pos.to_nat p + 1)%nat with (Pos.to_nat (p + 1)); try nia. eauto.
          - replace (Z.to_nat (Z.pos p + 1)) with (Pos.to_nat p + 1)%nat in *; cycle 1.
            { clear. rewrite Z2Nat.inj_add; try nia. ss. }
            rewrite H0 in NOTINIR. rewrite list_append_map in NOTINIR; ss. eapply disjoint_concat; et.
        }
        { clear - Heq. rewrite map_firstn. eapply norepet_nth_notin; try do 7 (econs; ss).
          eapply list_nth_z_map; et. rewrite Z2Nat.id; et. eapply list_nth_z_range; et.
        }
      + eapply Loc_cons_right_disjoint; eauto.
        { clear - Heq TTT. eapply Loc.disjoint_notin; cycle 1.
          - eapply list_nth_z_in. eapply list_nth_z_map; et.
          - rewrite map_firstn. erewrite <- firstn_skipn in TTT. eapply disjoint_app_inv in TTT. des; et.
        }
    - specialize (IHtys ir fr (ofs + 2) _ eq_refl); des; ss.
      esplits; eauto;
        try (eapply Loc_cons_right_disjoint; eauto;
             eapply Loc.disjoint_notin with (l1 := [_]); ss; et; ii; rewrite in_map_iff in *; ss; des; clarify).
      econs; eauto. eapply notin_regs_of_rpairs. nia.
  }
Qed.

Lemma loc_arguments_norepet: forall sg, Loc.norepet (regs_of_rpairs (loc_arguments sg)).
Proof.
  i. unfold loc_arguments. des_ifs.
  generalize (loc_arguments_norepet_aux (sig_args sg) 0 0 0). i. specialize (H _ eq_refl). des. ss.
Qed.

Lemma loc_norepet_app l0 l1
      (NOREPEAT: Loc.norepet (l0 ++ l1)):
    Loc.norepet l1.
Proof. induction l0; ss. inv NOREPEAT. eauto. Qed.

Lemma loc_notin_not_in mr locs:
  Loc.notin (R mr) locs <-> ~ In (R mr) locs.
Proof.
  induction locs; ss. split; ii; des; des_ifs.
  - eapply IHlocs; eauto.
  - eapply IHlocs; eauto.
  - apply not_or_and in H. des. split; auto. ii. clarify.
  - apply not_or_and in H. des. split; auto.
Qed.

Lemma in_one_in_rpair l (r: loc)
      (IN: In (One r) l):
    In r (regs_of_rpairs l).
Proof.
  induction l; ss; des; clarify.
  - destruct r; ss; eauto.
  - eapply in_or_app; eauto.
Qed.

Lemma loc_arguments_ofs_bounded
      sg lo
      (SZ: 0 <= lo /\ lo + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      ofs ty
      (IN: In (One (S Outgoing ofs ty)) (loc_arguments sg)):
  0 <= lo + 4 * ofs <= Ptrofs.max_unsigned.
Proof.
  hexploit loc_arguments_bounded.
  - instantiate (1:=sg). instantiate (1:=ty). instantiate (1:=ofs).
    revert ofs ty IN. induction (loc_arguments sg); ss; i.
    des; clarify; ss; eauto. eapply in_app_iff. right. eapply IHl; eauto.
  - i. split.
    + hexploit (loc_arguments_acceptable sg); eauto. intros ACCP. inv ACCP. lia.
    + destruct ty; ss; lia.
Qed.

  Lemma sig_args_length sg
  :
    Datatypes.length (sig_args sg) = Datatypes.length (loc_arguments sg).
Proof.
  unfold loc_arguments in *. des_ifs.
  generalize 0 at 1. generalize 0 at 1. generalize 0 at 1.
  induction (sig_args sg); ss; i. des_ifs; ss; f_equal; eauto.
Qed.

Lemma Val_has_type_list_length sg vs
      (TYP: Val.has_type_list vs (sig_args sg)):
    Datatypes.length vs = Datatypes.length (loc_arguments sg).
Proof.
  rewrite <- sig_args_length.
  revert vs TYP. induction (sig_args sg); ss; i; destruct vs; ss.
  des. f_equal; eauto.
Qed.

Ltac _locmap_tac :=
  try (first[rewrite Locmap.gss; ss; check_safe|rewrite Locmap.gso; ss]);
  try match goal with
      | [H: Loc.notin _ (_ :: _) |- _] => inv H
      | [H: Loc.norepet (_ :: _) |- _] => inv H
      | [ |- Loc.diff _ _] => by (eapply Loc.in_notin_diff; eauto)
      | [H: Loc.diff ?A ?B |- Loc.diff ?B ?A] => apply Loc.diff_sym; assumption
      | [H: R ?x <> R ?y |- _] =>
        tryif exists_prop (x <> y)
        then idtac
        else assert(x <> y) by (ii; clarify; ss)
      end;
  des_safe;
  idtac.

Local Opaque Loc.diff.
Ltac locmap_tac := repeat _locmap_tac.

Definition locmap_put (l: loc) (v: val) (ls: locset): locset :=
  fun loc => if Loc.eq loc l then v else ls loc.

Hint Unfold locmap_put.

Fixpoint fill_arguments (ls0: locset) (args: list val) (locs: list (rpair loc)): option locset :=
  match args, locs with
  | [], [] => Some ls0
  | arg :: args, loc :: locs =>
    match fill_arguments ls0 args locs with
    | Some ls1 =>
      match loc with
      | One loc => Some (locmap_put loc arg ls1)
      | Twolong hi lo => (* not used *)
        Some (Locmap.set lo arg.(Val.loword) (Locmap.set hi arg.(Val.hiword) ls1))
      end
    | None => None
    end
  | _, _ => None
  end.

Lemma fill_arguments_progress
      ls0 args locs
      (LEN: length args = length locs):
      exists ls1, <<LS: fill_arguments ls0 args locs =Some ls1>>.
Proof.
  ginduction args; ii; destruct locs; ss.
  - esplits; eauto.
  - exploit IHargs; eauto. i; des. rewrite LS. des_ifs; esplits; eauto.
Qed.

Lemma fill_arguments_spec
      vs sg locs ls0 ls1
      (LOCS: locs = loc_arguments sg)
      (FILL: fill_arguments ls0 vs locs = Some ls1):
    <<FILL: vs = map (fun p => Locmap.getpair p ls1) locs>> /\
    <<OUT: forall loc
             (* (NOTIN: Loc.notin loc (regs_of_rpairs locs)) *)
             (NOTIN: ~ In loc (regs_of_rpairs locs)),
      ls1 loc = ls0 loc>>.
Proof.
  subst.
  assert(ONES: forall lp, In lp (loc_arguments sg) -> is_one lp).
  { i. eapply loc_arguments_one; eauto. }
  assert(NOREPT: Loc.norepet (regs_of_rpairs (loc_arguments sg))).
  { apply loc_arguments_norepet. }
  abstr (loc_arguments sg) locs. clear_tac.
  ginduction locs; ii; destruct vs; ss.
  { clarify. }
  des_ifs_safe.
  exploit IHlocs; eauto. { eapply loc_norepet_app; eauto. } i; des.
  spc ONES. exploit ONES; eauto. i; des; ss. des_ifs; ss. clear_tac.
  split; ss.
  - red. f_equal; ss.
    + u. des_ifs.
    + clear - NOREPT. inv NOREPT. induction locs; ss.
      f_equal.
      * unfold locmap_put. destruct a; ss; des; apply_all_once Loc.diff_not_eq; des_ifs.
      * eapply loc_norepet_app in H2. eapply IHlocs; eauto. destruct a; inv H1; try inv H0; eauto.
  - ii; des. u. des_ifs.
    + contradict NOTIN. eauto.
    + erewrite OUT; eauto.
Qed.

Definition extcall_args_reg (mr: mreg) (sg: signature):
  {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
  {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
Proof.
  generalize (regs_of_rpairs (loc_arguments sg)). induction l.
  - ss. tauto.
  - ss. inv IHl; [tauto|]. destruct a.
    + destruct (mreg_eq r mr); [clarify; eauto|]. right. intros []; clarify.
    + right. intros []; clarify.
Qed.

Lemma arguments_loc sg sl delta ty
      (IN: In (S sl delta ty) (regs_of_rpairs (loc_arguments sg))):
    sl = Outgoing /\
    0 <= delta /\
    4 * delta + size_chunk (chunk_of_type ty) <= 4 * size_arguments sg.
Proof.
  generalize (loc_arguments_acceptable_2 _ _ IN). i. ss. des_ifs.
  set (loc_arguments_bounded _ _ _ IN).
  splits; eauto; [omega|]. unfold typesize in *. des_ifs; ss; lia.
Qed.

Lemma regs_of_rpair_In A (l: list (rpair A)):
    (forall r (IN: In (One r) l), In r (regs_of_rpairs l))
    /\ (forall r0 r1 (IN: In (Twolong r0 r1) l),
           In r0 (regs_of_rpairs l) /\ In r1 (regs_of_rpairs l)).
Proof.
  induction l; i; ss; split; i; des; clarify; ss; eauto.
  - eapply in_or_app. eauto.
  - split; eapply in_or_app; right; eapply (IHl0 _ _ IN).
Qed.
