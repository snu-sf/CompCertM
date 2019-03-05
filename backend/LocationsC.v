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
      (NOTIN: ~ In (R r) locs)
  :
    <<NOTIN: Loc.notin (R r) locs>>
.
Proof. red. ginduction locs; ii; ss. esplits; eauto. destruct a; ss. ii; clarify. eauto. Qed.

Lemma typealign_divide_8
      ty
  :
    <<DIV: (4 * typealign ty | 8)>>
.
Proof.
  red. change 8 with (4 * 2).
  eapply Z.mul_divide_mono_l.
  destruct ty; ss; try reflexivity; try apply Z.divide_1_l.
Qed.

Definition locset := Locmap.t.

Local Opaque Z.mul Z.add.
Local Opaque list_nth_z.

Definition is_one A (ap: rpair A): bool :=
  match ap with
  | One _ => true
  | Twolong _ _ => false
  end
.

(* Note: this is hacking for 64bit. It just simplifies proof, we don't exploit anything weird *)
Lemma loc_arguments_one
      sg
  :
    forall lp (IN: In lp (loc_arguments sg)), <<ONE: is_one lp>>
.
Proof.
  destruct sg; ss. unfold loc_arguments in *. ss. des_ifs. clear_tac.
  generalize 0 at 1 as ir. generalize 0 at 1 as fr. generalize 0 at 1 as ofs.
  ginduction sig_args; ii; ss.
  - des_ifs; repeat (des; ss; clarify); eapply IHsig_args; eauto.
Qed.

Lemma loc_result_one
      sg
  :
    is_one (loc_result sg)
.
Proof.
  unfold loc_result. des_ifs. unfold loc_result_64. des_ifs.
Qed.

Lemma chunk_type_chunk
      ty
  :
    (type_of_chunk (chunk_of_type ty)) = ty
.
Proof.
  destruct ty; ss.
Qed.

Print Loc.notin.
Print Loc.norepet.
Print Loc.no_overlap.

Lemma Loc_cons_right_disjoint
      xs0 xs1
      (DISJ: Loc.disjoint xs0 xs1)
      x
      (NOTIN: Loc.notin x xs0)
  :
    <<DISJ: Loc.disjoint xs0 (x :: xs1)>>
.
Proof.
  ii; ss.
  des; ss; clarify; eauto.
  apply Loc.diff_sym.
  eapply Loc.in_notin_diff; eauto.
Qed.

Lemma loc_arguments_norepet_aux
      tys (ir fr ofs: Z)
      locs
      (LOCS: (regs_of_rpairs (loc_arguments_64 tys ir fr ofs)) = locs)
  :
    (<<NOREP: Loc.norepet locs>>)
    /\
    (<<NOTINIR: Loc.disjoint (map R (List.firstn ir.(Z.to_nat) int_param_regs)) locs>>)
    /\
    (<<NOTINFR: Loc.disjoint (map R (List.firstn fr.(Z.to_nat) float_param_regs)) locs>>)
.
Proof.
  ginduction tys; ii; ss; clarify.
  { esplits; eauto.
    - econs; eauto.
    - ii; ss.
    - ii; ss.
  }
  des_ifs; ss.
  -
    (* rewrite Z.add_comm in *; ss. *)
    (* specialize (IHtys (1 + ir)%nat fr ofs _ eq_refl); des; ss. *)
    specialize (IHtys (ir + 1) fr ofs _ eq_refl); des; ss.
    esplits; eauto.
    + econs; eauto.
      eapply Loc.disjoint_notin; try apply NOTINIR.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      { admit "easy". }
      { admit "easy". }
    + eapply Loc_cons_right_disjoint; eauto.
      { admit "easy". }
  - specialize (IHtys ir fr (ofs + 2) _ eq_refl); des; ss.
    esplits; eauto.
    + econs; eauto.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      admit "easy".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
Qed.

Lemma loc_arguments_norepet
      sg
  :
    Loc.norepet (regs_of_rpairs (loc_arguments sg))
.
Proof.
  unfold loc_arguments. des_ifs.
  generalize (loc_arguments_norepet_aux (sig_args sg) 0 0 0). i. specialize (H _ eq_refl). des.
  ss.
Qed.

Lemma loc_norepet_app l0 l1
      (NOREPEAT: Loc.norepet (l0 ++ l1))
  :
    Loc.norepet l1.
Proof.
  induction l0; ss.
  inv NOREPEAT. eauto.
Qed.

Lemma loc_notin_not_in mr locs
  :
      Loc.notin (R mr) locs <-> ~ In (R mr) locs.
Proof.
  induction locs; ss.
  split; ii; des; des_ifs.
  - eapply IHlocs; eauto.
  - eapply IHlocs; eauto.
  - apply not_or_and in H. des. split; auto. ii. clarify.
  - apply not_or_and in H. des. split; auto.
Qed.

Lemma in_one_in_rpair l (r: loc)
      (IN: In (One r) l)
  :
    In r (regs_of_rpairs l).
Proof.
  induction l; ss; des; clarify.
  - destruct r; ss; eauto.
  - eapply in_or_app; eauto.
Qed.

Lemma loc_arguments_ofs_bounded
      sg
      (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      ofs ty
      (IN: In (One (S Outgoing ofs ty)) (loc_arguments sg))
  :
    0 <= 4 * ofs <= Ptrofs.max_unsigned.
Proof.
  hexploit loc_arguments_bounded.
  - instantiate (1:=sg). instantiate (1:=ty). instantiate (1:=ofs).
    revert ofs ty IN.
    induction (loc_arguments sg); ss; i.
    des; clarify; ss; eauto.
    eapply in_app_iff. right. eapply IHl; eauto.
  - i. split.
    + hexploit (loc_arguments_acceptable sg); eauto.
      intros ACCP. inv ACCP. lia.
    + destruct ty; ss; lia.
Qed.

Lemma sig_args_length sg
  :
    Datatypes.length (sig_args sg) = Datatypes.length (loc_arguments sg).
Proof.
  unfold loc_arguments in *. des_ifs.
  generalize 0 at 1.
  generalize 0 at 1.
  generalize 0 at 1.
  induction (sig_args sg); ss; i.
  des_ifs; ss; f_equal; eauto.
Qed.

Lemma Val_has_type_list_length sg vs
      (TYP: Val.has_type_list vs (sig_args sg))
  :
    Datatypes.length vs = Datatypes.length (loc_arguments sg).
Proof.
  rewrite <- sig_args_length.
  revert vs TYP. induction (sig_args sg); ss; i; destruct vs; ss.
  des.
  f_equal; eauto.
Qed.

Lemma Val_hiword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.hiword (Val.longofwords vhi vlo)) = vhi>>
.
Proof.
  u.
  unfold Val.longofwords, Val.hiword. des_ifs; ss; eauto.
  rewrite Int64.hi_ofwords. ss.
Qed.

Lemma Val_loword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.loword (Val.longofwords vhi vlo)) = vlo>>
.
Proof.
  u.
  unfold Val.longofwords, Val.loword. des_ifs; ss; eauto.
  rewrite Int64.lo_ofwords. ss.
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
  idtac
.
Local Opaque Loc.diff.
Ltac locmap_tac := repeat _locmap_tac.

Lemma mul_le_div
      a b
      (LE: 4 * a <= b)
  :
    <<LE: a <= b / 4>>
.
Proof.
  red.
  assert(4 * a / 4 = a).
  { rewrite Z.mul_comm.
    SearchAbout(_ * _ / _).
    rewrite Z.div_mul; ss.
  }
  rewrite <- H.
  eapply Z_div_le; eauto.
  xomega.
Qed.

Definition locmap_put (l: loc) (v: val) (ls: locset): locset :=
  fun loc =>
    if Loc.eq loc l
    then v
    else ls loc
.

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
  end
.

Lemma fill_arguments_progress
      ls0 args locs
      (LEN: length args = length locs)
  :
      exists ls1, <<LS: fill_arguments ls0 args locs =Some ls1>>
.
Proof.
  ginduction args; ii; destruct locs; ss.
  - esplits; eauto.
  - exploit IHargs; eauto. i; des. rewrite LS. des_ifs; esplits; eauto.
Qed.

Lemma fill_arguments_spec
      vs sg locs ls0 ls1
      (LOCS: locs = loc_arguments sg)
      (FILL: fill_arguments ls0 vs locs = Some ls1)
  :
    <<FILL: vs = map (fun p => Locmap.getpair p ls1) locs>> /\
    <<OUT: forall
              loc
              (* (NOTIN: Loc.notin loc (regs_of_rpairs locs)) *)
              (NOTIN: ~ In loc (regs_of_rpairs locs))
            ,
              ls1 loc = ls0 loc>>
.
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
  exploit IHlocs; eauto. { admit "norept app - ez". } i; des.
  spc ONES. exploit ONES; eauto. i; des; ss. des_ifs; ss. clear_tac.
  split; ss.
  - red. f_equal; ss.
    + u. des_ifs.
    + admit "this should hold".
  - ii; des.
    u. des_ifs.
    + contradict NOTIN. eauto.
    + erewrite OUT; eauto.
Qed.
