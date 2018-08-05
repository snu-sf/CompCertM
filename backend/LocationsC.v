Require Import OrderedType.
Require Import CoqlibC.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Export Machregs.
(** newly added **)
Require Export Locations.
Require Import Conventions Integers Asmregs Memory.

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

Module DEPR.

Fixpoint fill_arguments (ls0: locset) (args: list val) (locs: list (rpair loc)): option locset :=
  match args, locs with
  | [], [] => Some ls0
  | arg :: args, loc :: locs =>
    match fill_arguments ls0 args locs with
    | Some ls1 =>
      match loc with
      | One loc => Some (Locmap.set loc arg ls1)
      | Twolong hi lo => Some (Locmap.set lo arg.(Val.loword) (Locmap.set hi arg.(Val.hiword) ls1))
      end
    | None => None
    end
  | _, _ => None
  end
.

Lemma fill_arguments_spec_slot
      (rs: regset) m sg vs ls
      sp
      (RSP: (rs RSP) = Vptr sp Ptrofs.zero true)
      (EXT: extcall_arguments rs m sg vs)
      (FILL: fill_arguments (Locmap.init Vundef) vs (loc_arguments sg) = Some ls)
      (SZBOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
  :
    (<<SLOT: forall
        ofs ty
      ,
        (<<INSIDE: forall (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
          (<<LOAD: Mem.load (chunk_of_type ty) m sp (4 * ofs) = Some (ls (S Outgoing ofs ty))>>)
            \/ (<<UNDEF: ls (S Outgoing ofs ty) = Vundef>>)>>)
        /\
        (<<OUTSIDE: forall (OUT: (* Loc.notin *) ~ In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
            (<<UNDEF: (ls (S Outgoing ofs ty)) = Vundef>>)>>)>>)
.
Proof.
  unfold extcall_arguments in *.
  assert(BDD: forall ofs ty,
        In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
        0 <= ofs /\ (typealign ty | ofs) /\
        ofs + typesize ty <= Ptrofs.max_unsigned/4).
  { i.
    generalize (loc_arguments_acceptable_2 sg (S Outgoing ofs ty)); eauto. intro ACCP. special ACCP; ss. des.
    esplits; ss; try xomega.
    etransitivity; eauto.
    generalize (loc_arguments_bounded sg); eauto.
    eapply mul_le_div; eauto.
  }
  assert(NOREPT: Loc.norepet (regs_of_rpairs (loc_arguments sg))).
  { apply loc_arguments_norepet. }
  abstr (loc_arguments sg) locs. clears sg. clear sg.
  ginduction locs; ii; ss.
  { split; ii; ss. destruct vs; ss. clarify. }
  split; ii; ss.
  {
    assert(OFS: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
    { specialize (BDD ofs ty).
      special BDD.
      { ss. }
      des_safe.
      generalize (typesize_pos ty). i.
      split; try xomega.
      assert((4 * (Ptrofs.max_unsigned/4)) <= Ptrofs.max_unsigned).
      { eapply Z_mult_div_ge. xomega. }
      etransitivity; eauto.
      eapply Z.mul_le_mono_pos_l with (p:=4) (n:=ofs); try xomega.
    }
    apply in_app_or in IN.
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { ii. eapply BDD. apply in_app_iff. right. ss. }
    { admit "easy". }
    i; des_safe. specialize (H ofs ty). des_safe.
    des; cycle 1.
    - special INSIDE; ss.
      des; ss; cycle 1.
      + right.
        des_ifs; ss; locmap_tac.
      + left.
        des_ifs; ss; locmap_tac.
    - inv H1; ss.
      + des; ss; clarify; locmap_tac.
        inv H. left.
        unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
        rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
        rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
      + destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
        * rewrite e in *. right.
          des; ss; clarify; locmap_tac.
          admit "easy".
          admit "easy".
        * rewrite Val_hiword_spec in *; ss.
          rewrite Val_loword_spec in *; ss.
          clarify.
          des; ss; clarify; locmap_tac.
          { left.
            inv H. ss.
            unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
            rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
            rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
          }
          { left.
            inv H0. ss.
            unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
            rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
            rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
          }
  }
  {
    destruct vs; ss. inv EXT.
    des_ifs_safe; ss.
    hexploit IHlocs; eauto.
    { ii. eapply BDD. apply in_app_iff. right. ss. }
    { admit "easy". }
    i; des. specialize (H ofs ty). des.
    des_ifs; ss.
    - rename r into rrr.
      apply not_or_and in OUT. des.
      destruct (classic (Loc.diff rrr (S Outgoing ofs ty))).
      + locmap_tac. erewrite OUTSIDE; eauto.
      + unfold Locmap.set. des_ifs.
    - apply not_or_and in OUT. des.
      apply not_or_and in OUT0. des.
      destruct (classic (Loc.diff rlo (S Outgoing ofs ty))).
      {
        destruct (classic (Loc.diff rhi (S Outgoing ofs ty))).
        { locmap_tac. erewrite OUTSIDE; eauto. }
        unfold Locmap.set. des_ifs.
      }
      unfold Locmap.set. des_ifs.
  }
Qed.

Lemma fill_arguments_spec_reg
      (rs: regset) m sg vs ls
      sp
      (RSP: (rs RSP) = Vptr sp Ptrofs.zero true)
      (EXT: extcall_arguments rs m sg vs)
      (FILL: fill_arguments (Locmap.init Vundef) vs (loc_arguments sg) = Some ls)
  :
    (<<REG: forall
        r
      ,
        (<<INSIDE: forall (IN: In (R r) (regs_of_rpairs (loc_arguments sg))),
            <<EQ: ls (R r) = rs (preg_of r)>> \/ <<UNDEF: ls (R r) = Vundef>>>>)
        /\
        (<<OUTSIDE: forall (OUT: ~ In (R r) (regs_of_rpairs (loc_arguments sg))),
            <<UNDEF: ls (R r) = Vundef>>>>)>>)
.
Proof.
  unfold extcall_arguments in *.
  assert(NOREPT: Loc.norepet (regs_of_rpairs (loc_arguments sg))).
  { apply loc_arguments_norepet. }
  abstr (loc_arguments sg) locs. clears sg. clear sg.
  ginduction locs; ii; ss.
  { split; ii; ss. destruct vs; ss. clarify. }
  split; ii; ss.
  {
    apply in_app_or in IN.
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { admit "easy". }
    i; des_safe. specialize (H r). des_safe.
    inv H1; ss; clarify.
    - inv H; des; ss; clarify.
      + locmap_tac; eauto.
      + destruct (mreg_eq r0 r); ss; clarify; locmap_tac; eauto.
      + locmap_tac; eauto.
    - destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
      + rewrite e in *. ss.
        des; ss; clarify; inv H; ss; locmap_tac; eauto.
      + rewrite Val_loword_spec in *; ss.
        rewrite Val_hiword_spec in *; ss.
        des; ss; clarify; inv H; inv H0; ss; locmap_tac; eauto.
  }
  {
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { admit "easy". }
    i; des_safe. specialize (H r). des_safe.
    inv H1; ss; clarify.
    - apply not_or_and in OUT. des.
      inv H; des; ss; clarify; locmap_tac; eauto.
    - apply not_or_and in OUT. des.
      apply not_or_and in OUT0. des.
      destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
      + rewrite e in *. ss.
        rewrite <- OUTSIDE; ss.
        des; ss; clarify; inv H; ss; locmap_tac; eauto.
        * destruct lo; locmap_tac.
        * destruct lo; locmap_tac.
      + rewrite Val_loword_spec in *; ss.
        rewrite Val_hiword_spec in *; ss.
        rewrite <- OUTSIDE; ss.
        des; ss; clarify; inv H; inv H0; ss; try (by locmap_tac; eauto).
        destruct (classic (r0 = r)); ss; clarify; locmap_tac.
  }
Qed.

End DEPR.


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

