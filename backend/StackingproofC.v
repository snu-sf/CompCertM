Require Import CoqlibC Errors.
Require Import IntegersC ASTC Linking.
Require Import ValuesC MemoryC SeparationC Events GlobalenvsC Smallstep.
Require Import LTL Op LocationsC LinearC MachC.
Require Import Bounds ConventionsC StacklayoutC LineartypingC.
Require Import Stacking.

Local Open Scope string_scope.
Local Open Scope sep_scope.

(* newly added *)
Require Export Stackingproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSemExcl.
Require Import Conventions1C.
Require SimMemInjC.
Require Import AxiomsC.
Require SoundTop.
Require Import StoreArguments.
Require Import ModSemProps.
Require Import LiftDummy.
Require Import JunkBlock.

Set Implicit Arguments.

Local Opaque Z.add Z.mul Z.div.
Local Opaque sepconj.
Local Opaque function_bounds.
Local Opaque make_env.









Lemma sim_skenv_inj_globalenv_inject
      skenv_proj_src skenv_proj_tgt sm_arg (prog: Linear.program)
      (SIMSKE: SimMemInjC.sim_skenv_inj sm_arg tt skenv_proj_src skenv_proj_tgt)
      m_tgt0
      (NB: Ple (Genv.genv_next skenv_proj_src) (Mem.nextblock m_tgt0))
  :
    m_tgt0 |= globalenv_inject (SkEnv.revive skenv_proj_src prog) (SimMemInj.inj sm_arg)
.
Proof.
  ss.
  inv SIMSKE. inv INJECT.
  esplits; et.
  - econs; et.
    + ii. exploit Genv.genv_symb_range; eauto.
    + ii. uge0. des_ifs. exploit Genv.genv_defs_range; eauto.
    + ii. uge0. des_ifs. exploit Genv.genv_defs_range; eauto.
Qed.




Ltac sep_simpl_tac :=
  unfold NW in *;
  repeat (try rewrite sep_assoc in *;
          try rewrite sep_pure in *;
          try rewrite stack_contents_nil_left_false in *; try assumption;
          try rewrite stack_contents_nil_right_false in *; try assumption;
          try match goal with
              | [H: _ |= pure False |- _] => simpl in H; inv H
              | [H: _ |= _ ** pure False |- _] => apply sep_proj2 in H
              | [H: _ |= _ ** pure False ** _ |- _] => apply sep_pick2 in H
              end;
          idtac
         )
.

Notation "'stack_contents'" := (stack_contents_args) (only parsing).

Section STACKINGEXTRA.

Lemma match_stacks_sp_valid
      se tse ge j cs cs' sg sm0 sp'
      (STKS: match_stacks se tse ge j cs cs' sg sm0)
      (SP: parent_sp cs' = Vptr sp' Ptrofs.zero)
:
  <<SPVALID: sm0.(SimMemInj.tgt).(Mem.valid_block) sp' /\
             Ple sm0.(SimMemInj.tgt_parent_nb) sp' /\
             forall i, ~ sm0.(SimMemInj.tgt_external) sp' i>>
.
Proof.
  inv STKS; des_safe; ss; clarify; inv MAINARGS; esplits; eauto.
Qed.

Lemma match_stacks_sp_ofs:
  forall j se tse ge cs cs' sg sm,
  match_stacks se tse ge j cs cs' sg sm ->
  exists sp, (parent_sp cs') = Vptr sp Ptrofs.zero.
Proof.
  induction 1; ii; ss; esplits; eauto.
Qed.

Local Opaque Z.add Z.mul make_env function_bounds.
Lemma arguments_private
      sp_tgt spdelta
      m_src m_tgt
      stk_src stk_tgt
      F
      sg
      se tse ge sm
      (MATCH: m_tgt |= stack_contents F stk_src stk_tgt ** minjection F m_src)
      (STACKS: match_stacks se tse ge F stk_src stk_tgt sg sm)
      (SP: parent_sp stk_tgt = Vptr sp_tgt spdelta)
  :
    <<_ : forall ofs (OFS: 0 <= ofs < 4 * size_arguments sg),
    (<<PRIV: loc_out_of_reach F m_src sp_tgt (spdelta.(Ptrofs.unsigned) + ofs)>>)>>
.
Proof.
  ii.
  eapply separation_private; eauto.
  destruct stk_tgt; ss. { inv STACKS. inv MAINARGS. } des_ifs. destruct stk_src; ss.
  { sep_simpl_tac. des; ss. }
  des_ifs_safe.
  des_ifs; sep_simpl_tac.
  - unfold dummy_frame_contents in *. inv MATCH. ss.
    inv STACKS; ss; cycle 1.
    { inv STK; ss. }
    des; cycle 1.
    { apply tailcall_size in LE. xomega. }
    clarify.
  - Local Transparent sepconj. cbn.
    left. left. right. left.
    split; [ss|].
    Local Opaque sepconj.
    apply sep_pick1 in MATCH. unfold frame_contents in *.
    unfold fe_ofs_arg. rewrite ! Z.add_0_l in *.
    inv STACKS; ss. des_ifs_safe. des.
    rewrite Ptrofs.unsigned_zero in *.
    esplits; eauto; try xomega.
Qed.

Lemma arguments_perm
      se tse ge sm
      sp_tgt spdelta
      m_src m_tgt
      stk_src stk_tgt
      F
      sg
      (MATCH: m_tgt |= stack_contents F stk_src stk_tgt ** minjection F m_src)
      (STACKS: match_stacks se tse ge F stk_src stk_tgt sg sm)
      (SP: parent_sp stk_tgt = Vptr sp_tgt spdelta)
  :
    <<_ : forall ofs (OFS: 0 <= ofs < 4 *size_arguments sg),
    (<<PERM: Mem.perm m_tgt sp_tgt (spdelta.(Ptrofs.unsigned) + ofs) Cur Freeable>>)>>
.
Proof.
  ii.
  destruct stk_tgt; ss. { inv STACKS. inv MAINARGS. } des_ifs. destruct stk_src; ss.
  { sep_simpl_tac. des; ss. }
  des_ifs_safe.
  des_ifs; ss; sep_simpl_tac.
  - unfold dummy_frame_contents in *. inv MATCH. ss.
    inv STACKS; ss; cycle 1.
    { inv STK; ss. }
    des; cycle 1.
    { apply tailcall_size in LE. xomega. }
    clarify. eapply H4; eauto.
  - apply sep_pick1 in MATCH. unfold frame_contents in *.
    ss. des_ifs. des.
    apply sep_pick2 in MATCH.
    unfold fe_ofs_arg in *. inv MATCH. des; ss. eapply H2; eauto.
    inv STACKS; ss.
    rewrite ! Z.add_0_l in *. xomega.
Qed.

Lemma contains_locations_range
      j sp lo hi k rs
  :
    massert_imp (contains_locations j sp lo hi k rs)
                (range sp lo (lo + (4 * hi)))
.
Proof.
  rr. ss. esplits; et.
  ii. des. esplits; et.
  i. eapply Mem.perm_cur. eapply Mem.perm_implies with (p1 := Freeable); eauto with mem.
Qed.

Lemma contains_locations_range_2
      m j sp pos bound slot ls
      (SEP: m |= contains_locations j sp pos bound slot ls)
  :
    <<RANEG: m |= range sp pos (pos + 4 * bound)>>
.
Proof. ss. des. esplits; eauto. ii. eauto with mem. Qed.

Lemma agree_callee_save_regs_undef_outgoing_slots
      ls0 ls1
      (AG: agree_callee_save_regs ls0 ls1)
  :
    <<AG: agree_callee_save_regs ls0 ls1.(undef_outgoing_slots)>>
.
Proof.
  ii. unfold undef_outgoing_slots. apply AG; ss.
Qed.

Program Definition freed_contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos (* /\ pos + 4 * bound <= Ptrofs.modulus *)
    /\ Mem.valid_block m sp
    (* Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\ *)
    (* forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (Locations.typealign ty | ofs) -> *)
    (* exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v *)
    (*        /\ Val.inject j (ls (S sl ofs ty)) v *)
  ;
  m_footprint :=
    brange sp pos (pos + 4 * bound)
    (* fun b ofs => *)
    (* b = sp /\ pos <= ofs < pos + 4 * bound *)
|}.
Next Obligation.
  esplits; et.
  eapply Mem.valid_block_unchanged_on; et.
Qed.
Next Obligation.
  rr in H0. des. clarify.
Qed.

Program Definition contains_locations_tl (j: meminj) (sp: block) (pos from bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    from <= bound /\
    pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m sp (pos + 4 * from) (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, from <= ofs -> ofs + typesize ty <= bound -> (Locations.typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint :=
    (* fun b ofs => *)
    (* b = sp /\ pos + 4 * from <= ofs < pos + 4 * bound *)
    brange sp (pos + 4 * from) (pos + 4 * bound)
|}.
Next Obligation.
  esplits; et.
  { ii. eapply Mem.perm_unchanged_on; et. }
  ii. exploit H3; et. i; des. esplits; et.
  eapply Mem.load_unchanged_on; et.
  ii. des. esplits; et; try xomega. rewrite typesize_chunk in *. rr. esplits; et; xomega.
Qed.
Next Obligation.
  r in H0. des. clarify.
  exploit H2; et. i. eapply Mem.perm_valid_block; et.
Qed.

Lemma contains_locations_split
      j sp pos lo hi sl ls
      (RANGE: pos <= lo <= hi)
      (DIV: (2 | lo)%Z)
  :
    massert_imp (contains_locations j sp pos hi sl ls)
                (contains_locations j sp pos lo sl ls ** contains_locations j sp (pos + 4 * lo) (hi - lo) sl ls)
.
Proof.
  Local Transparent sepconj.
  (* unfold contains_locations. *)
  econs; ss.
  - ii. des.
    esplits; eauto with xomega; ss.
    { ii. eapply H2; try xomega; ss. }
    { eapply Z.divide_add_r; et. change 8 with (4 * 2).
      apply Z.mul_divide_mono_l. ss.
    }
    { ii. eapply H2; try xomega; ss. }
    { ii. replace (pos + 4 * lo + 4 * ofs) with (pos + 4 * (lo + ofs)) by xomega.
      specialize (H3 (lo + ofs)).
Abort.

Lemma contains_locations_split
      j sp pos lo hi sl ls
      (RANGE: 0 <= lo <= hi)
  :
    massert_imp (contains_locations j sp pos hi sl ls)
                (contains_locations j sp pos lo sl ls ** contains_locations_tl j sp pos lo hi sl ls)
.
Proof.
  Local Transparent sepconj.
  (* unfold contains_locations. *)
  -
    econs; ss.
    + ii. des.
      esplits; eauto with xomega; ss.
      { ii. eauto with xomega mem. }
      { ii. eauto with xomega mem. }
      unfold disjoint_footprint.
      ss. ii. des. clarify. rr in H5. des. clarify. xomega.
    + ii. u in H. des; clarify; esplits; et; try xomega.
Qed.

Lemma contains_locations_split_m_footprint
      j sp pos lo hi sl ls
      (RANGE: 0 <= lo <= hi)
  :
    (contains_locations j sp pos hi sl ls).(m_footprint)
    =
    (contains_locations j sp pos lo sl ls ** contains_locations_tl j sp pos lo hi sl ls).(m_footprint)
.
Proof.
  apply func_ext2.
  i. apply prop_ext.
  split; i.
  - ss. des. clarify. destruct (classic (x1 < pos + 4 * lo)).
    + left. esplits; et.
    + right. rr. split; et. xomega.
  - eapply contains_locations_split; et.
Qed.

Lemma contains_locations_merge
      j sp pos lo hi sl ls
      (RANGE: 0 <= lo <= hi)
  :
    massert_imp (contains_locations j sp pos lo sl ls ** contains_locations_tl j sp pos lo hi sl ls)
                (contains_locations j sp pos hi sl ls)
.
Proof.
  -
    econs; ss.
    + ii. des.
      esplits; eauto with xomega; ss.
      { ii.
        destruct (classic (ofs < pos + 4 * lo)).
        - eauto with xomega mem.
        - eauto with xomega mem. }
      { ii.
        destruct (classic (ofs + typesize ty <= lo)); eauto.
        - eapply H4; eauto. try xomega.
Abort.

Lemma free_freed_contains_locations
      j sp pos sz sl ls m0 m1 CTX
      (SEP: m0 |= contains_locations j sp pos sz sl ls ** CTX)
      (FREE: Mem.free m0 sp pos (pos + 4 * sz) = Some m1)
      (VALID: Mem.valid_block m0 sp)
  :
    <<SEP: m1 |= freed_contains_locations j sp pos sz sl ls ** CTX>>
.
Proof.
  eapply sepconj_isolated_mutation_revisited; et.
  - exploit Mem.free_unchanged_on; et. s.
    ii. eapply H0; et.
  - ss. des. esplits; et. eapply Mem.valid_block_free_1; et.
Qed.

Lemma brange_split
      blk lo mid hi
      (RANGE: lo <= mid < hi)
  :
    brange blk lo hi = brange blk lo mid \2/ brange blk mid hi
.
Proof.
  apply func_ext1; i.
  apply func_ext1; i.
  apply prop_ext.
  unfold brange.
  split.
  - ii. des; clarify.
    destruct (classic (x1 < mid)).
    + left. esplits; et.
    + right. esplits; et. xomega.
  - ii. des; clarify; esplits; et; xomega.
Qed.

Lemma unfree_freed_range
      sp m0 m1 lo mid hi
      (SEP: m0 |= freed_range sp lo mid ** range sp mid hi)
      (UNFREE: Mem_unfree m0 sp lo mid = Some m1)
  :
    <<SEP: m1 |= range sp lo hi>>
.
Proof.
  ss. des. esplits; et. ii.
  hexploit Mem_unfree_unchanged_on; et. intro UNCH; des.
  destruct (classic (i < mid)).
  - eapply Mem_unfree_perm; et.
  - eapply Mem.perm_unchanged_on; et.
    + u. ii. des. xomega.
    + eapply SEP3; et. xomega.
Qed.

Lemma unfree_freed_contains_locations
      j sp pos sz bound ls m0 m1
      CTX
      (SEP: m0 |= freed_contains_locations j sp pos sz Outgoing ls
               ** contains_locations_tl j sp pos sz bound Outgoing ls
               ** CTX)
      (FREE: Mem_unfree m0 sp pos (pos + 4 * sz) = Some m1)
      (BOUND: sz <= bound)
  :
    <<SEP: m1 |= contains_locations j sp pos bound Outgoing ls.(undef_outgoing_slots) ** CTX>>
.
Proof.
  rewrite <- sep_assoc in SEP.
  hexploit Mem_unfree_perm; et. intro PERM; des.
  exploit Mem_unfree_unchanged_on; et. intro UNCH; des.
  eapply sepconj_isolated_mutation_revisited with (CTX := CTX); try apply SEP; et.
  { clear SEP.
    ss.
    ii. left. ss.
  }
  {
    ss. des.
    esplits; et.
    - ii.
      destruct (classic (ofs < pos + 4 * sz)).
      + eapply PERM; try xomega.
      + eapply Mem.perm_unchanged_on; et.
        { u. ii. des; clarify. }
        eapply SEP5; try xomega.
    - ii.
      destruct (classic (sz <= ofs)).
      + exploit SEP6; et. i; des.
        esplits; et.
        eapply Mem.load_unchanged_on; et.
        u. ii. des. xomega.
      + assert(BDD: ofs < sz) by xomega.
        assert(LD: exists v, Mem.load (chunk_of_type ty) m1 sp (pos + 4 * ofs) = Some v).
        { exploit Mem.valid_access_load; et. rr. esplits; et.
          - eapply Mem.range_perm_implies with (p1 := Freeable); eauto with mem.
            ii.
            destruct (classic (ofs0 < pos + 4 * sz)).
            + eapply PERM; et. xomega.
            + eapply Mem.perm_unchanged_on; et.
              { u. ii; des. xomega. }
              eapply SEP5; et.
              rewrite typesize_chunk in *. split; try xomega.
          - rewrite align_type_chunk.
            eapply Z.divide_add_r.
            + etrans; et. eapply typealign_divide_8.
            + apply Z.mul_divide_mono_l. ss.
        }
        des.
        esplits; et.
  }
  {
    ss. des.
    ii. des; clarify.
    destruct (classic (x1 < pos + 4 * sz)).
    - left. rr. esplits; et.
    - right. rr. esplits; et. xomega.
  }
Qed.

Definition frame_contents_1_at_external f (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) sg :=
  let b := function_bounds f in
  let fe := make_env b in
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 (* ** pure True *)
 (* ** freed_range sp fe_ofs_arg (4 * size_arguments sg) *)
 ** freed_contains_locations j sp fe_ofs_arg (size_arguments sg) Outgoing ls
 ** contains_locations_tl j sp fe_ofs_arg (size_arguments sg) (bound_outgoing b) Outgoing ls
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents_at_external f (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) sg :=
  let b := function_bounds f in
  let fe := make_env b in
  mconj (frame_contents_1_at_external f j sp ls ls0 parent retaddr sg)
        ((* range sp fe_ofs_arg fe.(fe_stack_data) ** *)
         (freed_range sp fe_ofs_arg (4 * (size_arguments sg)) **
         range sp (4 * (size_arguments sg)) fe.(fe_stack_data)) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

Fixpoint stack_contents_at_external (j: meminj) (cs: list Linear.stackframe) (cs': list Mach.stackframe) sg : massert :=
  match cs, cs' with
  | [Linear.Stackframe f _ ls _], [Mach.Stackframe fb (Vptr sp' spofs) ra _] =>
    (freed_range sp' spofs.(Ptrofs.unsigned) (4 * (size_arguments sg)))
      ** range sp' (4 * (size_arguments sg)) (4 * (size_arguments f.(Linear.fn_sig)))
    (* pure True *)
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' spofs) ra c' :: cs' =>
      frame_contents_at_external f j sp' ls (parent_locset cs) (parent_sp cs') (parent_ra cs') sg
      ** stack_contents j cs cs'
  | _, _ => pure False
  end.

Lemma stack_contents_at_external_footprint_split
      j cs cs'
      f sp ls c fb sp' spofs ra c' sg
      (NONNIL: cs <> [])
  :
    m_footprint (stack_contents_at_external j
                                            ((Linear.Stackframe f sp ls c) :: cs)
                                            ((Mach.Stackframe fb (Vptr sp' spofs) ra c') :: cs') sg)
    =
    (m_footprint (frame_contents_at_external f j sp' ls (parent_locset cs) (parent_sp cs') (parent_ra cs') sg)
                 \2/
                 m_footprint (stack_contents j cs cs'))
.
Proof.
  ii; ss. des_ifs.
Qed.

Lemma stackframes_after_external_footprint
      j cs cs'
  :
    (stack_contents j cs cs').(m_footprint) =
    (stack_contents j cs.(stackframes_after_external) cs').(m_footprint)
.
Proof.
  apply func_ext1; i.
  apply func_ext1; i.
  apply prop_ext.
  split; i.
  - destruct cs; ss. des_ifs.
  - destruct cs; ss. des_ifs.
Qed.

Lemma frame_contents_1_at_external_m_footprint
      f j sp rs rs0 sp2 retaddr0
      sg
      (SZ: 0 <= size_arguments sg <= bound_outgoing (function_bounds f))
  :
    (frame_contents_1 f j sp rs rs0 sp2 retaddr0).(m_footprint)
    =
    (frame_contents_1_at_external f j sp rs rs0 sp2 retaddr0 sg).(m_footprint)
.
Proof.
  apply func_ext2. i. apply prop_ext.
  (* - ii. ss. des. esplits; eauto. *)
  unfold frame_contents_1 in *.
  unfold frame_contents_1_at_external in *.
  split; i.
  - Local Opaque sepconj.
    eapply sepconj_footprint_le; swap 2 3; et.
    rewrite <- sep_assoc_footprint with
        (P := freed_contains_locations j sp fe_ofs_arg (size_arguments sg) Outgoing rs).
    eapply sepconj_footprint_le; swap 2 3; et.
    erewrite contains_locations_split_m_footprint; et. refl.
  - eapply sepconj_footprint_le; swap 2 3; et.
    rewrite <- sep_assoc_footprint with
        (P := freed_contains_locations j sp fe_ofs_arg (size_arguments sg) Outgoing rs).
    eapply sepconj_footprint_le; swap 2 3; et.
    erewrite contains_locations_split_m_footprint; et. refl.
Qed.

Lemma frame_contents_at_external_m_footprint
      f j sp rs rs0 sp2 retaddr0 sg
      (SZ: 0 <= size_arguments sg <= bound_outgoing (function_bounds f))
      (BOUND: 4 * bound_outgoing (function_bounds f) <= fe_stack_data (make_env (function_bounds f)))
  :
    (frame_contents f j sp rs rs0 sp2 retaddr0).(m_footprint)
    =
    (frame_contents_at_external f j sp rs rs0 sp2 retaddr0 sg).(m_footprint)
.
Proof.
  unfold frame_contents, frame_contents_at_external in *.
  unfold fe_ofs_arg.
  ss.
  rewrite <- frame_contents_1_at_external_m_footprint; ss.
  apply func_ext2. i. apply prop_ext.
  split; i; des; et.
  - right.
    eapply sepconj_footprint_le; try apply H; et. clear H.
    Local Transparent sepconj.
    ss. ii. des. clarify.
    destruct (classic (4 * size_arguments sg <= x3)).
    + right. esplits; et.
    + left. rr. esplits; et. xomega.
  - right.
    eapply sepconj_footprint_le; try apply H; et. clear H.
    ss. ii. unfold brange in *. des; clarify; esplits; et; try xomega.
Qed.

Lemma stack_contents_at_external_m_footprint
      se tse tge sm0 stack cs' sg j F
      (STACKS: match_stacks se tse tge F stack cs' sg sm0)
  :
    <<LE: (stack_contents_at_external j stack cs' sg).(m_footprint)
          =
          (stack_contents j stack cs').(m_footprint)>>
.
Proof.
  apply func_ext2. i. apply prop_ext.
  generalize size_arguments_above; intro SZARG.
  inv STACKS.
  { ss. }
  { ss. u. split; i; des; clarify; esplits; et; psimpl; zsimpl; try xomega.
    { exploit tailcall_size; eauto. i. omega. }
    { specialize (SZARG sg). omega. }
    { destruct (classic (4 * size_arguments sg <= x1)).
      - right. esplits; et.
      - left. esplits; et. xomega.
    }
  }
  Local Opaque frame_contents frame_contents_at_external.
  inv STK; ss.
  { psimpl. zsimpl. rewrite <- frame_contents_at_external_m_footprint; ss; try xomega.
    - split; try xomega. specialize (SZARG sg). omega.
    - eapply bound_outgoing_stack_data; et.
  }
  {
    rewrite <- frame_contents_at_external_m_footprint ;ss.
    - split; try xomega. specialize (SZARG sg). omega.
    - eapply bound_outgoing_stack_data; et.
  }
Qed.


Lemma frame_contents_footprint_irr
      f j0 j1 spb ls0 ls1 sp ra
  :
    (frame_contents f j0 spb ls0 ls1 sp ra).(m_footprint) <2=
    (frame_contents f j1 spb ls0 ls1 sp ra).(m_footprint)
.
Proof.
  eapply sepconj_footprint_le; et.
  eapply mconj_footprint_le; et.
  eapply sepconj_footprint_le; et.
  eapply sepconj_footprint_le; et.
  eapply sepconj_footprint_le; et.
  abstr (fe_ofs_callee_save (make_env (function_bounds f))) ofs.
  abstr (used_callee_save (function_bounds f)) rs.
  clear - rs.
  ginduction rs; i; et.
  eapply sepconj_footprint_le; et.
Qed.

Lemma stack_contents_footprint_irr
      j0 j1 cs cs'
  :
    (stack_contents j0 cs cs').(m_footprint) <2=
    (stack_contents j1 cs cs').(m_footprint)
.
Proof.
  clear - cs.
  ginduction cs; i; ss.
  des_ifs.
  { eapply sepconj_footprint_le; et.
    eapply frame_contents_footprint_irr.
  }
  { eapply sepconj_footprint_le; et.
    eapply frame_contents_footprint_irr.
  }
Qed.

Lemma freed_contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (freed_contains_locations j sp pos bound sl ls)
              (freed_contains_locations j' sp pos bound sl ls).
Proof.
  intros; split; simpl; intros; auto.
Qed.

Lemma contains_locations_tl_incr:
  forall j j' sp pos from bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations_tl j sp pos from bound sl ls)
              (contains_locations_tl j' sp pos from bound sl ls).
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H4; eauto. intros (v & A & B). exists v; eauto.
Qed.

Local Transparent frame_contents_at_external.
Lemma frame_contents_at_external_incr:
  forall f j sp ls ls0 parent retaddr sg m P j',
    m |= frame_contents_at_external f j sp ls ls0 parent retaddr sg ** P ->
    inject_incr j j' ->
    m |= frame_contents_at_external f j' sp ls ls0 parent retaddr sg ** P.
Proof.
  unfold frame_contents_at_external, frame_contents_1_at_external; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  erewrite <- contains_callee_saves_incr by eauto.
  erewrite <- freed_contains_locations_incr by eauto.
  erewrite <- contains_locations_tl_incr by eauto.
  assumption.
Qed.
Local Opaque frame_contents_at_external.

Lemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall cs cs' P,
  m |= stack_contents j cs cs' ** P ->
  m |= stack_contents j' cs cs' ** P.
Proof.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  destruct sp0; auto.
  destruct cs, cs'; sep_simpl_tac; des; try congruence.
  { eapply dummy_frame_contents_incr; eauto. }
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
Qed.

Lemma stack_contents_at_external_change_meminj:
  forall m j j', inject_incr j j' ->
            forall cs cs' sg,
              m |= stack_contents_at_external j cs cs' sg ->
              m |= stack_contents_at_external j' cs cs' sg.
Proof.
  Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  des_ifs.
  - eapply frame_contents_at_external_incr; eauto.
  - eapply frame_contents_at_external_incr; eauto. rewrite sep_comm.
    eapply stack_contents_change_meminj; eauto. rewrite sep_comm. assumption.
Qed.

End STACKINGEXTRA.




Definition strong_wf_tgt (st_tgt0: Mach.state): Prop :=
  exists parent_sp parent_ra, last_option st_tgt0.(MachC.get_stack) = Some (Mach.dummy_stack parent_sp parent_ra)
.



Lemma external_call_parallel_rule:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
  external_call ef ge vargs1 m1 t vres1 m1' ->
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  exists j' vres2 m2',
     external_call ef ge vargs2 m2 t vres2 m2'
  /\ Val.inject j' vres1 vres2
  /\ m2' |= minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m2.
Proof.
  intros until vargs2; intros CALL SEP ARGS.
  destruct SEP as (A & B & C). simpl in A.
  exploit external_call_mem_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  intros (j' & vres2 & m2' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP).
  assert (MAXPERMS: forall b ofs p,
            Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists j', vres2, m2'; intuition auto.
  split; [|split].
- exact INJ'.
- apply m_invar with (m0 := m2).
+ apply globalenv_inject_incr with j m1; auto.
+ eapply Mem.unchanged_on_implies; eauto.
  intros; red; intros; red; intros.
  eelim C; eauto. simpl. exists b0, delta; auto.
- red; intros. destruct H as (b0 & delta & J' & E).
  destruct (j b0) as [[b' delta'] | ] eqn:J.
+ erewrite INCR in J' by eauto. inv J'.
  eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto.
  eapply Mem.valid_block_inject_1; eauto.
+ exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto.
Qed.

Lemma minjection_disjoint_footprint_private
      sm0 P
      (SEP: (SimMemInj.tgt sm0) |= P)
      (DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P)
  :
    P.(m_footprint) <2= sm0.(SimMemInj.tgt_private)
.
Proof.
  u.
  - ii. esplits; eauto.
    + ii. eapply DISJ; eauto. ss. esplits; eauto.
    + destruct P; ss. eapply m_valid; eauto.
Qed.

Lemma minjection_private_disjoint_footprint
      sm0 P
      (PRIV: P.(m_footprint) <2= sm0.(SimMemInj.tgt_private))
  :
    <<DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P>>
.
Proof.
  - ii. ss. des. eapply PRIV; eauto.
Qed.

Lemma external_call_parallel_rule_simmem
      (F V: Type) (ge0: Genv.t F V)
      sm_at sm_after P
      (SEP: sm_at.(SimMem.tgt) |= (minjection sm_at.(SimMemInj.inj) sm_at.(SimMem.src))
                             ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P)
      sm_arg sm_ret
      (MWF: SimMem.wf sm_at)
      (MWF0: SimMem.wf sm_arg)
      (MWF1: SimMem.wf sm_ret)
      (MWF2: SimMem.wf sm_after)
      (MWFAFTR : SimMem.wf (SimMemInj.unlift' sm_arg sm_ret))
      (MLE: SimMem.le sm_at sm_arg)
      (MLE0: SimMem.le (SimMem.lift sm_arg) sm_ret)
      (MLE1: SimMem.le (SimMem.unlift sm_at sm_ret) sm_after)
      (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret))
      (PRIV0: sm_at.(SimMemInj.tgt_private) = sm_arg.(SimMemInj.tgt_private))
      (PRIV1: sm_ret.(SimMemInj.tgt_private) = sm_after.(SimMemInj.tgt_private))
      (UNCH0: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_at) (SimMemInj.tgt sm_arg))
      (UNCH1: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_ret) (SimMemInj.tgt sm_after))
  :
    <<SEP: sm_after.(SimMem.tgt) |= (minjection sm_after.(SimMemInj.inj) sm_after.(SimMem.src))
                            ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P>>
.
Proof.
  (* See external_call_parallel_rule *)
  destruct SEP as (A & B & C). simpl in A.
  apply disjoint_footprint_sepconj in C. des. ss.
  eapply minjection_disjoint_footprint_private in DISJ1; cycle 1.
  { apply sep_drop in B. ss. }
  sep_split.
  { ss. eapply MWF2. }
  { apply disjoint_footprint_sepconj. ss.
    split; ss.
    apply minjection_private_disjoint_footprint.
    etrans; eauto.
    rewrite PRIV0. rewrite <- PRIV1.
    inv MLEAFTR. inv MLE0. inv MWF0. inv MWF1. ss.
    etrans; try apply TGTEXT0; eauto. rewrite TGTPARENTEQ0. reflexivity. }
  sep_split.
  { eapply globalenv_inject_incr in B; eauto.
    - apply sep_pick1 in B. ss. des. esplits; eauto.
      etrans; eauto. inv MLE. inv MLE0. inv MLE1. inv MLEAFTR.
      etrans; eauto with mem. etrans; eauto with mem.
    - apply SimMemInj.inject_separated_frozen; eauto.
      eapply SimMemInj.frozen_refl; eauto.
  }
  { ss. }
  destruct B as (X & Y & Z); ss.
  eapply m_invar; eauto.
  eapply Mem.unchanged_on_implies; cycle 1.
  { ii. exploit DISJ1; eauto. }
  rewrite PRIV0.
  etrans.
  { instantiate (1:= (SimMemInj.tgt sm_arg)). eauto. }
  etrans; cycle 1.
  { instantiate (1:= (SimMemInj.tgt sm_ret)). eauto. }
  clears sm_after. clear sm_after. clears sm_at. clear sm_at.
  inv MLE0. ss.
Unshelve.
  all: try apply Mem.empty.
Qed.

Local Transparent make_env sepconj.
Lemma contains_callee_saves_footprint
      j sp b rs0 ofs
      (FOOT: m_footprint
            (contains_callee_saves j sp (fe_ofs_callee_save (make_env b)) (used_callee_save b) rs0)
            sp ofs)
  :
    <<BOUND: fe_ofs_callee_save (make_env b) <=
             ofs < size_callee_save_area b (fe_ofs_callee_save (make_env b))>>
.
Proof.
  destruct b; ss. des_ifs.
  unfold size_callee_save_area. ss.
  clear_tac.
  assert(4 | 8).
  { econs. instantiate (1:=2). omega. }
  assert(0 < align (4 * bound_outgoing) 8 + 8 /\ (4 | align (4 * bound_outgoing) 8 + 8)).
  { hexploit (align_le (4 * bound_outgoing) 8); try lia. i. split; try lia.
    eapply Z.divide_add_r; try lia; ss.
    - etrans; cycle 1. eapply align_divides; try lia. eauto.
  (* TODO: strengthen zsimpl. *)
  }
  abstr (align (4 * bound_outgoing) 8 + 8) initofs.
  clear bound_outgoing_pos bound_stack_data_pos bound_local_pos. clear_tac.
  ginduction used_callee_save; ii; ss.
  assert((4 | (AST.typesize (mreg_type a))) /\
         ((AST.typesize (mreg_type a)) | 8) /\ 0 < (AST.typesize (mreg_type a))).
  { destruct a; ss; des_ifs; cbn; splits; try refl; try lia; ss. }
  destruct FOOT.
  - des.
    split.
    + etrans; eauto.
      eapply align_le; try lia.
    + eapply Z.lt_le_trans; eauto.
      etrans; cycle 1.
      { eapply size_callee_save_area_rec_incr; eauto. }
      rewrite ! size_type_chunk.
      refl.
  - exploit IHused_callee_save; revgoals; cycle 1; swap 1 3.
    { eauto. }
    { ss. }
    { esplits; eauto.
      - des. eapply Z.add_pos_pos; eauto. eapply Z.lt_le_trans. eapply H0. eapply align_le. omega.
      - des. eapply Z.divide_add_r; eauto. eapply Z.divide_trans. eapply H1. eapply align_divides. omega.
    }
    { ii. eapply used_callee_save_prop; eauto. }
    { inv used_callee_save_norepet. ss. }
    { ss. i; des. split; eauto.
      des. assert(initofs <= align initofs (AST.typesize (mreg_type a))). eapply align_le; omega. omega.
    }
Qed.
Local Opaque make_env sepconj.







Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Variable rao: Mach.function -> Mach.code -> ptrofs -> Prop.
Let md_src: Mod.t := (LinearC.module prog).
Let md_tgt: Mod.t := (MachC.module tprog rao).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).
Hypothesis return_address_offset_exists:
  forall f sg ros c v (FUNCT: Genv.find_funct tge v = Some (Internal f)),
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, rao f c ofs.
Hypothesis return_address_offset_deterministic:
  forall f c ofs ofs',
  rao f c ofs ->
  rao f c ofs' ->
  ofs = ofs'.

Let match_stacks := match_stacks skenv_link skenv_link.

Print Instances SimMem.class.
Print Instances SimSymb.class.

Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Compute last_option (@nil Z).
Compute last_option [1].
Compute last_option [1 ; 2].

Lemma functions_translated_inject
      sm0
      (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge)
      (SIMSKE: SimSymb.sim_skenv sm0 (ModSemPair.ss msp) (ModSem.skenv (ModSemPair.src msp))
                                 (ModSem.skenv (ModSemPair.tgt msp)))
      fptr_src fd_tgt fptr_tgt
      (FUNCSRC: Genv.find_funct tge fptr_tgt = Some fd_tgt)
      (INJ: Val.inject sm0.(SimMemInj.inj) fptr_src fptr_tgt)
  :
    <<SRCUB: fptr_src = Vundef>> \/
    exists fd_src,
      <<FUNCTGT: Genv.find_funct ge fptr_src = Some fd_src>>
      /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>>
.
Proof.
  ss.
  inv SIMSKE.
  hexploit (bsim_internal_funct_inject SIMGE); et.
  { eapply SimMemInjC.skenv_inject_revive; eauto. unfold ge. eauto. }
  i; des; eauto.
Qed.

Hypothesis TRANSL: match_prog prog tprog.

Definition locset_copy (diff: Z) (rs: Mach.regset): locset :=
  fun loc =>
    match loc with
    | S _ _ _ => Vundef
    | R r =>
      match rs r with
      | Vptr blk ofs => Vptr (blk.(Zpos) + diff).(Z.to_pos) ofs
      | _ => rs r
      end
    end
.
Hint Unfold locset_copy.

Lemma transf_function_sig
      f tf
      (TRANSFF: transf_function f = OK tf)
  :
    f.(Linear.fn_sig) = tf.(fn_sig)
.
Proof. unfold transf_function in *. des_ifs. Qed.

Local Opaque Pos.of_nat.
Lemma init_match_frame_contents
      sm_arg sg
      (SIMSKE: SimSymb.sim_skenv sm_arg (ModSemPair.ss msp) (ModSem.skenv (ModSemPair.src msp))
                                 (ModSem.skenv (ModSemPair.tgt msp)))
      m_tgt0 rs vs_src vs_tgt ls
      (STORE: StoreArguments.store_arguments sm_arg.(SimMemInj.tgt) rs (typify_list vs_tgt sg.(sig_args)) sg m_tgt0)
      (SG: 4 * size_arguments sg <= Ptrofs.modulus)
      (LS: LocationsC.fill_arguments
             (locset_copy (sm_arg.(SimMemInj.src).(Mem.nextblock).(Zpos) - m_tgt0.(Mem.nextblock).(Zpos)) rs)
             (typify_list vs_src sg.(sig_args)) (loc_arguments sg) = Some ls)
      (SIMVS: Val.inject_list (SimMemInj.inj sm_arg) vs_src vs_tgt)
      sm_init
      (SM0: sm_init = sm_arg.(SimMemInjC.update) sm_arg.(SimMemInj.src) m_tgt0 sm_arg.(SimMemInj.inj))
      (PRIV: forall ofs (BDD: 0 <= ofs < 4 * size_arguments sg),
          SimMemInj.tgt_private sm_init (Mem.nextblock sm_arg.(SimMemInj.tgt)) ofs)
      (MLE0: SimMem.le sm_arg sm_init)
      (MWF0: SimMem.wf sm_init)
      sm_junkinj n
      (SM1: sm_junkinj = sm_init.(SimMemInjC.update) (assign_junk_blocks sm_init.(SimMemInj.src) n)
                                                     (assign_junk_blocks m_tgt0 n)
                                                     (SimMemInjC.inject_junk_blocks
                                                        sm_init.(SimMemInj.src) m_tgt0 n
                                                        sm_arg.(SimMemInj.inj)))
      (MLE1: SimMem.le sm_init sm_junkinj)
      (MWF1: SimMem.wf sm_junkinj)
      (NB: Ple (Genv.genv_next (SkEnv.project skenv_link md_src.(Mod.sk))) (Mem.nextblock m_tgt0))
  :
    assign_junk_blocks m_tgt0 n
      |= dummy_frame_contents sm_arg.(SimMemInj.inj) ls sg (Mem.nextblock sm_arg.(SimMemInj.tgt)) 0
      ** minjection sm_junkinj.(SimMemInj.inj) sm_junkinj.(SimMemInj.src)
      ** globalenv_inject ge sm_junkinj.(SimMemInj.inj)
.
Proof.
  sep_split.
  { ss. zsimpl. esplits; eauto with lia.
    - apply Z.divide_0_r.
    - inv STORE. hexpl Mem.alloc_result NB. clarify. ii. rewrite assign_junk_blocks_perm. eapply PERM; et.
    - clear - SG SIMVS STORE LS. inv STORE.
      hexpl LocationsC.fill_arguments_spec. clear LS. clarify.
      hexpl Mem.alloc_result. clarify.
      intros ? ? OFS0 OFS1 ALIGN. zsimpl.
      destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)))).
      + hnf in VALS. generalize (loc_arguments_one sg); intro ONES. abstr (loc_arguments sg) locs.
        clear - OFS0 OFS1 SG H SIMVS VALS locs ONES FILL ALC.
        abstr (sig_args sg) tys.
        ginduction locs; ii; ss.
        exploit ONES; eauto. i.
        destruct a; ss.
        des; ss; clarify.
        { unfold typify_list in *.
          inv VALS. inv SIMVS; ss; des_ifs.
          inv H3. inv H7.
          exists (typify v' t). esplits; eauto.
          - unfold load_stack, Mem.loadv in *. ss. zsimpl. psimpl.
            rewrite assign_junk_blocks_load; ss; cycle 1.
            { eauto with mem. }
            psimpl. unfold Ptrofs.max_unsigned in *. set (typesize_pos ty). lia.
          - rewrite <- H6.
            eapply inject_typify; eauto. }
        { unfold typify_list in *.
          inv VALS. inv SIMVS; ss; des_ifs.
          eapply IHlocs; eauto. }
      + exploit OUT; eauto. i; des. ss. rewrite H0.
        exploit (Mem.valid_access_load m_tgt0 (chunk_of_type ty)); cycle 1.
        { i; des. esplits; eauto. erewrite assign_junk_blocks_load; eauto. eauto with mem. }
        red. esplits; eauto.
        * erewrite Stackingproof.size_type_chunk in *. rewrite Stackingproof.typesize_typesize in *.
          ii. eapply Mem.perm_implies.
          { eapply PERM. xomega. }
          eauto with mem.
        * rewrite Stackingproof.align_type_chunk. eapply Z.mul_divide_mono_l; eauto.
  }
  { apply disjoint_footprint_sepconj. split.
    - bar.
      ii; ss. rename H into X. rename H0 into Y. des.
      clarify. zsimpl. specialize (PRIV ofs). exploit PRIV; eauto with lia.
      intro TPRIV. hnf in TPRIV. ss. des. unfold SimMemInjC.inject_junk_blocks in *.
      des_ifs.
      { eapply TPRIV; eauto. rewrite assign_junk_blocks_perm in *; ss. }
      { bsimpl; des; des_sumbool; ss. rewrite assign_junk_blocks_perm in *. zsimpl. exploit Mem.perm_valid_block; eauto. }
      { eapply TPRIV; eauto. rewrite assign_junk_blocks_perm in *; ss. }
    - ii; ss.
  }
  sep_split.
  { ss. inv MWF1; ss. }
  { ss. }
  eapply sim_skenv_inj_globalenv_inject; et.
  { eapply SimSymb.mle_preserves_sim_skenv in SIMSKE; et. etrans; et. }
  { rewrite assign_junk_blocks_nextblock. ss. des_ifs; xomega. }
Unshelve. all: eauto.
Qed.

Lemma stack_contents_at_external_intro
      sm0 stack cs' sg sp sm1
      (STACKS: match_stacks tge _ (SimMemInj.inj sm0) stack cs' sg sm0)
      (RSP: parent_sp cs' = Vptr sp Ptrofs.zero)
      (FREETGT: Mem.free (SimMemInj.tgt sm0) sp 0 (4 * size_arguments sg) = Some (SimMemInj.tgt sm1))
      (SEP: SimMemInj.tgt sm0 |= stack_contents (SimMemInj.inj sm0) stack cs')
  :
  <<SEP: SimMemInj.tgt sm1 |= stack_contents_at_external (SimMemInj.inj sm0) stack cs' sg>>
.
Proof.
  hexploit Mem.nextblock_free; eauto. intro NB.
  destruct stack; ss. destruct cs'; ss. inv STACKS.
  des_ifs_safe.
  destruct stack.
  { des_ifs; sep_simpl_tac. psimpl. unfold dummy_frame_contents in *.
    apply contains_locations_range in SEP. zsimpl.
    eapply range_split0 with (mid := (4 * size_arguments sg)) in SEP; cycle 1.
    { generalize (size_arguments_above sg); i. inv STACKS; des; clarify; ss; split; try lia.
      - erewrite Conventions.tailcall_size; eauto. generalize (size_arguments_above sg_init); i. lia.
      - inv STK. inv MAINARGS.
    }
    destruct SEP as (A & B & C).
    sep_split; eauto.
    - ss. esplits; eauto; try lia. i.
      eapply Mem.valid_block_free_1; eauto.
      des. hexploit A1; eauto. i. eapply Mem.perm_valid_block; eauto.
    - eapply m_invar; eauto. hexpl Mem.free_unchanged_on UNCH. ii. ss. des; clarify. lia.
      (* TODO: Fix hexpl tactic *)
  }
  Local Opaque stack_contents_args.
  destruct cs'; ss.
  { inv STACKS. inv STK. }
  des_ifs_safe.

  exploit Mem.free_unchanged_on; eauto.
  { instantiate (1:= fun blk ofs => blk <> sp \/ ~(0 <= ofs < 4 * size_arguments sg)). ss. ii; des; eauto. }
  intro UNCH.

  {{
      assert(SZARG: 0 <= size_arguments sg <= bound_outgoing (function_bounds f)).
      { inv STACKS; ss. esplits; et. generalize (size_arguments_above sg). i. xomega. }
      assert(SZARG0: 4 * size_arguments sg <= fe_stack_data (make_env (function_bounds f))).
      { generalize (bound_outgoing_stack_data (function_bounds f)); i. xomega. }
      assert(UNCH0: Mem.unchanged_on
                      (~2 m_footprint
                        (contains_locations (SimMemInj.inj sm0) sp fe_ofs_arg
                                            (bound_outgoing (function_bounds f)) Outgoing rs))
                      (SimMemInj.tgt sm0) (SimMemInj.tgt sm1)).
      { eapply Mem.unchanged_on_implies; eauto.
        bar.
        intros ? ? FOOT VALID.
        s.
        destruct (eq_block b sp); clarify; et. right.
        intro CONTR.
        clear - SZARG CONTR FOOT.
        ss.
        repeat (apply_all_once not_and_or).
        des; ss.
        eapply FOOT; et. unfold fe_ofs_arg in *. xomega.
      }
      assert(UNCH1: Mem.unchanged_on (~2 m_footprint (frame_contents f (SimMemInj.inj sm0)
                                                                     sp rs rs0 sp2 retaddr0))
                                     (SimMemInj.tgt sm0) (SimMemInj.tgt sm1)).
      { eapply Mem.unchanged_on_implies; try apply UNCH0.
        ii. ss. des. clarify. apply not_or_and in H. des.
        apply H. unfold frame_contents_1.
        Local Transparent sepconj.
        s.
        Local Opaque sepconj.
        right. left. esplits; et.
      }
      eapply sepconj_isolated_mutation_revisited; et; clear UNCH1.
      {
        apply sep_pick1 in SEP.
        unfold frame_contents, frame_contents_at_external in *.
        ss.
        des.
        esplits; et.
        - clear SEP0.
          unfold frame_contents_1, frame_contents_1_at_external in *.
          apply sep_swap. rewrite sep_swap23. apply sep_swap in SEP.
          rewrite <- sep_assoc.
          eapply sepconj_isolated_mutation_revisited; et; swap 2 3.
          {
            eapply Mem.unchanged_on_implies; et.
          }
          {
            Local Transparent sepconj.
            s.
            Local Opaque sepconj.
            u. ii.
            unfold fe_ofs_arg in *. zsimpl.
            des; clarify; esplits; et; try xomega.
          }
          apply sep_pick1 in SEP.
          eapply contains_locations_split with (lo := (size_arguments sg)) in SEP; cycle 1.
          { xomega. }
          eapply sepconj_isolated_mutation_revisited; et; swap 2 3.
          { apply sep_pick1 in SEP.
            eapply free_freed_contains_locations with (CTX := pure True); et.
            { rewrite <- add_pure_r_eq. ss. }
            { eapply match_stacks_sp_valid; eauto. }
          }
          { eapply Mem.unchanged_on_implies; try apply UNCH; et. s.
            ii. apply not_and_or in H. des; et.
          }
        - clear SEP.
          apply range_split with (mid := (4 * size_arguments sg)) in SEP0; cycle 1.
          { esplits; et. xomega. }
          sep_simpl_tac.
          eapply sepconj_isolated_mutation_revisited; et.
          { eapply Mem.unchanged_on_implies; try apply UNCH.
            ii. ss. apply not_and_or in H. des; et.
          }
          {
            ss. unfold fe_ofs_arg. zsimpl. esplits; et; try xomega.
            + apply sep_pick1 in SEP0. ss. des. ss.
            + i. inv STACKS. des. eapply Mem.valid_block_free_1; et.
          }
      }
      {
        rewrite <- frame_contents_at_external_m_footprint; ss.
        apply bound_outgoing_stack_data.
      }
  }}
Unshelve.
  all: econs.
Qed.

Lemma stack_contents_at_external_spec_elim
      sm_ret stack cs' sg sp sm_after
      (STACKS: match_stacks tge _ (SimMemInj.inj sm_ret) stack.(stackframes_after_external) cs' sg sm_after)
      (RSP: parent_sp cs' = Vptr sp Ptrofs.zero)
      (UNFREETGT: Mem_unfree (SimMemInj.tgt sm_ret) sp 0 (4 * size_arguments sg) = Some (SimMemInj.tgt sm_after))
      (SEP: SimMemInj.tgt sm_ret |= stack_contents_at_external (SimMemInj.inj sm_ret) stack cs' sg)
  :
    <<SEP: SimMemInj.tgt sm_after |= stack_contents (SimMemInj.inj sm_ret)
                         stack.(stackframes_after_external) cs'>>
.
Proof.
  hexploit Mem_nextblock_unfree; eauto. intro NB.
  hexploit Mem_unfree_perm; et. intro PERM.
  hexploit Mem_unfree_unchanged_on; et. intro UNCH.
  destruct stack; ss. destruct cs'; ss.
  { inv STACKS. inv MAINARGS. }
  des_ifs_safe.
  destruct stack.
  { des_ifs; sep_simpl_tac; cycle 1.
    inv STACKS; cycle 1.
    { inv STK. inv MAINARGS. }
    ss.
    assert(SZLE: size_arguments sg <= size_arguments sg_init).
    { des; clarify.
      - refl.
      - rewrite tailcall_size; ss. eapply Z.ge_le. eapply size_arguments_above.
    }
    Local Transparent stack_contents_args.
    (* Local Opaque contains_locations. *)
    ss. unfold dummy_frame_contents.
    Local Opaque stack_contents_args.
    psimpl. zsimpl.
    esplits; try xomega.
    + eapply Z.divide_0_r.
    + clear - SEP. inv SEP. des. inv H0. des. eauto.
    + des; clarify.
      exploit tailcall_size; et. intro ZERO; des. rewrite ZERO in *. zsimpl.
      clear - SEP UNCH.
      apply sep_drop in SEP. ss. des. ii. eapply Mem.perm_unchanged_on; et. u. i. des. xomega.
    + i. zsimpl.
      assert(exists v, Mem.load (chunk_of_type ty) (SimMemInj.tgt sm_after) sp (4 * ofs) = Some v).
      { eapply Mem.valid_access_load. rr.
        rewrite align_type_chunk in *.
        split; ss.
        - rewrite typesize_chunk in *. ii.
          destruct (classic (ofs0 < (4 * size_arguments sg))).
          + eapply PERM; et. split; try xomega.
          + eapply Mem.perm_unchanged_on; et.
            * u. i. des_safe. xomega.
            * clear - SEP SZLE H0 H2 H3. apply sep_drop in SEP. ss. des. eapply SEP1; et. split; try xomega.
        - eapply Z.mul_divide_mono_l. eauto.
      }
      des_safe. esplits; et.
  }
  {
    inv STACKS.
    ss. des_ifs.
    Local Transparent stack_contents_args.
    ss.
    Local Opaque stack_contents_args.
    eapply sepconj_isolated_mutation_revisited; et.
    - generalize (bound_outgoing_stack_data (function_bounds f)); i.
      rewrite <- frame_contents_at_external_m_footprint; ss.
      + bar. u. ii. des; clarify.
        right.
        Local Transparent sepconj.
        s.
        left. esplits; et. xomega.
      + split; ss. eapply Z.ge_le. eapply size_arguments_above.
    - apply sep_pick1 in SEP.

      Local Transparent frame_contents frame_contents_at_external.
      Local Opaque sepconj.
      ss.
      des.
      split.
      + clear SEP0.
        unfold frame_contents_1, frame_contents_1_at_external in *.
        rewrite sep_swap. rewrite sep_swap in SEP. rewrite sep_swap23 in SEP. rewrite <- sep_assoc in SEP.
        eapply sepconj_isolated_mutation_revisited; try apply SEP; et.
        * Local Transparent sepconj.
          u. ii.
          des_safe. unfold fe_ofs_arg. zsimpl. et.
        * apply sep_pick1 in SEP. eapply unfree_freed_contains_locations with (CTX := pure True); et.
          { rewrite <- add_pure_r_eq. eauto. }
          eauto.
        * s. ii. des. clarify. u. unfold fe_ofs_arg in *. zsimpl.
          destruct (classic (x1 < 4 * size_arguments sg)); et.
          right. split; et. xomega.
      +
        eapply sepconj_isolated_mutation_revisited; try apply SEP; et.
        * u. ii.
          des_safe. unfold fe_ofs_arg. et.
        * apply sep_pick1 in SEP0.
          eapply unfree_freed_range; et.
        * s. ii. des. clarify. u. unfold fe_ofs_arg in *. zsimpl.
          destruct (classic (x1 < 4 * size_arguments sg)); et.
          right. split; et. xomega.
    - rewrite <- frame_contents_at_external_m_footprint; et.
      { split; et. eapply Z.ge_le. eapply size_arguments_above. }
      { eapply bound_outgoing_stack_data; et. }
  }
Qed.
Local Opaque sepconj.

Definition current_function (stk: Linear.stackframe): Linear.function :=
  match stk with
  | Linear.Stackframe f _ _ _ => f
  end
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Linear.state) (st_tgt0: MachC.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Stackingproof.match_states skenv_link skenv_link ge tge st_src0 st_tgt0.(st) sm0)
    (MCOMPATSRC: st_src0.(LinearC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(st).(get_mem) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (INITRS: exists dummy_stack_src,
        <<DUMMY: st_src0.(LinearC.get_stack).(last_option) = Some dummy_stack_src>> /\
        <<GOOD: forall
                   mr
                   (CALLEESAVE: Conventions1.is_callee_save mr)
                 ,
                   (<<UIU: dummy_stack_src.(current_locset) (R mr) = Vundef -> st_tgt0.(init_rs) mr = Vundef>>)
                   /\
                   (<<INJ: Val.inject sm0.(SimMemInj.inj) (dummy_stack_src.(current_locset) (R mr))
                                                              (st_tgt0.(init_rs) mr)>>)
                   (* <<EQ: dummy_stack_src.(current_locset) (R mr) = st_tgt0.(init_rs) mr>> *)
                   (* /\ <<PTRFREE: ~ is_real_ptr (st_tgt0.(init_rs) mr)>> *)
        >> /\
        <<SIG: dummy_stack_src.(current_function).(Linear.fn_sig) = st_tgt0.(init_sg)>>)
    (WFTGT: strong_wf_tgt st_tgt0.(MachC.st))
.

Inductive match_states_at
          (st_src0: Linear.state) (st_tgt0: MachC.state) (sm_at sm_arg: SimMem.t): Prop :=
| match_states_at_intro
    (INJ: sm_at.(SimMemInj.inj) = sm_arg.(SimMemInj.inj))
    (INJ: sm_at.(SimMem.src) = sm_arg.(SimMem.src))
    init_rs init_sg cs' tfptr rs sp skd fptr cs ls
    (SRCST: st_src0 = Linear.Callstate cs fptr (SkEnv.get_sig skd) ls (SimMemInj.src sm_arg))
    (TGTST: st_tgt0 = mkstate init_rs init_sg (Callstate cs' tfptr rs (SimMemInj.tgt sm_at)))
    (RSP: parent_sp cs' = Vptr sp Ptrofs.zero)
    (PRIV: brange sp 0 (4 * size_arguments (SkEnv.get_sig skd)) <2= sm_arg.(SimMemInj.tgt_private))
    (SIG: Genv.find_funct skenv_link fptr = Some skd)
    (VALID: Mem.valid_block (SimMemInj.tgt sm_arg) sp)
    (NB: sm_at.(SimMem.tgt).(Mem.nextblock) = sm_arg.(SimMem.tgt).(Mem.nextblock))
    (SEP: SimMemInj.tgt sm_arg |= stack_contents_at_external (SimMemInj.inj sm_arg) cs cs' (SkEnv.get_sig skd)
                        ** minjection (SimMemInj.inj sm_arg) (SimMemInj.src sm_arg) **
                        globalenv_inject ge (SimMemInj.inj sm_arg))
.

(* TODO: Move to LocationsC *)
Lemma loc_result_one
      sg
  :
    exists mr_res, <<ONE: loc_result sg = One mr_res>>
.
Proof. compute. des_ifs; eauto. Qed.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Inductive has_footprint (st_src0: Linear.state): MachC.state -> SimMem.t -> Prop :=
| has_footprint_intro
    (** copied from MachC **)
    stack rs m0 fptr sg blk ofs
    (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd /\ SkEnv.get_sig skd = sg)
    (RSP: (parent_sp stack) = Vptr blk ofs)
    (OFSZERO: ofs = Ptrofs.zero)
    init_rs init_sg
    (** newly added **)
    sm0
    (FOOT: SimMemInjC.has_footprint bot2 (brange blk (ofs.(Ptrofs.unsigned))
                                                 (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg))) sm0)
    (* (MTGT: m0 = sm0.(SimMem.tgt)) *)
  :
    has_footprint st_src0 (mkstate init_rs init_sg (Callstate stack fptr rs m0)) sm0
.

Inductive mle_excl (st_src0: Linear.state): MachC.state -> SimMem.t -> SimMem.t -> Prop :=
| mle_excl_intro
    (** copied from MachC **)
    init_rs init_sg stack fptr ls0 m0
    sg blk ofs
    (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd /\ SkEnv.get_sig skd = sg)
    (RSP: (parent_sp stack) = Vptr blk ofs)
    (** newly added **)
    sm0 sm1
    (MLEEXCL: SimMemInjC.le_excl bot2 (brange blk (ofs.(Ptrofs.unsigned))
                                                 (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg))) sm0 sm1)
    (* (MTGT: m0 = sm0.(SimMem.tgt)) *)
  :
    mle_excl st_src0 (mkstate init_rs init_sg (Callstate stack fptr ls0 m0)) sm0 sm1
.

Let SEGESRC: senv_genv_compat skenv_link ge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.
Let SEGETGT: senv_genv_compat skenv_link tge. Proof. eapply SkEnv.senv_genv_compat; et. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := match_states_at)
                               (sidx := unit)
                               (sound_states := fun _ _ _ => wt_state)
                               (has_footprint := has_footprint)
                               (mle_excl := mle_excl)
  ;
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply wt_state_local_preservation; eauto.
    eapply wt_prog; eauto.
  - inv FOOT. inv MLEEXCL. rewrite RSP in *. clarify. des. clarify. eapply SimMemInjC.foot_excl; et.
  - (* init bsim *)
    {
      inv INITTGT. inv STORE. folder.
      inv SIMARGS. ss.
      exploit functions_translated_inject; eauto.
      { eapply make_match_genvs; et. apply SIMSKENV. }
      { apply SIMSKENV. }
      i; des.
      { inv SAFESRC. rewrite SRCUB in *. ss. }
      destruct fd_src; ss. unfold bind in *. des_ifs.
      hexpl transf_function_sig SG.
      assert(LEN0: length (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f))) =
                   length (loc_arguments (Linear.fn_sig f))).
      {
        etransitivity.
        - unfold typify_list. rewrite zip_length. erewrite SimMem.sim_val_list_length; try apply VALS0. ss.
        - symmetry. rewrite SG.
          (* eapply extcall_arguments_imply in VALS. *)
          erewrite extcall_arguments_length; eauto with congruence.
          assert((length targs) = (length (sig_args (fn_sig fd)))).
          { erewrite <- extcall_arguments_length; eauto. erewrite loc_arguments_length; eauto. }
          inv TYP. xomega.
      }
      exploit (LocationsC.fill_arguments_progress
                 (locset_copy ((Args.m args_src).(Mem.nextblock).(Zpos) - m0.(Mem.nextblock).(Zpos)) rs)
                 (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f)))
                 (* args_src.(Args.vs) *)
                 (loc_arguments f.(Linear.fn_sig))); eauto. i; des.
      exploit (LocationsC.fill_arguments_spec
                 (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f)))
                 (* args_src.(Args.vs) *)
                 f.(Linear.fn_sig)); eauto. i; des.
      exploit SimMemInjC.mach_store_arguments_simmem; eauto.
      { econs; eauto with congruence. rp; eauto. }
      i; des.

      exploit (@SimMemInjC.inject_junk_blocks_parallel sm1 n); et. intro SM0; des. rename sm0 into sm2.

      esplits.
      { (* initial frame *)
        econs; eauto with congruence; cycle 2.
        - ii. hexpl OUT.
        - inv TYP.
          econs; eauto with congruence.
          erewrite SimMem.sim_val_list_length; try apply VALS0. ss.
          etrans; eauto with congruence.
        - instantiate (1:= n).
          ii. hexpl OUT.
          destruct loc; ss.
          + hexploit PTRFREE; eauto.
            { rewrite <- SG. eauto. }
            ii; eauto with congruence.
            rewrite MEMSRC. rewrite OUT0.
            rewrite <- MEMSRC in *.
            clear - SM (* NB *) H.
            des_ifs. ss. unfold Mem.valid_block in *. des.
            rewrite assign_junk_blocks_nextblock in *. unfold Plt in *.
            abstr (Mem.nextblock m0) y.
            abstr (Mem.nextblock (Args.m args_src)) m_src.

            Ltac Pos_compare_tac := try rewrite Pos.compare_lt_iff in *;
                                    try rewrite Pos.compare_gt_iff in *;
                                    apply_all_once Pos.compare_eq; clarify; try lia.
            replace (Z.pos b + Z.pos_sub m_src y) with (Z.pos_sub b y + Z.pos m_src); try nia; cycle 1.
            { rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac. }
            split; ss; try xomega.
            * ii.
              rewrite Z2Pos.inj_add in *; ss; try lia.
              rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac.
              rewrite Z.pos_sub_diag in *. zsimpl. rewrite Pos2Z.id in *. lia.
            * destruct (peq b y); ss.
              { clarify. rewrite Z.pos_sub_diag. zsimpl. rewrite Pos2Z.id in *. des_ifs; lia. }
              rewrite Z2Pos.inj_add in *; ss; try lia; cycle 1.
              {
                rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac.
              }
              replace (Z.pos_sub b y) with (b.(Zpos) - y.(Zpos))%Z; cycle 1.
              { ss. }
              rewrite Z2Pos.inj_sub; ss; try lia.
              des_ifs; lia.
          + rewrite OUT0 in *. ss.
      }
      { instantiate (1:= sm2). etrans; eauto. }
      { (* match states *)
        assert(INITRS: agree_regs (SimMemInj.inj sm2) ls1 rs).
        {
          ii. destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (Linear.fn_sig f))))).
          * red in VALS. inv TYP. ss. rewrite <- SG in *. clear - FILL VALS VALS0 H MLE0.
            generalize (loc_arguments_one (Linear.fn_sig f)). i.
            abstr (loc_arguments (Linear.fn_sig f)) locs. clear_tac.
            abstr (Args.vs args_src) vals_src. abstr (Args.vs args_tgt) vals_tgt. clear_tac.
            abstr (sig_args (Linear.fn_sig f)) tys. clear_tac.

            unfold typify_list in *.
            ginduction locs; ii; ss.
            exploit H0; eauto. i. destruct a; ss. des; clarify.
            { inv VALS. destruct vals_tgt; ss. des_ifs. inv VALS0.
              rename H4 into EARGP. inv EARGP. rename H2 into EARG. inv EARG; ss.
              clarify. rewrite <- H4. rewrite H.
              eapply inject_typify; eauto.
              inv MLE0. ss. eapply val_inject_incr; et.
            }
            inv VALS. destruct vals_tgt; ss. des_ifs. inv VALS0.
            unfold typify_list in *. ss. des_ifs.
            eapply IHlocs; eauto.
          * (* eapply Loc_not_in_notin_R in H; eauto. *)
            hexploit PTRFREE; eauto.
            { rewrite <- SG. eauto. }
            i. rewrite OUT; ss. rewrite DEF. s.
            rewrite <- MEMSRC in *. rewrite <- MEMTGT in *.
            clear - H0 MWF0 SM DEF MLE0. des_ifs. ss.
            econs; cycle 1.
            { instantiate (1:= 0%Z). psimpl. ss. }
            unfold SimMemInjC.inject_junk_blocks. ss. unfold Mem.valid_block in *.
            rewrite assign_junk_blocks_nextblock in *.
            abstr (Mem.nextblock m0) y.
            abstr (Mem.nextblock (Args.m args_src)) m_src.
            des.
            replace (Z.pos b + Z.pos_sub m_src y) with (Z.pos_sub b y + Z.pos m_src); try nia; cycle 1.
            { rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac. }
            destruct (peq b y) eqn: EQ.
            { clarify. rewrite Z.pos_sub_diag. zsimpl. rewrite Pos2Z.id.
              des_ifs; bsimpl; des; des_sumbool; try xomega; cycle 1.
              replace (m_src + y - m_src)%positive with y; ss.
              rewrite Pos.add_comm. rewrite Pos.add_sub. ss.
            }
            rewrite Z2Pos.inj_add; ss; cycle 1.
            { rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac. }
            des_ifs.
            {
              bsimpl; des; des_sumbool. unfold Plt in *.
              rewrite Pos.add_comm. rewrite Pos.add_assoc. rewrite Pos.add_sub.
              rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac.
              rewrite Pos2Z.id. rewrite Pos.add_sub_assoc; ss. rewrite Pos.add_comm. rewrite Pos.add_sub. ss.
            }
            assert(COND0: negb (plt (Z.to_pos (Z.pos_sub b y) + m_src) m_src)).
            { bsimpl. des_sumbool. ii. unfold Plt in *. xomega. }
            (* des_ifs. *)
            (* { unfold block. do 2 f_equal. bsimpl; des; des_sumbool; try lia. *)
            rewrite COND0 in *.
            assert(COND1: plt (Z.to_pos (Z.pos_sub b y) + m_src) (m_src + Pos.of_nat n)).
            { bsimpl. des_sumbool. ii. unfold Plt in *. rewrite ! Z.pos_sub_spec. des_ifs; Pos_compare_tac.
              destruct n; ss; try lia.
            }
            rewrite COND1 in *.
            ss.
        }
        rename targs into targs_tgt. rename TYP into TYPTGT.
        (* assert(TYPSRC: exists targs_src, typecheck (Args.vs args_src) (fn_sig fd) targs_src). *)
        (* { esplits; eauto. econs; eauto. inv TYPTGT. rewrite <- LEN. clear - VALS0. admit "ez". } *)
        (* des. *)
        econs; ss; eauto.
        - econs; ss; eauto.
          + rewrite DEF. ss. rewrite SM. ss. econs; ss; eauto with congruence.
          + econs; ss; eauto.
            * inversion SIMSKENV; clear SIMSKENV.
              eapply SimMemInjC.sim_skenv_symbols_inject with (sm0 := sm2); et.
              eapply SimSymb.mle_preserves_sim_skenv; eauto.
              eapply SimSymb.mle_preserves_sim_skenv; eauto.
            * eapply loc_arguments_bounded.
            * rewrite DEF. rewrite SM. s. unfold Mem.valid_block. rewrite assign_junk_blocks_nextblock. rewrite <- NB.
              exploit Mem.nextblock_alloc; et. i. rewrite H. rewrite MEMTGT.
              clear - ALC NB MWF.
              esplits.
              { des_ifs; xomega. }
              { inv MWF. etrans; et. xomega. }
              { (* TODO: make lemma *)
                ii. inv MWF; ss. eapply TGTEXT in H.
                rr in H; ss. des. r in H0. unfold Mem.valid_block in *.
                exploit Mem.nextblock_alloc; et. i. rewrite NB in *. rewrite H1 in *. xomega. }
          + eapply val_inject_incr; try apply MLE0; eauto.
            eapply val_inject_incr; try apply MLE; eauto.
          + psimpl. zsimpl. rewrite SG.
            rewrite MEMSRC. rewrite MEMTGT.
            exploit (@init_match_frame_contents sm_arg); try apply MLE; try apply MLE0; eauto.
            { apply SIMSKENV. }
            { inv TYPTGT. econs; eauto. rewrite <- MEMTGT. ss. }
            { inv TYPTGT. unfold Ptrofs.max_unsigned in *. s. xomega. }
            { rewrite <- SG. ss. rewrite <- MEMSRC in *. eauto. }
            { rewrite DEF, SM. s. f_equal; eauto. }
            { inv SIMSKENV. ss. inv SIMSKE. ss.
              etrans; et. inv MWF0. ss. }
            intro SEP.
            eapply dummy_frame_contents_incr; try apply MLE0; eauto.
            eapply dummy_frame_contents_incr; try apply MLE; eauto.
            subst; ss.
        - clarify; ss; congruence.
        - clarify.
        - esplits; ss.
          + i. ss. split; i.
            * rewrite OUT in H; ss.
              { des_ifs. }
              ii. hexpl loc_arguments_acceptable_2 ACCP. ss. clarify.
            * esplits; eauto.
        - rr. ss. esplits; eauto.
      }
    }
  - (* init progress *)
    des. inv SAFESRC. folder.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv SIMARGS. ss.
    exploit (fsim_internal_funct_inject SIMGE); et.
    { unfold ge. eapply SimMemInjC.skenv_inject_revive; et. eapply SIMSKENV. }
    i; des. monadInv MATCH. rename x into fd_tgt.
    assert(exists targs_tgt, <<TYPTGT: typecheck (Args.vs args_tgt) (fn_sig fd_tgt) targs_tgt>>).
    { inv TYP. eexists. econs; eauto.
      - erewrite <- inject_list_length; eauto. erewrite <- transf_function_sig; eauto.
      - erewrite <- transf_function_sig; eauto.
    }
    des.
    exploit (store_arguments_progress (Args.m args_tgt) targs_tgt (fn_sig fd_tgt)); et.
    { inv TYPTGT. eapply typify_has_type_list; et. }
    { inv TYPTGT. ss. }
    i; des.
    esplits; et.
    econs; et.
    { instantiate (1:= Vlong Int64.zero). ss. }
  - (* callstate wf *)
    inv MATCH; ss.

  - (* call fsim *)
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv CALLSRC. inv MATCH; ss. clarify.
    inv MATCHST; ss. destruct st_tgt0; ss. clarify. ss. clarify.
    des. exploit SOUND; ss; eauto. intro Q; des. exploit wt_callstate_agree; eauto. intros [AGCS AGARGS].
    assert(MCOMPAT0: sm0.(SimMemInj.inj) = j). { inv MCOMPAT. ss. } clarify.

    hexpl match_stacks_sp_ofs RSP.
    hexploit arguments_perm; eauto. { eapply sep_drop_tail3 in SEP. eauto. } i; des. psimpl.
    hexploit arguments_private; eauto. { eapply sep_drop_tail3 in SEP. eauto. } i; des. psimpl.
    hexploit Mem.range_perm_free. { ii. spc H. zsimpl. eapply H; eauto. } intros [m_tgt0 FREETGT].
    exploit transl_external_arguments; eauto. { apply sep_pick1 in SEP. eauto. } intro ARGS; des.

    assert(VALID: Mem.valid_block (SimMemInj.tgt sm0) sp).
    { exploit match_stacks_sp_valid; eauto. i; des. eauto. }

    exploit SimMemInj.free_right; eauto.
    { u. ii. esplits; eauto.
      do 2 spc H0. zsimpl. eauto.
    }
    { exploit match_stacks_sp_valid; eauto. i; des. eauto. }
    i; des. clarify.

    hexpl Mem.nextblock_free NB.
    assert(EXTTGT: exists skd_tgt,
              Genv.find_funct skenv_link tfptr = Some skd_tgt /\ SkEnv.get_sig skd_tgt = SkEnv.get_sig skd).
    {
      folder. esplits; eauto.
      (* copied from InliningproofC *)
      (** TODO: remove redundancy **)
      inv SIMSKENV. ss.
      assert(fptr_arg = tfptr).
      { inv FPTR; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
        inv SIMSKE. ss. inv INJECT; ss.
        exploit (DOMAIN b1); eauto.
        { eapply Genv.genv_defs_range; et. }
        i; clarify.
      }
      clarify.
    }
    esplits; eauto.
    + econs; eauto.
      * folder. eapply (fsim_external_funct_inject SIMGE); et.
        { unfold ge. eapply SimMemInjC.skenv_inject_revive; et. apply SIMSKENV. }
        ii. clarify.
      * psimpl. zsimpl. auto.
      * ii. rewrite Ptrofs.unsigned_zero. eapply Z.divide_0_r.
    + econs; ss; eauto with congruence.
    + econs; ss; et.
      econs; ss; et. u. i. des. clarify. eapply Mem.free_range_perm; et.
    + econs; eauto with congruence.
      * rp; eauto.
      * u. ii. des; clarify. specialize (H0 x1). zsimpl. esplits; eauto.
        { rp; [eapply H0; eauto|..]; eauto. }
        { unfold Mem.valid_block in *. eauto with congruence. }
      * rewrite <- sep_assoc. rewrite sep_comm.
        eapply globalenv_inject_incr with (j:= sm0.(SimMemInj.inj)); eauto.
        { rewrite <- MINJ. eapply inject_incr_refl. }
        { eapply SimMemInj.inject_separated_frozen. rewrite <- MINJ. eapply SimMemInj.frozen_refl. }
        rewrite <- sep_assoc in SEP. rewrite sep_comm in SEP. bar. move SEP at bottom.
        destruct SEP as (A & B & C).
        sep_split.
        { eapply m_invar; eauto. ss. eapply Mem_unchanged_on_bot; eauto.
          rewrite NB. refl. }
        { ss. }
        destruct B as (D & E & F).
        sep_split; revgoals.
        { ss. eapply MWF1. }
        { rewrite MSRC. rewrite MINJ.
          assert(LE:
                   (stack_contents_at_external (SimMemInj.inj sm0) stack cs' (SkEnv.get_sig skd)).(m_footprint)
                   <2=
                   (stack_contents (SimMemInj.inj sm0) stack cs').(m_footprint)).
          { erewrite stack_contents_at_external_m_footprint; et. }
          { clear - STACKS F. ii. eapply F; et. erewrite <- stack_contents_at_external_m_footprint; et. }
        }
        rewrite MINJ.
        eapply stack_contents_at_external_intro; eauto.

  - (* after fsim *)
    des.
    inv AFTERSRC. inv MATCH; ss. clarify.
    inv MATCHST; ss. destruct st_tgt0; ss. clarify. ss. clarify.
    assert(MCOMPAT0: sm0.(SimMemInj.inj) = j). { inv MCOMPAT; ss. } clarify.

    hexpl match_stacks_sp_ofs RSP.
    inv SIMRET.

    assert(VALID: Mem.valid_block (SimMemInj.tgt sm0) sp).
    { inv HISTORY. inv MATCHARG. ss. clarify. eauto with congruence. }
    assert(exists m_tgt0, <<UNFR: Mem_unfree sm_ret.(SimMemInj.tgt) sp 0 (4 * size_arguments sg_arg)
                                  = Some m_tgt0>>).
    { eapply Mem_unfree_suceeds; eauto.
      unfold Mem.valid_block in *. eapply Plt_Ple_trans; eauto. etransitivity; try eapply MLE. eapply MLEAFTR.
    }
    des.

    exploit (@SimMemInjC.unfree_right (SimMemInj.unlift' sm_arg sm_ret)); try apply UNFR; eauto.
    { inv HISTORY. inv CALLSRC. inv CALLTGT. rewrite RSP in *. clarify. psimpl. zsimpl. inv SIMARGS. ss. clarify.
      assert(sg = sg_arg).
      { des. clarify. inv SIMSKENV. inv SIMSKELINK. ss. r in SIMSKENV.
        exploit fsim_external_inject_eq; et. i. subst tfptr. clarify. }
      clarify.
      assert(NP: Mem_range_noperm (SimMemInj.tgt sm_arg) blk 0 (4 * size_arguments sg_arg)).
      { eapply Mem_free_noperm; eauto. }
      eapply Mem_unchanged_noperm; try apply NP; eauto.
      - eapply Mem.unchanged_on_implies; try apply MLE0. ii. ss.
        u. esplits; eauto.
        hexploit arguments_private; eauto.
        { eapply sep_drop_tail3 in SEP. eauto. }
        i; des. psimpl. spc H1. zsimpl. inv MATCHARG. rewrite <- MEMSRC0. rewrite <- INJ. u in H. des; clarify.
        eapply H1. eauto.
      - eapply Mem.valid_block_free_1; eauto.
    }
    { ss. bar. inv MLE. rewrite <- TGTPARENTEQ. clear_until_bar.
      r. unfold brange.
      hexploit match_stacks_sp_valid; eauto. intro SPVALID; des.
      ii. des_safe. clarify. eapply SPVALID1; eauto.
    }
    i; des. ss.

    assert(EXTTGT: exists skd, Genv.find_funct skenv_link tfptr = Some skd /\ SkEnv.get_sig skd = sg_arg).
    {
      inv HISTORY. ss. inv MATCHARG. ss.
      inv SIMSKENV. ss. inv SIMSKELINK. rr in SIMSKENV.
      esplits; et.
      rpapply SIG.
      { f_equal. clarify. symmetry. eapply fsim_external_inject_eq; et. }
      { clarify. }
    }
    exists sm1; esplits; eauto; [|i; split].
    + econs; et.
    + econs; eauto.
      * rewrite MEMTGT. inv MWFAFTR. ss.
        etrans; eauto.
        inv MLE. rewrite <- TGTPARENTEQNB.
        inv SIMSKENV. inv SIMSKELINK. ss.
      * psimpl. zsimpl. rp; eauto.
    + econs; ss; eauto with congruence; cycle 1.
      {
        clear - MLE2 GOOD DUMMY STACKS. destruct stack; ss; des_ifs; ss.
        { esplits; ss; eauto; ss. ii. exploit GOOD; eauto. i; des. esplits; et. eapply val_inject_incr; try apply MLE2; ss. }
        rewrite DUMMY. esplits; eauto.
        i. exploit GOOD; et. i; des. esplits; et. eapply val_inject_incr; try apply MLE2; ss.
      }
      assert(WTST: wt_state (Linear.Returnstate stack
       (Locmap.setpair (loc_result sg_arg) (typify (Retv.v retv_src) (proj_sig_res sg_arg))
          (LTL.undef_caller_save_regs ls_arg)) (Retv.m retv_src))).
      { clear - SOUND. exploit SOUND; ss; eauto. intro Q; des. inv Q.

      (** directly copied from LineartypingC.v **)
      (** TODO: provide it in metatheory **)
      (** I tried it (just add "(SOUND: sound_state su0 m_init st_src1)" in MatchSimModSem.v - AFTERFSIM,
          but it has some difficulty.. **)
      hexploit (loc_result_caller_save sg_arg); eauto. intro RES.
      hexploit (loc_result_one sg_arg); eauto. intro ONE.
      des.

      econs; ss; eauto.
      + ii. unfold Locmap.setpair. des_ifs. ss.
        apply wt_setreg; ss; cycle 1.
        { apply wt_undef_caller_save_regs; ss. }
        rewrite mreg_type_any. apply has_type_any.
      + ii.
        destruct l; ss.
        { rewrite locmap_get_set_loc_result; ss. des_ifs. rewrite AGCS; ss. }
        { rewrite locmap_get_set_loc_result; ss. des_ifs.
          - rewrite AGCS; ss.
          - rewrite AGCS; ss.
        }
      + ii. rewrite locmap_get_set_loc_result; ss.
      }
      inv WTST.
      assert(STACKS0: match_stacks tge _ (SimMemInj.inj sm_ret) (stackframes_after_external stack) cs' sg_arg sm1).
      {
        eapply match_stacks_change_meminj with (j:= (SimMemInj.inj sm0)).
        { eapply inject_incr_trans; try apply MLE0. eapply inject_incr_trans; try apply MLE. ss. }
        { rewrite <- MINJ.
          clear - SIMSKENV MLE2.
          i. inv SIMSKENV. ss. inv MLE2. clear MAXSRC MAXTGT.
          destruct (SimMemInj.inj sm0 b1) eqn:T; ss.
          - destruct p. exploit INCR; et. i; des. clarify.
          - inv FROZEN.
            exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. inv SIMSKELINK. inv INJECT.
            exploit DOMAIN; et. i. clarify.
        }
        { rewrite <- MINJ.
          clear - SIMSKENV MLE2.
          i. inv SIMSKENV. ss. inv MLE2. clear MAXSRC MAXTGT.
          destruct (SimMemInj.inj sm0 b1) eqn:T; ss.
          - destruct p. exploit INCR; et. i; des. clarify.
          - inv FROZEN.
            exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. inv SIMSKELINK. inv INJECT.
            inv SIMSKENV. xomega.
        }
        eapply match_stacks_le; try apply STACKS; et.
        { intros ? ? ? VALID0 MAP0. rewrite MINJ in *.
          bar.
          inv MLE0. ss.
          bar.
          inv HISTORY.
          ss. inv MATCHARG. ss. clarify.
          rewrite INJ in *.
          clear_until_bar.
          destruct (SimMemInj.inj sm_arg b) eqn:MAP1; ss.
          { destruct p; ss. apply INCR in MAP1. clarify. }
          { exfalso.
            inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des.
            clear - VALID0 OUTSIDE_TGT MLE.
            inv MLE.
            unfold Mem.valid_block in *. inv TGTUNCHANGED.
            xomega.
          }
        }
        {
          intros b_src b_tgt delta ofs VALID0 MAP0 PERM.
          assert(VALID1: Mem.valid_block (SimMemInj.src sm0) b_src).
          { rewrite MSRC in *. rewrite MINJ in *.
            inv HISTORY. inv MATCHARG; ss. clarify. rewrite H0 in *. rewrite INJ in *.
            clear - MLE0 VALID0 MAP0 PERM MWF0 MWF3 NB.
            apply NNPP. intro OUTSRC.
            destruct (SimMemInj.inj sm_arg b_src) eqn:T; ss.
            {
              destruct p; ss. clarify.
              exploit Mem.mi_freeblocks; et.
              { apply MWF3. }
              i; des. clarify.
            }
            inv MLE0.
            inv FROZEN.
            exploit NEW_IMPLIES_OUTSIDE; ss; eauto. i; des.
            unfold Mem.valid_block in *. rewrite NB in *. xomega.
          }
          inv MLE2.
          eapply MAXSRC; et.
        }
        {
          bar.
          inv STACKS; econs; et.
          inv AGL. econs; et.
        }
      }
      eapply match_states_return with (j:= sm_ret.(SimMemInj.inj)); eauto.
      * econs; ss; eauto. congruence.
      * eapply agree_regs_set_pair; cycle 1.
        { unfold typify. des_ifs. }
        (* TODO: Remove Mach.regset_after_external *)
        change regset_after_external with undef_caller_save_regs.
        eapply agree_regs_undef_caller_save_regs; eauto.
        eapply agree_regs_inject_incr; eauto.
        eapply inject_incr_trans; try apply MLE0. ss. apply MLE.
      * hexploit (parent_locset_after_external stack); et. i; des; clarify; ss.
        rewrite AFTER.
        eapply agree_callee_save_regs_undef_outgoing_slots.
        eapply agree_callee_save_regs_set_result.
        eapply agree_callee_save_regs_after; et.
      * bar. move HISTORY at bottom. inv HISTORY. inv MATCHARG. ss. clarify.
        rename sm0 into sm_at. rename sm1 into sm_after.
        rewrite RSP0 in *. clarify.
        hexpl Mem_nextblock_unfree NB.
        rewrite <- sep_assoc. rewrite sep_comm.
        rewrite <- sep_assoc in SEP0. rewrite sep_comm in SEP0. destruct SEP0 as (A & B & C).
        sep_split.
        { eapply globalenv_inject_incr_strong with (j:= sm_arg.(SimMemInj.inj)); eauto.
          - inv MLE0. ss.
          - eapply SimMemInj.inject_separated_frozen.
            inv MLE0. ss. inv MWF2.
            eapply SimMemInj.frozen_shortened; eauto.
            + refl.
            + refl.
          - rewrite <- NB0. inv MLE0; ss. clear - TGTUNCHANGED. change Pos.le with Ple. eauto with mem.
        }
        { ss. }
        rewrite sep_comm. rewrite sep_comm in B. destruct B as (D & E & F).
        sep_split.
        { ss. rp; try eapply MWF2; eauto with congruence. }
        { hexploit minjection_disjoint_footprint_private; eauto. intro PRIV0.
          rewrite MEMSRC. eapply minjection_private_disjoint_footprint.
          assert(SimMemInj.tgt_private sm_arg <2= SimMemInj.tgt_external sm_ret).
          { clear - MLE0. inv MLE0. ss. rewrite <- TGTPARENTEQ. ss. }
          inv MWF.
          etrans; try eassumption; eauto.
          etrans; try eassumption; eauto.

          etrans; try eassumption; eauto.
          etrans; cycle 1.
          { erewrite stack_contents_at_external_m_footprint; et. }
          erewrite <- stackframes_after_external_footprint. eapply stack_contents_footprint_irr; eauto.

        }
        assert(STEP0: SimMemInj.tgt sm_ret |= stack_contents_at_external (SimMemInj.inj sm_arg)
                                    cs cs'0 (SkEnv.get_sig skd)).
        { eapply m_invar; eauto. inv MLE0. ss. eapply Mem.unchanged_on_implies; eauto.
          ii. eapply minjection_disjoint_footprint_private; eauto. }

        assert(STEP1: SimMemInj.tgt sm_ret |= stack_contents_at_external (SimMemInj.inj sm_ret)
                                    cs cs'0 (SkEnv.get_sig skd)).
        { inv MLE0. eapply stack_contents_at_external_change_meminj; eauto. }

        eapply stack_contents_at_external_spec_elim; et.

  - (* final fsim *)
    inv FINALSRC. inv MATCH. inv MATCHST.
    exploit match_stacks_sp_ofs; eauto; intro RSP; des_safe.


    ss; clarify.
    (* des_ifs; sep_simpl_tac; des; ss. Undo 1. *)
    (* des_ifs; sep_simpl_tac; des_safe; ss. Undo 1. (*** TODO: Fix des_safe with check_safe!! ***) *)
    des.
    des_ifs; sep_simpl_tac; des; ss.
    (* unsguard AGLOCS. *)
    destruct st_tgt0; ss. clarify. ss. clarify. ss.
    inv STACKS.
    hexploit (loc_result_one init_sg); eauto. i; des_safe.
    Local Transparent stack_contents_args dummy_frame_contents.
    ss. unfold dummy_frame_contents in *. psimpl. clarify.
    hexploit (Mem.range_perm_free sm0.(SimMemInj.tgt) sp 0 (4 * (size_arguments init_sg))); eauto.
    { clear - SEP. apply sep_pick1 in SEP. rr in SEP. des. zsimpl. eauto with xomega. }
    intros (sm_tgt1 & FREETGT).

    assert(j = sm0.(SimMemInj.inj)).
    { inv MCOMPAT; ss. }
    clarify.

    exploit SimMemInj.free_right; eauto.
    { clear - SEP SPVALID.
      apply sep_drop_tail3 in SEP.
      destruct SEP as (A & B & DISJ). ss. des. zsimpl. clear_tac.
      ii. rr in DISJ.
      rr. esplits; eauto.
      specialize (DISJ sp ofs). ss.
      ii. exploit DISJ; eauto.
    }
    i; des_safe. rename sm1 into sm_ret.

    eexists sm_ret, (Retv.mk _ _). esplits; eauto; cycle 1.
    + econs; ss; eauto.
      * rewrite ONE. ss. specialize (AGREGS mr_res).
        eapply val_inject_incr; try apply MLE; eauto.
    + econs; eauto.
      * ii. specialize (AGCSREGS mr). ss. specialize (GOOD mr H). des_safe.
        rewrite <- AGCSREGS in *; ss.
        destruct (Val.eq (ls0 (R mr)) Vundef).
        { rewrite GOOD; ss. }
        specialize (AGREGS mr).
        clear - GOOD0 AGREGS n.
        inv GOOD0; inv AGREGS; try rewrite <- H in *; try rewrite <- H0 in *; ss; clarify.

  - (* step lemma *)
    left; i.
    esplits; eauto.
    { apply LinearC.modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@transf_step_correct prog rao skenv_link skenv_link ge tge); eauto.
    { apply make_match_genvs; eauto. apply SIMSKENV. }
    { inv STEPSRC. eauto. }
    { hexploit1 SOUND; ss. des. et. }
    i; des.
    destruct st_tgt0. ss. folder.
    r in STEPSRC; des.
    exploit (lift_plus (Mach.step rao) (fun st => get_stack st <> []) strong_wf_tgt); ss; et.
    { intros ? X Y. rr in X. des. rewrite Y in *. ss. }
    { i. folder. unfold strong_wf_tgt in *. des. inv HSTEP; ss; eauto.
      - des_ifs; ss; eauto.
      - des_ifs; ss; eauto. right. ii. inv HSTEP0; ss. }
    { ii. unfold strong_wf_tgt in *; des. inv HSTEP; try inv STACKS; ss; clarify; et; des_ifs; et. }
    { intro T. inv H0; ss; clarify; try inv STACKS; ss. }
    i; des.
    esplits; eauto.
    + left.
      eapply spread_dplus; et.
      { eapply modsem_determinate; eauto. }
      s. folder. eapply MachC.lift_plus; et.
    + econs; ss; et.
      * inv H0; inv MCOMPAT; ss.
      * inv H0; inv MCOMPAT; ss.
      * inv H0; ss.
      * esplits; et.
        { eapply LinearC.step_preserves_last_option; et. }
        { ii. exploit GOOD; et. i; des. esplits; et. eapply val_inject_incr; try apply MLE; et. }

Unshelve.
  all: ss.
  all: try (by econs).
  all: try apply Mem.empty.
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Variable rao: function -> code -> ptrofs -> Prop.
Hypothesis return_address_offset_exists:
  forall f sg ros c id (FUNCT: In (id, Gfun (Internal f)) (prog_defs tprog)),
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, rao f c ofs.
Hypothesis return_address_offset_deterministic:
  forall f c ofs ofs',
  rao f c ofs ->
  rao f c ofs' ->
  ofs = ofs'.
Hypothesis TRANSF: match_prog prog tprog.

Definition mp: ModPair.t := ModPair.mk (LinearC.module prog) (MachC.module tprog rao) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. des_ifs. esplits; eauto. eapply transf_function_sig; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. inv SIMSKENV. eapply sim_modsem; eauto.
    i. ss. uge0. des_ifs.
    unfold SkEnv.revive in *. apply Genv_map_defs_def in Heq. des. ss. gesimpl.
    apply Genv_map_defs_def in FIND. des. unfold o_bind, o_join, o_map in *. des_ifs. ss. clear_tac.
    eapply return_address_offset_exists; et.
    eapply in_prog_defmap; et.
Qed.

End SIMMOD.
