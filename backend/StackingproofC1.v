Require Import CoqlibC Errors.
Require Import Integers ASTC Linking.
Require Import ValuesC MemoryC Separation Events GlobalenvsC Smallstep.
Require Import LTL Op LocationsC LinearC MachC.
(* Require Import BoundsC Conventions StacklayoutC Lineartyping. *)
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Import Stacking.

Local Open Scope string_scope.
Local Open Scope sep_scope.

(* newly added *)
Require Export StackingproofC0.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC ArgPassing MatchSimModSem.
Require Import SimSymbId SimMemInj.

Set Implicit Arguments.



Section ALIGN.

  Lemma align_refl
        x
        (NONNEG: x >= 0)
  :
    <<ALIGN: align x x = x>>
  .
  Proof.
    destruct (Z.eqb x 0) eqn: T.
    { rewrite Z.eqb_eq in T. clarify. }
    rewrite Z.eqb_neq in T.
    red.
    unfold align.
    replace ((x + x - 1) / x) with 1.
    { xomega. }
    replace (x + x - 1) with (1 * x + (1 * x + (- 1))); cycle 1.
    { xomega. }
    rewrite Z.div_add_l; try eassumption.
    rewrite Z.div_add_l; try eassumption.
    replace (Z.div (Zneg xH) x) with (Zneg xH).
    { xomega. }
    destruct x; ss.
    clear - p.
    unfold Z.div. des_ifs.
    ginduction p; i; ss; des_ifs.
  Qed.

  Lemma align_zero
        x
    :
      <<ALIGN: align x 0 = 0>>
  .
  Proof.
    unfold align. red. ss.
    xomega.
  Qed.

  Lemma align_divisible
        z y
        (DIV: (y | z))
        (NONNEG: y > 0)
    :
      <<ALIGN: align z y = z>>
  .
  Proof.
    red.
    unfold align.
    replace ((z + y - 1) / y) with (z / y + (y - 1) / y); cycle 1.
    {
      unfold Z.divide in *. des. clarify.
      rewrite Z_div_mult; ss.
      replace (z0 * y + y - 1) with (z0 * y + (y - 1)); cycle 1.
      { xomega. }
      rewrite Z.div_add_l with (b := y); ss.
      xomega.
    }
    replace ((y - 1) / y) with 0; cycle 1.
    { erewrite Zdiv_small; ss. xomega. }
    unfold Z.divide in *. des. clarify.
    rewrite Z_div_mult; ss.
    rewrite Z.add_0_r.
    xomega.
  Qed.

  Lemma align_idempotence
        x y
        (NONNEG: y > 0)
    :
      <<ALIGN: align (align x y) y = align x y>>
  .
  Proof.
    apply align_divisible; ss.
    apply align_divides; ss.
  Qed.

End ALIGN.

Hint Rewrite align_refl: align.
Hint Rewrite align_zero: align.
Hint Rewrite align_idempotence: align.




Local Opaque Z.add Z.mul Z.div.

(* Section DUMMY_FUNCTION. *)

(*   Variable sg: signature. *)
  
(*   Lemma dummy_function_used_callee_save *)
(*     : *)
(*     (dummy_function sg).(function_bounds).(used_callee_save) = [] *)
(*   . *)
(*   Proof. ss. Qed. *)

(*   Lemma dummy_function_bound_local *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(bound_local) = 0 *)
(*   . *)
(*   Proof. ss. Qed. *)

(*   Lemma dummy_function_bound_outgoing *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(bound_outgoing) = (size_arguments sg) *)
(*   . *)
(*   Proof. *)
(*     ss. unfold dummy_function. cbn. *)
(*     rewrite Z.max_l; try xomega. rewrite Z.max_r; try xomega. *)
(*     generalize (size_arguments_above sg). i. xomega. *)
(*   Qed. *)

(*   Lemma dummy_function_bound_stack_data *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(bound_stack_data) = 0 *)
(*   . *)
(*   Proof. ss. Qed. *)

(*   Lemma dummy_function_size_callee_save_area *)
(*         ofs *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(size_callee_save_area) ofs = ofs *)
(*   . *)
(*   Proof. ss. Qed. *)

(*   Lemma dummy_function_fe_ofs_local *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_local) = (align (4 * size_arguments sg) 8 + 8) *)
(*   . *)
(*   Proof. *)
(*     unfold make_env. ss. des_ifs_safe. *)
(*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *)
(*     { generalize (size_arguments_above sg). i. xomega. } *)
(*     rewrite align_divisible; try xomega. *)
(*     apply Z.divide_add_r; try xomega. *)
(*     - apply align_divides; auto. xomega. *)
(*     - reflexivity. *)
(*   Qed. *)

(*   Lemma dummy_function_fe_ofs_link *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_link) = (align (4 * size_arguments sg) 8) *)
(*   . *)
(*   Proof. *)
(*     unfold make_env. ss. des_ifs_safe. *)
(*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *)
(*     { generalize (size_arguments_above sg). i. xomega. } *)
(*     ss. *)
(*   Qed. *)

(*   Lemma dummy_function_fe_ofs_retaddr *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_retaddr) = (align (4 * size_arguments sg) 8 + 8) *)
(*   . *)
(*   Proof. *)
(*     unfold make_env. ss. des_ifs_safe. *)
(*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *)
(*     { generalize (size_arguments_above sg). i. xomega. } *)
(*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     { apply align_divides. xomega. } *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     { apply align_divides. xomega. } *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     apply Z.divide_add_r; try xomega. *)
(*     - apply align_divides; auto. xomega. *)
(*     - reflexivity. *)
(*   Qed. *)

(*   Lemma dummy_function_fe_size *)
(*     : *)
(*       (dummy_function sg).(function_bounds).(make_env).(fe_size) = (align (4 * size_arguments sg) 8 + 8 + 8) *)
(*   . *)
(*   Proof. *)
(*     unfold make_env. *)
(*     (*??????????????? simpl. -> inf loop, but cbn works!!!!!!!!!!!!! *) *)
(*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *)
(*     { generalize (size_arguments_above sg). i. xomega. } *)
(*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     { apply align_divides. xomega. } *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     { apply align_divides. xomega. } *)
(*     rewrite align_divisible; try xomega; cycle 1. *)
(*     apply Z.divide_add_r; try xomega. *)
(*     - apply align_divides; auto. xomega. *)
(*     - reflexivity. *)
(*   Qed. *)

(* End DUMMY_FUNCTION. *)

(* Hint Rewrite dummy_function_used_callee_save: dummy. *)
(* Hint Rewrite dummy_function_bound_local: dummy. *)
(* Hint Rewrite dummy_function_bound_outgoing: dummy. *)
(* Hint Rewrite dummy_function_bound_stack_data: dummy. *)
(* Hint Rewrite dummy_function_size_callee_save_area: dummy. *)
(* Hint Rewrite dummy_function_fe_ofs_local: dummy. *)
(* Hint Rewrite dummy_function_fe_ofs_link: dummy. *)
(* Hint Rewrite dummy_function_fe_ofs_retaddr: dummy. *)
(* Hint Rewrite dummy_function_fe_size: dummy. *)

Print typesize.
Print loc_arguments_64. (* always + 2 *)
(* Lemma loc_arguments_64_complete *)
(*       x tys ir fr *)
(*       (SIZE0: x < 4 * size_arguments_64 tys ir fr 0) *)
(*       (SIZE1: 0 <= x) *)
(*       (IR: 0 <= ir) *)
(*       (FR: 0 <= fr) *)
(*   : *)
(*     exists sl pos ty, <<IN: In (S sl pos ty) (loc_arguments_64 tys ir fr 0).(regs_of_rpairs)>> *)
(*                             /\ <<OFS: pos <= x < pos + 4 * ty.(typesize)>> *)
(* . *)
(* Proof. *)
(*   ginduction tys; ii; ss. *)
(*   { xomega. } *)
(*   destruct a; ss. *)
(*   - des. *)
(*     des_ifs; try (exploit IHtys; eauto; try xomega; i; des; []; esplits; eauto; ss; right; eauto). *)
(*     assert(6 <= ir). *)
(*     { xomega. } *)
(*     ss. esplits; eauto; try xomega. ss. rewrite Z.add_0_l in *. rewrite Z.mul_1_r. *)
(*     unfold size_arguments_64 in SIZE0. ss. des_ifs. *)
(*     u in SIZE0. *)
(*     destruct ir; try xomega. *)
(*     ss. *)
(*   - *)
(* Qed. *)

(* Lemma size_arguments_loc_arguments *)
(*       ofs sg *)
(*       (SIZE: 0 <= ofs < 4 * size_arguments sg) *)
(*   : *)
(*     exists sl pos ty, In (S sl pos ty) (loc_arguments sg).(regs_of_rpairs) *)
(* . *)
(* Proof. *)
(*   destruct sg; ss. unfold size_arguments in *. unfold loc_arguments in *. des_ifs_safe. ss. clear_tac. *)
(*   ginduction sig_args; ii; ss. *)
(*   { xomega. } *)
(* Qed. *)




Section SEPARATIONC.

  Lemma disjoint_footprint_drop_empty
        P Q0 Q1
        (EMPTY: Q0.(m_footprint) <2= bot2)
        (DISJ: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (Q0 ** Q1)>>
  .
  Proof.
    ii. ss. unfold disjoint_footprint in *. des; eauto.
    eapply EMPTY; eauto.
  Qed.

  Lemma disjoint_footprint_mconj
        P Q0 Q1
        (DISJ0: disjoint_footprint P Q0)
        (DISJ1: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (mconj Q0 Q1)>>
  .
  Proof.
    ii. ss. unfold disjoint_footprint in *. des; eauto.
  Qed.

  Lemma disjoint_footprint_sepconj
        P Q0 Q1
        (DISJ0: disjoint_footprint P Q0)
        (DISJ1: disjoint_footprint P Q1)
  :
    <<DISJ: disjoint_footprint P (Q0 ** Q1)>>
  .
  Proof.
    ii. ss. unfold disjoint_footprint in *. des; eauto.
  Qed.

  (* Lemma mconj_sym *)
  (*       P Q *)
  (*   : *)
  (*     <<EQ: massert_eqv (mconj P Q) (mconj Q P)>> *)
  (* . *)
  (* Proof. *)
  (*   red. *)
  (*   split; ii. *)
  (*   - econs. *)
  (*     + ii. unfold mconj in *. ss. des; ss. *)
  (*     + ii. ss. des; eauto. *)
  (*   - econs. *)
  (*     + ii. unfold mconj in *. ss. des; ss. *)
  (*     + ii. ss. des; eauto. *)
  (* Qed. *)

  Lemma massert_eq
        pred0 footprint0 INVAR0 VALID0
        pred1 footprint1 INVAR1 VALID1
        (EQ0: pred0 = pred1)
        (EQ1: footprint0 = footprint1)
    :
      Build_massert pred0 footprint0 INVAR0 VALID0 = Build_massert pred1 footprint1 INVAR1 VALID1
  .
  Proof.
    clarify.
    f_equal.
    apply Axioms.proof_irr.
    apply Axioms.proof_irr.
  Qed.

  Axiom prop_ext: ClassicalFacts.prop_extensionality.

  Lemma mconj_sym
        P Q
    :
      <<EQ: (mconj P Q) = (mconj Q P)>>
  .
  Proof.
    apply massert_eq; ss.
    - apply Axioms.functional_extensionality. ii; ss.
      apply prop_ext.
      split; i; des; split; ss.
    - apply Axioms.functional_extensionality. ii; ss.
      apply Axioms.functional_extensionality. ii; ss.
      apply prop_ext.
      split; i; des; eauto.
  Qed.

End SEPARATIONC.













Section SIMMODSEM.

Local Existing Instance Val.mi_normal.
Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Variable rao: Mach.function -> Mach.code -> ptrofs -> Prop.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).

Definition msp: ModSemPair.t :=
  ModSemPair.mk (LinearC.modsem skenv_link_src prog) (MachC.modsem rao skenv_link_tgt tprog) tt
.

Inductive match_states (rs_init_src rs_init_tgt: regset)
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Linear.state) (st_tgt0: Mach.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt)
    (MATCHST: StackingproofC0.match_states prog tprog rao st_src0 st_tgt0)
    (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0)
    (* TODO: put sm intside match_states. j is actually sm0.(inj) *)
    (MWF: SimMem.wf sm0)
    (* (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge) *)
.

Lemma functions_translated_inject
      j
      (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge)
      (SIMGE0: DUMMY_PROP) (* globalenv_inject match_globalenvs *)
      fptr_src fd_src
      (FUNCSRC: Genv.find_funct ge fptr_src = Some fd_src)
      fptr_tgt
      (INJ: Val.inject j fptr_src fptr_tgt)
  :
    exists fd_tgt,
      <<FUNCTGT: Genv.find_funct tge fptr_tgt = Some fd_tgt>>
      /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>>
.
Proof.
  admit "ez".
Qed.

Global Program Instance mem_unchanged_on_PreOrder P: RelationClasses.PreOrder (Mem.unchanged_on P).
Next Obligation. ii; ss. eapply Mem.unchanged_on_refl. Qed.
Next Obligation. ii; ss. eapply Mem.unchanged_on_trans; eauto. Qed.

Local Opaque sepconj.
Local Opaque function_bounds.
Local Opaque make_env.
Ltac sep_split := econs; [|split]; swap 2 3.
Hint Unfold fe_ofs_arg.
Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *)
Hint Unfold to_mregset.
Ltac perm_impl_tac := eapply Mem.perm_implies with Freeable; [|eauto with mem].

Lemma delta_range
      F m_src m_tgt
      (INJECT: Mem.inject F m_src m_tgt)
      fd_src fd_tgt
      (TRANSFUNC: transf_function fd_src = OK fd_tgt)
      blk_src blk_tgt delta
      (INJVAL: F blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_src blk_src 0 (4 * size_arguments (Linear.fn_sig fd_src)) Cur Freeable)
      (SIZEARG: 0 < 4 * size_arguments (Linear.fn_sig fd_src) <= Ptrofs.max_unsigned)
  :
   <<DELTA: 0 <= delta <= Ptrofs.max_unsigned>> /\
   <<DELTA: 4 * size_arguments (Linear.fn_sig fd_src) + delta <= Ptrofs.max_unsigned>>
.
Proof.
  unfold NW.
  split.
  - exploit Mem.mi_representable; eauto; cycle 1.
    { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. }
    left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max.
    perm_impl_tac. eapply PERM. split; try xomega.
  - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1.
    { instantiate (1:= (4 * size_arguments (Linear.fn_sig fd_src)).(Ptrofs.repr)).
      rewrite Ptrofs.unsigned_repr; cycle 1.
      { split; try xomega. }
      i. des. xomega.
    }
    right.
    rewrite Ptrofs.unsigned_repr; cycle 1.
    { split; try xomega. }
    eapply Mem.perm_cur_max. perm_impl_tac.
    eapply PERM. split; try xomega.
Qed.

Theorem init_match_states
        sm_arg
        (SIMSKENV: SimSymb.sim_skenv sm_arg tt (SkEnv.project skenv_link_src (defs prog))
                                     (SkEnv.project skenv_link_tgt (defs tprog)))
        (MWF: SimMem.wf sm_arg)
        rs_arg_src rs_arg_tgt
        (SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt)
        st_init_src
        (INITSRC: LinearC.initial_frame skenv_link_src prog rs_arg_src sm_arg.(src_mem) st_init_src)
  :
    exists st_init_tgt sm_init idx_init,
    <<INITTGT: initial_frame skenv_link_tgt tprog rs_arg_tgt sm_arg.(tgt_mem) st_init_tgt >> /\
    <<MCOMPAT: mem_compat (LinearC.modsem skenv_link_src prog) (modsem rao skenv_link_tgt tprog)
                          st_init_src st_init_tgt sm_init >> /\
    <<MLE: SimMem.le sm_arg sm_init >> /\
    <<MATCH: match_states rs_arg_src rs_arg_tgt sm_arg idx_init st_init_src st_init_tgt sm_init>>
.
Proof.
  ss.
  inv INITSRC.
  assert(RSPINJ:= SIMRS SP).
  assert(PCINJ:= SIMRS PC).
  dup DB. inv DB. ss. inv DC. inv CB. ss.
  exploit (functions_translated_inject); eauto.
  { admit "sim ge". }
  intro FPTRTGT; des.
  destruct fd_tgt; ss; unfold bind in *; ss; des_ifs.
  rename fd into fd_src. rename f into fd_tgt.
  ss. rewrite RSPPTR in *. inv RSPINJ.
  rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ.
  rename blk into sp_src. rename b2 into sp_tgt.
  rename m_init into m_init_src.
  rewrite Ptrofs.add_zero_l in *.
  hexploit Mem.free_range_perm; eauto. intro PERMSRC.
  set (sm_init := (mk sm_arg.(inj)
                   sm_arg.(src_private) sm_arg.(tgt_private)
                   sm_arg.(src_external) sm_arg.(tgt_external)
                   m_init_src sm_arg.(tgt_mem)
                   sm_arg.(src_mem_parent) sm_arg.(tgt_mem_parent))).
  exploit Mem.free_result; eauto. i; des. clarify.
  assert(MWF0: SimMem.wf sm_init).
  { ss. econs; ss; try apply MWF; eauto.
    + eapply Mem.free_left_inject; eauto. apply MWF.
    + etransitivity; try apply MWF; eauto. admit "ez".
  }
  eexists _, sm_init, 0%nat; cbn.
  esplits; eauto.
  - econs; eauto.
  - ss.
  - ss. econs; ss; eauto.
    + admit "drop_perm ez".
    + reflexivity.
    + eapply frozen_refl.
    + admit "drop_perm ez".
    + reflexivity.
  - ss.
    econs; ss; eauto.
    assert(PTRRA: is_ptr (rs_arg_tgt RA)).
    { u in RAPTR. des_ifs. specialize (SIMRS RA). rewrite Heq0 in *. inv SIMRS; ss. }
    (* autounfold with * in PTRRA. *)
    (* u in PTRRA. des_ifs. clear_tac. *)
    (* rename b into ra. rename i into delta_ra. *)
    rename delta into delta_sp. clear_tac.

    econs; eauto.
    + econs 1; eauto; cycle 1.
      { rewrite RSPPTRTGT. ss. }
      i.
      assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)).
      { eapply loc_arguments_acceptable_2; eauto. }
      assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty).
      { destruct ACC. unfold slot_valid, proj_sumbool.
        rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. }
      {
        intros; red.
          eapply Z.le_trans with (size_arguments _); eauto.
          apply loc_arguments_bounded; eauto.
        u.
        xomega.
      }
    + ii.
      ss. u. eapply SIMRS; eauto.
    + ii. des_ifs.
    + u. des_ifs.
      rename Heq0 into RSPTGT.
      assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) ->
                    0 <= delta_sp <= Ptrofs.max_unsigned
                    /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned).
      { i; eapply delta_range; eauto. apply MWF. admit "max_unsigned". (* xomega. *) }
      rewrite sep_comm. rewrite sep_assoc.
      sep_split.
      { simpl. apply MWF0. }
      { apply disjoint_footprint_drop_empty.
        { ss. }
        intros ? delta INJDUP. ii. ss. des. clarify.
        rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'.
        destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1.
        { omega. }
        special DELTA; ss. clear_tac.
        rewrite Ptrofs.unsigned_repr in *; try omega.
        (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *)
        assert(sp_src' = sp_src).
        { apply NNPP. intro DISJ.
          hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP.
          exploit OVERLAP; eauto.
          { eapply Mem.perm_free_3; eauto. }
          { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. }
          { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. }
        }
        clarify.
        hexploit (Mem_drop_perm_none_spec (src_mem sm_arg) sp_src 0
                                          (4 * size_arguments (Linear.fn_sig fd_src))); eauto. i; des.
        eapply INSIDE; eauto. omega.
      }
      sep_split.
      { ss. admit "sim_genv". }
      { ss. }
{
  ss. rewrite Ptrofs.unsigned_repr_eq.
  assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus).
  { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. }
  split; eauto.
  split; eauto.
  { eapply POSBOUND. }
  destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1.
  { esplits; auto.
    - specialize (POSBOUND delta_sp). xomega.
    - ii. xomega.
    - i. generalize (typesize_pos ty). i. xomega.
  }
  special DELTA; ss.
  des.
  specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *.
  erewrite Z.mod_small; try xomega.
  split; try xomega.
  Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name].
  dsplit_r; try xomega.
  { rewrite Z.add_comm.
    change (delta_sp) with (0 + delta_sp).
    eapply Mem.range_perm_inject; try apply MWF; eauto.
  }
  ii; des.
  {
    assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (tgt_mem sm_arg) sp_tgt (delta_sp + 4 * ofs) = Some v).
    { eapply Mem.valid_access_load; eauto.
      hnf.
      rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk.
      split; try xomega.
      - ii. perm_impl_tac. eapply DSPLIT. xomega.
      - apply Z.divide_add_r.
        + rewrite <- align_type_chunk.
          eapply Mem.mi_align; try apply MWF; eauto.
          instantiate (1:= Nonempty).
          instantiate (1:= 0).
          rewrite Z.add_0_l.
          ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC.
          rewrite <- PLAYGROUND.typesize_chunk in *. xomega.
        + apply Z.mul_divide_mono_l. ss.
    }
    des.
    esplits; eauto.
    des_ifs; try (by econs; eauto).
    Local Opaque Ptrofs.modulus.
    unfold load_stack in *. ss.
    rewrite ! Ptrofs.add_zero_l in *. unfold fe_ofs_arg in *. rewrite Z.add_0_l in *.
    exploit Mem.load_inject; try apply MWF; eauto. intro LOADTGT0; des.
    assert(v = v2).
    { erewrite Ptrofs.unsigned_repr in LOADTGT0; eauto. rewrite Z.add_comm in LOADTGT0. clarify.
      split; try xomega.
      admit " < sz_arg < ptrofs.max_unsigned".
    }
    clarify.
  }
}
Qed.

Lemma match_stacks_parent_sp
      j cs stack sg
      (MATCH: match_stacks tprog j cs stack sg)
  :
    <<RSPPTR: is_real_ptr (parent_sp stack)>>
.
Proof.
  induction MATCH; ss.
Qed.

Definition update_meminj (F: meminj) (blk_src blk_tgt: block) (delta: Z): meminj :=
  fun blk: block => if eq_block blk blk_src then Some (blk_tgt, delta) else F blk
.
Hint Unfold update_meminj.

Lemma no_overlap_equiv
      F m0 m1
      (PERM: all4 (Mem.perm m0 <4> Mem.perm m1))
      (OVERLAP: Mem.meminj_no_overlap F m0)
  :
    <<OVERLAP: Mem.meminj_no_overlap F m1>>
.
Proof.
  ii; ss. eapply OVERLAP; eauto; eapply PERM; eauto.
Qed.

Lemma update_no_overlap
      F m0
      (OVERLAP: Mem.meminj_no_overlap F m0)
      sz blk_src blk_tgt delta m1
      (ALLOC: Mem.alloc m0 0 sz = (m1, blk_src))
      (PRIVTGT: forall
          ofs
          (SZ: 0 <= ofs < sz)
        ,
          loc_out_of_reach F m0 blk_tgt (ofs + delta))
  :
    <<OVERLAP: Mem.meminj_no_overlap
                 (update_meminj F blk_src blk_tgt delta)
                 (* (fun blk: block => if eq_block blk_src blk then Some (blk_tgt, delta) else F blk) *)
                 m1>>
.
Proof.
  u.
  hnf. ii; ss.
  destruct (classic (b1' = b2')); cycle 1.
  { left; ss. }
  right. clarify.
  des_ifs; ss; cycle 1.
Admitted.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states); eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - (* INITFSIM *)
    exploit init_match_states; eauto. i; des.
    esplits; eauto.
  - (* ATPROGRESS *)
    (* NNNNNNNNNNNNNNNNNNNNNNNNOTE WE CAN DO FSIM HERE TOO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
    inv MATCH.
    esplits; eauto.
    u in CALLSRC. des.
    destruct sm0; ss. inv MCOMPAT; ss. des. clarify.
    inv CALLSRC; ss. inv MATCHST; ss.
    fold_all ge.
    u.
    inv BD. inv BC.
    esplits; eauto.
    econs; eauto.
    + fold_all tge.
      admit "this should hold. is_call_progress".
    + econs; eauto.
      { reflexivity. }
      instantiate (1:= fake_ptr_one). ss.
    (* inv STORE; ss. *)
    (* u in PCPTR. des_ifs. clear_tac. ss. *)
    (* destruct b0; ss; cycle 1. *)
    (* { inv FPTR. ss. esplits; eauto. econs; eauto. } *)
    (* destruct (Genv.find_funct tge tfptr) eqn:T; cycle 1. *)
    (* { esplits; eauto. econs; eauto. } *)
    (* unfold Genv.find_funct in *. des_ifs_safe; inv FPTR; ss. *)
    (* assert(delta = 0). *)
    (* { admit "by genv match". } *)
    (* clarify. rewrite Ptrofs.add_zero in *. clarify. *)
    (* des_ifs. *)
    (* esplits; eauto. *)
    (* econs; eauto. *)
    (* ss. fold_all tge. des_ifs. *)
    (* admit "by genv match". *)
  - (* ATFSIM *)
    revert_until MATCH.
    assert(ATFSIM: forall
              rs_arg_src m_arg_src
              (ATSRC: LinearC.at_external skenv_link_src prog st_src0 rs_arg_src m_arg_src)
            ,
              exists (rs_arg_tgt : regset) (m_arg_tgt : mem) (sm_arg : t'),
                (<<ATEXT: MachC.at_external skenv_link_tgt tprog st_tgt0 rs_arg_tgt m_arg_tgt >>) /\
                (<<MSRC: src_mem sm_arg = m_arg_src >>) /\
                (<<MTGT: tgt_mem sm_arg = m_arg_tgt >>) /\
                (<<SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt >>) /\
                (<<MLE: le' sm0 sm_arg >>) /\ (<<MWF: wf' sm_arg >>)).
{
  ii; ss.
  inv ATSRC; ss. inv BD. inv BC.
  rename blk into sp_src.
  inv MATCH; ss. inv MATCHST; ss.
  assert(ARGSTGT: forall l (IN: In l (regs_of_rpairs (loc_arguments sg_arg))),
            (exists v : val, Mach.extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls_arg l) v)).
  { eapply transl_external_argument; eauto. apply sep_pick1 in SEP. eauto. }
  inv MCOMPAT; ss. des. clarify.
  assert(sm0.(inj) = j).
  { admit "put sm inside match_states". }
  clarify.
  exploit match_stacks_parent_sp; eauto. i; des.
  u in H. des_ifs. clear_tac. rename b into sp_tgt. rename i into spdelta.
  set (sm_arg := (mk (fun blk => if eq_block blk sp_src
                                 then Some (sp_tgt, spdelta.(Ptrofs.unsigned))
                                 else sm0.(inj) blk)
                     sm0.(src_private) sm0.(tgt_private)
                     sm0.(src_external) sm0.(tgt_external)
                     m_arg_src sm0.(tgt_mem)
                     sm0.(src_mem_parent) sm0.(tgt_mem_parent))).
  unfold load_stack in *. ss.

  exploit (@B2C_mem_spec sg_arg m_alloc sp_src ls_arg); eauto.
  { eapply Mem_alloc_range_perm; eauto. }
  i; des. clarify.

  assert(MLE: SimMem.le sm0 sm_arg).
  {
    subst sm_arg.
    econs; cbn; eauto with mem; try xomega.
    - ii; ss. des_ifs; ss. exfalso.
      exploit Mem.mi_freeblocks; try apply MWF; eauto.
      { eauto with mem. }
      i; ss. clarify.
    - eapply Mem_unchanged_on_trans_strong; eauto.
      { eapply Mem.alloc_unchanged_on; eauto. }
      eapply Mem.unchanged_on_implies; eauto. cbn. admit "ez".
    - econs; eauto.
      ii; ss. des; ss. des_ifs.
      split; ss.
      + admit "ez".
      + admit "we should add this into match_states".
    - admit "ez".
  }
  exploit Mem.alloc_result; eauto. i; des. clarify.
  exploit Mem.nextblock_alloc; eauto. intro ALLOCNB.
  assert(MWF0: SimMem.wf sm_arg).
  { subst sm_arg.
    econs; cbn; try apply MWF; eauto.
    -


      assert(spdelta = Ptrofs.zero).
      { inv STACKS; ss; clarify.
      }
      assert(Mem.inject
               (fun blk : block =>
                  if eq_block blk (Mem.nextblock (src_mem sm0))
                  then Some (sp_tgt, Ptrofs.unsigned spdelta)
                  else inj sm0 blk) m_alloc sm0.(tgt_mem)).
      { eapply Mem_alloc_left_inject. }




      move MWF at bottom. inv MWF. clear_until PUBLIC.
      econs; eauto; unfold Mem.valid_block in *.
      + inv PUBLIC.
        econs; ss; eauto.
        * ii; des_ifs; ss; cycle 1.
          { eapply mi_inj; eauto. rewrite <- PERM in *; ss. eapply Mem.perm_alloc_4; eauto. }
          admit "????????????????".
          (* assert(ARGSRC: exists pos ty, *)
          (*           In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg_arg)) /\ *)
          (*           pos <= ofs < pos + (typesize ty) * 4 *)
          (*       ). *)
          (* { admit "only turn on permission when it has argument". } *)
          (* des. exploit ARGSTGT; eauto. i; des. inv H. unfold load_stack in *; ss. *)
          (* exploit Mem.load_valid_access; eauto. *)
        * ii; des_ifs; ss; cycle 1.
          { eapply mi_inj; eauto. ii. exploit H0; eauto. i; des. rewrite <- PERM in *; ss.
            eapply Mem.perm_alloc_4; eauto. }
          admit "??".
        * ii; des_ifs; ss; cycle 1.
          { eapply memval_inject_incr; eauto; try apply MLE.
            inv mi_inj.
            admit "unchanged_on ez".
          }
          admit "??".
      + ii; des_ifs; ss; cycle 1.
        { apply PUBLIC. unfold Mem.valid_block in *. rewrite <- NB in *. rewrite ALLOCNB in *. xomega. }
        unfold Mem.valid_block in *. rewrite <- NB in *. rewrite ALLOCNB in *. xomega.
      + ii; des_ifs; ss; try (by eapply PUBLIC; eauto); cycle 1.
        inv STACKS; ss; clarify.
        { admit "strengthen match_stacks". }
        eapply PUBLIC; eauto.
      + eapply no_overlap_equiv; eauto. eapply update_no_overlap; try apply PUBLIC; eauto.
        { admit "loc_out_of_reach". }
      + ii; des_ifs; ss; cycle 1.
        { eapply PUBLIC; eauto. rewrite <- ! PERM in *. des; ss.
          - left. eapply Mem.perm_alloc_4; eauto.
          - right. eapply Mem.perm_alloc_4; eauto. }
        admit "somehow..".
      + admit "???".
    - ii; ss. hnf. des_ifs.
      + admit "wf -> valid_block".
      + inv MWF. eapply SRCDISJ; eauto.
    - admit "remove tgt private.
REFACTORING NEEDED !!!!!!!!
Note: we can just keep tgt_privae = bot in match_states. we make private right before call, and remove it again right after call.
IDEA: we only need 'external', not private. !!!!!!!!!
".
    - admit "ez".
    - admit "ez".
  }
  inv CD. ss.
  do 2 eexists. exists sm_arg. cbn.
  esplits; cbn; try reflexivity; eauto.
  - econs; eauto.
    + fold tge. admit "this should hold".
    + econs; eauto.
      * reflexivity.
  - u. i. destruct (to_mreg pr) eqn:T; ss.
    + unfold agree_regs in AGREGS.
      eapply val_inject_incr; eauto. eapply MLE.
    + des_ifs; try (by econs; eauto).
      * eapply val_inject_incr; eauto. apply MLE.
      * rewrite Heq. econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss.
      * u in RAPTR. des_ifs. econs; eauto.
}
  -
    +
  destruct (classic ((regs_of_rpairs (loc_arguments sg_arg)) = [])).
  { inv CD.
    do 2 eexists. eexists (mk _ _ _ _ _ _ _ _ _). cbn.
    esplits; cbn; try reflexivity; eauto.
    - econs; eauto.
      + fold tge. admit "this should hold".
      + econs; eauto. reflexivity.
    - u. i. destruct (to_mreg pr) eqn:T; ss.
      des_ifs; try (by econs; eauto).
      + unfold agree_regs in AGREGS.
        (fun blk =>
           if eq_block blk sp_src
           then Some (sp_tgt, spofs_tgt.(Ptrofs.unsigned))
           else sm0.(inj) blk)
  }
  set (sm_arg := (mk (fun blk => if eq_block blk sp_src
                                 then Some (sp_tgt, spofs_tgt.(Ptrofs.unsigned))
                                 else sm0.(inj) blk)
                     sm0.(src_private) sm0.(tgt_private)
                     sm0.(src_external) sm0.(tgt_external)
                     m_arg_src sm0.(tgt_mem)
                     sm0.(src_mem_parent) sm0.(tgt_mem_parent))).
  esplits; eauto.
}

  - (* ATBSIM *)
    inv CALLTGT.
    inv MATCH; ss.
    inv MATCHST; ss.
    rename m into m_src.
    exploit transl_external_arguments; eauto.
    { apply sep_pick1 in SEP. eauto. }
    intro ARGS; des.

    bar. move SAFESRC at bottom. u in SAFESRC. des.
    rename m_arg into m_arg_src. rename rs_arg0 into rs_arg_src. inv SAFESRC. inv STORE.
    rename sp into sp_src. des. bar.

    fold_all ge. fold_all tge.
    exploit match_stacks_parent_sp; eauto. intro PTR; des. u in PTR. des_ifs.
    rename b into sp_tgt. rename i into spofs_tgt.
    set (sm_arg := (mk (fun blk => if eq_block blk sp_src
                                   then Some (sp_tgt, spofs_tgt.(Ptrofs.unsigned))
                                   else sm0.(inj) blk)
                       sm0.(src_private) sm0.(tgt_private)
                       sm0.(src_external) sm0.(tgt_external)
                       m_arg_src sm0.(tgt_mem)
                       sm0.(src_mem_parent) sm0.(tgt_mem_parent))).
    do 2 eexists; exists sm_arg. cbn.
    esplits; eauto.
    + econs; eauto.
      econs; eauto.
    + inv MCOMPAT; ss.
    + admit "ttttttttttttttttttttttttttttttttttttttt raw admit!!!!!!!!!!!!!!!!!!!8".
    + econs; eauto.
      * admit "this should hold".
      * admit "this should hold".
      * admit "this should hold".
      * admit "this should hold".
      * admit "this should hold".
      * admit "this should hold".
    + econs; ss; try apply MWF; eauto.
      *


        ttttttttttttttttttttttttt
    inv FPTR; ss.
    + esplits; eauto.
      instantiate (2:= mregset_of _). ss.
      Set Printing All.
      econs; eauto.
      eapply at_external_intro.
    econs; eauto.
    eapply at_external_intro.
    econs; eauto.
    inv CALLSRC.
    ss. u. des.
    esplits
    destruct sm_arg; ss. clarify.
    unfold SimMem.sim_regset in *. ss. apply Axioms.functional_extensionality in SIMRS. clarify.
    inv INITSRC.
    assert(SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge).
    { subst_locals. eapply sim_skenv_revive; eauto. { ii. clarify. u. des_ifs. } }
    esplits; eauto.
    + apply initial_frame_intro with (fd := transf_function fd); eauto.
      fold_all ge. fold_all tge. clearbody ge tge.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      inv SIMGE. specialize (mge_defs b). inv mge_defs; eq_closure_tac. unfold Genv.find_def. rewrite <- H0.
      inv H1; ss.
    + instantiate (1:= SimMemId.mk _ _). econs; ss; eauto.
    + u. repeat (econs; ss; eauto).
  - inv CALLSRC. des. inv MATCH. ss. destruct sm0; ss.
    inv MATCHST; inv H; ss; clarify.
    inv MCOMPAT. ss. fold_all ge. des. clarify.
    u. esplits; eauto.
    econs; eauto.
    fold_all tge.
    clearbody ge tge.
    admit "simskenv - ez".
  - inv CALLTGT. inv MATCH; ss. fold_all tge. u in *. destruct sm0; ss. inv MCOMPAT; ss. u in *. clarify.
    do 2 eexists. eexists (SimMemId.mk _ _).
    esplits; ss; eauto. inv MATCHST; ss.
    econs; eauto.
    u. fold_all ge.
    admit "simskenv - ez".
  - apply Axioms.functional_extensionality in SIMRSRET. clarify.
    apply Axioms.functional_extensionality in SIMRSARG. clarify.
    inv AFTERSRC. inv MATCH; ss. inv MCOMPAT. u in *. clarify.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    inv MATCHST; ss. des_ifs. clear_tac. destruct sm0; ss. clarify.
    destruct sm_ret; ss. clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      econs; eauto.
  - inv FINALSRC. inv MATCH; ss. inv MATCHST; ss. inv MCOMPAT0; ss. u in *. destruct sm0; ss. des_ifs.
    inv STACKS; ss. inv MCOMPAT; ss. u in *. des_ifs. clear_tac.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    esplits; eauto.
    + apply final_frame_intro with (fd:= transf_function fd); eauto.
      fold_all ge. u. fold_all tge.
      admit "simskenv - ez".
    + ii; ss.
  - esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    ii. hexploit (@step_simulation prog ge tge); eauto.
    { ii. eapply not_external; eauto. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
    + econs; ss; eauto.
Unshelve.
  all: try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - econs; eauto. admit "easy".
  - ii. eapply sim_modsem; eauto.
Qed.

End SIMMOD.






Section PRESERVATION.

Local Existing Instance Val.mi_normal.
Context `{SimSymbId: @SimSymb.SimSymb.class SimMemInj}.
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Variable return_address_offset: function -> code -> ptrofs -> Prop.
Let match_states := match_states prog tprog return_address_offset.

Lemma functions_translated_inject
      j
      (GENV: True)
      fptr_src fd_src
      (FUNCSRC: Genv.find_funct (Genv.globalenv prog) fptr_src = Some fd_src)
      fptr_tgt
      (INJ: Val.inject j fptr_src fptr_tgt)
  :
    exists fd_tgt,
      <<FUNCTGT: Genv.find_funct (Genv.globalenv tprog) fptr_tgt = Some fd_tgt>>
      /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>>
.
Proof.
  admit "easy".
Qed.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (LinearC.modsem prog) (MachC.modsem return_address_offset tprog) (admit "simsymb") Nat.lt.

Local Transparent dummy_stack.

Ltac sep_split := econs; [|split]; swap 2 3.
Hint Unfold fe_ofs_arg.
Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *)
Hint Unfold mregset_of.
Ltac perm_impl_tac := eapply Mem.perm_implies with Writable; [|eauto with mem].

Lemma match_stack_contents
      sm_init
      (MWF: SimMem.SimMem.wf sm_init)
      ra_blk delta_ra
      rs_init_src rs_init_tgt
      (RSREL: (SimMem.SimMem.sim_regset) sm_init rs_init_src rs_init_tgt)
      (RA: rs_init_tgt RA = Vptr ra_blk delta_ra true)
      fd_src fd_tgt
      (FINDFSRC: Genv.find_funct (Genv.globalenv prog) (rs_init_src PC) = Some (Internal fd_src))
      (FINDFTGT: Genv.find_funct (Genv.globalenv tprog) (rs_init_tgt PC) = Some (Internal fd_tgt))
      (TRANSFF: transf_function fd_src = OK fd_tgt)
      ls_init vs_init m_init_src
      (LOADARGSSRC: load_arguments rs_init_src (src_mem sm_init) (Linear.fn_sig fd_src) vs_init m_init_src)
      (LOCSET: fill_arguments (Locmap.init Vundef) vs_init (Linear.fn_sig fd_src).(loc_arguments)
               = Some ls_init)
      sp_src sp_tgt delta_sp
      (RSPSRC: rs_init_src RSP = Vptr sp_src Ptrofs.zero true)
      (RSPTGT: rs_init_tgt RSP = Vptr sp_tgt (Ptrofs.repr delta_sp) true)
      (RSPINJ: inj sm_init sp_src = Some (sp_tgt, delta_sp))
  :
    <<MATCHSTACK:
    sm_init.(tgt_mem) |= stack_contents tprog return_address_offset (inj sm_init)
                      [LinearC.dummy_stack (Linear.fn_sig fd_src) ls_init]
                      [dummy_stack (rs_init_tgt RSP) (Vptr ra_blk delta_ra true)] **
                      minjection (inj sm_init) m_init_src **
                      globalenv_inject (Genv.globalenv prog) sm_init.(inj)>>
.
Proof.
  u in RSREL.
Local Opaque sepconj.
Local Opaque function_bounds.
Local Opaque make_env.
  rewrite RSPTGT. u.
  unfold dummy_frame_contents.
  rewrite sep_comm. rewrite sep_assoc.
  inv LOADARGSSRC. rename PERM into PERMSRC. rename VAL into VALSRC. rename DROP into DROPSRC.
  rewrite RSPSRC in *. clarify. rename sp into sp_src.
  assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) ->
                0 <= delta_sp <= Ptrofs.max_unsigned
                /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned).
  {
    i.
    Print Mem.inject'.
    split.
    - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1.
      { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. }
      left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max.
      perm_impl_tac. eapply PERMSRC. split; try xomega.
    -
      assert(SZARGBOUND: 4 * size_arguments (Linear.fn_sig fd_src) <= Ptrofs.max_unsigned).
      {
        hexploit size_no_overflow; eauto. intro OVERFLOW.
        clear - OVERFLOW.
        Local Transparent function_bounds.
        Local Transparent make_env.
        u in *.
        ss.
        des_ifs. unfold function_bounds in *. cbn in *.
        admit "Add this in initial_frame of LinearC".
      }
      exploit Mem.mi_representable; try apply MWF; eauto; cycle 1.
      { instantiate (1:= (4 * size_arguments (Linear.fn_sig fd_src)).(Ptrofs.repr)).
        rewrite Ptrofs.unsigned_repr; cycle 1.
        { split; try xomega. }
        i. des. xomega.
      }
      right.
      rewrite Ptrofs.unsigned_repr; cycle 1.
      { split; try xomega. }
      eapply Mem.perm_cur_max. perm_impl_tac.
      eapply PERMSRC. split; try xomega.
  }
  assert(MINJ: Mem.inject (inj sm_init) m_init_src (tgt_mem sm_init)).
  { eapply Mem_set_perm_none_left_inject; eauto. apply MWF. }
  sep_split.
  { simpl. eassumption. }
  { apply disjoint_footprint_drop_empty.
    { ss. }
    intros ? delta INJDUP. ii. ss. des. clarify.
    rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'.
    destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1.
    { omega. }
    special DELTA; ss. clear_tac.
    rewrite Ptrofs.unsigned_repr in *; try omega.
    (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *)
    assert(sp_src' = sp_src).
    { apply NNPP. intro DISJ.
      hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP.
      exploit OVERLAP; eauto.
      { eapply Mem_set_perm_none_impl; eauto. }
      { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. }
      { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. }
    }
    clarify.
    hexploit Mem_set_perm_none_spec; eauto. i; des.
    eapply INSIDE; eauto. omega.
  }
  sep_split.
  { ss. admit "sim_genv". }
  { ss. }
  ss. rewrite Ptrofs.unsigned_repr_eq.
  assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus).
  { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. }
  split; eauto.
  split; eauto.
  { eapply POSBOUND. }
  destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1.
  { esplits; auto.
    - specialize (POSBOUND delta_sp). xomega.
    - ii. xomega.
    - i. generalize (typesize_pos ty). i. xomega.
  }
  special DELTA; ss.
  des.
  specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *.
  erewrite Z.mod_small; try xomega.
  split; try xomega.
  Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name].
  dsplit_r; try xomega.
  { rewrite Z.add_comm.
    change (delta_sp) with (0 + delta_sp).
    eapply Mem.range_perm_inject; try apply MWF; eauto.
  }
  ii; des.
  {
    rename H1 into OFS0. rename H2 into OFS1. rename H3 into OFS2.
    clear - VALSRC LOCSET PERMSRC DSPLIT (* DROPSRC *) RSPSRC RSPTGT RSPINJ OFS0 OFS1 OFS2 MWF.
    abstr (Linear.fn_sig fd_src) sg.
    unfold extcall_arguments in *.
    exploit fill_arguments_spec_slot; eauto.
    { admit "Add this in initial_frame of LinearC". }
    i; des.
    set (loc_arguments sg) as locs in *.
    assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (tgt_mem sm_init) sp_tgt (delta_sp + 4 * ofs) = Some v).
    { eapply Mem.valid_access_load; eauto.
      hnf.
      rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk.
      split; try xomega.
      - ii. perm_impl_tac. eapply DSPLIT. xomega.
      - apply Z.divide_add_r.
        + rewrite <- align_type_chunk.
          eapply Mem.mi_align; try apply MWF; eauto.
          instantiate (1:= Nonempty).
          instantiate (1:= 0).
          rewrite Z.add_0_l.
          ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC.
          rewrite <- PLAYGROUND.typesize_chunk in *. xomega.
        + apply Z.mul_divide_mono_l. ss.
    }
    destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs locs))).
    - exploit INSIDE; eauto. i; des.
      + rewrite Z.add_comm.
        eapply Mem.load_inject; try apply MWF; eauto.
      + rewrite UNDEF.
        esplits; eauto.
    - exploit OUTSIDE; eauto. intro LOCSRC; des.
      rewrite LOCSRC.
      exploit Mem.valid_access_load; eauto.
      { hnf. instantiate (2:= chunk_of_type ty).
        rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk.
        instantiate (1:= delta_sp + 4 * ofs).
        instantiate (1:= sp_tgt).
        instantiate (1:= sm_init.(tgt_mem)).
        split; try xomega.
        - ii. perm_impl_tac. eapply DSPLIT. xomega.
        - apply Z.divide_add_r.
          + rewrite <- align_type_chunk.
            eapply Mem.mi_align; try apply MWF; eauto.
            instantiate (1:= Nonempty).
            instantiate (1:= 0).
            rewrite Z.add_0_l.
            ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC.
            rewrite <- PLAYGROUND.typesize_chunk in *. xomega.
          + apply Z.mul_divide_mono_l. ss.
      }
  }
Qed.

Theorem init_match_states
        (sm_init: SimMem.SimMem.t) fptr_init_src fptr_init_tgt
        (FPTRREL: Val.inject (inj sm_init) fptr_init_src fptr_init_tgt)
        rs_init_src rs_init_tgt
        (RSREL: SimMem.SimMem.sim_regset sm_init rs_init_src rs_init_tgt)
        (WF: wf' sm_init)
        (SIMSKENV: ModSemPair.sim_skenv msp sm_init)
        st_init_src
        (INITSRC: LinearC.initial_frame prog rs_init_src sm_init.(src_mem) st_init_src)
  :
    exists st_init_tgt,
      <<INITTGT: initial_frame tprog rs_init_tgt (tgt_mem sm_init) st_init_tgt>>
                               /\ <<MATCH: match_states st_init_src st_init_tgt>>
.
Proof.
  ss. u in *. unfold ModSemPair.sim_skenv in *. ss. clear SIMSKENV.
  inv INITSRC.
  exploit (functions_translated_inject); eauto. intro FPTRTGT; des.
  destruct fd_tgt; ss; unfold bind in *; ss; des_ifs.
  rename fd into fd_src. rename f into fd_tgt.
  assert(RSPINJ:= RSREL SP).
  ss. rewrite RSPPTR in *. inv RSPINJ.
  rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ.
  rename sp into sp_src. rename b2 into sp_tgt. rename m_init into m_init_src.
  rewrite Ptrofs.add_zero_l in *.
  esplits; eauto.
  - econs; eauto.
  -
    assert(PTRRA: is_real_ptr (rs_init_tgt RA)).
    { admit "add to sem (of LinearC)". }
    u in PTRRA. des_ifs. clear_tac.
    rename b into ra. rename i into delta_ra. rename delta into delta_sp. clear_tac.

    econs; eauto.
    + econs 1; eauto; cycle 1.
      { rewrite RSPPTRTGT. ss. }
      i.
      assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)).
      { eapply loc_arguments_acceptable_2; eauto. }
      assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty).
      { destruct ACC. unfold slot_valid, proj_sumbool.
        rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. }
      {
        intros; red.
          eapply Z.le_trans with (size_arguments _); eauto.
          apply loc_arguments_bounded; eauto.
        u.
        xomega.
      }
    + ii.
      u in RSREL.
      u in RSREL. u.
      u.
      assert((ls_init (R r)) = Vundef \/ (ls_init (R r)) = rs_init_src (preg_of r)).
      { hexploit fill_arguments_spec_reg; eauto.
        { apply LOADARG. }
        i; des.
        specialize (H r). des.
        destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (Linear.fn_sig fd_src))))).
        - special INSIDE; ss. des; eauto.
        - special OUTSIDE; ss. eauto. }
      des.
      * rewrite H. econs; eauto.
      * rewrite H. eapply RSREL.
    + ii. des_ifs.
    + eapply match_stack_contents; eauto. ss.
Qed.

Theorem sim
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { admit "garbage". }
  ii.
  ss.
  split; ss.
Qed.

End PRESERVATION.
