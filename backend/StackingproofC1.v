Require Import CoqlibC Errors.
Require Import Integers ASTC Linking.
Require Import ValuesC Memory Separation Events GlobalenvsC Smallstep.
Require Import LTL Op Locations LinearC MachC.
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Import Stacking.

Local Open Scope sep_scope.

(* newly added *)
Require Import sflib.
Require Export StackingproofC0.
Require Import SimModSem.
Require Import SimMemInj.
Require SimSymb.
Require Import Asmregs.

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





Section DUMMY_FUNCTION.

  Variable sg: signature.
  
  Lemma dummy_function_used_callee_save
    :
    (dummy_function sg).(function_bounds).(used_callee_save) = []
  .
  Proof. ss. Qed.

  Lemma dummy_function_bound_local
    :
      (dummy_function sg).(function_bounds).(bound_local) = 0
  .
  Proof. ss. Qed.

  Lemma dummy_function_bound_outgoing
    :
      (dummy_function sg).(function_bounds).(bound_outgoing) = (size_arguments sg)
  .
  Proof.
    ss. unfold dummy_function. cbn.
    rewrite Z.max_l; try xomega. rewrite Z.max_r; try xomega.
    generalize (size_arguments_above sg). i. xomega.
  Qed.

  Lemma dummy_function_bound_stack_data
    :
      (dummy_function sg).(function_bounds).(bound_stack_data) = 0
  .
  Proof. ss. Qed.

  Lemma dummy_function_size_callee_save_area
        ofs
    :
      (dummy_function sg).(function_bounds).(size_callee_save_area) ofs = ofs
  .
  Proof. ss. Qed.

  Hint Rewrite dummy_function_size_callee_save_area: dummy.

  Lemma dummy_function_fe_size
    :
      (dummy_function sg).(function_bounds).(make_env).(fe_size) = 0
  .
  Proof.
    unfold make_env.
    (*??????????????? simpl. -> inf loop, but cbn works!!!!!!!!!!!!! *)
    cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1.
    { generalize (size_arguments_above sg). i. xomega. }
    autorewrite with align. des_ifs.
  Abort.

End DUMMY_FUNCTION.

Hint Rewrite dummy_function_used_callee_save: dummy.
Hint Rewrite dummy_function_bound_local: dummy.
Hint Rewrite dummy_function_bound_outgoing: dummy.
Hint Rewrite dummy_function_bound_stack_data: dummy.
Hint Rewrite dummy_function_size_callee_save_area: dummy.

Local Opaque Z.add Z.mul Z.div.


Print typesize.
Print loc_arguments_64. (* always + 2 *)
(* Lemma size_arguments_loc_arguments_64 *)
(*       x tys ir fr *)
(*       (SIZE: 0 <= x < 4 * size_arguments_64 tys ir fr 0) *)
(*   : *)
(*     exists sl pos ty, In (S sl pos ty) (loc_arguments_64 tys ir fr 0).(regs_of_rpairs) *)
(* . *)
(* Proof. *)
(*   ginduction tys; ii; ss. *)
(*   { xomega. } *)
(*   destruct a; ss. *)
(*   - des_ifs. *)
(*     + esplits; eauto. *)
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

Section PRESERVATION.

Local Existing Instance Val.mi_normal.
Context `{SimSymbId: @SimSymb.SimSymb.class SimMemInj}.
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Variable return_address_offset: function -> code -> ptrofs -> Prop.
Let match_states := match_states prog tprog return_address_offset.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (LinearC.modsem prog) (MachC.modsem return_address_offset tprog) (admit "simsymb") Nat.lt.

Local Transparent dummy_stack.

Ltac sep_split := econs; [|split]; swap 2 3.
Hint Unfold fe_ofs_arg.
 
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
      <<INITTGT: initial_frame rs_init_tgt (tgt_mem sm_init) st_init_tgt>>
                               /\ <<MATCH: match_states st_init_src st_init_tgt>>
.
Proof.
  ss. u in *. unfold ModSemPair.sim_skenv in *. ss. clear SIMSKENV.
  inv INITSRC.
  esplits; eauto.
  - econs; eauto.
  -
    assert(PTRRSP: is_real_fptr (rs_init_tgt RSP)).
    { admit "corollary of sem.". }
    assert(PTRRA: is_real_ptr (rs_init_tgt RA)).
    { admit "add to sem". }

    econs; eauto.
    + instantiate (1:= sm_init.(inj)).
      u in *. des_ifs.
      generalize (Ptrofs.eq_spec i0 Ptrofs.zero). i; des_ifs. clarify. clear_tac.
      econs; eauto.
      i.
      assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)).
      { eapply loc_arguments_acceptable_2; eauto. }
      assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd)) Outgoing ofs ty).
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
      Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *)
      u in RSREL. u.
      Hint Unfold mregset_of.
      u.
      inv LOCSET.
      rewrite <- REGS.
      eapply RSREL.
    + ii. des_ifs.
    + eapply RSREL.
    +
      {
        Local Opaque sepconj.
        simpl. des_ifs.
        u in PTRRA. des_ifs. u in PTRRSP. des_ifs.
        generalize (Ptrofs.eq_spec i Ptrofs.zero). i; des_ifs. clarify. clear_tac.

        rewrite sep_assoc. rewrite sep_comm. rewrite sep_assoc.
        rewrite sep_pure. split; ss.
        rewrite sep_assoc.
        rewrite sep_comm.
        rewrite sep_assoc.
        sep_split.
        { simpl. esplits; eauto. admit "SimSymbId". admit "SimSymbId". }
        { ii. ss. }
        rewrite sep_comm.
        sep_split.
        { simpl. apply WF. }
        { ii. admit "raw admit. footprint". }
        unfold frame_contents.
        econs.
        - sep_split.
          { unfold make_env in *.
            autorewrite with dummy.
            des_ifs. cbn.
            esplits; eauto.
            - apply align_divides. xomega.
            - admit "easy".
            - rewrite Z.mul_0_r. rewrite Z.add_0_r.
              About size_no_overflow.
              admit "[SIZE]
1) transf_function is succeeded -> size is somehow bound.
2) worst case, add to sem.".
            -
              (* Print Hint *. *)
              (* Print HintDb typeclass_instances. *)
              Fail autorewrite with zarith. (* TODO *)
              rewrite Z.mul_0_r. rewrite Z.add_0_r.
              ii. des. xomega.
            - ii.
              generalize (typesize_pos ty). i. xomega.
          }
          { cbn. des_ifs.
            ii. ss. des. clarify.
Local Transparent sepconj.
            ss. des; ss; clarify; clear_tac; try xomega.
Local Opaque sepconj.
          }

          sep_split.
          { autorewrite with dummy.
            ss.
            esplits; eauto; u; try xomega.
            - apply Z.divide_0_r.
            - admit "[SIZE] ditto.".
            - rewrite Z.add_0_l. ii.
              inv LOCSET.
          }
        -
      }
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
