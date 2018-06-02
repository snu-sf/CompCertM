Require Import CoqlibC Errors.
Require Import Integers ASTC Linking.
Require Import ValuesC MemoryC Separation Events GlobalenvsC Smallstep.
Require Import LTL Op Locations LinearC MachC.
Require Import BoundsC Conventions StacklayoutC Lineartyping.
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




Local Opaque Z.add Z.mul Z.div.

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

  Lemma dummy_function_fe_ofs_local
    :
      (dummy_function sg).(function_bounds).(make_env).(fe_ofs_local) = (align (4 * size_arguments sg) 8 + 8)
  .
  Proof.
    unfold make_env. ss. des_ifs_safe.
    cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1.
    { generalize (size_arguments_above sg). i. xomega. }
    rewrite align_divisible; try xomega.
    apply Z.divide_add_r; try xomega.
    - apply align_divides; auto. xomega.
    - reflexivity.
  Qed.

  Lemma dummy_function_fe_ofs_link
    :
      (dummy_function sg).(function_bounds).(make_env).(fe_ofs_link) = (align (4 * size_arguments sg) 8)
  .
  Proof.
    unfold make_env. ss. des_ifs_safe.
    cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1.
    { generalize (size_arguments_above sg). i. xomega. }
    ss.
  Qed.

  Lemma dummy_function_fe_ofs_retaddr
    :
      (dummy_function sg).(function_bounds).(make_env).(fe_ofs_retaddr) = (align (4 * size_arguments sg) 8 + 8)
  .
  Proof.
    unfold make_env. ss. des_ifs_safe.
    cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1.
    { generalize (size_arguments_above sg). i. xomega. }
    rewrite Z.mul_0_r. rewrite ! Z.add_0_r.
    rewrite align_divisible; try xomega; cycle 1.
    { apply align_divides. xomega. }
    rewrite align_divisible; try xomega; cycle 1.
    { apply align_divides. xomega. }
    rewrite align_divisible; try xomega; cycle 1.
    apply Z.divide_add_r; try xomega.
    - apply align_divides; auto. xomega.
    - reflexivity.
  Qed.

  Lemma dummy_function_fe_size
    :
      (dummy_function sg).(function_bounds).(make_env).(fe_size) = (align (4 * size_arguments sg) 8 + 8 + 8)
  .
  Proof.
    unfold make_env.
    (*??????????????? simpl. -> inf loop, but cbn works!!!!!!!!!!!!! *)
    cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1.
    { generalize (size_arguments_above sg). i. xomega. }
    rewrite Z.mul_0_r. rewrite ! Z.add_0_r.
    rewrite align_divisible; try xomega; cycle 1.
    { apply align_divides. xomega. }
    rewrite align_divisible; try xomega; cycle 1.
    { apply align_divides. xomega. }
    rewrite align_divisible; try xomega; cycle 1.
    apply Z.divide_add_r; try xomega.
    - apply align_divides; auto. xomega.
    - reflexivity.
  Qed.

End DUMMY_FUNCTION.

Hint Rewrite dummy_function_used_callee_save: dummy.
Hint Rewrite dummy_function_bound_local: dummy.
Hint Rewrite dummy_function_bound_outgoing: dummy.
Hint Rewrite dummy_function_bound_stack_data: dummy.
Hint Rewrite dummy_function_size_callee_save_area: dummy.
Hint Rewrite dummy_function_fe_ofs_local: dummy.
Hint Rewrite dummy_function_fe_ofs_link: dummy.
Hint Rewrite dummy_function_fe_ofs_retaddr: dummy.
Hint Rewrite dummy_function_fe_size: dummy.

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

  Lemma mconj_sym
        P Q
    :
      <<EQ: (mconj P Q) = (mconj Q P)>>
  .
  Proof.
    admit "".
  Qed.

End SEPARATIONC.






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
      ls_init
      (LOCSET: fill_slots (to_locset rs_init_src) (loc_arguments (Linear.fn_sig fd_src)) rs_init_src
                          (src_mem sm_init) ls_init)
      sp_src m_init_src
      (MPERM: Mem_set_perm (src_mem sm_init) sp_src fe_ofs_arg
                           (4 * size_arguments (Linear.fn_sig fd_src)) None = Some m_init_src)
      sp_tgt delta_sp
      (RSPSRC: rs_init_src RSP = Vptr sp_src Ptrofs.zero true)
      (RSPSTKSRC: m_init_src.(is_stack_block) sp_src)
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
Local Opaque make_env_ofs.
  rewrite RSPTGT. u.
  rewrite sep_assoc. rewrite sep_comm. rewrite sep_assoc. rewrite sep_pure. split; ss. rewrite sep_assoc.
  assert(MINJ: Mem.inject (inj sm_init) m_init_src (tgt_mem sm_init)).
  { eapply Mem_set_perm_none_left_inject; eauto. apply MWF. }
  sep_split.
  { simpl. eassumption. }
  { apply disjoint_footprint_drop_empty.
    { ss. }
Local Transparent make_env_ofs.
    unfold frame_contents. rewrite mconj_sym.
    apply disjoint_footprint_mconj.
    - apply disjoint_footprint_sepconj.
      + cbn. des_ifs. autorewrite with dummy in *. rewrite Z.mul_0_r. rewrite Z.add_0_r.
        repeat (autorewrite with align; try xomega).
        rewrite align_divisible; try xomega; cycle 1.
        { admit "easy". }
        assert(PRIVTGT: forall
                  ofs
                  (OFS: delta_sp <= ofs <= delta_sp + (align (4 * size_arguments (Linear.fn_sig fd_src)) 8 + 8))
                ,
                  loc_out_of_reach sm_init.(inj) sm_init.(tgt_mem) sp_tgt ofs).
        { admit "this should hold. Perm none". }


        intros blk_src delta INJDUP. ii. ss. des. clarify.
        rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'.

        assert(sp_src = sp_src').
        { apply NNPP. intro DISJ.
          (* exploit Mem.mi_perm; try apply INJDUP; try apply MINJ; eauto. *)
          (* rewrite ! Z.sub_add. ii. *)
          Print Mem.meminj_no_overlap.
          hexploit Mem.mi_no_overlap; eauto. intro OVERLAP.
          exploit OVERLAP; eauto; cycle 1.
          { intro TMP. des; eauto. apply TMP; eauto.
            instantiate (1:= ofstgt - delta_sp). rewrite ! Z.sub_add. ss.
          }
          Print Mem.inject'.
        }
        specialize (PRIVTGT delta). special PRIVTGT.
        { admit "easy". }
        unfold loc_out_of_reach in *.
        dup PRIVTGT.
        specialize (PRIVTGT _ _ RSPINJ).
        specialize (PRIVTGT0 _ _ INJ).
        special PRIVTGT.
        assert(b0 = sp_src).
        { apply NNPP.
          ii.
          (* ofs0 + delta0 = ofs1 + delta_sp *)
          (* sp_tgt + delta has permisison. *)
        }
      +
  }
    unfold frame_contents.
    
    ii.
    Print loc_out_of_reach.
    ss. des.
    -
      Local Transparent sepconj.
      ss.
      Local Opaque sepconj.
      autorewrite with dummy in *.
      rewrite Z.mul_0_r in *. rewrite Z.add_0_r in *.
      exploit Mem_set_perm_none_spec; eauto. i; des_safe.
      des; clarify; try xomega.
      + Print Mem.meminj_no_overlap.
        destruct (classic (b0 = sp_src)).
        * clarify.
          rewrite Z.add_0_l in *.
          eapply INSIDE; [|eauto].
          split; try xomega.
          u.
        * admit "focus on sm_init.(src_mem). sp_src has permission (fill_slots can read it)".
    -
      
      admit "raw admit. footprint".
  }
  { 
  unfold 
Qed.


  1 subgoal (ID 4488)
  
  prog : Linear.program
  tprog : program
  TRANSF : match_prog prog tprog
  return_address_offset : function -> code -> ptrofs -> Prop
  match_states := StackingproofC0.match_states prog tprog return_address_offset : Linear.state -> state -> Prop
  fptr_init_src, fptr_init_tgt : val
  FPTRREL : Val.inject (inj sm_init) fptr_init_src fptr_init_tgt
  rs_init_src, rs_init_tgt : regset
  RSREL : forall pr : PregEq.t, Val.inject (inj sm_init) (rs_init_src pr) (rs_init_tgt pr)
  WF : wf' sm_init
  fd_src : Linear.function
  ls_init : locset
  sp_src : block
  m_init_src : mem
  FINDFUNC : Genv.find_funct (Genv.globalenv prog) (rs_init_src PC) = Some (Internal fd_src)
  LOCSET : fill_slots (to_locset rs_init_src) (loc_arguments (Linear.fn_sig fd_src)) rs_init_src
             (src_mem sm_init) ls_init
  RSPPTR : rs_init_src RSP = Vptr sp_src Ptrofs.zero true
  MPERM : Mem_set_perm (src_mem sm_init) sp_src fe_ofs_arg (4 * size_arguments (Linear.fn_sig fd_src)) None =
          Some m_init_src
  fd_tgt : function
  FUNCTGT : Genv.find_funct (Genv.globalenv tprog) (rs_init_tgt PC) = Some (Internal fd_tgt)
  Heq : transf_function fd_src = OK fd_tgt
  sp_tgt : block
  delta_sp : Z
  RSPINJ : inj sm_init sp_src = Some (sp_tgt, delta_sp)
  RSPPTRTGT : rs_init_tgt RSP = Vptr sp_tgt (Ptrofs.repr delta_sp) true
  ra : block
  :

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
      inv LOCSET.
      rewrite <- REGS.
      eapply RSREL.
    + ii. des_ifs.
    +
      {
        Local Opaque sepconj.
        simpl. rewrite RSPPTRTGT. ss.
        (* generalize (Ptrofs.eq_spec i Ptrofs.zero). i; des_ifs. clarify. clear_tac. *)

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
        { simpl. eapply Mem_set_perm_none_left_inject; eauto. apply WF. }
        { ii.
          Local Opaque function_bounds.
          Local Opaque make_env.
          Print loc_out_of_reach.
          ss. des.
          -
            Local Transparent sepconj.
            ss.
            Local Opaque sepconj.
            autorewrite with dummy in *.
            rewrite Z.mul_0_r in *. rewrite Z.add_0_r in *.
            exploit Mem_set_perm_none_spec; eauto. i; des_safe.
            des; clarify; try xomega.
            + Print Mem.meminj_no_overlap.
              destruct (classic (b0 = sp_src)).
              * clarify.
                rewrite Z.add_0_l in *.
                eapply INSIDE; [|eauto].
                split; try xomega.
                u.
              * admit "focus on sm_init.(src_mem). sp_src has permission (fill_slots can read it)".
          -
            
          admit "raw admit. footprint".
        }
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
