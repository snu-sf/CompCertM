Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC MemoryC2 Lia IntegersC SimMemInj.
Require Import mktac.
Set Implicit Arguments.

Inductive def_match A V: globdef A V -> globdef A V -> Prop :=
| def_match_gfun f: def_match (Gfun f) (Gfun f)
| def_match_gvar inf init0 init1 ro vol
  :
    def_match
      (Gvar (mkglobvar inf init0 ro vol))
      (Gvar (mkglobvar inf init1 ro vol))
.

Program Instance def_match_reflexive A V : Reflexive (@def_match A V).
Next Obligation.
Proof.
  i. destruct x; try econs. destruct v; try econs.
Qed.

Lemma def_match_refl A V (g: globdef A V)
  :
    def_match g g
.
Proof. refl. Qed.
Hint Resolve def_match_refl.

Lemma exec_load_mem_equal
      ge chunk m0 m1 a rd
      rs0 rs1
      (EXEC: exec_load ge chunk m0 a rs0 rd = Next rs1 m1)
  :
    m0 = m1.
Proof.
  unfold exec_load in *. des_ifs.
Qed.

Lemma exec_store_max_perm
      ge chunk m0 m1 a rd l
      rs0 rs1
      b ofs k p
      (EXEC: exec_store ge chunk m0 a rs0 rd l = Next rs1 m1)
      (PERM: Mem.perm m1 b ofs k p)
  :
    Mem.perm m0 b ofs k p.
Proof.
  unfold exec_store, Mem.storev in *. des_ifs.
  eapply Mem.perm_store_2; eauto.
Qed.

Lemma asm_step_max_perm se ge_src rs0 rs1 m0 m1 tr
      (STEP: Asm.step ge_src se (Asm.State rs0 m0) tr (Asm.State rs1 m1))
      b ofs p
      (VALID: Mem.valid_block m0 b)
      (PERM: Mem.perm m1 b ofs Max p)
  :
    Mem.perm m0 b ofs Max p.
Proof.
  revert VALID.
  replace m1 with (st_m (Asm.State rs1 m1)) in PERM; eauto.
  replace m0 with (st_m (Asm.State rs0 m0)); eauto.
  generalize dependent (Asm.State rs0 m0).
  generalize dependent (Asm.State rs1 m1).
  i. ginduction STEP; i; ss.
  - unfold exec_instr in *;
      des_ifs; ss; clarify;
      (all_once_fast ltac:(fun H=> try (eapply exec_load_mem_equal in H; clarify; fail)));
      (try (eapply exec_store_max_perm; eauto; fail)).
    + unfold goto_label in *. des_ifs.
    + unfold goto_label in *. des_ifs.
    + unfold goto_label in *. des_ifs.
    + unfold goto_label in *. des_ifs.
    + eapply Mem.perm_store_2 in Heq1; eauto.
      eapply Mem.perm_store_2 in Heq0; eauto.
      eapply Mem.perm_alloc_4; eauto. ii. clarify.
      eapply Mem.fresh_block_alloc; eauto.
    + eapply Mem.perm_free_3; eauto.
  - exploit external_call_max_perm; eauto.
  - exploit external_call_max_perm; eauto.
Qed.

Ltac tac_p := ss; try (symmetry; eapply Ptrofs.add_zero; fail);
              repeat ((try rewrite Ptrofs.add_assoc); (try rewrite Ptrofs.sub_add_l));
              try (ss; f_equal; apply Ptrofs.add_commut).

Section ASMSTEP.

  Context `{CTX: Val.meminj_ctx}.

  Definition agree (j: meminj) (rs_src rs_tgt: regset) : Prop :=
    forall pr, Val.inject j (rs_src pr) (rs_tgt pr).

  Lemma agree_step j rs0 rs1 pr v0 v1
        (AGREE: agree j rs0 rs1)
        (INJ: Val.inject j v0 v1)
    :
      agree j (rs0 # pr <- v0) (rs1 # pr <- v1).
  Proof.
    ii. unfold Pregmap.set. des_ifs.
  Qed.

  Lemma inject_separated_refl j m_src m_tgt
    :
      inject_separated j j m_src m_tgt.
  Proof.
    ii. clarify.
  Qed.

  Remark mull_inject:
    forall f v1 v1' v2,
      Val.inject f v1 v1' ->
      Val.inject f (Val.mull v1 v2) (Val.mull v1' v2).
  Proof.
    intros. unfold Val.mull. des_ifs; inv H. econs.
  Qed.

  Lemma eval_addrmode_inject
        j ge_src ge_tgt a
        rs_src0 rs_tgt0
        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge_src i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge_tgt i = Some b_tgt>>) /\
              (<<INJ: j b_src = Some (b_tgt, 0)>>))
        (AGREE: agree j rs_src0 rs_tgt0)
    :
      Val.inject j (eval_addrmode ge_src a rs_src0) (eval_addrmode ge_tgt a rs_tgt0).
  Proof.
    unfold eval_addrmode, eval_addrmode64 in *.
    des_ifs; ss; repeat (eapply Val.addl_inject; eauto).
    - unfold Genv.symbol_address in *. des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
      + exploit SYMBLE; eauto. i. des. clarify.
    - eapply mull_inject; eauto.
    - eapply mull_inject; eauto.
    - unfold Genv.symbol_address in *. des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
      + exploit SYMBLE; eauto. i. des. clarify.
    - unfold Genv.symbol_address in *. des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
    - cinv (AGREE i); ss; des_ifs; econs; eauto.
      + repeat (rewrite Ptrofs.add_assoc). f_equal.
        rewrite Ptrofs.add_commut.
        repeat (rewrite Ptrofs.add_assoc). auto.
      + repeat (rewrite Ptrofs.add_assoc). f_equal.
        rewrite Ptrofs.add_commut.
        repeat (rewrite Ptrofs.add_assoc). auto.
    - cinv (AGREE i); ss; unfold Genv.symbol_address in *; des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
    - cinv (AGREE i); ss; des_ifs; econs; eauto.
    - cinv (AGREE i); ss; unfold Genv.symbol_address in *; des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
    - unfold Genv.symbol_address in *; des_ifs.
      + exploit SYMBLE; eauto. i. des. clarify.
      + exploit SYMBLE; eauto. i. des. clarify.
        econs; eauto. tac_p.
  Qed.

  Lemma exec_load_inject
        j ge_src ge_tgt chunk m_src0 m_tgt0 m_src1 a rd
        rs_src0 rs_tgt0 rs_src1
        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge_src i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge_tgt i = Some b_tgt>>) /\
              (<<INJ: j b_src = Some (b_tgt, 0)>>))
        (AGREE: agree j rs_src0 rs_tgt0)
        (INJ: Mem.inject j m_src0 m_tgt0)
        (EXEC: exec_load ge_src chunk m_src0 a rs_src0 rd = Next rs_src1 m_src1)
    :
      exists rs_tgt1,
        (<<MEMSAME: m_src0 = m_src1>>) /\
        (<<AGREE: agree j rs_src1 rs_tgt1>>) /\
        (<<INJ: Mem.inject j m_src1 m_tgt0>>) /\
        (<<EXEC: exec_load ge_tgt chunk m_tgt0 a rs_tgt0 rd = Next rs_tgt1 m_tgt0>>) /\
        (<<UNCHSRC: Mem.unchanged_on
                      (loc_unmapped j /2\ SimMemInj.valid_blocks m_src0)
                      m_src0 m_src1>>)
  .
  Proof.
    exploit eval_addrmode_inject; eauto. intros ADDR.
    instantiate (1:=a) in ADDR.
    unfold exec_load in *. des_ifs.
    - eapply Mem.loadv_inject in Heq0; eauto; des; clarify.
      esplits; eauto; [|refl].
      repeat (eapply agree_step; eauto). ss.
      unfold Pregmap.set in *.
      specialize (AGREE PC). des_ifs; try by inv Heq1.
      + inv Heq1; ss; econs; eauto; tac_p.
      + inv AGREE; ss; econs; eauto; tac_p.
    - eapply Mem.loadv_inject in Heq0; eauto; des; clarify.
  Qed.

  Lemma undef_regs_agree j l rs_src rs_tgt
        (AGREE : agree j rs_src rs_tgt)
    :
      agree j (undef_regs l rs_src) (undef_regs l rs_tgt).
  Proof.
    revert rs_src rs_tgt AGREE. induction l; ss; i. ii.
    unfold Pregmap.set in *.
    eapply IHl. ii. des_ifs.
  Qed.

  Lemma nextinstr_agree j rs_src rs_tgt
        (AGREE: agree j rs_src rs_tgt)
    :
      agree j (nextinstr rs_src) (nextinstr rs_tgt).
  Proof.
    unfold nextinstr. apply agree_step; eauto.
    apply Val.offset_ptr_inject; eauto.
  Qed.

  Lemma exec_store_inject
        j ge_src ge_tgt chunk m_src0 m_tgt0 m_src1 a rd l
        rs_src0 rs_tgt0 rs_src1
        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge_src i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge_tgt i = Some b_tgt>>) /\
              (<<INJ: j b_src = Some (b_tgt, 0)>>))
        (AGREE: agree j rs_src0 rs_tgt0)
        (INJ: Mem.inject j m_src0 m_tgt0)
        (EXEC: exec_store ge_src chunk m_src0 a rs_src0 rd l = Next rs_src1 m_src1)
    :
      exists rs_tgt1 m_tgt1,
        (<<AGREE: agree j rs_src1 rs_tgt1>>) /\
        (<<INJ: Mem.inject j m_src1 m_tgt1>>) /\
        (<<EXEC: exec_store ge_tgt chunk m_tgt0 a rs_tgt0 rd l = Next rs_tgt1 m_tgt1>>) /\
        (<<UNCHSRC: Mem.unchanged_on
                      (loc_unmapped j /2\ SimMemInj.valid_blocks m_src0)
                      m_src0 m_src1>>) /\
        (<<UNCHTGT: Mem.unchanged_on
                      (loc_out_of_reach j m_src0 /2\ SimMemInj.valid_blocks m_tgt0)
                      m_tgt0 m_tgt1>>)
  .
  Proof.
    exploit eval_addrmode_inject; eauto. intros ADDR.
    hexploit undef_regs_agree; eauto. intros UAGREE.
    instantiate (1:=a) in ADDR.
    unfold exec_store in *. des_ifs.
    - dup Heq0.
      eapply Mem.storev_mapped_inject in Heq0; cycle 1; eauto; des; clarify.
      esplits; eauto.
      + unfold nextinstr_nf, nextinstr. ss.
        repeat (eapply agree_step; eauto).
        unfold Pregmap.set in *.
        specialize (UAGREE PC). des_ifs; try by inv Heq1.
        inv UAGREE; ss; econs; eauto; tac_p.
      + eapply Mem.unchanged_on_implies with
            (P:=loc_unmapped j /2\ valid_blocks m_src0); eauto.
        unfold Mem.storev in *. des_ifs.
        eapply Mem.store_unchanged_on; eauto.
        ii. des. inv ADDR. unfold loc_unmapped in *. clarify.
      + eapply Mem.unchanged_on_implies with
            (P:=loc_out_of_reach j m_src0 /2\ valid_blocks m_tgt0); eauto.
        unfold Mem.storev in *. des_ifs.
        eapply Mem.store_unchanged_on; eauto.
        ii. des. inv ADDR. unfold loc_out_of_reach in *.
        eapply H0; eauto.
        eapply Mem.store_valid_access_3 in Heq1.
        unfold Mem.valid_access in *.
        eapply Mem.perm_cur. eapply Mem.perm_implies.
        * eapply Heq1.
          replace (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr delta))) with
              (Ptrofs.unsigned i0 + delta) in *.
          -- lia.
          -- clear - INJ H6 Heq1.
             admit "ez make lemma".
        * econs.
    - eapply Mem.storev_mapped_inject in Heq0; cycle 1; eauto; des; clarify.
  Qed.

  Lemma regset_after_external_inject rs_src rs_tgt j
        (AGREE: agree j rs_src rs_tgt)
    :
      agree j (regset_after_external rs_src) (regset_after_external rs_tgt).
  Proof.
    unfold regset_after_external in *. ii. des_ifs.
  Qed.

  Lemma set_pair_inject rs_src rs_tgt l v_src v_tgt j
        (AGREE: agree j rs_src rs_tgt)
        (VAL: Val.inject j v_src v_tgt)
    :
      agree j (set_pair l v_src rs_src) (set_pair l v_tgt rs_tgt).
  Proof.
    unfold set_pair. des_ifs; repeat (eapply agree_step; eauto).
    - eapply Val.hiword_inject; eauto.
    - eapply Val.loword_inject; eauto.
  Qed.

  Lemma extcall_arg_inject rs1 rs2 m1 m2 l arg1 j
        (AGREE: agree j rs1 rs2)
        (INJ: Mem.inject j m1 m2)
        (ARGS: extcall_arg rs1 m1 l arg1)
    :
      exists arg2 : val,
        (<<ARGINJ: Val.inject j arg1 arg2>>) /\
        (<<ARGS: extcall_arg rs2 m2 l arg2>>).
  Proof.
    inv ARGS.
    - esplits; eauto. econs; eauto.
    - exploit Mem.loadv_inject; eauto.
      + eapply Val.offset_ptr_inject; eauto.
      + i. des. esplits; eauto.
        econs; eauto.
  Qed.

  Lemma extcall_arg_pair_inject rs1 rs2 m1 m2 l arg1 j
        (AGREE: agree j rs1 rs2)
        (INJ: Mem.inject j m1 m2)
        (ARGS: extcall_arg_pair rs1 m1 l arg1)
    :
      exists arg2 : val,
        (<<ARGINJ: Val.inject j arg1 arg2>>) /\
        (<<ARGS: extcall_arg_pair rs2 m2 l arg2>>).
  Proof.
    inv ARGS.
    - exploit extcall_arg_inject; eauto. i. des. esplits; eauto.
      econs; eauto.
    - eapply extcall_arg_inject in H; eauto.
      eapply extcall_arg_inject in H0; eauto. des.
      esplits; eauto.
      + eapply Val.longofwords_inject; eauto.
      + econs; eauto.
  Qed.

  Lemma extcall_arguments_inject rs1 rs2 m1 m2 sg args1 j
        (AGREE: agree j rs1 rs2)
        (INJ: Mem.inject j m1 m2)
        (ARGS: extcall_arguments rs1 m1 sg args1)
    :
      exists args2 : list val,
        (<<ARGINJ: Val.inject_list j args1 args2>>) /\
        (<<ARGS: extcall_arguments rs2 m2 sg args2>>).
  Proof.
    unfold extcall_arguments in *.
    revert args1 ARGS. induction (loc_arguments sg); ss; i; inv ARGS.
    - esplits; eauto. econs.
    - exploit IHl; eauto.
      exploit extcall_arg_pair_inject; eauto. i. des.
      exists (arg2::args2).
      esplits; eauto. econs; eauto.
  Qed.

  Lemma eval_builtin_arg_inject A F V (ge1 ge2: Genv.t F V) e1 e2 sp1 sp2 m1 m2 j
        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge1 i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge2 i = Some b_tgt>>) /\
              (<<INJ: j b_src = Some (b_tgt, 0)>>))
        (VALS: forall x : A, Val.inject j (e1 x) (e2 x))
        (INJ: Mem.inject j m1 m2)
        (a : builtin_arg A) (v1 : val)
        (EVAL: eval_builtin_arg ge1 e1 sp1 m1 a v1)
        (SPINJ: Val.inject j sp1 sp2)
    :
      exists v2 : val,
        (<<EVAL: eval_builtin_arg ge2 e2 sp2 m2 a v2>>) /\
        (<<VAL: Val.inject j v1 v2>>).
  Proof.
    revert v1 EVAL.
    induction a; i; inv EVAL; ss; try (esplits; eauto; econs; eauto; fail).
    - exploit Mem.loadv_inject; eauto; ss; i.
      + eapply Val.offset_ptr_inject; eauto.
      + des. esplits; eauto. econs. eauto.
    - esplits; eauto.
      + econs.
      + eapply Val.offset_ptr_inject; eauto.
    - exploit Mem.loadv_inject; eauto.
      + instantiate (1:= Senv.symbol_address ge2 id ofs).
        unfold Senv.symbol_address in *. ss.
        des_ifs_safe. exploit SYMBLE; eauto. i. des. rewrite FINDTGT.
        econs; eauto. psimpl. auto.
      + i. des. esplits; eauto. econs; eauto.
    - esplits; eauto.
      + econs.
      + unfold Senv.symbol_address in *. ss.
        des_ifs_safe. exploit SYMBLE; eauto. i. des. rewrite FINDTGT.
        econs; eauto. psimpl. auto.
    - eapply IHa1 in H1. eapply IHa2 in H3. des.
      esplits; eauto.
      + econs; eauto.
      + eapply Val.longofwords_inject; eauto.
    - eapply IHa1 in H1. eapply IHa2 in H3. des.
      esplits; eauto.
      + econs; eauto.
      + des_ifs. eapply Val.addl_inject; eauto.
  Qed.

  Lemma eval_builtin_args_inject A F V (ge1 ge2: Genv.t F V) e1 e2 sp1 sp2 m1 m2 j
        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge1 i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge2 i = Some b_tgt>>) /\
              (<<INJ: j b_src = Some (b_tgt, 0)>>))
        (VALS: forall x : A, Val.inject j (e1 x) (e2 x))
        (INJ: Mem.inject j m1 m2)
        (al : list (builtin_arg A)) (vl1 : list val)
        (EVAL: eval_builtin_args ge1 e1 sp1 m1 al vl1)
        (SPINJ: Val.inject j sp1 sp2)
    :
      exists vl2 : list val,
        (<<EVAL: eval_builtin_args ge2 e2 sp2 m2 al vl2>>) /\
        (<<VALLIST: Val.inject_list j vl1 vl2>>).
  Proof.
    revert al EVAL. induction vl1; ss; i.
    - inv EVAL. esplits; econs.
    - inv EVAL.
      exploit IHvl1; eauto. i. des.
      exploit eval_builtin_arg_inject; eauto. i. des.
      exists (v2::vl2). splits; eauto. econs; eauto.
  Qed.

  Lemma agree_incr rs_src rs_tgt j0 j1
        (AGREE: agree j0 rs_src rs_tgt)
        (INCR: inject_incr j0 j1)
    :
      agree j1 rs_src rs_tgt.
  Proof.
    ii. eauto.
  Qed.

  Lemma set_res_agree j res vres vres' rs_src rs_tgt
        (AGREE: agree j rs_src rs_tgt)
        (INJ: Val.inject j vres vres')
    :
      agree j (set_res res vres rs_src) (set_res res vres' rs_tgt).
  Proof.
    revert rs_src rs_tgt AGREE vres vres' INJ. induction res; ss; i.
    - apply agree_step; eauto.
    - eapply IHres2; eauto.
      + eapply IHres1; eauto. eapply Val.hiword_inject; eauto.
      + eapply Val.loword_inject; eauto.
  Qed.

  Lemma unsigned_add ofs delta
        (RANGE: delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned)
    :
      Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))
      = Ptrofs.unsigned ofs + delta.
  Proof.
    rewrite Ptrofs.add_unsigned.
    replace (Ptrofs.unsigned (Ptrofs.repr delta)) with delta.
    * eapply Ptrofs.unsigned_repr; eauto. des. splits; eauto.
    * symmetry. eapply Ptrofs.unsigned_repr; eauto. des. splits; [xomega|].
      assert (Ptrofs.unsigned ofs >= 0); [|xomega].
      set (Ptrofs.unsigned_range ofs). des. xomega.
  Qed.

  Lemma cmplu_inject j rs_src rs_tgt v1_src v2_src v1_tgt v2_tgt m_src m_tgt c
        (AGREE: agree j rs_src rs_tgt)
        (INJ: Mem.inject j m_src m_tgt)
        (VAL1: Val.inject j v1_src v1_tgt)
        (VAL2: Val.inject j v2_src v2_tgt)
    :
      Val.inject j (Val.maketotal (Val.cmplu (Mem.valid_pointer m_src) c v1_src v2_src))
                 (Val.maketotal (Val.cmplu (Mem.valid_pointer m_tgt) c v1_tgt v2_tgt)).
  Proof.
    unfold Val.cmplu. inv INJ. inv mi_inj.
    unfold Val.maketotal, option_map.
    destruct (Val.cmplu_bool (Mem.valid_pointer m_src) c v1_src v2_src) eqn: CMP_SRC; eauto.
    replace (Val.cmplu_bool (Mem.valid_pointer m_tgt) c v1_tgt v2_tgt) with (Some b); eauto.
    { unfold Val.of_bool; des_ifs; econs. }
    erewrite Val.cmplu_bool_inject; eauto; ss; i; unfold Mem.valid_pointer, proj_sumbool in *; eauto; ss; i; des_ifs.
    - exfalso. eapply n.
      exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + left; eapply Mem.perm_max; eauto.
      + i. erewrite unsigned_add; eauto.
    - exfalso. eapply n.
      exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + left; eapply Mem.perm_max; eauto.
      + i. erewrite unsigned_add; eauto.
    - exfalso. eapply n.
      exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + left; eapply Mem.perm_max; eauto.
      + i. erewrite unsigned_add; eauto.
    - exfalso. eapply n0.
      exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + right; eapply Mem.perm_max; eauto.
      + i. erewrite unsigned_add; eauto.
        rp; eauto. xomega.
    - exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + left. eapply Mem.perm_max; eauto.
      + i. erewrite Ptrofs.unsigned_repr; des; split; try xomega.
        set (Ptrofs.unsigned_range ofs). des. xomega.
    - exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + left. eapply Mem.perm_max; eauto.
      + i. erewrite Ptrofs.unsigned_repr; des; split; try xomega.
        set (Ptrofs.unsigned_range ofs). des. xomega.
    - exploit mi_perm; eauto. i.
      exploit mi_representable; eauto.
      + right. eapply Mem.perm_max; eauto.
      + i. erewrite Ptrofs.unsigned_repr; des; split; try xomega.
        set (Ptrofs.unsigned_range ofs). des. xomega.
    - exploit mi_no_overlap; eauto.
      + eapply Mem.perm_max; eauto.
      + eapply Mem.perm_max; eauto.
      + i.
        erewrite unsigned_add; eauto; cycle 1.
        { exploit mi_representable; cycle 1; eauto.
          left. eapply Mem.perm_max; eauto. }
        erewrite unsigned_add; eauto; cycle 1.
        { exploit mi_representable; cycle 1; eauto.
          left. eapply Mem.perm_max; eauto. }
  Qed.

  Lemma compare_longs_inject j rs_src rs_tgt v1_src v2_src v1_tgt v2_tgt m_src m_tgt
        (AGREE: agree j rs_src rs_tgt)
        (INJ: Mem.inject j m_src m_tgt)
        (VAL1: Val.inject j v1_src v1_tgt)
        (VAL2: Val.inject j v2_src v2_tgt)
    :
      agree
        j
        (compare_longs v1_src v2_src rs_src m_src)
        (compare_longs v1_tgt v2_tgt rs_tgt m_tgt).
  Proof.
    unfold compare_longs.
    eapply agree_step; eauto.
    eapply agree_step; eauto; cycle 1.
    { inv VAL1; inv VAL2; clarify; ss; econs. }
    eapply agree_step; eauto; cycle 1.
    { exploit (Val.subl_inject j v1_src v1_tgt v2_src v2_tgt); eauto.
      intros VAL. inv VAL; eauto; ss. }
    eapply agree_step; eauto; cycle 1.
    { eapply cmplu_inject; eauto. }
    eapply agree_step; eauto; cycle 1.
    { eapply cmplu_inject; eauto. }
  Qed.

  Ltac tac_sl := try (esplits; [
                        econs; eauto; ss|
                        unfold nextinstr_nf, nextinstr; ss;
                        repeat (eapply agree_step; eauto);
                        u;
                        unfold Val.offset_ptr in *;
                        unfold Pregmap.set in *; des_ifs; eq_closure_tac;
                        econs; eauto; rewrite Ptrofs.add_zero; refl|
                        eauto|
                        refl|
                        eapply inject_separated_refl]).

  Ltac tac_ld :=
    (all_once_fast ltac:(fun H => try (eapply exec_load_inject in H; try eassumption; check_safe;
                                       eauto; des; esplits; eauto;
                                       [econs; eauto|
                                        eapply inject_separated_refl|refl]))); fail.

  Ltac tac_st :=
    (all_once_fast ltac:(fun H => try (eapply exec_store_inject in H; try eassumption; check_safe;
                                       eauto; des; esplits; eauto;
                                       [econs; eauto|
                                        eapply inject_separated_refl]))); fail.

  Ltac agree_inv AGREE :=
    match goal with
    | [|- context[(?rs: regset -> val) (?pr: preg)]] => cinv (AGREE pr)
    end; ss.

  Ltac agree_invs AGREE := repeat (agree_inv AGREE).

  Ltac propagate_eq_typ TYP :=
    repeat (multimatch goal with
            | [H1: @eq TYP ?A ?B, H2: @eq TYP ?B ?C |- _ ] =>
              tryif (check_equal A C)
              then fail
              else
                tryif (exists_prop (A = C) + exists_prop (C = A))
                then idtac
                else
                  let name := fresh "EQ_CLOSURE_TAC" in
                  hexploit eq_trans; [exact H1|exact H2|]; intro name
            | [H1: ?B = ?A, H2: ?B = ?C |- _ ] =>
              tryif (check_equal A C)
              then fail
              else
                tryif (exists_prop (A = C) + exists_prop (C = A))
                then idtac
                else
                  let name := fresh "EQ_CLOSURE_TAC" in
                  hexploit eq_trans; [exact (eq_sym H1)|exact H2|]; intro name
            end)
  .

  Ltac eq_closure_tac_typ TYP :=
    repeat (propagate_eq_typ TYP; clarify).

  Lemma zero_ext_inject n v1 v2 j
        (INJ: Val.inject j v1 v2)
    :
      Val.inject j (Val.zero_ext n v1) (Val.zero_ext n v2).
  Proof.
    unfold Val.zero_ext in *. des_ifs; inv INJ.
    econs.
  Qed.

  Lemma sign_ext_inject n v1 v2 j
        (INJ: Val.inject j v1 v2)
    :
      Val.inject j (Val.sign_ext n v1) (Val.sign_ext n v2).
  Proof.
    inv INJ; ss.
  Qed.

  Lemma agree_ir (i: ireg)
    :
      forall j rs_src rs_tgt
             (AGREE: agree j rs_src rs_tgt),
        Val.inject j (rs_src i) (rs_tgt i).
  Proof.
    eauto.
  Qed.

  Lemma val_long_same_inj v1 v2 j
        (EQ: v1 = v2)
    :
      Val.inject j (Vlong v1) (Vlong v2).
  Proof.
    clarify.
  Qed.

  Lemma val_float_same_inj v1 v2 j
        (EQ: v1 = v2)
    :
      Val.inject j (Vfloat v1) (Vfloat v2).
  Proof.
    clarify.
  Qed.

  Lemma val_int_same_inj v1 v2 j
        (EQ: v1 = v2)
    :
      Val.inject j (Vint v1) (Vint v2).
  Proof.
    clarify.
  Qed.

  Lemma val_single_same_inj v1 v2 j
        (EQ: v1 = v2)
    :
      Val.inject j (Vsingle v1) (Vsingle v2).
  Proof.
    clarify.
  Qed.

  Ltac val_inj_tac :=
    ((econs; eauto) ||
     (eapply val_long_same_inj) ||
     (eapply val_float_same_inj) ||
     (eapply val_int_same_inj) ||
     (eapply val_single_same_inj)).

  Ltac tac_cal AGREE :=
    try (progress (unfold goto_label in *); des_ifs_safe);
         (esplits; eauto; [econs; eauto; ss; try (unfold goto_label in *; des_ifs; fail)
                          | repeat (eapply agree_step; eauto); ss;
                            (fail|| idtac; [.. |unfold Val.offset_ptr;
                                                repeat (try (rewrite Pregmap.gss);
                                                        (try (rewrite Pregmap.gso; [| ii; clarify; fail]))); des_ifs;
                                                try (val_inj_tac; ss; tac_p)]);
                            (try ((agree_invs AGREE); ss; unfold option_map, Val.maketotal; des_ifs; ss; val_inj_tac; tac_p; check_safe))
                          | eapply inject_separated_refl|refl|refl]).

  Lemma eval_testcond_inj rs_src rs_tgt j c v
        (AGREE: agree j rs_src rs_tgt)
        (EVAL: eval_testcond c rs_src = Some v)
    :
      eval_testcond c rs_tgt = Some v.
  Proof.
    unfold eval_testcond in *. destruct c; revert EVAL; agree_invs AGREE.
  Qed.

  Theorem asm_step_preserve_injection
        rs_src0 rs_src1 m_src0 m_src1 tr j0
        rs_tgt0 m_tgt0
        se_src se_tgt ge_src ge_tgt

        (DEFLE: forall
            b_src b_tgt delta d_src
            (FINDSRC: Genv.find_def ge_src b_src = Some d_src)
            (INJ: j0 b_src = Some (b_tgt, delta)),
            exists d_tgt,
              (<<FINDTGT: Genv.find_def ge_tgt b_tgt = Some d_tgt>>) /\
              (<<DELTA: delta = 0>>) /\
              (<<DEFMATCH: def_match d_src d_tgt>>))

        (SYMBLE: forall
            i b_src
            (FINDSRC: Genv.find_symbol ge_src i = Some b_src),
            exists b_tgt,
              (<<FINDTGT: Genv.find_symbol ge_tgt i = Some b_tgt>>) /\
              (<<INJ: j0 b_src = Some (b_tgt, 0)>>))

        (SYMBINJ: symbols_inject j0 se_src se_tgt)
        (* (NOEXTFUN: no_extern_fun ge_src) *)
        (AGREE: agree j0 rs_src0 rs_tgt0)
        (INJ: Mem.inject j0 m_src0 m_tgt0)
        (STEP: Asm.step se_src ge_src (Asm.State rs_src0 m_src0) tr (Asm.State rs_src1 m_src1))
    :
      exists rs_tgt1 m_tgt1 j1,
        (<<STEP: Asm.step se_tgt ge_tgt (Asm.State rs_tgt0 m_tgt0) tr (Asm.State rs_tgt1 m_tgt1)>>) /\
        (<<AGREE: agree j1 rs_src1 rs_tgt1>>) /\
        (<<INJ: Mem.inject j1 m_src1 m_tgt1>>) /\
        (<<INCR: inject_incr j0 j1>>) /\
        (<<SEP: inject_separated j0 j1 m_src0 m_tgt0>>) /\

        (<<UNCHSRC: Mem.unchanged_on
                      (loc_unmapped j0 /2\ SimMemInj.valid_blocks m_src0)
                      m_src0 m_src1>>) /\
        (<<UNCHTGT: Mem.unchanged_on
                      (loc_out_of_reach j0 m_src0 /2\ SimMemInj.valid_blocks m_tgt0)
                      m_tgt0 m_tgt1>>)
  .
  Proof.
    inv STEP.

    - cinv (AGREE PC); eq_closure_tac.

      assert (delta = 0).
      { unfold Genv.find_funct_ptr in *. des_ifs.
        exploit DEFLE; eauto. i. des. eauto. }

      assert (FIND: Genv.find_funct_ptr ge_tgt b2 = Some (Internal f)).
      { unfold Genv.find_funct_ptr in *. des_ifs_safe.
        exploit DEFLE; eauto. i. des. rewrite FINDTGT in *.
        inv DEFMATCH; auto. }

      clarify.
      replace (Ptrofs.add ofs (Ptrofs.repr 0)) with ofs in *; cycle 1.
      { rewrite Ptrofs.add_zero. refl. }

      assert (ADDRINJ: forall id ofs,
                 Val.inject
                   j0
                   (Genv.symbol_address ge_src id ofs)
                   (Genv.symbol_address ge_tgt id ofs)).
      {
        i. unfold Genv.symbol_address. des_ifs_safe.
        exploit SYMBLE; eauto. i. des.
        rewrite FINDTGT. econs; eauto.
        psimpl. auto.
      }

      unfold exec_instr in *.

      des_ifs; ss; clarify.

      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_ld.
      + tac_ld.
      + tac_st.
      + tac_st.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_ld.
      + tac_st.
      + tac_cal AGREE.
      + tac_ld.
      + tac_st.
      + tac_ld.
      + tac_st.
      + tac_ld.
      + tac_st.
      + tac_st.
      + tac_st.
      + tac_cal AGREE.
      + tac_ld.
      + tac_cal AGREE.
      + tac_ld.
      + tac_cal AGREE.
      + tac_ld.
      + tac_cal AGREE.
      + tac_ld.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE
        + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE
        + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
        unfold eval_addrmode32.
        des_ifs; agree_invs AGREE; ss;
          try (match goal with
               | [|- context[Genv.symbol_address ge_src ?ib ?io]] => cinv (ADDRINJ ib io)
               end; des_ifs).
      + tac_cal AGREE.
        unfold eval_addrmode64. des_ifs.
        des_ifs; agree_invs AGREE; ss; (replace Archi.ptr64 with true; [|eauto]);
          (repeat (eapply Val.addl_inject); eauto); try val_inj_tac; tac_p.
        * f_equal. rewrite Ptrofs.add_permut. f_equal. apply Ptrofs.add_commut.
        * f_equal. rewrite Ptrofs.add_permut. f_equal. apply Ptrofs.add_commut.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
          eapply mull_inject; eauto.
        * repeat (eapply Val.addl_inject); eauto.
          eapply mull_inject; eauto.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
          eapply mull_inject; eauto.
        * repeat (eapply Val.addl_inject); eauto.
          eapply mull_inject; eauto.
        * repeat (eapply Val.addl_inject); eauto.
        * repeat (eapply Val.addl_inject); eauto.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
        agree_invs AGREE; des_ifs; unfold andb, proj_sumbool in *; des_ifs; clarify.
        * try val_inj_tac; tac_p; try f_equal.
        * try val_inj_tac; tac_p; try f_equal.
          rewrite <- Ptrofs.sub_add_l.
          rewrite Ptrofs.sub_shifted. eauto.
        * try val_inj_tac; tac_p; try f_equal.
        * try val_inj_tac; tac_p; try f_equal.
        * try val_inj_tac; tac_p; try f_equal.
          rewrite <- Ptrofs.sub_add_l.
          rewrite Ptrofs.sub_shifted. eauto.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          apply Val.offset_ptr_inject; ss.
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          apply Val.offset_ptr_inject; ss.
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          apply Val.offset_ptr_inject; ss.
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          apply Val.offset_ptr_inject; ss.
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * repeat (eapply agree_step; eauto); ss.
          -- agree_inv AGREE; des_ifs.
             agree_inv AGREE; des_ifs.
          -- eapply Val.offset_ptr_inject.
             repeat (try (rewrite Pregmap.gss);
                     (try (rewrite Pregmap.gso; [| ii; clarify; fail]))); des_ifs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
         eapply compare_longs_inject; eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          apply compare_longs_inject; eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.of_bool. des_ifs; econs.
          -- unfold Val.of_bool. des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
          -- unfold Val.cmpu, Val.cmpu_bool; ss.
             des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_longs. (repeat eapply agree_step; eauto); agree_invs AGREE.
          -- unfold Val.of_bool. des_ifs; econs.
          -- unfold Val.of_bool. des_ifs; econs.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          repeat erewrite (@eval_testcond_inj rs_src0 rs_tgt0); ss; eauto.
          unfold goto_label, nextinstr. repeat f_equal.
        * repeat (eapply agree_step; eauto); ss.
          eapply Val.offset_ptr_inject. apply agree_step; eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          repeat erewrite (@eval_testcond_inj rs_src0 rs_tgt0); ss; eauto.
          unfold goto_label, nextinstr. repeat f_equal.
        * repeat (eapply agree_step; eauto); ss.
          eapply Val.offset_ptr_inject. eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
          instantiate (1 := match eval_testcond c rs_tgt0 with
                            | Some true => (nextinstr rs_tgt0 # rd <- (rs_tgt0 r1))
                            | Some false =>  (nextinstr rs_tgt0)
                            | None => (nextinstr rs_tgt0 # rd <- Vundef)
                            end).
          des_ifs; eauto.
        * unfold nextinstr. des_ifs; ss; repeat eapply agree_step; eauto.
          -- apply Val.offset_ptr_inject.
             repeat (rewrite Pregmap.gso; [| ii; clarify]). eauto.
          -- unfold Pregmap.set. ii. des_ifs; eauto.
          -- apply Val.offset_ptr_inject.
             repeat (rewrite Pregmap.gso; [| ii; clarify]). eauto.
          -- apply Val.offset_ptr_inject.
             repeat (rewrite Pregmap.gso; [| ii; clarify]). eauto.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + esplits; eauto.
        * econs; eauto; ss.
        * repeat (eapply agree_step; eauto); ss.
          -- unfold Val.of_optbool.
             des_ifs; try econs.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
          -- apply Val.offset_ptr_inject. apply agree_step; eauto.
             unfold Val.of_optbool.
             des_ifs; try econs.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_inj in Heq0; ss; eauto; clarify.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * repeat (eapply agree_step; eauto); ss.
          -- unfold compare_floats.
             cinv (AGREE r1); ss; repeat (eapply agree_step; eauto).
             ++ cinv (AGREE r2); ss; repeat (eapply agree_step; eauto).
                ** unfold Val.of_bool. des_ifs; econs.
                ** unfold Val.of_bool. des_ifs; econs.
                ** unfold Val.of_bool. des_ifs; econs.
                ** des_ifs; repeat (eapply agree_step; eauto).
             ++ des_ifs; repeat (eapply agree_step; eauto).
          -- apply Val.offset_ptr_inject.
             unfold compare_floats.
             cinv (AGREE r1); ss; repeat (eapply agree_step; eauto).
             ++ cinv (AGREE r2); ss; repeat (eapply agree_step; eauto).
                ** unfold Val.of_bool. des_ifs; econs.
                ** unfold Val.of_bool. des_ifs; econs.
                ** unfold Val.of_bool. des_ifs; econs.
                ** des_ifs; repeat (eapply agree_step; eauto).
             ++ des_ifs; repeat (eapply agree_step; eauto).
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * unfold nextinstr.
          apply agree_step; eauto.
          -- unfold compare_floats32.
             agree_inv AGREE; repeat (eapply agree_step; eauto).
             ++ agree_inv AGREE; repeat (eapply agree_step; eauto);
                  try (unfold Val.of_bool; des_ifs; econs).
                des_ifs; repeat (eapply agree_step; eauto);
                  try (unfold Val.of_bool; des_ifs; econs).
             ++ des_ifs; repeat (eapply agree_step; eauto);
                  try (unfold Val.of_bool; des_ifs; econs).
          -- apply Val.offset_ptr_inject; eauto.
             unfold compare_floats32.
             cinv (AGREE r1); ss; unfold Pregmap.set; des_ifs; clarify; ss.
        * eapply inject_separated_refl.
        * refl.
        * refl.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
        erewrite eval_testcond_inj; ss; eauto. unfold goto_label, nextinstr. des_ifs; clarify.
        repeat f_equal. tac_p.
      + tac_cal AGREE.
        erewrite eval_testcond_inj; ss; eauto. unfold goto_label, nextinstr.
        repeat f_equal. agree_inv AGREE; eq_closure_tac_typ val. f_equal. tac_p.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_inj rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr. des_ifs; clarify.
        repeat f_equal. tac_p.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_inj rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr.
        repeat f_equal. agree_inv AGREE; eq_closure_tac_typ val. f_equal. tac_p.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_inj rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr.
        repeat f_equal. agree_inv AGREE; eq_closure_tac_typ val. tac_p.
      + tac_cal AGREE.
        * replace (rs_tgt0 r) with (Vint i); cycle 1.
          { cinv (AGREE r); eq_closure_tac_typ val. }
          rewrite Heq0. unfold goto_label. rewrite Heq1.
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]).
          rewrite <- H1. repeat f_equal. instantiate (1:=0). tac_p.
        * repeat (rewrite Pregmap.gso in *; [| ii; clarify; fail]).
          rewrite H3 in *; clarify.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_ld.
      + tac_st.
      + tac_ld.
      + tac_st.
      + tac_cal AGREE.
      + admit "allocframe".
      + admit "freeframe".

    - exploit eval_builtin_args_inject; eauto. i. des.
      exploit ec_mem_inject; eauto.
      { apply external_call_spec. }
      i. des.
      esplits; eauto.
      + cinv (AGREE PC); eq_closure_tac_typ val. econs 2; eauto.
        * unfold Genv.find_funct_ptr in *. instantiate (1:=f).
          des_ifs_safe.
          exploit DEFLE; eauto. i. des. rewrite FINDTGT.
          inv DEFMATCH. auto.
        * assert (delta = 0).
          { unfold Genv.find_funct_ptr in *.
            des_ifs_safe.
            exploit DEFLE; eauto. i. des. auto. }
          clarify.
          psimpl. eauto.
      + eapply agree_incr in AGREE; eauto.
        unfold nextinstr_nf. eapply nextinstr_agree.
        eapply undef_regs_agree.
        eapply set_res_agree; eauto.
        eapply undef_regs_agree. eauto.
      + eapply Mem.unchanged_on_implies; eauto. i. des. eauto.
      + eapply Mem.unchanged_on_implies; eauto. i. des. eauto.

    - exploit extcall_arguments_inject; eauto. i. des.
      exploit ec_mem_inject; eauto.
      { apply external_call_spec. }
      i. des.
      esplits; eauto.
      + cinv (AGREE PC); eq_closure_tac_typ val. econs 3; eauto.
        * assert (delta = 0).
          { unfold Genv.find_funct_ptr in *.
            des_ifs_safe.
            exploit DEFLE; eauto. i. des. auto. }
          clarify.
          psimpl. eauto.
        * unfold Genv.find_funct_ptr in *.
          unfold Genv.find_funct_ptr in *.
          des_ifs_safe.
          exploit DEFLE; eauto. i. des. rewrite FINDTGT.
          inv DEFMATCH. auto.
      + eapply agree_step; eauto.
        eapply set_pair_inject; eauto.
        eapply regset_after_external_inject; eauto.
        eapply agree_incr; eauto.
      + eapply Mem.unchanged_on_implies; eauto. i. des. eauto.
      + eapply Mem.unchanged_on_implies; eauto. i. des. eauto.
  Qed.

End ASMSTEP.