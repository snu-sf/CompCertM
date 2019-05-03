Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC Lia IntegersC SimMemInj AsmStepInj.
Require Import mktac.
Set Implicit Arguments.

Section ASMSTEP.

  Definition agree (rs_src rs_tgt: regset) : Prop :=
    forall pr, Val.lessdef (rs_src pr) (rs_tgt pr).

  Lemma agree_step rs0 rs1 pr v0 v1
        (AGREE: agree rs0 rs1)
        (INJ: Val.lessdef v0 v1)
    :
      agree (rs0 # pr <- v0) (rs1 # pr <- v1).
  Proof.
    ii. unfold Pregmap.set. des_ifs.
  Qed.

  Lemma extcall_arg_extends rs1 rs2 m1 m2 l arg1
        (AGREE: agree rs1 rs2)
        (EXT: Mem.extends m1 m2)
        (ARGS: extcall_arg rs1 m1 l arg1)
    :
      exists arg2 : val,
        (<<ARGEXT: Val.lessdef arg1 arg2>>) /\
        (<<ARGS: extcall_arg rs2 m2 l arg2>>).
  Proof.
    inv ARGS.
    - esplits; eauto. econs.
    - exploit Mem.loadv_extends; try eassumption.
      + instantiate (1:=Val.offset_ptr (rs2 RSP) (Ptrofs.repr (fe_ofs_arg + 4 * ofs))).
        unfold inject_id in *. cinv (AGREE RSP); try econs; clarify.
      + i. des. esplits; eauto.
        econs; eauto.
  Qed.

  Lemma extcall_arg_pair_extends rs1 rs2 m1 m2 l arg1
        (AGREE: agree rs1 rs2)
        (EXT: Mem.extends m1 m2)
        (ARGS: extcall_arg_pair rs1 m1 l arg1)
    :
      exists arg2 : val,
        (<<ARGEXT: Val.lessdef arg1 arg2>>) /\
        (<<ARGS: extcall_arg_pair rs2 m2 l arg2>>).
  Proof.
    inv ARGS.
    - exploit extcall_arg_extends; eauto. i. des. esplits; eauto.
      econs; eauto.
    - eapply extcall_arg_extends in H; eauto.
      eapply extcall_arg_extends in H0; eauto. des.
      esplits.
      + eapply Val.longofwords_lessdef; eauto.
      + econs; eauto.
  Qed.

  Lemma extcall_arguments_extends rs1 rs2 m1 m2 sg args1
        (AGREE: agree rs1 rs2)
        (EXT: Mem.extends m1 m2)
        (ARGS: extcall_arguments rs1 m1 sg args1)
    :
      exists args2 : list val,
        (<<ARGEXT: Val.lessdef_list args1 args2>>) /\
        (<<ARGS: extcall_arguments rs2 m2 sg args2>>).
  Proof.
    unfold extcall_arguments in *.
    revert args1 ARGS. induction (loc_arguments sg); ss; i; inv ARGS.
    - esplits; eauto. econs.
    - exploit IHl; eauto.
      exploit extcall_arg_pair_extends; eauto. i. des.
      exists (arg2::args2).
      esplits; eauto. econs; eauto.
  Qed.

  Remark mull_lessdef:
    forall v1 v1' v2,
      Val.lessdef v1 v1' ->
      Val.lessdef (Val.mull v1 v2) (Val.mull v1' v2).
  Proof.
    intros. unfold Val.mull. des_ifs; inv H. econs.
  Qed.

  Lemma eval_addrmode_extends
        ge rs_src0 rs_tgt0 a
        (AGREE: agree rs_src0 rs_tgt0)
    :
      Val.lessdef (eval_addrmode ge a rs_src0) (eval_addrmode ge a rs_tgt0).
  Proof.
    unfold eval_addrmode, eval_addrmode64 in *.
    des_ifs; ss; repeat (eapply Val.addl_lessdef; eauto).
    - eapply mull_lessdef; eauto.
    - eapply mull_lessdef; eauto.
    - cinv (AGREE i); econs.
    - cinv (AGREE i); econs.
    - cinv (AGREE i); econs.
    - cinv (AGREE i); econs.
  Qed.

  Lemma exec_load_extends
        ge chunk m_src0 m_tgt0 m_src1 a rd
        rs_src0 rs_tgt0 rs_src1
        (AGREE: agree rs_src0 rs_tgt0)
        (EXT: Mem.extends m_src0 m_tgt0)
        (EXEC: exec_load ge chunk m_src0 a rs_src0 rd = Next rs_src1 m_src1)
    :
      exists rs_tgt1,
        (<<MEMSAME: m_src0 = m_src1>>) /\
        (<<AGREE: agree rs_src1 rs_tgt1>>) /\
        (<<EXT: Mem.extends m_src1 m_tgt0>>) /\
        (<<EXEC: exec_load ge chunk m_tgt0 a rs_tgt0 rd = Next rs_tgt1 m_tgt0>>)
  .
  Proof.
    exploit eval_addrmode_extends; eauto. intros ADDR.
    instantiate (1:=a) in ADDR.
    unfold exec_load in *. des_ifs.
    - eapply Mem.loadv_extends in Heq0; eauto; des; clarify.
      esplits; eauto.
      repeat (eapply agree_step; eauto). ss.
      unfold Pregmap.set in *. des_ifs.
      + inv Heq1; eauto.
      + cinv (AGREE PC); eauto.
    - eapply Mem.loadv_extends in Heq0; eauto; des; clarify.
  Qed.

  Lemma undef_regs_agree l rs_src rs_tgt
        (AGREE : agree rs_src rs_tgt)
    :
      agree (undef_regs l rs_src) (undef_regs l rs_tgt).
  Proof.
    revert rs_src rs_tgt AGREE. induction l; ss; i. ii.
    unfold Pregmap.set in *.
    eapply IHl. ii. des_ifs.
  Qed.

  Lemma nextinstr_agree rs_src rs_tgt
        (AGREE: agree rs_src rs_tgt)
    :
      agree (nextinstr rs_src) (nextinstr rs_tgt).
  Proof.
    unfold nextinstr. apply agree_step; eauto.
    cinv (AGREE PC); eauto.
  Qed.

  Lemma exec_store_extends
        ge chunk m_src0 m_tgt0 m_src1 a rd l
        rs_src0 rs_tgt0 rs_src1
        (AGREE: agree rs_src0 rs_tgt0)
        (EXT: Mem.extends m_src0 m_tgt0)
        (EXEC: exec_store ge chunk m_src0 a rs_src0 rd l = Next rs_src1 m_src1)
    :
      exists rs_tgt1 m_tgt1,
        (<<AGREE: agree rs_src1 rs_tgt1>>) /\
        (<<EXT: Mem.extends m_src1 m_tgt1>>) /\
        (<<EXEC: exec_store ge chunk m_tgt0 a rs_tgt0 rd l = Next rs_tgt1 m_tgt1>>)
  .
  Proof.
    exploit eval_addrmode_extends; eauto. intros ADDR.
    hexploit undef_regs_agree; eauto. intros UAGREE.
    instantiate (1:=a) in ADDR.
    unfold exec_store in *. des_ifs.
    - exploit Mem.storev_extends; try apply Heq0; eauto.
      i. des. clarify. esplits; eauto.
      unfold nextinstr_nf, nextinstr. ss.
      repeat (eapply agree_step; eauto).
      unfold Pregmap.set in *. des_ifs.
      cinv (UAGREE PC); eauto.
    - eapply Mem.storev_extends in Heq0; cycle 1; eauto; des; clarify.
  Qed.

  Lemma regset_after_external_extends rs_src rs_tgt
        (AGREE: agree rs_src rs_tgt)
    :
      agree (regset_after_external rs_src) (regset_after_external rs_tgt).
  Proof.
    unfold regset_after_external in *. ii. des_ifs.
  Qed.

  Lemma set_pair_extends rs_src rs_tgt l v_src v_tgt
        (AGREE: agree rs_src rs_tgt)
        (VAL: Val.lessdef v_src v_tgt)
    :
      agree (set_pair l v_src rs_src) (set_pair l v_tgt rs_tgt).
  Proof.
    unfold set_pair. des_ifs; repeat (eapply agree_step; eauto).
    - eapply Val.hiword_lessdef; eauto.
    - eapply Val.loword_lessdef; eauto.
  Qed.

  Lemma eval_builtin_arg_extends A F V (ge: Genv.t F V) e1 e2 sp1 sp2 m1 m2
        (VALS: forall x : A, Val.lessdef (e1 x) (e2 x))
        (EXT: Mem.extends m1 m2)
        (a : builtin_arg A) (v1 : val)
        (EVAL: eval_builtin_arg ge e1 sp1 m1 a v1)
        (SPEXT: Val.lessdef sp1 sp2)
    :
      exists v2 : val,
        (<<EVAL: eval_builtin_arg ge e2 sp2 m2 a v2>>) /\
        (<<VAL: Val.lessdef v1 v2>>).
  Proof.
    revert v1 EVAL.
    induction a; i; inv EVAL; ss; try (esplits; eauto; econs; eauto; fail).
    - exploit Mem.loadv_extends; eauto; ss; i. inv SPEXT; ss.
      des. esplits; eauto. econs. auto.
    - esplits.
      + econs.
      + inv SPEXT; eauto.
    - exploit Mem.loadv_extends; eauto; ss; i.
      des. esplits; eauto. econs. auto.
    - eapply IHa1 in H1. eapply IHa2 in H3. des.
      esplits.
      + econs; eauto.
      + eapply Val.longofwords_lessdef; eauto.
    - eapply IHa1 in H1. eapply IHa2 in H3. des.
      esplits.
      + econs; eauto.
      + des_ifs. eapply Val.addl_lessdef; eauto.
  Qed.

  Lemma eval_builtin_args_extends A F V (ge: Genv.t F V) e1 e2 sp1 sp2 m1 m2
        (VALS: forall x : A, Val.lessdef (e1 x) (e2 x))
        (EXT: Mem.extends m1 m2)
        (al : list (builtin_arg A)) (vl1 : list val)
        (EVAL: eval_builtin_args ge e1 sp1 m1 al vl1)
        (SPEXT: Val.lessdef sp1 sp2)
    :
      exists vl2 : list val,
        (<<EVAL: eval_builtin_args ge e2 sp2 m2 al vl2>>) /\
        (<<VALLIST: Val.lessdef_list vl1 vl2>>).
  Proof.
    revert al EVAL. induction vl1; ss; i.
    - inv EVAL. esplits; econs.
    - inv EVAL.
      exploit IHvl1; eauto. i. des.
      exploit eval_builtin_arg_extends; eauto. i. des.
      exists (v2::vl2). splits; eauto. econs; eauto.
  Qed.

  Lemma set_res_agree res vres vres' rs_src rs_tgt
        (AGREE: agree rs_src rs_tgt)
        (EXT: Val.lessdef vres vres')
    :
      agree (set_res res vres rs_src) (set_res res vres' rs_tgt).
  Proof.
    revert rs_src rs_tgt AGREE vres vres' EXT. induction res; ss; i.
    - apply agree_step; eauto.
    - eapply IHres2; eauto.
      + eapply IHres1; eauto. eapply Val.hiword_lessdef; eauto.
      + eapply Val.loword_lessdef; eauto.
  Qed.

  Lemma cmplu_extends rs_src rs_tgt v1_src v2_src v1_tgt v2_tgt m_src m_tgt c
        (AGREE: agree rs_src rs_tgt)
        (EXT: Mem.extends m_src m_tgt)
        (VAL1: Val.lessdef v1_src v1_tgt)
        (VAL2: Val.lessdef v2_src v2_tgt)
    :
      Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m_src) c v1_src v2_src))
                  (Val.maketotal (Val.cmplu (Mem.valid_pointer m_tgt) c v1_tgt v2_tgt)).
  Proof.
    unfold Val.cmplu, Val.maketotal, option_map. Local Opaque Val.cmplu_bool.
    destruct (Val.cmplu_bool (Mem.valid_pointer m_src) c v1_src v2_src) eqn:EQ; ss.
    erewrite Val.cmplu_bool_lessdef; try apply EQ; eauto.
    i. unfold Mem.valid_pointer, proj_sumbool in *. des_ifs. exfalso.
    exploit Mem.perm_extends; eauto.
  Qed.

  Lemma compare_longs_extends rs_src rs_tgt v1_src v2_src v1_tgt v2_tgt m_src m_tgt
        (AGREE: agree rs_src rs_tgt)
        (EXT: Mem.extends m_src m_tgt)
        (VAL1: Val.lessdef v1_src v1_tgt)
        (VAL2: Val.lessdef v2_src v2_tgt)
    :
      agree
        (compare_longs v1_src v2_src rs_src m_src)
        (compare_longs v1_tgt v2_tgt rs_tgt m_tgt).
  Proof.
    unfold compare_longs.
    eapply agree_step; eauto.
    eapply agree_step; eauto; cycle 1.
    { inv VAL1; inv VAL2; clarify; ss. unfold Val.subl_overflow. des_ifs. }
    eapply agree_step; eauto; cycle 1.
    { inv VAL1; inv VAL2; clarify; ss. unfold Val.subl. des_ifs. }
    eapply agree_step; eauto; cycle 1.
    { eapply cmplu_extends; eauto. }
    eapply agree_step; eauto; cycle 1.
    { eapply cmplu_extends; eauto. }
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
    (all_once_fast ltac:(fun H => try (eapply exec_load_extends in H; try eassumption; check_safe;
                                       eauto; des; esplits; eauto; econs; eauto)));
    fail.

  Ltac tac_st :=
    (all_once_fast ltac:(fun H => try (eapply exec_store_extends in H; try eassumption; check_safe;
                                       eauto; des; esplits; eauto;econs; eauto)));
    fail.

  Ltac agree_inv AGREE :=
    match goal with
    | [|- context[(?rs: regset -> val) (?pr: preg)]] => cinv (AGREE pr)
    end; ss.

  Ltac agree_inv_strong AGREE :=
    match goal with
    | [|- context[(?rs: regset -> val) (?pr: preg)]] =>
      let X := fresh in set (X := AGREE pr); apply val_inject_id in X; inv X;
                        unfold inject_id in *; clarify
    end; ss.

  Ltac agree_invs AGREE := repeat (agree_inv_strong AGREE).

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
  
  Ltac tac_cal AGREE :=
    try (progress (unfold goto_label in *); des_ifs_safe);
         (esplits; eauto; [econs; eauto; ss; try (unfold goto_label in *; des_ifs; fail)
                          | repeat (eapply agree_step; eauto); ss;
                            (fail|| idtac; [.. |unfold Val.offset_ptr;
                                                repeat (try (rewrite Pregmap.gss);
                                                        (try (rewrite Pregmap.gso; [| ii; clarify; fail]))); des_ifs;
                                                try (econs; ss; tac_p)]);
                            (try ((agree_invs AGREE); ss; unfold option_map, Val.maketotal; des_ifs; ss; econs; ss; tac_p; check_safe))]).

  Lemma eval_testcond_ext rs_src rs_tgt c v
        (AGREE: agree rs_src rs_tgt)
        (EVAL: eval_testcond c rs_src = Some v)
    :
      eval_testcond c rs_tgt = Some v.
  Proof.
    unfold eval_testcond in *.
    destruct c; revert EVAL; agree_invs AGREE.
  Qed.

  Lemma Val_offset_ptr_lessdef v v' ofs
        (EXT: Val.lessdef v v')
    :
      Val.lessdef (Val.offset_ptr v ofs) (Val.offset_ptr v' ofs).
  Proof.
    inv EXT; ss.
  Qed.

  Local Opaque Mem.storev.
  Theorem asm_step_preserve_extension
        rs_src0 rs_src1 m_src0 m_src1 tr
        rs_tgt0 m_tgt0
        se ge
        (* (NOEXTFUN: no_extern_fun ge_src) *)
        (AGREE: agree rs_src0 rs_tgt0)
        (EXT: Mem.extends m_src0 m_tgt0)
        (STEP: Asm.step se ge (Asm.State rs_src0 m_src0) tr (Asm.State rs_src1 m_src1))
    :
      exists rs_tgt1 m_tgt1,
        (<<STEP: Asm.step se ge (Asm.State rs_tgt0 m_tgt0) tr (Asm.State rs_tgt1 m_tgt1)>>) /\
        (<<AGREE: agree rs_src1 rs_tgt1>>) /\
        (<<EXT: Mem.extends m_src1 m_tgt1>>)
  .
  Proof.
    inv STEP.

    - cinv (AGREE PC); eq_closure_tac.

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
        des_ifs; agree_invs AGREE; ss.
      + tac_cal AGREE.
        unfold eval_addrmode64. des_ifs.
        des_ifs; agree_invs AGREE; ss; (replace Archi.ptr64 with true; [|eauto]);
          (repeat (eapply Val.addl_inject); eauto); try econs; ss; tac_p.
        * apply Val.lessdef_same. f_equal. psimpl. auto.
        * apply Val.lessdef_same. f_equal. psimpl. auto.
        * repeat (eapply Val.addl_lessdef); eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
          eapply mull_lessdef; eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
          eapply mull_lessdef; eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
          eapply mull_lessdef; eauto.
        * repeat (eapply Val.addl_lessdef); eauto.
          eapply mull_lessdef; eauto.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE. repeat (eapply Val.addl_lessdef); eauto.
      + tac_cal AGREE.
      + tac_cal AGREE.
        agree_invs AGREE; des_ifs; unfold andb, proj_sumbool in *; des_ifs; clarify.
        * apply Val.lessdef_same. psimpl. auto.
        * apply Val.lessdef_same. psimpl. auto.
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
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]).
          cinv (AGREE PC); eauto.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]).
          cinv (AGREE PC); eauto.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
          cinv (AGREE PC); eauto.
      + esplits; eauto.
        * econs; eauto; ss.
          cinv (AGREE RDX); rewrite Heq in *; clarify.
          cinv (AGREE RAX); rewrite Heq0 in *; clarify.
          cinv (AGREE r1); rewrite Heq1 in *; clarify.
          rewrite Heq2.
          ss.
        * unfold nextinstr_nf, nextinstr; ss.
          repeat (eapply agree_step; eauto).
          repeat (rewrite Pregmap.gso; [| ii; clarify; fail]). eauto.
          cinv (AGREE PC); eauto.
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
          -- cinv (AGREE rd); ss. cinv (AGREE rd); ss. cinv (AGREE r1); ss.
             unfold Val.shl. des_ifs.
          -- repeat (try (rewrite Pregmap.gss);
                     (try (rewrite Pregmap.gso; [| ii; clarify; fail]))); des_ifs.
             cinv (AGREE PC); eauto.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          eapply compare_longs_extends; eauto.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          apply compare_longs_extends; eauto.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_ints. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
        * apply nextinstr_agree.
          unfold compare_longs. (repeat eapply agree_step; eauto); agree_invs AGREE.
      + esplits; eauto.
        * econs; eauto; ss.
          repeat erewrite (@eval_testcond_ext rs_src0 rs_tgt0); ss; eauto.
          unfold goto_label, nextinstr. repeat f_equal.
        * repeat (eapply agree_step; eauto); ss. unfold Pregmap.set. des_ifs.
          cinv (AGREE PC); ss.
      + esplits; eauto.
        * econs; eauto; ss.
          repeat erewrite (@eval_testcond_ext rs_src0 rs_tgt0); ss; eauto.
          unfold goto_label, nextinstr. repeat f_equal.
        * repeat (eapply agree_step; eauto); ss.
          cinv (AGREE PC); eauto.
      + esplits; eauto.
        * econs; eauto; ss.
          instantiate (1 := match eval_testcond c rs_tgt0 with
                            | Some true => (nextinstr rs_tgt0 # rd <- (rs_tgt0 r1))
                            | Some false =>  (nextinstr rs_tgt0)
                            | None => (nextinstr rs_tgt0 # rd <- Vundef)
                            end).
          des_ifs; eauto.
        * unfold nextinstr. des_ifs; ss; repeat eapply agree_step; eauto.
          -- repeat (rewrite Pregmap.gso; [| ii; clarify]). cinv (AGREE PC); eauto.
          -- unfold Pregmap.set. ii. des_ifs; eauto.
          -- repeat (rewrite Pregmap.gso; [| ii; clarify]). cinv (AGREE PC); eauto.
          -- repeat (rewrite Pregmap.gso; [| ii; clarify]). cinv (AGREE PC); eauto.
      + esplits; eauto.
        * econs; eauto; ss.
        * repeat (eapply agree_step; eauto); ss.
          -- unfold Val.of_optbool.
             des_ifs; try econs.
             ++ erewrite eval_testcond_ext in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_ext in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_ext in Heq0; ss; eauto; clarify.
             ++ erewrite eval_testcond_ext in Heq0; ss; eauto; clarify.
          -- unfold Pregmap.set. des_ifs. cinv (AGREE PC); ss.
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
             ++ cinv (AGREE r2); ss; des_ifs; repeat (eapply agree_step; eauto).
             ++ des_ifs; repeat (eapply agree_step; eauto).
          -- apply Val_offset_ptr_lessdef.
             unfold compare_floats.
             cinv (AGREE r1); ss; repeat (eapply agree_step; eauto).
             ++ cinv (AGREE r2); ss; des_ifs; repeat (eapply agree_step; eauto).
             ++ des_ifs; repeat (eapply agree_step; eauto).
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
             ++ cinv (AGREE r2); ss; des_ifs; repeat (eapply agree_step; eauto);
                  try (unfold Val.of_bool; des_ifs; econs).
             ++ des_ifs; repeat (eapply agree_step; eauto);
                  try (unfold Val.of_bool; des_ifs; econs).
          -- apply Val_offset_ptr_lessdef; eauto.
             unfold compare_floats32.
             cinv (AGREE r1); ss; unfold Pregmap.set; des_ifs; clarify; ss.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
        erewrite eval_testcond_ext; ss; eauto. unfold goto_label, nextinstr. des_ifs; clarify.
      + tac_cal AGREE.
        erewrite eval_testcond_ext; ss; eauto. unfold goto_label, nextinstr. repeat f_equal.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_ext rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr. des_ifs; clarify.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_ext rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr.
        repeat f_equal.
      + tac_cal AGREE.
        repeat erewrite (@eval_testcond_ext rs_src0 rs_tgt0); ss; eauto. unfold goto_label, nextinstr.
        repeat f_equal.
      + tac_cal AGREE.
        replace (rs_tgt0 r) with (Vint i); cycle 1.
        { cinv (AGREE r); eq_closure_tac_typ val. }
        rewrite Heq0. unfold goto_label. rewrite Heq1.
        repeat (rewrite Pregmap.gso; [| ii; clarify; fail]).
        rewrite <- EQ_CLOSURE_TAC. repeat f_equal. cinv (AGREE PC); eq_closure_tac.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_cal AGREE.
      + tac_ld.
      + tac_st.
      + tac_ld.
      + tac_st.
      + tac_cal AGREE.
      + exploit Mem.alloc_result; eauto. i. clarify.
        exploit Mem.alloc_extends; eauto; try refl. i. des.
        exploit Mem.storev_extends; try apply Heq0; eauto. i. des.
        exploit Mem.storev_extends; try apply Heq1; eauto. i. des.
        esplits; try apply EXT2; eauto.
        * econs; eauto. ss. rewrite H.
          psimpl. rewrite H1. rewrite H7. ss.
        * eapply nextinstr_agree; eauto.
          repeat eapply agree_step; eauto.

      + cinv (AGREE RSP); rewrite Heq1 in *; clarify.
        exploit Mem.free_parallel_extends; try apply Heq2; eauto. i. des.
        exploit Mem.load_extends; try apply Heq; eauto. i. des.
        exploit Mem.load_extends; try apply Heq0; eauto. i. des.

        esplits; eauto.
        * econs; eauto; ss. rewrite <- H4. ss.
          rewrite H1. rewrite H8. rewrite H. ss.
        * eapply nextinstr_agree. repeat eapply agree_step; eauto.

    - exploit eval_builtin_args_extends; eauto. i. des.
      exploit ec_mem_extends; eauto.
      { apply external_call_spec. }
      i. des.
      esplits; eauto.
      + cinv (AGREE PC); eq_closure_tac_typ val. econs 2; eauto.
      + unfold nextinstr_nf. eapply nextinstr_agree.
        eapply undef_regs_agree.
        eapply set_res_agree; eauto.
        eapply undef_regs_agree. eauto.

    - exploit extcall_arguments_extends; eauto. i. des.
      exploit ec_mem_extends; eauto.
      { apply external_call_spec. }
      i. des.
      esplits; eauto.
      + cinv (AGREE PC); eq_closure_tac_typ val. econs 3; eauto.
      + eapply agree_step; eauto.
        eapply set_pair_extends; eauto.
        eapply regset_after_external_extends; eauto.
  Qed.

End ASMSTEP.
