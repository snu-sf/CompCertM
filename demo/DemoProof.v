Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import CtypesC CminorC Csyntax AsmC.
Require Import sflib.

Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import MatchSimModSem.

Require DemoSource.
Require DemoTarget.
Require Import DemoHeader.

Require Import Floats Integers IntegersC.
Require Import Fappli_rnd_odd.
Definition round_to_odd (v: val): val := Val.orl (Val.shrlu v (Vint Int.one)) (Val.andl v (Vlong Int64.one)).

Lemma arithmetic_fact
      l
  :
    Val.floatoflongu (Vlong l) =
    if zlt l.(Int64.unsigned) Int64.half_modulus
    then Val.floatoflong (Vlong l)
    else
      match Val.floatoflong (round_to_odd (Vlong l)) with
      | Some half => Some (Val.addf half half)
      | None => None
      end
.
Proof.
  ss.
  destruct (classic (Int64.unsigned l < 2 ^ 53)).
  { ss.
    assert(T: zlt (Int64.unsigned l) Int64.half_modulus).
    { des_sumbool.
      rewrite Int64.half_modulus_power in *. ss. rewrite two_power_pos_correct in *.
      rewrite Z.pow_pos_fold in *.
      etrans; eauto.
      eapply Z.pow_lt_mono_r; try xomega.
    }
    assert(T0: Int64.unsigned l <= Z.pow_pos 2 53).
    {
      rewrite Int64.half_modulus_power in *. ss. rewrite two_power_pos_correct in *.
      apply Z.lt_le_incl in H.
      rewrite Z.pow_pos_fold in *.
      etrans; eauto.
      eapply Z.pow_le_mono_r; try xomega.
    }
    assert(T1: Z.abs (Int64.signed l) <= Z.pow_pos 2 53).
    {
      unfold Z.abs, Int64.signed. des_ifs; try congruence.
      generalize (Zlt_neg_0 p); i.
      generalize (Int64.unsigned_range l); i.
      xomega.
    }
    des_ifs. do 2 f_equal.
    apply Float.of_longu_of_long_1.
    unfold Int64.ltu. des_ifs.
  }
  ss.
  destruct (Int64.ltu l (Int64.repr Int64.half_modulus)) eqn:T;
    dup T; unfold Int64.ltu in T; des_ifs; do 2 f_equal; clear_tac.
  {
    assert(Z.pow_pos 2 53 <= Int64.unsigned l) by lia.
    assert(T: 2 ^ 36 <= (Int64.unsigned l)).
    {
      ss.
      rewrite Z.pow_pos_fold in *.
      etrans; eauto.
      eapply Z.pow_le_mono_r; try xomega.
    }
    assert(T1: Z.pow_pos 2 36 <= Z.abs (Int64.signed l)).
    {
      ss. etrans; eauto.
      unfold Int64.signed.
      des_ifs.
      lia.
    }
    (* unfold Float32.of_longu. *)
    (* rewrite Float32.of_long_round_odd. *)
    rewrite Float.of_longu_of_long_1; ss.
  }
  { rename g0 into G.
    unfold Val.addfs.
    des_ifs.
    unfold Val.floatoflong, round_to_odd in *. des_ifs.
    f_equal.
    Local Opaque Val.shrlu.
    apply Z.ge_le in G.
    rewrite Int64.half_modulus_power in *. ss.
    rewrite two_power_pos_correct in *.
    assert(P0: Z.pow_pos 2 36 <= Int64.unsigned l).
    { etrans; eauto. unfold Val.orl in *. des_ifs. }
    (* des_ifs. ss. clarify. *)
    rename i into rto.
    assert(P1: Z.pow_pos 2 36 <= (Z.abs (Int64.signed (Int64.or (Int64.shru' l Int.one)
                                                                (Int64.and l Int64.one))))).
    { clear - G.
      assert(Z.pow_pos 2 36 <= (Int64.signed (Int64.or (Int64.shru' l Int.one) (Int64.and l Int64.one))));
        try lia.
      rewrite Int64.signed_eq_unsigned; cycle 1.
      {
        unfold Int64.max_signed.
        assert(Int64.unsigned (Int64.or (Int64.shru' l Int.one) (Int64.and l Int64.one)) < Int64.half_modulus);
          try lia.
        rewrite Int64.half_modulus_power.
        assert(Z.max (Int64.size (Int64.shru' l Int.one)) (Int64.size (Int64.and l Int64.one))
               <= (Int64.zwordsize - 1)).
        { ss.
          assert((Int64.size (Int64.shru' l Int.one)) <= 63).
          { apply Int64.bits_size_3; ss.
            i. unfold Int64.zwordsize in *. ss.
            assert(i = 63) by lia. clarify.
            rewrite Int64.bits_shru'; ss.
          }
          assert((Int64.size (Int64.and l Int64.one)) <= 63).
          { etrans.
            { eapply Int64.size_and; eauto. }
            etrans.
            { eapply Z.le_min_r; eauto. }
            ss.
          }
          lia.
        }
        hexploit (Int64.or_interval (Int64.shru' l Int.one) (Int64.and l Int64.one)); eauto. intro P; des.
        eapply Z.lt_le_trans; eauto.
        eapply two_p_monotone; eauto.
        split.
        { etrans; cycle 1.
          { eapply Z.le_max_r. }
          eapply Int64.size_range; eauto.
        }
        {
          ss.
        }
      }
      etrans; cycle 1.
      { eapply Int64.or_le; eauto. }
      rewrite Int64.unsigned_repr in *; ss.
      (* assert(Int64.unsigned l <= 2 * Int64.unsigned (Int64.shru' l Int.one)). *)
      (* { *)
      (* } *)
      assert(Int64.testbit l 63 = true).
      { rewrite Int64.sign_bit_of_unsigned. des_ifs. rewrite Int64.half_modulus_power in *. ss.
        rewrite two_power_pos_correct in *. lia.
      }
      assert(Int64.testbit (Int64.shru' l Int.one) 62 = true).
      { rewrite Int64.bits_shru'; cycle 1.
        { ss. }
        des_ifs.
      }
      hexploit (Int64.bits_le (Int64.repr (2 ^ 62)) (Int64.shru' l Int.one)).
      { i.
        Local Opaque Z.shiftr Z.testbit.
        rewrite Int64.testbit_repr in *; try by ss.
        destruct (zeq i 62); cycle 1.
        { rewrite Z.pow2_bits_false in *; ss. lia. }
        clarify.
      }
      intro P.
      etrans; eauto.
      rewrite Int64.unsigned_repr; ss.
    }

    f_equal.
    rewrite Float.of_longu_of_long_2; ss.
    rewrite Float.mul2_add.
    f_equal.
    f_equal.
    Local Transparent Val.shrlu.
    unfold Val.orl in *. ss. des_ifs.
  }
Qed.


Program Definition mp: ModPair.t :=
  ModPair.mk DemoSource.md DemoTarget.md tt.

Program Definition nat_idx (n: nat): Ord.idx := @Ord.mk nat Nat.lt _ _.

Lemma nat_S_ord n:
  Ord.ord (nat_idx n) (nat_idx (S n)).
Proof. eapply Ord.lift_idx_spec. ss. Qed.
Hint Resolve nat_S_ord.

Lemma E0_double:
  E0 = E0 ** E0.
Proof. auto. Qed.
Hint Resolve E0_double.

Require Import StoreArguments.

Theorem correct
  :
    ModPair.sim mp
.
Proof.
  econs; eauto; ss. i. inv SSLE.
  econs; ss; i.
  { i. eapply SoundTop.sound_state_local_preservation. }
  { i. eapply Preservation.local_preservation_noguarantee_weak; eauto. eapply SoundTop.sound_state_local_preservation. }

  assert (FPTRSRC: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program Cminor.fn_sig DemoSource.prog)) DemoSource.prog) (Args.fptr args_src) =
                   Some (AST.Internal DemoSource.func)).
  { clear - INCLSRC FINDFSRC WFSRC.
    unfold Genv.find_funct in *. des_ifs.
    apply Genv.find_funct_ptr_iff in FINDFSRC. apply Genv.find_funct_ptr_iff.
    unfold SkEnv.revive. exploit SkEnv.project_impl_spec; eauto. i. inv H.
    erewrite Genv_map_defs_def_inv; eauto. unfold o_bind, o_join, o_map.
    destruct (Genv.invert_symbol skenv_link_src b) eqn:SEQ; cycle 1.
    { exploit DEFORPHAN; eauto. i. des. clarify. }
    exploit DEFKEPT; eauto. i. des. apply prog_defmap_image in PROG. ss. des; clarify.
    apply Genv.invert_find_symbol in SEQ.
    exploit Genv.find_invert_symbol.
    - erewrite SYMBKEEP; eauto.
    - intros INVSYMB. rewrite INVSYMB. ss. }
  assert (FPTRTGT: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig DemoTarget.prog)) DemoTarget.prog)
                                   (Args.fptr args_tgt) = Some (AST.Internal (DemoTarget.func))).
  { clear - INCLTGT FINDFTGT WFTGT.
    unfold Genv.find_funct in *. des_ifs.
    apply Genv.find_funct_ptr_iff in FINDFTGT. apply Genv.find_funct_ptr_iff.
    unfold SkEnv.revive. exploit SkEnv.project_impl_spec; eauto. i. inv H.
    erewrite Genv_map_defs_def_inv; eauto. unfold o_bind, o_join, o_map.
    destruct (Genv.invert_symbol skenv_link_tgt b) eqn:SEQ; cycle 1.
    { exploit DEFORPHAN; eauto. i. des. clarify. }
    exploit DEFKEPT; eauto. i. des. apply prog_defmap_image in PROG. ss. des; clarify.
    apply Genv.invert_find_symbol in SEQ.
    exploit Genv.find_invert_symbol.
    - erewrite SYMBKEEP; eauto.
    - intros INVSYMB. rewrite INVSYMB. ss. }

  esplits; ss; i; cycle 1.
  { des. inv SAFESRC. clarify. inv SIMARGS. ss.
    eapply asm_initial_frame_succeed; eauto; ss.
    eapply inject_list_length in VALS.
    rewrite <- LEN. eauto. }

  clear SAFESRC.
  inv INITTGT. clarify. inv TYP. ss. destruct args_tgt. ss.
  destruct vs; clarify. destruct vs; clarify; ss.
  inv SIMARGS. ss. clarify. inv VALS. inv H3. destruct args_src.
  ss. clarify. clear SZ. unfold AsmC.store_arguments in *. des.
  dup STORE0. inv STORE0.
  unfold typify_list, zip in *. inv VALS. des_ifs_safe.
  unfold Conventions1.loc_arguments, Conventions1.size_arguments in *. ss. des_ifs.
  inv H3. inv H0.

  eexists. eexists (SimMemInj.mk _ _ _ _ _ _ _). esplits; eauto.
  - econs; ss; eauto; try refl.
    econs. i. des. clarify.
  - econs; eauto. ss.
  - unfold Genv.find_funct in FINDF. des_ifs.
    instantiate (1:=nat_idx 10).
    destruct (Val.floatoflongu (typify v0 AST.Tlong)) eqn:VEQ; cycle 1.
    { instantiate (1:=unit). unfold lxsim. pcofix CIH. pfold. ss.
      econs 1. ii.
      econs 1; cycle 2.
      { eapply CminorC.modsem_receptive; eauto. }
      { split; ii.
        - inv H0. inv H1. clarify.
        - inv H0. inv H1. }
      ii. ss. inv STEPSRC; ss; clarify.
      esplits; auto.
      - right. splits; eauto. econs 1.
      - refl.
      - left. pfold. econs 1. ii.
        econs 1; cycle 2.
        { eapply CminorC.modsem_receptive; eauto. }
        { split; ii.
          - inv H0. inv H1.
          - inv H0. inv H1. }
        ii. ss. inv STEPSRC. inv H11. ss. inv H3. ss. clarify. }

    dup VEQ. unfold typify, to_mregset in *. ss.
    unfold Val.floatoflongu in VEQ0. des_ifs; inv H2; ss.
    rename H into RDIV.

    unfold lxsim. pcofix CIH. pfold. ss.
    econs 2. i; des.

    splits; cycle 1.
    { esplits. instantiate (1:= mkstate _ (State _ _)). econs; ss.
      econs; eauto; [des_ifs|ss]. }

    rewrite Z.mul_0_r in *.
    destruct (Mem.alloc (SimMemInj.src sm_arg) 0 0) eqn:MEQ0.
    destruct (Mem.free m b0 0 0) eqn:MEQ1; cycle 1.
    { exfalso. hexploit Mem.range_perm_free.
      - ii. exfalso. instantiate (1:=0) in H. instantiate (1:=0) in H. nia.
      - intros [m2 FREE]. rewrite MEQ1 in *. clarify. }
    destruct (Mem.free (JunkBlock.assign_junk_blocks m0 n) (Mem.nextblock (SimMemInj.tgt sm_arg)) 0 0) eqn:MEQ2; cycle 1.
    { exfalso. hexploit Mem.range_perm_free.
      - ii. exfalso. instantiate (1:=0) in H. instantiate (1:=0) in H. nia.
      - intros [m3 FREE]. rewrite MEQ2 in *. clarify. }

    assert (exists sm1, ((<<MWF: SimMemInj.wf' sm1>>) /\
                         (<<MLE: SimMemInj.le' sm_arg sm1>>) /\
                         (<<MEMSRC: SimMemInj.src sm1 = m2>>) /\
                         (<<MEMTGT: SimMemInj.tgt sm1 = m3>>))).
    { hexploit SimMemInj.alloc_parallel; try refl; eauto.
      i. des. rewrite ALC in *. clarify.

      set (sm2 := SimMemInjC.update
                    sm1
                    (SimMemInj.src sm1) m0 (SimMemInj.inj sm1)).
      assert (MWF1: SimMemInj.wf' sm2).
      { unfold sm2. inv MWF0. econs; eauto; ss.
        - eapply MemoryC.private_unchanged_inject; eauto.
          ii. des_ifs. omega.
        - ii. eapply TGTEXT in PR. inv PR. econs; ss.
          unfold SimMemInj.valid_blocks, Mem.valid_block.
          rewrite <- NB. auto.
        - etrans; eauto. rewrite NB. refl. }
      assert (MLE1: SimMemInj.le' sm1 sm2).
      { unfold sm2. econs; eauto.
        - refl.
        - eapply Mem.unchanged_on_implies; eauto.
          i. ss. des_ifs. omega.
        - eapply SimMemInj.frozen_refl.
        - i. ss. ii.
          eapply Mem.unchanged_on_perm; eauto. ss. des_ifs. omega. }
      exploit SimMemInjC.inject_junk_blocks_tgt; eauto.
      i. des. clarify.
      exploit SimMemInj.free_parallel; eauto.
      i. des. exists sm0. esplits; eauto.
      - etrans; eauto. etrans; eauto. etrans; eauto.
      - ss. instantiate (1:=n) in FREETGT.
        eapply Mem.alloc_result in ALC. rewrite ALC in *. clarify. }
    des.

    econs 2.
    { ss. split; cycle 1; eauto.
      econs 2; eauto.
      { econs; ss; eauto. }
      econs 2; eauto.
      { econs; ss; eauto. econs; eauto.
        - econs; ss.
        - unfold typify. des_ifs. }
      econs 1; eauto. }

    assert (NEXT0: (compare_longs (Val.andl (rs RDI) (rs RDI)) (Vlong Int64.zero) rs (JunkBlock.assign_junk_blocks m0 n)) PC
                   = Vptr b Ptrofs.zero).
    { unfold compare_longs, Pregmap.set in *. des_ifs. }
    assert (RDI0: (compare_longs (Val.andl (rs RDI) (rs RDI)) (Vlong Int64.zero) rs (JunkBlock.assign_junk_blocks m0 n)) RDI
                  = Vlong i).
    { unfold compare_longs, Pregmap.set in *. des_ifs. }
    assert (SF0: (compare_longs (Val.andl (rs RDI) (rs RDI)) (Vlong Int64.zero) rs (JunkBlock.assign_junk_blocks m0 n)) SF
                 = if (Int64.lt i Int64.zero)
                   then (Vint Int.one)
                   else (Vint Int.zero)).
    { unfold compare_longs, Pregmap.set. ss. rewrite <- RDIV. ss.
      unfold Int64.negative. rewrite Int64.and_idem. rewrite Int64.sub_zero_l.  des_ifs. }
    assert (RA0: (compare_longs (Val.andl (rs RDI) (rs RDI)) (Vlong Int64.zero) rs (JunkBlock.assign_junk_blocks m0 n)) RA
                 = rs RA).
    { unfold compare_longs, Pregmap.set in *. des_ifs. }
    Local Opaque compare_longs.

    left. pfold. econs 1. intros _.
    destruct (Int64.lt i Int64.zero) eqn:CASE.

    + econs 2.
      * split; eauto.
        econs; eauto; [econs;[eapply modsem_determinate; eauto|]; instantiate (1:= mkstate _ _); econs; ss; econs; ss; eauto; [des_ifs| ..];ss|];
          unfold nextinstr_nf, nextinstr, undef_regs;
          repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0); des_ifs.

        do 9 (econs 2; eauto; [econs;[eapply modsem_determinate; eauto|]; instantiate (1:= mkstate _ _); econs; ss; econs; ss; eauto; [des_ifs| ..];ss|];
          unfold nextinstr_nf, nextinstr, undef_regs;
          repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0); des_ifs).
        econs 1; eauto.
      * left. pfold. econs 4; cycle 2; ss.
        -- econs; ss; eauto.
           ++ ii. unfold Conventions1.is_callee_save in *.
              des_ifs; unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           ++ esplits; eauto. rewrite Heq. ss. des_ifs. eauto.
           ++ unfold Conventions1.size_arguments. des_ifs. ss. zsimpl. eauto.
           ++ unfold Conventions1.loc_result. des_ifs.
           ++ unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
              unfold external_state. des_ifs. exfalso.
              unfold Genv.find_funct, Genv.find_funct_ptr in Heq2. des_ifs.
              eapply Genv.genv_defs_range in Heq3.
              exploit RANOTFPTR; eauto.
           ++ destruct (Genv.find_funct skenv_link_tgt (rs RA)) eqn:FINDRA; auto.
              unfold Genv.find_funct, Genv.find_funct_ptr in FINDRA. des_ifs.
              exfalso. eapply Genv.genv_defs_range in Heq2.
              exploit RANOTFPTR; eauto.
        -- instantiate (1:= sm1).
           unfold nextinstr_nf, nextinstr, undef_regs;
             repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           econs; ss; eauto.
           rpapply Val.inject_float. clear - CASE.
           unfold Int64.lt, Int64.signed in *. des_ifs.
           { rewrite Int64.unsigned_zero in *. set (Int64.unsigned_range_2 i). nia. }
           ss. rewrite Float.mul2_add. rewrite Float.of_longu_of_long_2; auto.
           unfold Int64.ltu. des_ifs.
        -- ss.
        -- eauto.

    + econs 2.
      * split; eauto.
        econs; eauto; [econs;[eapply modsem_determinate; eauto|]; instantiate (1:= mkstate _ _); econs; ss; econs; ss; eauto; [des_ifs| ..];ss|];
          unfold nextinstr_nf, nextinstr, undef_regs;
          repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0); des_ifs.
        do 4 (econs 2; eauto; [econs;[eapply modsem_determinate; eauto|]; instantiate (1:= mkstate _ _); econs; ss; econs; ss; eauto; [des_ifs| ..];ss|];
              unfold nextinstr_nf, nextinstr, undef_regs;
              repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0); des_ifs).
        econs 1; eauto.
      * left. pfold. econs 4; cycle 2; ss.
        -- econs; ss; eauto.
           ++ ii. unfold Conventions1.is_callee_save in *.
              des_ifs; unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           ++ esplits; eauto. rewrite Heq. ss. des_ifs. eauto.
           ++ unfold Conventions1.size_arguments. des_ifs. ss. zsimpl. eauto.
           ++ unfold Conventions1.loc_result. des_ifs.
           ++ unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
              unfold external_state. des_ifs. exfalso.
              unfold Genv.find_funct, Genv.find_funct_ptr in Heq2. des_ifs.
              eapply Genv.genv_defs_range in Heq3.
              exploit RANOTFPTR; eauto.
           ++ destruct (Genv.find_funct skenv_link_tgt (rs RA)) eqn:FINDRA; auto.
              unfold Genv.find_funct, Genv.find_funct_ptr in FINDRA. des_ifs.
              exfalso. eapply Genv.genv_defs_range in Heq2.
              exploit RANOTFPTR; eauto.
        -- instantiate (1:= sm1).
           unfold nextinstr_nf, nextinstr, undef_regs;
             repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           econs; ss; eauto.
           rpapply Val.inject_float. clear - CASE.
           f_equal. rewrite Float.of_longu_of_long_1; auto.
           set (Int64.unsigned_range i).
           unfold Int64.ltu, Int64.lt, Int64.signed in *. zsimpl. des_ifs.
           rewrite Int64.unsigned_zero in *. rewrite Int64.unsigned_repr in *; nia.
        -- ss.
        -- eauto.
           Unshelve. all: eauto.
Qed.
