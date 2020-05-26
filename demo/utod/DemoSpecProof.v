Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import Csyntax AsmC AsmExtra.
Require Import sflib.

Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import MatchSimModSem.

Require DemoSpec.
Require DemoTarget.
Require Import DemoHeader Any.

Require Import Floats Integers IntegersC.
(* Require Import Fappli_rnd_odd. *)
Definition round_to_odd (v: val): val := Val.orl (Val.shrlu v (Vint Int.one)) (Val.andl v (Vlong Int64.one)).

Lemma arithmetic_fact
      l
  :
    Val.floatoflongu (Vlong l) =
    if zlt (Int64.unsigned l) Int64.half_modulus
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
  ModPair.mk DemoSpec.module DemoTarget.md (SimSymbId.mk DemoSpec.module DemoTarget.md).

Program Definition nat_idx (n: nat): Ord.idx := @Ord.mk nat Nat.lt _ _.

Lemma nat_S_ord n:
  Ord.ord (nat_idx n) (nat_idx (S n)).
Proof. eapply Ord.lift_idx_spec. ss. Qed.
Hint Resolve nat_S_ord.

Lemma E0_double:
  E0 = E0 ** E0.
Proof. auto. Qed.
Hint Resolve E0_double.

Require Import StoreArguments StoreArgumentsProps.

Theorem correct
  :
    ModPair.sim mp
.
Proof.
  econs; eauto; ss. i. eexists. inv SSLE.
  econs; ss; i.
  { i. eapply SoundTop.sound_state_local_preservation. }
  { i. eapply Preservation.local_preservation_noguarantee_weak; eauto. eapply SoundTop.sound_state_local_preservation. }
  { esplits; et. }

  assert (FPTRTGT: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig DemoTarget.prog)) DemoTarget.prog)
                                   (Args.get_fptr args_tgt) = Some (AST.Internal (DemoTarget.func))).
  {  clear - INCLTGT FINDFTGT WFTGT.
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
  { des. inv SAFESRC. clarify. rr in SIMARGS; des. inv SIMARGS0; ss. clarify.
    eapply asm_initial_frame_succeed; eauto; ss.
    eapply inject_list_length in VALS.
    rewrite <- VALS. ss. }

  assert (ARGLONG: exists lng, (Args.vs args_src) = [Vlong lng]).
  { inv SAFESRC. inv H. rewrite VS. eauto. }
  inv INITTGT; ss; clarify. inv TYP. ss.
  rr in SIMARGS; des. inv SIMARGS0; ss. clarify. inv VALS; ss. rename H1 into HD. rename H3 into TL.
  inv TL; ss.
  ss. clarify. unfold AsmC.store_arguments in *. des.
  dup STORE0. inv STORE0.
  unfold typify_list, zip in *. inv VALS. des_ifs_safe.
  unfold Conventions1.loc_arguments, Conventions1.size_arguments in *. ss. des_ifs.
  inv H4.

  eexists (DemoSpec.mkstate lng (SimMemInj.src sm_arg)). esplits; eauto.
  - refl.
  - ss.
  - unfold Genv.find_funct in FINDF. des_ifs.
    instantiate (1:=nat_idx 10).
    destruct (Val.floatoflongu (typify (Vlong lng) AST.Tlong)) eqn:VEQ; cycle 1.
    { instantiate (1:=unit). unfold lxsim. pfold. ss.
      intros _. econs 1. ii. econs 1.
      - split; ii.
        + rr in H. des. inv H.
        + rr in H. des. inv H.
          clear - VEQ SPEC. unfold typify in *. clarify.
          des_ifs. ss.
      - ii. inv STEPSRC.
      - econs; ii; ss. }

    dup VEQ. unfold typify, to_mregset in *. ss.
    unfold Val.floatoflongu in VEQ0. des_ifs; inv HD; ss. inv H2. inv H0.
    rename H into RDIV.

    rewrite Z.mul_0_r in *.
    destruct (Mem.free (JunkBlock.assign_junk_blocks m0 n) (Mem.nextblock (SimMemInj.tgt sm_arg)) 0 0) as [m|] eqn:MEQ; cycle 1.
    { exfalso. hexploit Mem.range_perm_free.
      - ii. exfalso. instantiate (1:=0) in H. instantiate (1:=0) in H. nia.
      - intros [m FREE]. rewrite MEQ in *. clarify. }

    assert (exists sm1, ((<<MWF: SimMemInj.wf' sm1>>) /\
                         (<<MLE: SimMemInj.le' sm_arg sm1>>) /\
                         (<<MEMSRC: SimMemInj.src sm1 = SimMemInj.src sm_arg>>) /\
                         (<<MEMTGT: SimMemInj.tgt sm1 = m>>))).
    {
      assert (UNCH0: Mem.unchanged_on top2 (SimMemInj.tgt sm_arg) m).
      { etrans.
        - eapply store_arguments_unchanged_on; eauto.
        - etrans.
          + eapply JunkBlock.assign_junk_blocks_unchanged_on.
          + eapply Mem.free_unchanged_on; eauto. ii. omega. }
      dup UNCH0. eapply Mem.unchanged_on_nextblock in UNCH0.
      exists (SimMemInjC.update
                    sm_arg (SimMemInj.src sm_arg) m (SimMemInj.inj sm_arg)).
      unfold SimMemInjC.update; ss; eauto.
      split.
      - inv MWF. econs; ss; eauto.
        + eapply MemoryC.private_unchanged_inject; eauto.
        + etrans; eauto.
          unfold SimMemInj.tgt_private. ss. ii. des. split; eauto.
          unfold SimMemInj.valid_blocks, Mem.valid_block in *. xomega.
        + etrans; eauto.
      - esplits; eauto. econs; ss; eauto.
        + refl.
        + eapply Mem.unchanged_on_implies; eauto.
        + econs. ii. des. clarify. + econs. ii. des. clarify.
        + ii. eapply Mem.perm_unchanged_on_2; eauto. } des.

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
    { unfold compare_longs, Pregmap.set. ss. rewrite RDIV in *. ss.
      unfold Int64.negative. rewrite Int64.and_idem. rewrite Int64.sub_zero_l. des_ifs. }
    assert (RA0: (compare_longs (Val.andl (rs RDI) (rs RDI)) (Vlong Int64.zero) rs (JunkBlock.assign_junk_blocks m0 n)) RA
                 = rs RA).
    { unfold compare_longs, Pregmap.set in *. des_ifs. }
    Local Opaque compare_longs.

    pfold. econs 1. intros _.
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
      * eauto.
      * eauto.
      * left. pfold. econs 4; cycle 2; ss.
        -- et.
        -- econs; ss; eauto.
           ++ rewrite Heq. ss. des_ifs. esplits; eauto.
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
           ++ ii. unfold Conventions1.is_callee_save in *.
              des_ifs; unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           ++ unfold Conventions1.size_arguments. des_ifs. ss. zsimpl. eauto.
           ++ unfold Conventions1.loc_result. des_ifs.
        -- rr. esplits; ss; et.
           unfold nextinstr_nf, nextinstr, undef_regs;
             repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           econs; ss; eauto.
           rpapply Val.inject_float. clear - CASE.
           unfold Int64.lt, Int64.signed in *. des_ifs.
           { rewrite Int64.unsigned_zero in *. set (Int64.unsigned_range_2 i). nia. }
           ss. rewrite Float.mul2_add. rewrite Float.of_longu_of_long_2; auto.
           unfold Int64.ltu. des_ifs.
        -- refl.
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
      * eauto.
      * et.
      * left. pfold. econs 4; cycle 2; ss.
        -- et.
        -- econs; ss; eauto.
           ++ rewrite Heq. ss. des_ifs. esplits; eauto.
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
           ++ ii. unfold Conventions1.is_callee_save in *.
              des_ifs; unfold nextinstr_nf, nextinstr, undef_regs;
                repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           ++ unfold Conventions1.size_arguments. des_ifs. ss. zsimpl. eauto.
           ++ unfold Conventions1.loc_result. des_ifs.
        -- rr. esplits; ss; et.
           unfold nextinstr_nf, nextinstr, undef_regs;
             repeat ((try (rewrite Pregmap.gso by clarify));(try rewrite Pregmap.gss)); (repeat rewrite RDI0); (repeat rewrite SF0); (repeat rewrite RA0); (repeat rewrite NEXT0).
           econs; ss; eauto.
           rpapply Val.inject_float. clear - CASE.
           f_equal. rewrite Float.of_longu_of_long_1; auto.
           set (Int64.unsigned_range i).
           unfold Int64.ltu, Int64.lt, Int64.signed in *. zsimpl. des_ifs.
           rewrite Int64.unsigned_zero in *. rewrite Int64.unsigned_repr in *; nia.
        -- refl.
        -- eauto.
           Unshelve. all: eauto.
Qed.
