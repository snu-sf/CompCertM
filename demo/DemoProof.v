Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory Globalenvs Events Smallstep.
Require Import CtypesC CsemC Csyntax AsmC.
Require Import sflib.

Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemId.
Require SoundTop.
Require Import MatchSimModSem.

Require DemoSource.
Require DemoTarget.
Require Import DemoHeader.


Definition mp: ModPair.t := ModPair.mk DemoSource.md DemoTarget.md tt.

Theorem correct
  :
    ModPair.sim mp
.
Proof.
  econs; eauto.
  { ss. }
  i.
  (* eapply match_states_sim; eauto. *)
  admit "Prove this!".
Qed.

Require Import Floats Integers.
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
