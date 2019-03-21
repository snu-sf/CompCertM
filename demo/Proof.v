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

Require Source.
Require Target.
Require Import Header.


Definition mp: ModPair.t := ModPair.mk Source.md Target.md tt.

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
(* double_round_mult_beta_odd_FLX *)
Definition round_to_odd (v: val): val := Val.orl (Val.shrlu v (Vint Int.one)) (Val.andl v (Vlong Int64.one)).

Axiom double_round_mult: forall
      X Y
  ,
    (Float32.mul (Float32.of_double X) (Float32.of_double Y))
    =
    (Float32.of_double (Float.mul X Y))
.

Definition X := Int64.repr (- 2048).
Definition Y := Int64.repr (2047).

Lemma x_bit_false
      j
      (RANGE: 0 <= j <= 10)
  :
    Int64.testbit X j = false
.
Proof.
  i.
  destruct (zeq j 0); clarify.
  destruct (zeq j 1); clarify.
  destruct (zeq j 2); clarify.
  destruct (zeq j 3); clarify.
  destruct (zeq j 4); clarify.
  destruct (zeq j 5); clarify.
  destruct (zeq j 6); clarify.
  destruct (zeq j 7); clarify.
  destruct (zeq j 8); clarify.
  destruct (zeq j 9); clarify.
  destruct (zeq j 10); clarify.
  xomega.
Qed.

Lemma x_bit_true
      j
      (RANGE: 11 <= j < 64)
  :
    Int64.testbit X j = true
.
Proof.
  i.
  destruct (zeq j 11); subst; ss.
  destruct (zeq j 12); subst; ss.
  destruct (zeq j 13); subst; ss.
  destruct (zeq j 14); subst; ss.
  destruct (zeq j 15); subst; ss.
  destruct (zeq j 16); subst; ss.
  destruct (zeq j 17); subst; ss.
  destruct (zeq j 18); subst; ss.
  destruct (zeq j 19); subst; ss.
  destruct (zeq j 20); subst; ss.
  destruct (zeq j 21); subst; ss.
  destruct (zeq j 22); subst; ss.
  destruct (zeq j 23); subst; ss.
  destruct (zeq j 24); subst; ss.
  destruct (zeq j 25); subst; ss.
  destruct (zeq j 26); subst; ss.
  destruct (zeq j 27); subst; ss.
  destruct (zeq j 28); subst; ss.
  destruct (zeq j 29); subst; ss.
  destruct (zeq j 30); subst; ss.
  destruct (zeq j 31); subst; ss.
  destruct (zeq j 32); subst; ss.
  destruct (zeq j 33); subst; ss.
  destruct (zeq j 34); subst; ss.
  destruct (zeq j 35); subst; ss.
  destruct (zeq j 36); subst; ss.
  destruct (zeq j 37); subst; ss.
  destruct (zeq j 38); subst; ss.
  destruct (zeq j 39); subst; ss.
  destruct (zeq j 40); subst; ss.
  destruct (zeq j 41); subst; ss.
  destruct (zeq j 42); subst; ss.
  destruct (zeq j 43); subst; ss.
  destruct (zeq j 44); subst; ss.
  destruct (zeq j 45); subst; ss.
  destruct (zeq j 46); subst; ss.
  destruct (zeq j 47); subst; ss.
  destruct (zeq j 48); subst; ss.
  destruct (zeq j 49); subst; ss.
  destruct (zeq j 50); subst; ss.
  destruct (zeq j 51); subst; ss.
  destruct (zeq j 52); subst; ss.
  destruct (zeq j 53); subst; ss.
  destruct (zeq j 54); subst; ss.
  destruct (zeq j 55); subst; ss.
  destruct (zeq j 56); subst; ss.
  destruct (zeq j 57); subst; ss.
  destruct (zeq j 58); subst; ss.
  destruct (zeq j 59); subst; ss.
  destruct (zeq j 60); subst; ss.
  destruct (zeq j 61); subst; ss.
  destruct (zeq j 62); subst; ss.
  destruct (zeq j 63); subst; ss.
  lia.
Qed.

Lemma lem
      l
  :
    Val.singleoflongu (Vlong l) =
    if zlt l.(Int64.unsigned) Int64.half_modulus
    then Val.singleoflong (Vlong l)
    else
      match Val.singleoflong (round_to_odd (Vlong l)) with
      | Some half => Some (Val.addfs half half)
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
    rewrite Float32.of_longu_double_1; ss.
    rewrite Float32.of_long_double_1; ss.
    f_equal.
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
    rewrite Float32.of_longu_double_2; ss.
    rewrite Float32.of_long_double_2; ss.
    rewrite Float.of_longu_of_long_1; ss.
    {
      unfold Int64.ltu. des_ifs.
      assert(TT: Int64.unsigned (Int64.and (Int64.or l (Int64.add (Int64.and l (Int64.repr 2047))
                                                                  (Int64.repr 2047)))
                                           (Int64.repr (- 2048)))
                 < Int64.unsigned (Int64.repr Int64.half_modulus)).
      {
        rewrite Int64.unsigned_repr; cycle 1.
        { unfold Int64.max_unsigned. unfold Int64.half_modulus. ss. }
        rewrite Int64.half_modulus_power.
        eapply Z.lt_le_trans.
        { eapply Int64.and_interval; eauto. }
        ss.
        etrans.
        { eapply two_p_monotone; eauto.
          split; ss.
          - admit "ez".
          - eapply Z.le_min_l; eauto.
        }
        assert((Int64.size (Int64.or l (Int64.add (Int64.and l (Int64.repr 2047)) (Int64.repr 2047))))
               <= 63); cycle 1.
        { rewrite two_p_equiv. rewrite two_power_pos_equiv.
          eapply Z.pow_le_mono_r; eauto. ss. }
        rewrite Int64.size_or.
        eapply Z.ge_le; eauto.
        rewrite Zmax_spec. des_ifs.
        - eapply Int64.size_interval_2; eauto; try lia.
          specialize (Int64.unsigned_range l); i.
          split; try lia.
          rewrite Int64.half_modulus_power in *. ss.
        - eapply Int64.size_interval_2; try lia.
          specialize (Int64.unsigned_range (Int64.add (Int64.and l (Int64.repr 2047)) (Int64.repr 2047))); i.
          split; try lia.
          rewrite Int64.unsigned_add_carry.
          assert(P: Int64.unsigned (Int64.and l (Int64.repr 2047)) <= Int64.unsigned (Int64.repr 2047)).
          { rewrite Int64.and_commut. eapply Int64.and_le; eauto. }
          assert(Q: Int64.unsigned (Int64.repr 2047) + Int64.unsigned (Int64.repr 2047) < two_power_pos 63).
          { rewrite Int64.unsigned_repr; ss. }
          assert(R: Int64.unsigned (Int64.and l (Int64.repr 2047)) + Int64.unsigned (Int64.repr 2047)
                    < two_power_pos 63).
          { lia. }
          assert(CARRY: (Int64.add_carry (Int64.and l (Int64.repr 2047)) (Int64.repr 2047) Int64.zero) = Int64.zero).
          { unfold Int64.add_carry. des_ifs. rewrite Int64.unsigned_zero in *.
            rewrite Int64.modulus_power in *. ss.
            assert(two_power_pos 63 < two_power_pos 64).
            { ss. }
            lia.
          }
          rewrite CARRY. ss. rewrite Int64.unsigned_zero. rewrite Z.mul_0_l. rewrite Z.sub_0_r.
          ss.
      }
      lia.
    }
  }
  { rename g0 into G.
    unfold Val.addfs.
    des_ifs.
    unfold Val.singleoflong, round_to_odd in *. des_ifs.
    f_equal.
    Local Opaque Val.shrlu.
    apply Z.ge_le in G.
    rewrite Int64.half_modulus_power in *. ss.
    rewrite two_power_pos_correct in *.
    assert(P0: Z.pow_pos 2 36 <= Int64.unsigned l).
    { etrans; eauto. admit "ez". }
    (* des_ifs. ss. clarify. *)
    rename i into rto.
    assert(P1: Z.pow_pos 2 36 <= (Z.abs (Int64.signed (Int64.or (Int64.shru' l Int.one) (Int64.and l Int64.one))))).
    { clear - G. admit "ez". }
    
    (* exploit Float.of_longu_of_long_2; eauto. intro K. *)
    rewrite Float32.mul2_add.
    rewrite Float32.of_longu_double_2; ss.
    rewrite Float32.of_long_double_2; ss.

    rewrite Float.of_longu_of_long_2; ss.
    {
      (* rewrite <- Float.mul2_add. *)
      fold X in *. fold Y in *.
      rewrite <- double_round_mult.
      do 2 f_equal; ss; cycle 1.
      { rewrite Float32.of_int_double. ss. }
      f_equal.
      eapply Int64.same_bits_eq; eauto.
      i.
      Local Transparent Val.shrlu.
      unfold Val.orl in *. ss. des_ifs.
      Ltac ibit := repeat (try rewrite ! Int64.bits_and; ss;
                           try rewrite ! Int64.bits_or; ss;
                           unfold Int64.zwordsize in *; try lia
                          ).
      ibit.
      rewrite ! Int64.bits_shru; ss.
      des_ifs; rewrite Int64.unsigned_one in *; cycle 1.
      { ss.
        unfold Int64.zwordsize in *; ss.
        assert(i = 63).
        { lia. }
        clarify.
        Local Opaque Z.sub Z.add Z.testbit.
        Local Opaque Int64.testbit.
        (* Local Opaque Z.testbit. *)

        (* unfold Int64.testbit. *)
        (* rewrite Int64.unsigned_one in *. *)
        (* replace (Z.testbit 1 63) with false; cycle 1. *)
        (* { ss. } *)
        Ltac bsimpl2 :=
          repeat (try rewrite ! andb_false_r;
                  try rewrite ! andb_false_l;
                  try rewrite ! orb_false_l;
                  try rewrite ! orb_false_r;
                  try rewrite ! andb_true_r;
                  try rewrite ! andb_true_l;
                  try rewrite ! orb_true_r;
                  try rewrite ! orb_true_l;
                  idtac
                 )
        .
        bsimpl2.
        symmetry.
        apply orb_false_intro.
        { rewrite Int64.bits_shru'; ss. }
        { unfold Y. admit "this should hold". }
      }
      (* assert(X_: Int64.testbit X 0 = false). *)
      (* { ss. } *)
      destruct (Int64.testbit Int64.one i) eqn:S0.
      { rewrite Int64.bits_one in *. des_sumbool. clarify.
        ibit. zsimpl. bsimpl. split; ss.
      }
      rewrite Int64.bits_one in *. des_sumbool.
      bsimpl2.
      destruct (classic (i <= 9)).
      {
        rewrite x_bit_false; try lia. bsimpl2.
        ibit.
        apply andb_false_intro2.
        apply x_bit_false. lia.
      }

      destruct (zeq i 10).
      {
        clarify.
        rewrite x_bit_false; try lia. bsimpl2.
        unfold X, Y. ibit.
        rewrite x_bit_true; try lia. bsimpl2.
        apply andb_false_intro1.
        apply 
      }

      unfold Int64.zwordsize in *; ss.
      rewrite x_bit_true; try lia.
      
      destruct (Int64.testbit X i) eqn:S1;
        destruct (Int64.testbit l i) eqn:S2; bsimpl2; ss; ibit.
      -
      destruct (Int64.testbit X i) eqn:S0; ibit; bsimpl2.
      - destruct (Int64.testbit Int64.one i) eqn:S1; bsimpl2.
        + destruct (Int64.testbit l i) eqn:S2; bsimpl2; ss.
        ss.
        s.
        s.
        s.
        ss.
      }
      -
        repeat (try rewrite ! Int64.bits_and; ss;
                try rewrite ! Int64.bits_or; ss); try xomega.
        rewrite ! Int64.bits_shru'; ss.
        des_ifs.
        rewrite Int.unsigned_one in *.
        unfold X, Y.
      -
      destruct (classic (i = 0)).
      { clarify. ss. do 2 f_equal.
      
          

      assert(Q: (Int64.or (Int64.shru (Int64.and (Int64.or l (Int64.add (Int64.and l Y) Y)) X) Int64.one)
             (Int64.and (Int64.and (Int64.or l (Int64.add (Int64.and l Y) Y)) X) Int64.one))
                = (Int64.and
             (Int64.or (Int64.or (Int64.shru' l Int.one) (Int64.and l Int64.one))
                (Int64.add (Int64.and (Int64.or (Int64.shru' l Int.one) (Int64.and l Int64.one)) Y) Y)) X)).
      {
      }
      rewrite Q.
      set (Int64.add (Int64.and l Y) Y) as Z.
      set (Int64.and (Int64.or l (Int64.add (Int64.and l (Int64.repr 2047)) (Int64.repr 2047)))
                   (Int64.repr (- 2048))) as X.
    }
  }
Qed.
    f_equal.
    (* eapply Float.of_longu_of_long_1; eauto. *)
    (* { *)
    (* } *)
    {
      rewrite Float.of_longu_decomp. ss.
      rewrite Float.of_long_decomp. ss.
      f_equal.
      f_equal.
      rewrite Float.of_intu_of_int_1; ss.
      unfold Int.ltu. des_ifs.
      unfold Float.ox8000_0000 in *.
      unfold Int64.hiword in *.
      admit "".
    }
  }
  { unfold Val.addfs.
    des_ifs.
    unfold Val.singleoflong, round_to_odd in *. des_ifs.
    f_equal.
    rewrite Float32.mul2_add. ss. des_ifs.
    des_ifs.
  }
  ss.
  des_ifs.
  - ss.
    des_ifs; ss.
    unfold Float32.of_longu, Float32.of_long.


    destruct (classic (Int64.unsigned l <= 2 ^ 53)).
    +
      rewrite Float32.of_longu_double_2; ss.
      rewrite Float32.of_long_double_2; ss.
      
      xomega.
      unfold Int64.half_modulus, Int64.modulus in *. ss.
    two_power_nat in *.
    ss.
    xomega.
  Local Transparent Float32.of_longu Float32.of_long.
  ss.
  unfold Float32.of_longu.
Qed.
Val.singleoflongu
  Val.singleoflong

  Float32.of_longu
  Float32.of_long

  Integers.Int64.unsigned
  Integers.Int64.signed











  
Float32.of_longu = 
fun n : int64 => Fappli_IEEE_extra.BofZ 24 128 eq_refl eq_refl (Int64.unsigned n)
     : int64 -> float32
Float32.of_long = 
fun n : int64 => Fappli_IEEE_extra.BofZ 24 128 eq_refl eq_refl (Int64.signed n)
     : int64 -> float32

Q: s64->f32
Coq: Read s64 as signed and cast
