Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Conventions.


Lemma proj_bytes_only_bytes
      mvs bts
      (PROJ: proj_bytes mvs = Some bts)
  :
    forall mv (IN: In mv mvs), exists bt, mv = Byte bt
.
Proof.
  ginduction mvs; ii; ss. des_ifs. des; clarify; ss; eauto.
Qed.

Lemma decode_fragment_all chunk vl v mv q n
      (DECODE: decode_val chunk vl = v)
      (IN: In (Fragment mv q n) vl)
      (VALUE: v <> Vundef)
  :
    mv = v
.
Proof.
  unfold decode_val in *.
  destruct (proj_bytes vl) eqn:T.
  { hexploit proj_bytes_only_bytes; eauto. i; des. clarify. }
  clear T.
  sguard in IN.
  destruct chunk; ss; des_ifs; clear_tac.
  - destruct vl; ss.
    repeat my_tac.
    unsguard IN. des; clarify.
  - destruct vl; ss.
    repeat my_tac.
    unsguard IN. des; clarify.
  - destruct vl; ss.
    repeat my_tac.
    unsguard IN. des; clarify.
  - destruct vl; ss.
    repeat my_tac.
    unsguard IN. des; clarify.
  - destruct vl; ss.
    repeat my_tac.
    unsguard IN. des; clarify.
Qed.

Lemma decode_normal_all_normal chunk vl v
      (DECODE: decode_val chunk vl = v)
      (VALUE: v <> Vundef /\ forall blk ofs b, v <> Vptr blk ofs b)
      mv
      (IN: In mv vl)
  :
    forall blk ofs b q n, mv <> Fragment (Vptr blk ofs b) q n.
Proof.
  ii. des. rewrite H in *.
  destruct v; ss.
  - exploit decode_fragment_all; eauto. i. clarify.
  - exploit decode_fragment_all; eauto. i. clarify.
  - exploit decode_fragment_all; eauto. i. clarify.
  - exploit decode_fragment_all; eauto. i. clarify.
  - exfalso. eapply VALUE0. eauto.
Qed.

Lemma decode_pointer_all_pointer chunk vl mv blk ofs b
      (DECODE: decode_val chunk vl = Vptr blk ofs b)
      (IN: In mv vl)
  :
    exists q n, mv = Fragment (Vptr blk ofs b) q n.
Proof.
  unfold decode_val, Val.load_result in *. des_ifs.
  - unfold proj_value in *.
    des_ifs; repeat (repeat (apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
    all: eauto.
    des_ifs.
  - unfold proj_value in *.
    des_ifs; repeat (repeat (apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
    all: eauto.
    des_ifs.
Qed.

Lemma typesize_chunk
      ty
  :
    4 * ty.(typesize) = size_chunk (chunk_of_type ty)
.
Proof. destruct ty; ss. Qed.
