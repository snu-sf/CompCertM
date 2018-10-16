Require Import CoqlibC Decidableplus.
Require Import ASTC Machregs Locations.
(** newly added **)
Require Export Conventions1.

Set Implicit Arguments.



Lemma loc_arguments_length_aux
      tys ir fr ofs
  :
    <<LEN: length (loc_arguments_64 tys ir fr ofs) = length tys>>
.
Proof.
  ginduction tys; ii; ss.
  des_ifs; s; rewrite IHtys; ss.
Qed.

Lemma loc_arguments_length
      sg
  :
    <<LEN: length (loc_arguments sg) = length (sig_args sg)>>
.
Proof.
  destruct sg; ss.
  unfold loc_arguments. des_ifs. ss.
  rewrite loc_arguments_length_aux. ss.
Qed.

