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

Local Opaque Z.add Z.mul Z.sub Z.div.
Local Opaque list_nth_z.

Let size_arguments_loc_arguments_aux: forall
    tys
    ofs
    x y z
    (IN: z <= ofs < size_arguments_64 tys x y z)
  ,
    exists base ty, <<IN: In (S Outgoing base ty) (regs_of_rpairs (loc_arguments_64 tys x y z))>>
.
Proof.
  i. ginduction tys; ii; ss.
  { xomega. }
  destruct a; ss; des_ifs; ss; try (by esplits; eauto);
    try (exploit IHtys; eauto; []; i; des; []); try (by esplits; eauto).
Qed.

Lemma size_arguments_loc_arguments
      sg ofs
      (IN: 0 <= ofs < size_arguments sg)
  :
    exists ofs ty, <<IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))>>
.
Proof.
  destruct sg; ss.
  unfold size_arguments, loc_arguments in *. ss. des_ifs. clear_tac.
  eapply size_arguments_loc_arguments_aux; eauto.
Qed.

