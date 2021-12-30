Require Import CoqlibC ASTC.
From compcertr Require Import
     Decidableplus
     Machregs
     Locations.
(** newly added **)
From compcertr Require Export Conventions1.
From compcertr Require Conventions.

Set Implicit Arguments.



Lemma loc_arguments_length_aux: forall tys ir fr ofs,
    <<LEN: length (loc_arguments_elf64 tys ir fr ofs) = length tys>>.
Proof. i. ginduction tys; ii; ss. des_ifs; s; rewrite IHtys; ss. Qed.

Lemma loc_arguments_length: forall sg,
    <<LEN: length (loc_arguments sg) = length (sig_args sg)>>.
Proof.
  destruct sg; ss. unfold loc_arguments. des_ifs. ss. rewrite loc_arguments_length_aux. ss.
Qed.

Local Opaque Z.add Z.mul Z.sub Z.div.
Local Opaque list_nth_z.

(* Let max_outgoing_lemma *)
(*     tys x y z w0 w1 *)
(*     (NNIL: tys <> []) *)
(*     (LE0: w0 <= z) *)
(*     (LE1: w1 <= z) *)
(*   : *)
(*     fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys x y z) w0 = *)
(*     fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys x y z) w1 *)
(* . *)
(* Proof. *)
(*   ginduction tys; ii; ss. *)
(*   des_ifs; ss. *)
(*   - destruct tys; ss. rewrite IHtys; et. *)
(* Qed. *)

Definition typ_dec: forall x y: typ, {x = y} + {x <> y}. decide equality. Defined.

Let Fixpoint num_fregs (tys: list typ): nat :=
  match tys with
  | [] => 0
  | Tfloat as ty :: tys | Tsingle as ty :: tys => (num_fregs tys) + 1
  | _ :: tys => num_fregs tys
  end
.
Let Fixpoint num_iregs (tys: list typ): nat :=
  match tys with
  | [] => 0
  | Tint as ty :: tys | Tlong as ty :: tys | Tany32 as ty :: tys | Tany64 as ty :: tys => (num_iregs tys) + 1
  | _ :: tys => num_iregs tys
  end
.

(* Let num_fregs (tys: list typ): nat := count_occ typ_dec tys Tfloat + count_occ typ_dec tys Tsingle. *)
(* Let num_iregs (tys: list typ): nat := *)
(*   count_occ typ_dec tys Tint + count_occ typ_dec tys Tlong + *)
(*   count_occ typ_dec tys Tany32 + count_occ typ_dec tys Tany64. *)
Let is_enough (tys: list typ) (ir fr: nat): Prop :=
  ((num_iregs tys = 0 \/ (num_iregs tys + ir <= length int_param_regs_elf64))%nat /\
   (num_fregs tys = 0 \/ (num_fregs tys + fr <= length float_param_regs_elf64))%nat).
Let max_outgoing_lemma
    tys ir fr ofs
    (POS: 0 <= ir)
    (POS0: 0 <= fr)
  :
    (** no outgoing **)
    <<A: forall w0, fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys ir fr ofs) w0 = w0>> \/
    (** yes outgoing **)
    <<B: forall w0 w1 (LE0: w0 <= ofs) (LE1: w1 <= ofs),
      fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys ir fr ofs) w0 =
      fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys ir fr ofs) w1>>
.
Proof.
  destruct (classic (is_enough tys (Z.to_nat ir) (Z.to_nat fr))).
  - left. ii. unfold is_enough in *.
    ginduction tys; ii; ss; et.
    pose a as X.
    des_ifs; ss; try (erewrite IHtys; ss; rewrite list_nth_z_eq in *; ss; lia);
      try (rewrite list_nth_z_eq in *; ss; rewrite nth_error_None in *; ss; lia).
  - right. ii. unfold is_enough in *.
    ginduction tys; ii; ss; et.
    { contradict H. tauto. }
    des_ifs; ss; try (erewrite IHtys; ss; try lia; apply list_nth_z_range in Heq; cbn in *; ss; lia);
      rewrite ! Z.max_r; try lia.
Qed.

Let size_arguments_loc_arguments_aux: forall
    tys ofs x y z
    (POSx: 0 <= x)
    (POSy: 0 <= y)
    (POSz: 0 <= z)
    (IN: z <= ofs < fold_left Conventions.max_outgoing_2 (loc_arguments_elf64 tys x y z) 0),
    exists base ty, (<<IN: In (S Outgoing base ty) (regs_of_rpairs (loc_arguments_elf64 tys x y z))>>)
               /\ (<<RANGE: base <= ofs < base + (Memdata.size_chunk (chunk_of_type ty))>>).
Proof.
  i. ginduction tys; ii; ss; try extlia.
  destruct a; ss; des_ifs; ss; try (exploit IHtys; try apply IN; et; try lia; i; des; esplits; et; fail).
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
  - rewrite Z.max_r in *; try lia.
    hexploit (@max_outgoing_lemma tys x y); ss. i; des.
    + erewrite A in IN0. esplits; et. ss. lia.
    + erewrite (@B _ 0) in IN0; et; try lia.
      destruct (classic (z + 2 <= ofs)).
      * try (exploit IHtys; splits; try apply IN0; et; try lia; i; des; esplits; et; fail).
      * esplits; et. ss. lia.
Qed.

Lemma size_arguments_loc_arguments
      sg ofs
      (IN: 0 <= ofs < Conventions.size_arguments sg):
    exists base ty, (<<IN: In (S Outgoing base ty) (regs_of_rpairs (loc_arguments sg))>>)
               /\ (<<RANGE: base <= ofs < base + (Memdata.size_chunk (chunk_of_type ty))>>).
Proof.
  destruct sg; ss. unfold Conventions.size_arguments, loc_arguments in *. ss. des_ifs. clear_tac.
  eapply size_arguments_loc_arguments_aux; ss.
Qed.

Lemma loc_args_callee_save_disjoint sg mr
      (EXT: In (R mr) (regs_of_rpairs (loc_arguments sg))):
    ~ Conventions1.is_callee_save mr.
Proof.
  exploit in_regs_of_rpairs_inv; eauto. i. des.
  exploit loc_arguments_acceptable; eauto. i.
  unfold forall_rpair, loc_argument_acceptable in *.
  des_ifs; ss; des; clarify; eauto.
Qed.
