Require Import CoqlibC Maps.
Require Import Values.
Require Import Locations Stacklayout Conventions.
Require Import MemoryC Integers AST.
(** newly added **)
Require Export Asmregs.
Require Import Locations.


Module PLAYGROUND.
(* Lemma extcall_arguments_perm_aux *)
(*       rs m tys vs *)
(*       ir fr (* ofs *) *)
(*       (ARGS: list_forall2 (extcall_arg_pair rs m) (loc_arguments_64 tys ir fr 0) vs) *)
(*       sp spofs *)
(*       (RSPPTR: rs RSP = Vptr sp spofs true) *)
(*   : *)
(*     <<PERM: Mem.range_perm m sp (Ptrofs.unsigned spofs) *)
(*                            (Ptrofs.unsigned spofs + size_arguments_64 tys ir fr 0) Cur Nonempty>> *)
(* . *)
(* Proof. *)
(*   ginduction tys; i. *)
(*   { ii. inv ARGS. ss. xomega. } *)
(*   destruct a; inv ARGS; try (by des_ifs). *)
(*   - specialize (IHtys _ _ _ _ _ H1). *)
(* Qed. *)




(* Lemma loc_arguments_64_complete *)
(*       x tys ir fr *)
(*       (SIZE0: x < 4 * size_arguments_64 tys ir fr 0) *)
(*       (SIZE1: 0 <= x) *)
(*       (IR: 0 <= ir) *)
(*       (FR: 0 <= fr) *)
(*   : *)
(*     exists sl pos ty, <<IN: In (S sl pos ty) (loc_arguments_64 tys ir fr 0).(regs_of_rpairs)>> *)
(*                             /\ <<OFS: pos <= x < pos + 4 * ty.(typesize)>> *)
(* . *)
(* Proof. *)
(*   ginduction tys; ii; ss. *)
(*   { xomega. } *)
(*   destruct a; ss. *)
(*   - des. *)
(*     des_ifs; try (exploit IHtys; eauto; try xomega; i; des; []; esplits; eauto; ss; right; eauto). *)
(*     assert(6 <= ir). *)
(*     { xomega. } *)
(*     ss. esplits; eauto; try xomega. ss. rewrite Z.add_0_l in *. rewrite Z.mul_1_r. *)
(*     unfold size_arguments_64 in SIZE0. ss. des_ifs. *)
(*     u in SIZE0. *)
(*     destruct ir; try xomega. *)
(*     ss. *)
(*   - *)
(* Qed. *)
Lemma typesize_chunk
      ty
  :
    4 * ty.(typesize) = size_chunk (chunk_of_type ty)
.
Proof. destruct ty; ss. Qed.

Print extcall_arg.
Local Opaque Z.mul Z.add Z.div Z.sub.
Local Opaque list_nth_z.
Lemma size_arguments_loc_arguments
      ofs
      tys ir fr acc
      (SIZE: acc <= ofs < size_arguments_64 tys ir fr acc)
  :
    exists pos ty, <<IN: In (S Outgoing pos ty) (loc_arguments_64 tys ir fr acc).(regs_of_rpairs)>> /\
                            <<BOUND: pos <= ofs < pos + ty.(typesize)>>
.
Proof.
  unfold size_arguments in *. unfold loc_arguments in *.
  ginduction tys; ii; ss.
  { xomega. }
  destruct a; ss.
  - des_ifs.
    + exploit IHtys; eauto. i; des. esplits; cbn; eauto.
    + cbn.
      do 2 eexists. split; eauto. red. ss.
      admit "IT DOES NOT HOLD!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! 2 ofs for int value !!!!!!!!!!!!".
  - admit "".
  - admit "".
  - admit "".
  - admit "".
  - admit "".
Qed.

Lemma extcall_arguments_perm_aux
      rs m tys vs
      ir fr (* ofs *)
      (ARGS: list_forall2 (extcall_arg_pair rs m) (loc_arguments_64 tys ir fr 0) vs)
      sp
      (RSPPTR: rs RSP = Vptr sp Ptrofs.zero true)
  :
    <<PERM: Mem.range_perm m sp 0 (4 * (size_arguments_64 tys ir fr 0)) Cur Nonempty>>
.
Proof.
  assert(BOUND: forall
            loc
            (IN: In loc (loc_arguments_64 tys ir fr 0))
          ,
            exists v, In v vs /\ extcall_arg_pair rs m loc v).
  { ii. eapply list_forall2_in_left; eauto. }

  ii.
  set (ofsdiv := ofs/4).
  assert(DIVBOUND: 0 <= ofsdiv < size_arguments_64 tys ir fr 0).
  { admit "". }
  exploit size_arguments_loc_arguments; eauto. i; des.
  assert(POS: 0 <= pos).
  { admit "easy". }
  exploit in_regs_of_rpairs_inv; eauto. i; des.
  exploit BOUND; eauto. i; des.
  inv H4.
  - Local Opaque Z.mul.
    inv H5; ss; des; clarify.
    unfold fe_ofs_arg in *.
    rewrite RSPPTR in *.
    ss. rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *.
    (* rewrite Ptrofs.unsigned_repr in *; cycle 1. *)
    (* { *)
    exploit Mem.load_valid_access; eauto. intro VALID; des. hnf in VALID. des.
    eapply Mem.perm_implies with (p1 := Readable); [|eauto with mem].
    eapply VALID. rewrite <- typesize_chunk.
    split.
    + rewrite Ptrofs.unsigned_repr_eq.
      assert(4 * pos <= ofs).
      { admit "". }
      etransitivity; eauto. eapply Z.mod_le; try xomega.
      generalize Ptrofs.modulus_pos. i. xomega.
    + assert(ofs < 4 * pos + 4 * (typesize ty)).
      { admit "". }
      rewrite Ptrofs.unsigned_repr_eq. eapply Z.lt_le_trans; eauto.
      apply Z.add_le_mono_r.
      admit "somehow..".
  - admit "".
Qed.

Lemma extcall_arguments_perm
      rs m sg vs
      (ARGS: extcall_arguments rs m sg vs)
      sp
      (RSPPTR: (rs RSP) = Vptr sp Ptrofs.zero true)
  :
    Mem.range_perm m sp 0 (size_arguments sg) Cur Nonempty
.
Proof.
(*   unfold extcall_arguments in *. *)
(*   destruct sg; ss. unfold loc_arguments, size_arguments in *. ss. des_ifs. clear_tac. *)
(*   ginduction sig_args; i; ss. *)
(*   { ii. xomega. } *)
(*   destruct a; ss. *)
(*   - inv ARGS. *)
(* Qed. *)
Admitted.


End PLAYGROUND.

(* Reset size_arguments_loc_arguments. *)


Inductive load_arguments (rs_arg: regset) (m_arg: mem) (sg_init: signature)
          (vs_init: list val) (m_init: mem): Prop :=
| load_arguments_intro
    sp
    (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true)
    (PERM: Mem.range_perm m_arg sp 0 (4 * (size_arguments sg_init)) Cur Writable)
    (VAL: extcall_arguments rs_arg m_arg sg_init vs_init)
    (DROP: Mem_set_perm m_arg sp 0 (4 * (size_arguments sg_init)) None = Some m_init)
.

