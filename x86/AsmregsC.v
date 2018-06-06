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



Definition to_preg := preg_of.

Definition to_mreg (pr: preg): option mreg :=
  match pr with
  | PC => None
  | ST0 => Some FP0
  | CR _ => None
  | RA => None
  | IR ir =>
    match ir with
    | RAX => Some AX
    | RBX => Some BX
    | RCX => Some CX
    | RDX => Some DX
    | RSI => Some SI
    | RDI => Some DI
    | RBP => Some BP
    | RSP => None
    | R8 => Some Machregs.R8
    | R9 => Some Machregs.R9
    | R10 => Some Machregs.R10
    | R11 => Some Machregs.R11
    | R12 => Some Machregs.R12
    | R13 => Some Machregs.R13
    | R14 => Some Machregs.R14
    | R15 => Some Machregs.R15
    end
  | FR fr =>
    match fr with
    | XMM0 => Some X0
    | XMM1 => Some X1
    | XMM2 => Some X2
    | XMM3 => Some X3
    | XMM4 => Some X4
    | XMM5 => Some X5
    | XMM6 => Some X6
    | XMM7 => Some X7
    | XMM8 => Some X8
    | XMM9 => Some X9
    | XMM10 => Some X10
    | XMM11 => Some X11
    | XMM12 => Some X12
    | XMM13 => Some X13
    | XMM14 => Some X14
    | XMM15 => Some X15
    end
  end
.

Lemma to_preg_to_mreg
      mr0
  :
    mr0.(to_preg).(to_mreg) = Some mr0
.
Proof.
  destruct mr0; ss.
Qed.

Lemma to_mreg_injective
      pr0 pr1
      (SOME: is_some (pr0.(to_mreg)))
      (EQ: pr0.(to_mreg) = pr1.(to_mreg))
  :
    <<EQ: pr0 = pr1>>
.
Proof.
  destruct pr0; ss; destruct pr1; ss; des_ifs.
Qed.

Lemma preg_of_injective
      mr0 mr1
      (EQ: preg_of mr0 = preg_of mr1)
  :
    <<EQ: mr0 = mr1>>
.
Proof. destruct mr0, mr1; ss. Qed.

Lemma to_mreg_to_preg
      pr0
  :
    o_map (pr0.(to_mreg)) (to_preg) = Some pr0 \/ pr0.(to_mreg) = None
.
Proof.
  destruct pr0; ss; des_ifs; eauto.
Qed.

Corollary to_mreg_some_to_preg
      pr0 mr0
      (SOME: pr0.(to_mreg) = Some mr0)
  :
    <<EQ: mr0.(to_preg) = pr0>>
.
Proof.
  eapply to_mreg_injective with (pr0 := mr0.(to_preg)) (pr1 := pr0).
  { rewrite to_preg_to_mreg; ss. }
  rewrite to_preg_to_mreg; ss.
Qed.

Print Conventions1.
(* Note: callee_save registers all reside in mregs. So we can just put undef on preg\mreg. *)

Inductive is_callee_save (sg: signature) (pr: preg): Prop :=
| is_callee_save_some
    mr
    (MREG: pr.(to_mreg) = Some mr)
    (CALLEESAVE: Conventions1.is_callee_save mr)
| is_callee_save_none
    (MREG: pr.(to_mreg) = None)
.

Inductive callee_saved (sg: signature) (rs0 rs1: regset): Prop :=
| callee_saved_intro
    (TODO: True)
    (CALLEESAVE: forall
        r
        (CALLEESAVE: is_callee_save sg r)
      ,
        <<SAVE: Val.lessdef (rs0 r) (rs1 r)>>)
(* In Compcert' sg is not needed (see is_callee_save). Is it true in real-world too? *)
.

