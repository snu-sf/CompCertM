Require Import CoqlibC Maps.
Require Import Values.
Require Import Locations Stacklayout Conventions.
Require Import MemoryC Integers AST.
(** newly added **)
Require Export Asmregs.
Require Import Locations.

Set Implicit Arguments.



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

Definition is_callee_save (sg: signature) (pr: preg): bool :=
  match pr.(to_mreg) with
  | Some mr => Conventions1.is_callee_save mr
  | None => false
  end
.
(* Inductive is_callee_save (sg: signature) (pr: preg): Prop := *)
(* | is_callee_save_some *)
(*     mr *)
(*     (MREG: pr.(to_mreg) = Some mr) *)
(*     (CALLEESAVE: Conventions1.is_callee_save mr) *)
(* . *)

Inductive callee_saved (sg: signature) (rs0 rs1: regset): Prop :=
| callee_saved_intro
    (CALLEESAVE: forall
        r
        (CALLEESAVE: is_callee_save sg r = true)
      ,
        (* <<SAVE: (rs0 r) = (rs1 r)>> *)
        <<SAVE: Val.lessdef (rs0 r) (rs1 r)>>
    )
(* In Compcert' sg is not needed (see is_callee_save). Is it true in real-world too? *)
.

Inductive fill_garbage (sg: signature) (rs0 rs1: regset): Prop :=
| fill_garbage_intro
    (CALLERSAVE: forall
        r
        (CALLERSAVE: is_callee_save sg r = false)
      ,
        <<GARBAGE: (rs1 r) = Vundef>>
    )
    (CALLEESAVE: forall
        r
        (CALLEESAVE: is_callee_save sg r = true)
      ,
        <<SAVE: (rs0 r) = (rs1 r)>>
    (* <<SAVE: Val.lessdef (rs0 r) (rs1 r)>> *)
    )
.










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

(* Reset PLAYGROUND. *)










Inductive store_arguments (vs: list val) (m0: mem) (sg: signature):
  regset -> mem -> Prop :=
| store_arguments_intro
    m1 sp
    (ALLOC: Mem.alloc m0 Stacklayout.fe_ofs_arg (size_arguments sg) = (m1, sp))
    (rs_arg: regset)
    (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true)
    m_arg
    (STORE: extcall_arguments rs_arg m_arg sg vs /\ Mem.unchanged_on top2 m0 m_arg /\
            m1.(Mem.nextblock) = m_arg.(Mem.nextblock) /\
            (forall ofs (OUTSIDE: ~ 0 <= ofs < 4 * size_arguments sg), ~Mem.perm m_arg sp ofs Cur Nonempty) /\
            Mem.range_perm m_arg sp 0 (4 * size_arguments sg) Cur Freeable)
  :
    store_arguments vs m0 sg rs_arg m_arg
.

Inductive load_arguments (rs_arg: regset) (m_arg: mem) (sg_init: signature)
          (vs_init: list val) (m_init: mem): Prop :=
| load_arguments_intro
    sp
    (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true)
    (PERM: Mem.range_perm m_arg sp 0 (4 * (size_arguments sg_init)) Cur Writable)
    (VAL: extcall_arguments rs_arg m_arg sg_init vs_init)
    (DROP: Mem_set_perm m_arg sp 0 (4 * (size_arguments sg_init)) None = Some m_init)
.

Lemma load_arguments_dtm
      rs_arg m_arg sg_init
      vs_init0 vs_init1 m_init0 m_init1
      (LOAD0: load_arguments rs_arg m_arg sg_init vs_init0 m_init0)
      (LOAD1: load_arguments rs_arg m_arg sg_init vs_init1 m_init1)
  :
    vs_init0 = vs_init1 /\ m_init0 = m_init1
.
Proof.
  inv LOAD0. inv LOAD1.
  rewrite RSPPTR in *. clarify.
  determ_tac extcall_arguments_determ.
Qed.

Definition dead_block (m: mem) (b: block): Prop := forall ofs, ~Mem.perm m b ofs Cur Nonempty.

Lemma Mem_unchanged_on_trans_strong
      P m0 m1 m2
      (UNCH0: Mem.unchanged_on P m0 m1)
      (UNCH1: Mem.unchanged_on (P /2\ (fun b _ => Mem.valid_block m0 b)) m1 m2)
  :
    <<UNCH2: Mem.unchanged_on P m0 m2>>
.
Proof.
  inv UNCH0. inv UNCH1.
  econs; i.
  - xomega.
  - etransitivity.
    { eapply unchanged_on_perm; eauto. }
    eapply unchanged_on_perm0; eauto.
    { unfold Mem.valid_block in *. xomega. }
  - erewrite <- unchanged_on_contents; eauto.
    dup H0. apply Mem.perm_valid_block in H1. unfold Mem.valid_block in *.
    erewrite <- unchanged_on_contents0; eauto.
    eapply unchanged_on_perm; eauto.
Qed.

Local Opaque Z.mul.

Theorem store_arguments_progress
        vs0 m0 sg
  :
    exists rs_arg m_arg,
      <<STORE: store_arguments vs0 m0 sg rs_arg m_arg>>
.
Proof.
  admit "This is needed for user to reason about their program. This will be complex job,
and Compcert avoided it by translation validation, so we should do this from the scratch.
NOTE: Old version of Compcert should have related code.
> 6224148 - (HEAD -> master) Reorganization test directory (2010-02-17 13:44:32 +0000) <xleroy>
I checked this commit, there is a pass called Reload which deals this problem.".
Qed.

Theorem store_load_arguments_progress
        vs0 m0 sg rs_arg m_arg
        (STORE: store_arguments vs0 m0 sg rs_arg m_arg)
  :
    exists vs1 m1,
      <<LOAD: load_arguments rs_arg m_arg sg vs1 m1>>
.
Proof.
  inv STORE. des.
  assert(exists m2, Mem_set_perm m_arg sp 0 (4 * size_arguments sg) None = Some m2).
  { admit "it always suceeds". }
  des.
  esplits; eauto. econs; eauto.
  - eapply Mem.range_perm_implies; eauto.
    econs; eauto.
Qed.

Theorem store_load_arguments_spec
        vs0 m0 sg rs_arg m_arg
        (STORE: store_arguments vs0 m0 sg rs_arg m_arg)
        vs1 m1
        (LOAD: load_arguments rs_arg m_arg sg vs1 m1)
  :
    <<VAL: vs0 = vs1>> /\ <<MEM: Mem.unchanged_on top2 m0 m1
                                 /\ dead_block m1 m0.(Mem.nextblock)
                                 /\ Pos.succ m0.(Mem.nextblock) = m1.(Mem.nextblock)>>
.
Proof.
  inv STORE. inv LOAD.
  rewrite RSPPTR in *. clarify.
  determ_tac extcall_arguments_determ; eauto.
  exploit Mem_set_perm_none_spec; eauto. i; des.
  assert(sp0 = (Mem.nextblock m0)).
  { exploit Mem.alloc_result; eauto. }
  clarify.
  rename m1 into tt. rename m2 into m1. rename tt into m2.
  esplits; eauto.
  - eapply Mem_unchanged_on_trans_strong; eauto.
    admit "Add to set_perm_none_spec. this should hold".
  - hnf. ii.
    destruct (classic (0 <= ofs < 4 * size_arguments sg)).
    + eapply INSIDE; eauto.
    + erewrite <- OUTSIDE in H; cycle 1.
      { right. xomega. }
      eapply STORE3; eauto.
  - exploit Mem.nextblock_alloc; eauto. i; des. rewrite <- H.
    rewrite STORE2.
    admit "Add to set_perm_none_spec. this should hold".
Qed.




Inductive store_result (rs_init: regset) (v: val) (sg_init: signature): regset -> Prop :=
| store_result_intro
    rs_garbage rs_ret
    (GARBAGE: fill_garbage sg_init rs_init rs_garbage)
    (STORE: set_pair (loc_external_result sg_init) v rs_garbage = rs_ret)
  :
    store_result rs_init v sg_init rs_ret
.

Definition disjoint X (dec: forall x0 x1, {x0 = x1} + {x0 <> x1}) (rp: rpair X): bool :=
  match rp with
  | One _ => true
  | Twolong x0 x1 => negb (dec x0 x1)
  end
.

Definition get_pair (rp: rpair preg) (rs: regset): val :=
  match rp with
  | One r0 => rs r0
  | Twolong r0 r1 => Val.longofwords (rs r0) (rs r1)
  end
.

Lemma longofwords_lessdef
      retv
  :
    <<LD: Val.lessdef (Val.longofwords (Val.hiword retv) (Val.loword retv)) retv>>
.
Proof.
  destruct retv; ss.
  rewrite Int64.ofwords_recompose. econs; eauto.
Qed.

Lemma longofwords_long
      retv
      (LONG: Val.has_type retv Tlong)
  :
    <<EQ: (Val.longofwords (Val.hiword retv) (Val.loword retv)) = retv>>
.
Proof.
  destruct retv; ss.
  rewrite Int64.ofwords_recompose. econs; eauto.
Abort.


Lemma longofwords_long (* We need more strict type checking *)
      retv
      (LONG: exists i0, retv = Vlong i0)
  :
    <<EQ: (Val.longofwords (Val.hiword retv) (Val.loword retv)) = retv>>
.
Proof.
  des. clarify. ss.
  rewrite Int64.ofwords_recompose. econs; eauto.
Qed.

Lemma getpair_setpair
      rp retv rs
      (DISJ: disjoint preg_eq rp)
  :
    <<LD: Val.lessdef (get_pair rp (set_pair rp retv rs)) retv>>
.
Proof.
  destruct rp; ss.
  - unfold Pregmap.set. des_ifs.
  - unfold Pregmap.set. simpl_bool. des_sumbool. des_ifs.
    eapply longofwords_lessdef.
Qed.

Inductive load_result (rs_arg: regset) (rs_ret: regset) (sg: signature): val -> Prop :=
| load_result_intro
    retv
    (LOAD: get_pair (loc_external_result sg) rs_ret = retv)
    (CALLEESAVE: callee_saved sg rs_arg rs_ret)
  :
    load_result rs_arg rs_ret sg retv
.

Lemma callee_saved_set
      sg rs0 rs1
      (SAVED: callee_saved sg rs0 rs1)
      r0 v0
      (NOTCALLEE: is_callee_save sg r0 = false)
  :
    <<SAVED: callee_saved sg rs0 (Pregmap.set r0 v0 rs1)>>
.
Proof.
  inv SAVED.
  econs; eauto.
  ii. specialize (CALLEESAVE r CALLEESAVE0).
  unfold Pregmap.set. des_ifs.
Qed.

Lemma callee_saved_set_pair
      sg rs0 rs1
      (SAVED: callee_saved sg rs0 rs1)
      rp0 v0
      (NOTCALLEE: forall_rpair (fun r => is_callee_save sg r = false) rp0)
  :
    <<SAVED: callee_saved sg rs0 (set_pair rp0 v0 rs1)>>
.
Proof.
  unfold set_pair in *. des_ifs.
  - eapply callee_saved_set; eauto.
  - ss. des.
    eapply callee_saved_set; eauto.
    eapply callee_saved_set; eauto.
Qed.

Lemma loc_external_result_caller_save
      sg
  :
    forall_rpair (fun pr => is_callee_save sg pr = false) (loc_external_result sg)
.
Proof.
  hexploit (loc_result_caller_save sg); eauto. i.
  unfold forall_rpair in *. unfold loc_external_result in *. unfold map_rpair in *. unfold is_callee_save in *.
  des_ifs; ss; rewrite to_preg_to_mreg in *; clarify.
Qed.

Theorem store_load_result_progress
        rs_arg retv0 sg rs_ret
        (STORE: store_result rs_arg retv0 sg rs_ret)
  :
    exists retv1,
      <<LOAD: load_result rs_arg rs_ret sg retv1>> /\ <<LD: Val.lessdef retv1 retv0>>
.
Proof.
  inv STORE.
  esplits.
  - econs; eauto.
    eapply callee_saved_set_pair; eauto.
    { inv GARBAGE. econs; eauto. ii. erewrite CALLEESAVE; eauto. }
    eapply (loc_external_result_caller_save sg); eauto.
  - eapply getpair_setpair; eauto.
    unfold loc_external_result. unfold loc_result, loc_result_64, loc_result_32. des_ifs.
Qed.

(* TODO: more specs? store_results always suceeds, load_result/store_result is dtm, etc. *)
Theorem store_load_result_spec
        rs_arg retv0 retv1 sg rs_ret
        (STORE: store_result rs_arg retv0 sg rs_ret)
        (LOAD: load_result rs_arg rs_ret sg retv1)
  :
    <<LD: Val.lessdef retv1 retv0>>
.
Proof.
  inv STORE. inv LOAD.
  esplits; eauto.
  - eapply getpair_setpair; eauto.
    unfold loc_external_result. unfold loc_result, loc_result_64, loc_result_32. des_ifs.
Qed.

Lemma fill_garbage_dtm
      sg_init rs_init rs_garbage0 rs_garbage1
      (GARBAGE0: fill_garbage sg_init rs_init rs_garbage0)
      (GARBAGE1: fill_garbage sg_init rs_init rs_garbage1)
  :
    rs_garbage0 = rs_garbage1
.
Proof.
  inv GARBAGE0. inv GARBAGE1.
  apply Axioms.functional_extensionality.
  i.
  destruct (is_callee_save sg_init x) eqn:T.
  - erewrite <- CALLEESAVE; eauto.
    erewrite <- CALLEESAVE0; eauto.
  - erewrite CALLERSAVE; eauto.
    erewrite CALLERSAVE0; eauto.
Qed.

Lemma store_result_dtm
      rs_init v_ret sg_init rs_ret0 rs_ret1
      (STORE: store_result rs_init v_ret sg_init rs_ret0)
      (STORE0: store_result rs_init v_ret sg_init rs_ret1)
  :
    <<EQ: rs_ret0 = rs_ret1>>
.
Proof.
  inv STORE. inv STORE0.
  determ_tac fill_garbage_dtm.
Qed.

Lemma load_result_dtm
      rs_init v_ret sg_init rs_ret0 rs_ret1
      (LOAD: load_result rs_init v_ret sg_init rs_ret0)
      (LOAD0: load_result rs_init v_ret sg_init rs_ret1)
  :
    <<EQ: rs_ret0 = rs_ret1>>
.
Proof.
  inv LOAD. inv LOAD0.
  ss.
Qed.

