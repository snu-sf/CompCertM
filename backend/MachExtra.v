Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import LocationsC.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Import Mach.


Ltac extcall_simpl :=
  repeat match goal with
         | [ H: extcall_arg_pair _ _ _ (One _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (S _ _ _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (R _) _ |- _ ] => inv H
         end
.

Inductive store_arguments (m0: mem) (rs: regset) (vs: list val) (sg: signature) (m2: mem): Prop :=
| store_arguments_intro
    m1 blk
    (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, blk))
    (VALS: extcall_arguments rs m2 (Vptr blk Ptrofs.zero true) sg vs)
    (UNCH: Mem.unchanged_on (fun b ofs => if eq_block b blk
                                          then (* ~ (0 <= ofs < 4 * size_arguments sg) *) False
                                          else True) m1 m2)
    (NB: m1.(Mem.nextblock) = m2.(Mem.nextblock))
    (PERM: Mem.range_perm m2 blk 0 (4 * size_arguments sg) Cur Freeable)
.

Local Opaque Z.mul Z.sub Z.div.
Local Transparent size_arguments.
Local Transparent loc_arguments.

Module FillArgs.

  Fixpoint fill_arguments (sp: block) (rs0: regset) (m0: mem) (args: list val) (locs: list (rpair loc)):
    option (regset * mem) :=
    match args, locs with
    | [], [] => Some (rs0, m0)
    | arg :: args, loc :: locs =>
      do (rs1, m1) <- fill_arguments sp rs0 m0 args locs ;
        match loc with
        | One (R r) => Some (rs1 # r <- arg, m1)
        (* | One (S Outgonitgttttttt ofs ty) => *)
        | One (S Outgoing ofs ty) =>
          (* do m2 <- Mach.store_stack m0 sp ty (4 * ofs).(Ptrofs.repr) arg ; *)
          do m2 <- Mem.store (chunk_of_type ty) m1 sp (4 * ofs) arg ;
            Some (rs1, m2)
        | _ => None
        end
    | _, _ => None
    end
  .

  Hint Unfold curry2.
  Local Opaque list_nth_z.
  Ltac divtac_ :=
    try apply Z.divide_0_r;
    try apply Z.divide_refl;
    try (apply Z.mul_divide_cancel_l; ss; try xomega; check_safe);
    try eapply Z.divide_add_r; eauto;
    try (by (eapply Z.divide_factor_l; eauto));
    try (by (eapply Z.divide_refl; eauto));
    try xomega.
  Ltac divtac := repeat divtac_.

  Let fill_arguments_progress_aux
      sig_args m0 rs0 m1 sp args
      x y z
      (LEN: Datatypes.length args = Datatypes.length sig_args)
      (ALC: Mem.alloc m0 0 (4 * size_arguments_64 sig_args x y z) = (m1, sp))
      (* (ZWF: 0 <= 4 * z <= Ptrofs.max_unsigned) *)
      (ZWF: 0 <= z /\ (2 | z))
    :
      exists rs1 m2,
        (<<FILL:
           fill_arguments (* (Vptr sp Ptrofs.zero true) *) sp rs0 m1 args
                          (loc_arguments_64 sig_args x y z) = Some (rs1, m2)>>)
        /\
        (* <<VALID: forall chunk ofs (LO: lo <= ofs) (HI: ofs + size_chunk chunk <= hi) (ALIGN: align_chunkMem.valid_access m2 *)
        (<<PERM: Mem.range_perm m2 sp 0 (4 * size_arguments_64 sig_args x y z) Cur Freeable>>)
  .
  Proof.
    ginduction sig_args; ii; ss; destruct args; ss.
    { esplits; eauto. eapply Mem_alloc_range_perm; eauto. }
    des.
    des_ifs; try (exploit IHsig_args; eauto; try (by esplits; divtac); i; des; check_safe);
      try (rewrite FILL; u); try by (esplits; eauto).
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. change 8 with (4 * 2). divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
    - match goal with
      | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
      end.
      { eapply Mem.valid_access_implies with Freeable; eauto with mem.
        split.
        + ii. eapply PERM; eauto. split; try xomega. ss.
          generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
        + ss. divtac.
      }
      des_ifs. esplits; eauto.
      ii. eapply Mem.perm_store_1; eauto.
  Qed.

  Theorem fill_arguments_progress
        sg m0 rs0 m1 sp args
        (LEN: length args = length sg.(sig_args))
        (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, sp))
    :
      exists rs1 m2, (<<STORE: fill_arguments (* (Vptr sp Ptrofs.zero true) *) sp rs0 m1 args (loc_arguments sg)
                               = Some (rs1, m2)>>)
  .
  Proof.
    (* set (SG:= sg). *)
    destruct sg; ss.
    unfold loc_arguments, size_arguments in *. ss. des_ifs. clear_tac.
    exploit fill_arguments_progress_aux; eauto.
    { split; try xomega. divtac. }
    i; des. eauto.
  Qed.

  (* Local Transparent loc_arguments size_arguments. *)
  (* Let fill_arguments_spec_aux: forall *)
  (*     sig_args sig_res sig_cc *)
  (*     m0 rs0 m1 sp args *)
  (*     (LEN: Datatypes.length args = Datatypes.length sig_args) *)
  (*     x y z *)
  (*     (ALC: Mem.alloc m0 0 (4 * size_arguments_64 sig_args x y z) = (m1, sp)) *)
  (*     rs1 m2 *)
  (*     (FILL: fill_arguments sp rs0 m1 args (loc_arguments_64 sig_args x y z) = Some (rs1, m2)) *)
  (*   , *)
  (*     <<STORE: store_arguments m0 rs1 args {| sig_args := sig_args; sig_res := sig_res; sig_cc := sig_cc |} m1>> *)
  (* . *)
  (* Proof. *)
  (*   ii. *)
  (*   ginduction args; ii; ss; des_ifs_safe. *)
  (*   { econs; eauto. *)
  (*     - unfold size_arguments. des_ifs. ss. *)
  (*     - rr. unfold loc_arguments. ss. des_ifs. rewrite Heq0. econs; eauto. *)
  (*     - refl. *)
  (*     - eapply Mem_alloc_range_perm; eauto. *)
  (*   } *)
  (* Qed. *)

  Hint Unfold o_bind2.

  (* Lemma list_forall2_sep *)
  (*       X Y *)
  (*       (P Q: X -> Y -> Prop) *)
  (*       xs ys *)
  (*       (ALL: list_forall2 P xs ys) *)
  (*       (SEP: forall x y, P x y -> Q x y) *)
  (*   : *)
  (*     <<ALL: list_forall2 Q xs ys>> *)
  (* . *)
  (* Proof. *)
  (* Qed. *)

  Let fill_arguments_unchanged_on
        sp rs0 m0 args x y z rs1 m1 tys
        (LEN: length args = length tys)
        (FILL: fill_arguments sp rs0 m0 args (loc_arguments_64 tys x y z) = Some (rs1, m1))
    :
      (* <<UNCH: Mem.unchanged_on (brange sp 0 (4 * z)) m0 m1>> *)
      (<<UNCH: Mem.unchanged_on (fun b ofs => if eq_block b sp
                                              then (0 <= ofs < 4 * z)
                                              else True) m0 m1>>)
  .
  Proof.
    ginduction args; ii; ss; des_ifs_safe; destruct tys; ss.
    { r. refl. }
    u in FILL.
    des_ifs_safe. destruct r0; ss.
    { unfold Regmap.set in *. clarify. destruct p; ss.
      des_ifs; eapply IHargs; eauto.
    }
    { des_ifs_safe. destruct p; ss.
      des_ifs.
      - r. etrans; cycle 1.
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
        exploit IHargs; eauto. i.
        eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; try xomega.
      - exploit IHargs; eauto. i; des.
        r. etrans; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
      - exploit IHargs; eauto. i; des.
        r. etrans; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
      - exploit IHargs; eauto. i; des.
        r. etrans; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
      - exploit IHargs; eauto. i; des.
        r. etrans; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
      - exploit IHargs; eauto. i; des.
        r. etrans; eauto.
        { eapply Mem.unchanged_on_implies; eauto.
          u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
        { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
    }
  Qed.

  (* TODO: remove same lemma in AsmregsC *)
  Lemma typesize_chunk
        ty
    :
      size_chunk (chunk_of_type ty) =
      4 * ty.(typesize)
  .
  Proof. destruct ty; ss. Qed.

  Let fill_arguments_spec_aux: forall
      sg m0 rs0 m1 sp args
      x y z
      (ALC: Mem.alloc m0 0 (4 * size_arguments_64 (sig_args sg) x y z) = (m1, sp))
      rs1 m2
      (FILL: fill_arguments sp rs0 m1 args (loc_arguments_64 (sig_args sg) x y z) = Some (rs1, m2))
      (LEN: length args = length sg.(sig_args))
      (DISJ: Loc.norepet (regs_of_rpairs (loc_arguments_64 (sig_args sg) x y z)))
      (ONE: forall lp, In lp (loc_arguments_64 (sig_args sg) x y z) -> <<ONE: is_one lp >>)
      (MAX: 4 * (size_arguments_64 (sig_args sg) x y z) <= Ptrofs.max_unsigned)
      (TYPED: Val.has_type_list args sg.(sig_args))
      (ACC: forall lp, In lp (loc_arguments_64 (sig_args sg) x y z) ->
                       <<ACC: forall_rpair loc_argument_acceptable lp>>)
      (BDD: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments_64 (sig_args sg) x y z)))
        ,
          <<BDD: ofs + typesize ty <= size_arguments_64 (sig_args sg) x y z>>)
    ,
      <<ALL: list_forall2 (extcall_arg_pair rs1 m2 (Vptr sp Ptrofs.zero true)) (loc_arguments_64 (sig_args sg) x y z) args>>
  .
  Proof.
    i.
    exploit fill_arguments_unchanged_on; eauto.
    intro UNCH; des.
    (* abstr (4 * (size_arguments_64 (sig_args sg) x y z)) sz. *)
    (* abstr (loc_arguments_64 (sig_args sg) x y z) locs. *)
    abstr (sig_args sg) tys.
    (* generalize (loc_arguments_64_charact tys x y z). intro CHAR. *)
    set (TYS:= tys) in *.
    ginduction args; ii; destruct tys; ss; des_ifs_safe.
    { econs; eauto. }
    u in FILL. des_ifs_safe; ss. destruct p; ss.
    unfold Regmap.set in *.
    destruct t; ss.
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
            change Mint32 with (chunk_of_type Tint).
            rewrite Val.load_result_same; ss.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mint32));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
            change Mfloat64 with (chunk_of_type Tfloat).
            rewrite Val.load_result_same; ss.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat64));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
            change Mint64 with (chunk_of_type Tlong).
            rewrite Val.load_result_same; ss.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat64));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
            change Mfloat32 with (chunk_of_type Tsingle).
            rewrite Val.load_result_same; ss.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat32));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
            change Many32 with (chunk_of_type Tany32).
            rewrite Val.load_result_same; ss.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many32));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
    - des_safe. des_ifs.
      + exploit IHargs; eauto.
        { locmap_tac. }
        i; des.
        econs; eauto.
        * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
          econs; eauto.
      + rename m2 into m3. rename m into m2.
        exploit IHargs; eauto.
        { locmap_tac. }
        { eapply fill_arguments_unchanged_on; eauto. }
        i; des.
        econs; eauto.
        * econs; eauto. econs; eauto. cbn. ss.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; ss.
          { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          }
          {
            hexploit BDD; eauto. i; des. ss.
            exploit ACC; eauto. i; ss; des.
            split; try xomega.
          }
        * eapply list_forall2_imply; eauto.
          ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
          extcall_simpl.
          econs; eauto.
          match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
          { rp; [econs|..]; try refl; eauto. }
          econs; eauto.
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many64));
            try apply H3; eauto.
          { eapply Mem.store_unchanged_on; eauto. }
          { locmap_tac.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_regs_of_rpairs; eauto. ss. eauto. }
            intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
            u; ii. des; try xomega.
          }
  Qed.

  Let fill_arguments_perm: forall
      sp rs0 m0 args locs rs1 m1
      (FILL: fill_arguments sp rs0 m0 args locs = Some (rs1, m1))
    ,
      <<PERM: forall ofs k p, Mem.perm m0 sp ofs k p -> Mem.perm m1 sp ofs k p>>
  .
  Proof.
    i.
    ginduction args; ii; ss; des_ifs_safe.
    { des_ifs. }
    u in FILL. des_ifs_safe. des_ifs.
    - destruct p0; ss. eapply IHargs; eauto.
    - destruct p0; ss. eapply Mem.perm_store_1; eauto. eapply IHargs; eauto.
  Qed.

  Theorem fill_arguments_spec
          sg m0 rs0 m1 sp args targs
          (* (LEN: length args = length sg.(sig_args)) *)
          (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, sp))
          rs1 m2
          (LEN: length args = length sg.(sig_args))
          (TYPIFY: typify_list args sg.(sig_args) = targs)
          (MAX: 4 * size_arguments sg <= Ptrofs.max_unsigned)
          (FILL: fill_arguments sp rs0 m1 targs (loc_arguments sg) = Some (rs1, m2))
    :
      store_arguments m0 rs1 targs sg m2
  .
  Proof.
    generalize (loc_arguments_norepet sg). intro DISJ.
    generalize (loc_arguments_one sg). intro ONE.
    (* destruct sg; ss. unfold size_arguments, loc_arguments in *. *)
    ss. des_ifs. clear_tac.
    unfold loc_arguments in *. des_ifs.
    assert(LEN2: length (typify_list args (sig_args sg)) = length (sig_args sg)).
    { u. rewrite zip_length. lia. }
    econs; eauto.
    - rr.
      eapply fill_arguments_spec_aux; ss; eauto.
      + eapply typify_has_type_list; eauto.
      + ii. eapply loc_arguments_acceptable; eauto. unfold loc_arguments. des_ifs. eauto.
      + i. eapply loc_arguments_bounded; eauto.
    - eapply Mem.unchanged_on_implies.
      { eapply fill_arguments_unchanged_on; try apply FILL; eauto. }
      i. des_ifs.
    - admit "ez - nextblock".
    - ii. eapply fill_arguments_perm; eauto. eauto with mem.
  Qed.

End FillArgs.

Theorem store_arguments_progress
        m0 vs tvs sg
        (TYP: typecheck vs sg tvs)
  :
    exists rs m2, <<STR: store_arguments m0 rs tvs sg m2>>
.
Proof.
  inv TYP.
  destruct (Mem.alloc m0 0 (4 * size_arguments sg)) eqn:ALC.
  rename m into m1. rename b into blk.
  assert(LEN2: Datatypes.length (typify_list vs (sig_args sg)) = Datatypes.length (sig_args sg)).
  { unfold typify_list. rewrite zip_length. xomega. }
  exploit (FillArgs.fill_arguments_progress sg m0 (Regmap.init Vundef)); eauto. i; des.
  exploit (FillArgs.fill_arguments_spec sg m0 (Regmap.init Vundef) m1 blk vs (typify_list vs (sig_args sg))); eauto.
Qed.

