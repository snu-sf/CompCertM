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
Require Import SimMemInj.
Require Stacklayout.
(** newly added **)
Require Import Mach mktac MemdataC.


Definition agree `{CTX: Val.meminj_ctx}  (j: meminj) (rs0 rs1: Mach.regset) : Prop :=
  forall mr, Val.inject j (rs0 mr) (rs1 mr).

Lemma typesize_chunk
      ty
  :
    size_chunk (chunk_of_type ty) =
    4 * ty.(typesize)
.
Proof. destruct ty; ss. Qed.

Section STOREARGUMENTS.

  Inductive val_undef : memval -> Prop :=
  | val_undef_fragment
      q n
    :
      val_undef (Fragment Vundef q n)
  | val_undef_undef
    :
      val_undef Undef
  .

  Definition memval_undefs (chunk: memory_chunk) (m: ZMap.t memval) ofs : Prop :=
    Forall val_undef (Mem.getN (size_chunk_nat chunk) ofs m).

  Inductive Val_longofwords' : val -> val -> val -> Prop :=
  | longofwords_value
      n1 n2 v1 v2 v
      (INT1: v1 = Vint n1)
      (INT2: v2 = Vint n2)
      (LONG: v = Vlong (Int64.ofwords n1 n2))
    :
      Val_longofwords' v1 v2 v
  | longofwords_undef
    :
      Val_longofwords' Vundef Vundef Vundef.

  Inductive extcall_arg (rs: Mach.regset) (m: mem) (sp: val) : loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall ofs ty v,
      Mem.loadv
        (chunk_of_type ty) m
        (Val.offset_ptr sp (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs))) = Some v ->
      forall (UNDEFS: forall blk stack_ofs (UNDEF: v = Vundef)
                             (ADDR: sp = Vptr blk stack_ofs true),
                 memval_undefs (chunk_of_type ty) (m.(Mem.mem_contents)!!blk)
                               (Ptrofs.unsigned stack_ofs + (Stacklayout.fe_ofs_arg + 4 * ofs))),
        extcall_arg rs m sp (S Outgoing ofs ty) v
  .

  Inductive extcall_arg_pair (rs: Mach.regset) (m: mem) (sp: val) : rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m sp l v ->
      extcall_arg_pair rs m sp (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo v,
      extcall_arg rs m sp hi vhi ->
      extcall_arg rs m sp lo vlo ->
      forall (LONG: Val_longofwords' vhi vlo v),
        extcall_arg_pair rs m sp (Twolong hi lo) v.

  Definition extcall_arguments
             (rs: Mach.regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
    list_forall2 (extcall_arg_pair rs m sp) (loc_arguments sg) args.

  Inductive store_arguments (m0: mem) (rs: Mach.regset) (vs: list val) (sg: signature) (m2: mem): Prop :=
  | store_arguments_intro
      m1 blk
      (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, blk))
      (VALS: extcall_arguments rs m2 (Vptr blk Ptrofs.zero true) sg vs)
      (UNCH: Mem.unchanged_on (fun b ofs => if eq_block b blk
                                            then ~ (0 <= ofs < 4 * size_arguments sg)
                                            else True) m1 m2)
      (NB: m1.(Mem.nextblock) = m2.(Mem.nextblock))
      (PERM: Mem.range_perm m2 blk 0 (4 * size_arguments sg) Cur Freeable)
  .

End STOREARGUMENTS.


Section STOREARGUMENTS_PROPERTY.


  Lemma store_undef_memval_undefs chunk m0 m1 blk ofs
        (STORE: Mem.store chunk m0 blk ofs Vundef = Some m1)
        (OFS: 0 <= ofs <= Ptrofs.max_unsigned)
  :
    memval_undefs chunk (m1.(Mem.mem_contents)!!blk) ofs.
  Proof.
    eapply Mem.store_mem_contents in STORE. ii; eauto. rewrite STORE.
    i. rewrite PMap.gss.
    unfold memval_undefs.
    replace (size_chunk_nat chunk) with
        (Datatypes.length (encode_val chunk Vundef)); cycle 1.
    { apply encode_val_length. }
    rewrite Mem.getN_setN_same.
    unfold encode_val, list_repeat.
    des_ifs; ss; repeat constructor.
  Qed.

  Lemma memval_undefs_unchanged_on P m m' chunk b ofs
        (UNCHANGED: Mem.unchanged_on P m m')
        (RANGE: forall i, ofs <= i < ofs + size_chunk chunk -> P b i)
        (UNDEFS: memval_undefs chunk (m.(Mem.mem_contents)!!b) ofs)
        (PERM: Mem.range_perm m b ofs (ofs + size_chunk chunk) Cur Readable)
    :
      memval_undefs chunk (m'.(Mem.mem_contents)!!b) ofs.
  Proof.
    unfold memval_undefs in *.
    replace (Mem.getN (size_chunk_nat chunk) ofs (Mem.mem_contents m') !! b)
      with (Mem.getN (size_chunk_nat chunk) ofs (Mem.mem_contents m) !! b); auto.
    rewrite size_chunk_conv in *.
    generalize dependent ofs.
    induction (size_chunk_nat chunk); ss; i.
    f_equal.
    - erewrite <- Mem.unchanged_on_contents; eauto.
      + eapply RANGE. lia.
      + eapply PERM. lia.
    - eapply IHn.
      + i. eapply RANGE. lia.
      + inv UNDEFS. eauto.
      + ii. eapply PERM. lia.
  Qed.


  Lemma longofwords_imply vh vl v
        (LONG: Val_longofwords' vh vl v)
    :
      Val.longofwords vh vl = v.
  Proof.
    inv LONG; clarify.
  Qed.

  Lemma extcall_arguments_same (rs0 rs1: Mach.regset) sp m sg args
        (ARGS: extcall_arguments rs0 m sp sg args)
        (SAME: forall r (IN: In (R r) (regs_of_rpairs (loc_arguments sg))),
            rs0 r = rs1 r)
    :
      extcall_arguments rs1 m sp sg args.
  Proof.
    clear - ARGS SAME. unfold extcall_arguments in *.
    revert args ARGS SAME. generalize (loc_arguments sg). induction l; ss; i.
    - inv ARGS. econs.
    - inv ARGS. econs; eauto.
      + inv H1.
        * econs 1. inv H; eauto.
          -- erewrite SAME.
             ++ econs.
             ++ econs. eauto.
          -- econs; eauto.
        * inv H; inv H0.
          -- econs; eauto; erewrite SAME; eauto; (try by econs; eauto).
             ss. eauto.
          -- econs; eauto; try erewrite SAME; eauto; (try by econs; eauto).
          -- econs; eauto; try erewrite SAME; eauto; (try by econs; eauto).
             ss. eauto.
          -- econs; eauto; try erewrite SAME; eauto; (try by econs; eauto).
      + eapply IHl; eauto.
        ii. eapply SAME. eapply in_app; eauto.
  Qed.

  Definition extcall_arg_in_reg (rs: regset) (l: rpair loc) (v: val) : Prop :=
    forall r (EQ: l = One (R r)), v = rs r.

  Definition extcall_arg_in_stack (m: ZMap.t memval) (l: rpair loc) (v: val) : Prop :=
    forall ofs ty (EQ: l = One (S Outgoing ofs ty)),
      (<<LOAD:
         Some (decode_val (chunk_of_type ty) (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * ofs) m)) = Some v>>) /\
      (<<UNDEFS: forall (UNDEF: v = Vundef),
          memval_undefs (chunk_of_type ty) m (4 * ofs)>>).

  Lemma extcall_arguments_extcall_arg_in_reg
        rs m blk sg vs
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (ARGS: list_forall2
                 (extcall_arg_pair rs m (Vptr blk Ptrofs.zero true))
                 (loc_arguments sg) vs)
    :
      list_forall2
        (extcall_arg_in_reg rs)
        (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg).
    generalize (loc_arguments_ofs_bounded sg SZ).
    revert vs ARGS.
    induction (loc_arguments sg); ss; i.
    - inv ARGS. econs.
    - inv ARGS. econs.
      + ii. clarify. inv H3. inv H2. auto.
      + eapply IHl; eauto.
  Qed.

  Lemma extcall_arguments_extcall_arg_in_stack
        rs m blk sg vs
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (ARGS: list_forall2
                 (extcall_arg_pair rs m (Vptr blk Ptrofs.zero true))
                 (loc_arguments sg) vs)
    :
      list_forall2
        (extcall_arg_in_stack (m.(Mem.mem_contents) !! blk))
        (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg).
    generalize (loc_arguments_ofs_bounded sg SZ).
    revert vs ARGS.
    induction (loc_arguments sg); ss; i.
    - inv ARGS. econs.
    - inv ARGS. econs.
      + ii. clarify. inv H3. inv H2. split.
        * ss. Local Transparent Mem.load. unfold Mem.load in *. des_ifs.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; eauto.
        * ii. ss. hexploit UNDEFS; eauto.
      + eapply IHl; eauto.
  Qed.

  Lemma extcall_arg_in_stack_in_reg_extcall_argument
        m blk m_blk rs vs sg
        (STACK: list_forall2
                  (extcall_arg_in_stack m_blk)
                  (loc_arguments sg) vs)
        (REGS: list_forall2
                 (extcall_arg_in_reg rs)
                 (loc_arguments sg) vs)
        (MBLK: m.(Mem.mem_contents) !! blk = m_blk)
        (PERM: Mem.range_perm m blk 0 (4 * size_arguments sg) Cur Freeable)
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
    :
      list_forall2
        (extcall_arg_pair rs m (Vptr blk Ptrofs.zero true)) (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg).
    generalize (loc_arguments_ofs_bounded sg SZ).
    assert (RANGE: forall ofs ty (In: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
               Mem.range_perm m blk (4 * ofs) (4 * (ofs + typesize ty)) Cur Freeable).
    { i. hexploit loc_arguments_bounded; eauto.
      ii. eapply PERM. split; try lia.
      hexploit loc_arguments_acceptable; eauto; cycle 1.
      - instantiate (1:= One (S Outgoing ofs ty)).
        i. inv H1. lia.
      - instantiate (1:= sg).
        generalize (loc_arguments_one sg).
        revert In. clear. induction (loc_arguments sg); ss.
        i. dup H. specialize (H _ (or_introl eq_refl)).
        unfold is_one in *. des_ifs.
        ss. des; clarify; eauto. }
    generalize (loc_arguments_one sg).
    revert vs STACK REGS RANGE.
    induction (loc_arguments sg); ss; i.
    - inv STACK. econs.
    - inv STACK. inv REGS. econs.
      + destruct a; cycle 1.
        { exfalso. hexploit H; eauto. }
        destruct r.
        * econs. exploit H7; eauto. i. clarify. econs.
        * destruct sl.
          { exfalso. exploit H1; eauto. }
          { exfalso. exploit H1; eauto. }
          econs. exploit H4; eauto. i. des. econs.
          { unfold Mem.loadv in *. ss. unfold Mem.load. des_ifs.
            - rewrite Ptrofs.add_zero_l.
              rewrite Ptrofs.unsigned_repr; eauto.
            - exfalso. apply n.
              unfold Mem.valid_access. split; ii.
              + eapply Mem.perm_implies; eauto.
                * eapply RANGE; eauto.
                  rewrite Ptrofs.add_zero_l in *.
                  rewrite Ptrofs.unsigned_repr in *.
                  -- split; destruct ty; ss; try lia.
                  -- exploit H0; eauto.
                  -- exploit H0; eauto.
                * econs.
              + rewrite Ptrofs.add_zero_l in *.
                rewrite Ptrofs.unsigned_repr in *.
                * exploit H1; eauto.
                  i. inv H2.
                  destruct ty; ss; eapply Z.mul_divide_mono_l with (p := 4) in H5; eauto.
                * exploit H0; eauto.
                * exploit H0; eauto. }
          -- i. exploit UNDEFS; eauto. clarify.
      + eapply IHl; eauto.
        ii. eapply RANGE; eauto.
        eapply in_or_app; eauto.
  Qed.

  Lemma store_arguments_unchanged_on m0 m1 rs args sg
        (STORE: store_arguments m0 rs args sg m1)
    :
      Mem.unchanged_on (SimMemInj.valid_blocks m0) m0 m1.
  Proof.
    inv STORE. dup ALC. eapply Mem.alloc_unchanged_on in ALC0.
    eapply Mem.unchanged_on_trans; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    i. ss. des_ifs. red in H.
    exfalso. eapply Mem.fresh_block_alloc; eauto.
  Qed.

End STOREARGUMENTS_PROPERTY.



Module _FillArgsParallel.

  Definition copy_memval (v: val) (mv: memval) : memval :=
    match v, mv with
    | Vundef, _ => Undef
    | _, Fragment _ q n => Fragment v q n
    | _, _ => mv
    end.

  Definition copy_list_memval (v: val): list memval -> list memval := map (copy_memval v).

  Lemma copy_list_memval_decode_undef vl vl'
        (COPY: copy_list_memval Vundef vl = vl')
    :
      vl' = list_repeat (List.length vl) Undef.
  Proof.
    revert vl' COPY. induction vl; ss; i; clarify.
    f_equal. eapply IHvl; eauto.
  Qed.

  Local Existing Instance Val.mi_normal.
  (* Context `{CTX: Val.meminj_ctx}. *)

  Lemma copy_list_memval_decode_pointer j vl vl' chunk v blk ofs b
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
        (VALUE: v = Vptr blk ofs b)
    :
      decode_val chunk vl' = v.
  Proof.
    clarify. inv INJ; ss.
    - unfold decode_val in H3. destruct vl; ss.
      + des_ifs.
      + des_ifs_safe.
        destruct m, chunk; ss; des_ifs_safe.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs.
        * destruct v; ss.
        * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs.
    - unfold decode_val in H3. destruct vl; ss.
      + des_ifs_safe.
        destruct m, chunk; ss; des_ifs_safe.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * des_ifs.
        * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs.
        * destruct v; ss.
        * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs.
  Qed.

  Lemma copy_list_memval_decode j vl vl' chunk v
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
        (LENGTH: Nat.lt 0 (length vl))
    :
      decode_val chunk vl' = v.
  Proof.
    inv INJ.
    - rewrite H1. f_equal.
      apply eq_Forall2_eq. eapply Forall2_in_map.
      i. rewrite <- H1.
      destruct a; ss. f_equal. symmetry.
      eapply decode_fragment_all; eauto. ii. clarify.
    - rewrite H1. f_equal.
      apply eq_Forall2_eq. eapply Forall2_in_map.
      i. rewrite <- H1.
      destruct a; ss. f_equal. symmetry.
      eapply decode_fragment_all; eauto. ii. clarify.
    - rewrite H1. f_equal.
      apply eq_Forall2_eq. eapply Forall2_in_map.
      i. rewrite <- H1.
      destruct a; ss. f_equal. symmetry.
      eapply decode_fragment_all; eauto. ii. clarify.
    - rewrite H1. f_equal.
      apply eq_Forall2_eq. eapply Forall2_in_map.
      i. rewrite <- H1.
      destruct a; ss. f_equal. symmetry.
      eapply decode_fragment_all; eauto. ii. clarify.
    - eapply copy_list_memval_decode_pointer; eauto.
      rewrite <- H.
      econs; eauto.
    - eapply copy_list_memval_decode_pointer; eauto.
      rewrite <- H.
      econs; eauto.
    - eapply copy_list_memval_decode_pointer; eauto.
      rewrite <- H.
      econs; eauto.
    - exploit copy_list_memval_decode_undef. eauto. i.
      rewrite H.
      destruct vl; ss.
      + inv LENGTH.
      + unfold decode_val. des_ifs.
        Unshelve. eauto.
  Qed.

  Lemma copy_list_memval_inject j vl vl' chunk v
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
    :
      list_forall2 (memval_inject j) vl' vl.
  Proof.
    clarify. destruct v.
    - exploit copy_list_memval_decode_undef; eauto. i.
      rewrite H.
      eapply repeat_Undef_inject_any.
    - eapply Forall2_in_map. i.
      destruct a; ss; try econs.
      erewrite decode_fragment_all; eauto.
      ii. rewrite H in *. inv INJ.
    - eapply Forall2_in_map. i.
      destruct a; ss; try econs.
      erewrite decode_fragment_all; eauto.
      ii. rewrite H in *. inv INJ.
    - eapply Forall2_in_map. i.
      destruct a; ss; try econs.
      erewrite decode_fragment_all; eauto.
      ii. rewrite H in *. inv INJ.
    - eapply Forall2_in_map. i.
      destruct a; ss; try econs.
      erewrite decode_fragment_all; eauto.
      ii. rewrite H in *. inv INJ.
    - eapply Forall2_in_map. i.
      destruct a; ss; try econs.
      erewrite decode_fragment_all; eauto.
      ii. rewrite H in *. inv INJ.
  Qed.

  Definition fill_arg_src_reg (rs: regset) (arg: val) (loc: rpair loc)
    : regset :=
    match loc with
    | One (R r) =>
      rs#r <- arg
    | _ => rs
    end.

  Fixpoint fill_args_src_reg (args: list val) (locs: list (rpair loc))
    : regset :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_src_reg (fill_args_src_reg vtl ltl) vhd lhd
    | _, _ => fun _ => Vundef
    end.

  Lemma fill_args_src_reg_args args locs
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (ONES: forall l (IN: In l locs), is_one l)
        (LENGTH: length args = length locs)
    :
      list_forall2 (extcall_arg_in_reg (fill_args_src_reg args locs)) locs args.
  Proof.
    revert NOREPEAT args LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv LENGTH. destruct a; inv NOREPEAT.
      + exploit IHlocs; eauto. i.
        unfold fill_arg_src_reg. des_ifs.
        * econs; eauto.
          -- ii. inv EQ. rewrite Regmap.gss. auto.
          -- eapply list_forall2_lift; [|eauto].
             { ii. clarify. unfold Regmap.set. des_ifs; eauto.
               exfalso. eapply loc_notin_not_in; eauto.
               eapply in_one_in_rpair; eauto. }
        * econs; eauto. ii. inv EQ.
      + exfalso. exploit ONES; eauto.
  Qed.

  Lemma fill_args_src_reg_agree j args args_tgt locs rs_tgt
        (INJECT: Val.inject_list j args args_tgt)
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_reg rs_tgt) locs args_tgt)
    :
      agree j (fill_args_src_reg args locs) rs_tgt.
  Proof.
    generalize dependent args.
    revert rs_tgt args_tgt ARGS. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss.
    - destruct args; ss. inv INJECT. inv LENGTH. inv ARGS.
      unfold fill_arg_src_reg. des_ifs.
      + ii. unfold Regmap.set. des_ifs.
        * exploit H5; eauto. i. clarify.
        * eapply IHlocs; eauto.
      + eapply IHlocs; eauto.
      + eapply IHlocs; eauto.
  Qed.


  Definition fill_arg_src_blk (m_tgt m: ZMap.t memval) (arg: val) (loc: rpair loc)
    : ZMap.t memval :=
    match loc with
    | One (S Outgoing ofs ty) =>
      Mem.setN (copy_list_memval arg (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * ofs) m_tgt)) (4 * ofs) m
    | _ => m
    end.

  Fixpoint fill_args_src_blk (m_tgt m: ZMap.t memval) (args: list val) (locs: list (rpair loc))
    : ZMap.t memval :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_src_blk m_tgt (fill_args_src_blk m_tgt m vtl ltl) vhd lhd
    | _, _ => m
    end.

  Lemma fill_args_src_blk_inject m_tgt j args_tgt args locs
        (INJECT: Val.inject_list j args args_tgt)
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt) locs args_tgt)
    :
      forall ofs, memval_inject
                    j
                    (ZMap.get ofs (fill_args_src_blk m_tgt (ZMap.init Undef) args locs))
                    (ZMap.get ofs m_tgt).
  Proof.
    generalize dependent args.
    revert m_tgt args_tgt ARGS. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss. rewrite ZMap.gi. econs.
    - destruct args; ss. inv INJECT. inv LENGTH. inv ARGS.
      unfold fill_arg_src_blk. des_ifs.
      + eapply IHlocs; eauto.
      + eapply IHlocs; eauto.
      + eapply IHlocs; eauto.
      + exploit IHlocs; eauto. instantiate (1:=ofs). intros INJ.
        { exploit Mem.setN_inj.
          - instantiate (3:=j).
            instantiate (2:=copy_list_memval v (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * pos) m_tgt)).
            instantiate (1:=Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * pos) m_tgt).
            specialize (H5 pos ty eq_refl). des. clarify.
            { eapply copy_list_memval_inject; eauto. }
          - instantiate (4:=top1).
            instantiate (3:=fill_args_src_blk m_tgt (ZMap.init Undef) args locs).
            instantiate (1:=m_tgt).
            instantiate (1:=0).
            i. rewrite Z.add_0_r.
            eapply IHlocs; eauto.
          - econs.
          - instantiate (2:= ofs). instantiate (1:=4*pos).
            repeat rewrite Z.add_0_r.
            i.
            replace (ZMap.get ofs (Mem.setN (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * pos) m_tgt) (4*pos) m_tgt)) with (ZMap.get ofs m_tgt) in H; eauto.
            { generalize ofs.
              clear - m_tgt.
              generalize (4 * pos). revert m_tgt.
              generalize (size_chunk_nat (chunk_of_type ty)).
              induction n; ss; i.
              replace (Mem.getN n (z + 1) m_tgt) with
                  (Mem.getN n (z + 1) (ZMap.set z (ZMap.get z m_tgt) m_tgt)).
              - rewrite <- IHn.
                rewrite ZMap.gsspec. des_ifs.
              - clear IHn. generalize z m_tgt (z+1).
                induction n; ss; i. f_equal.
                + rewrite ZMap.gsspec. des_ifs.
                + rewrite IHn. eauto. }
        }
      + eapply IHlocs; eauto.
  Qed.

  Lemma fill_args_src_blk_args m_tgt m j args_tgt args locs
        (INJECT: Val.inject_list j args args_tgt)
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt) locs args_tgt)
    :
      list_forall2 (extcall_arg_in_stack (fill_args_src_blk m_tgt m args locs)) locs args.
  Proof.
    revert NOREPEAT args_tgt args ARGS INJECT LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv LENGTH.
      inv ARGS. inv INJECT.
      exploit IHlocs; eauto.
      { ii. eapply loc_norepet_app; eauto. }
      unfold fill_arg_src_blk. des_ifs.
      + econs; eauto. ii. inv EQ.
      + econs; eauto. ii. inv EQ.
      + econs; eauto. ii. inv EQ.
      + econs; eauto.
        { ii. inv EQ. specialize (H2 ofs ty0 eq_refl). des. clarify.
          assert (LEQ: size_chunk_nat (chunk_of_type ty0) =
                       Datatypes.length (copy_list_memval v (Mem.getN (size_chunk_nat (chunk_of_type ty0)) (4 * ofs) m_tgt))).
          { unfold copy_list_memval. rewrite list_length_map.
            rewrite Mem.getN_length. auto. }
          split.
          - pattern (size_chunk_nat (chunk_of_type ty0)) at 1.
            rewrite LEQ.
            erewrite Mem.getN_setN_same.
            exploit copy_list_memval_decode; eauto.
            + rewrite Mem.getN_length.
              destruct ty0; compute; lia.
            + i. rewrite H1. auto.
          - ii. clarify. unfold memval_undefs in *.
            pattern (size_chunk_nat (chunk_of_type ty0)) at 1.
            rewrite LEQ.
            erewrite Mem.getN_setN_same.
            unfold copy_list_memval. unfold copy_memval. ss.
            eapply Forall_map.
            ii. econs.
        }
        { eapply list_forall2_lift; [| eauto].
          ii. clarify. specialize (H1 ofs ty0 eq_refl). des. clarify.
          split; i.
          - erewrite Mem.getN_setN_outside; eauto.
            ss. inv NOREPEAT.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_one_in_rpair; eauto. } intros DIFF. ss.
            unfold copy_list_memval in *.
            erewrite map_length. rewrite Mem.getN_length.
            repeat rewrite <- size_chunk_conv.
            repeat rewrite typesize_chunk. des; clarify; lia.
          - ii. unfold memval_undefs in *.
            erewrite Mem.getN_setN_outside; auto.
            ss. inv NOREPEAT.
            exploit Loc.in_notin_diff; eauto.
            { eapply in_one_in_rpair; eauto. } intros DIFF. ss.
            unfold copy_list_memval in *.
            erewrite map_length. rewrite Mem.getN_length.
            repeat rewrite <- size_chunk_conv.
            repeat rewrite typesize_chunk. des; clarify; lia. }
      + econs; eauto. ii. inv EQ.
  Qed.

  Lemma fill_args_src_blk_default m_tgt m args locs
    :
      fst (fill_args_src_blk m_tgt m args locs) = fst m.
  Proof.
    revert m locs. induction args; ss; i.
    unfold fill_arg_src_blk. des_ifs; ss.
    rewrite Mem.setN_default. ss.
  Qed.

  Program Definition fill_args_src_mem (m_tgt0 m_tgt1 : mem) (m_src0: mem)
          (args: list val) (locs: list (rpair loc)) : mem :=
    Mem.mkmem
      (PMap.set
         (m_src0.(Mem.nextblock))
         (fill_args_src_blk
            (m_tgt1.(Mem.mem_contents) !! (m_tgt0.(Mem.nextblock)))
            (ZMap.init Undef) args locs)
         (m_src0.(Mem.mem_contents)))
      (PMap.set
         (m_src0.(Mem.nextblock))
         (m_tgt1.(Mem.mem_access) !! (m_tgt0.(Mem.nextblock)))
         (m_src0.(Mem.mem_access)))
      (Pos.succ m_src0.(Mem.nextblock))
      _ _ _.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - eapply Mem.access_max.
    - eapply Mem.access_max.
  Qed.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - exfalso. eapply H. eapply Plt_succ.
    - eapply Mem.nextblock_noaccess. ii.
      eapply H. etrans; eauto. eapply Plt_succ.
  Qed.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - rewrite fill_args_src_blk_default. eauto.
    - eapply Mem.contents_default.
  Qed.

End _FillArgsParallel.


Section STOREARGPRARALLEL.

  Local Existing Instance Val.mi_normal.

  Theorem store_arguments_parallel_inject
          j m_src0 m_tgt0 m_tgt1 rs_tgt vs vs' sg
          (TYP: Val.has_type_list vs' sg.(sig_args))
          (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
          (* (TYP: typechecked_args sg vs) *)
          (* (TYP: typechecked_args sg vs') *)
          (VALINJ: Val.inject_list j vs vs')
          (INJ: Mem.inject j m_src0 m_tgt0)
          (ARGSRC: store_arguments m_tgt0 rs_tgt vs' sg m_tgt1)
    :
      exists m_src1 rs_src,
        (<<ARGTGT: store_arguments m_src0 rs_src vs sg m_src1>>) /\
        (<<INJ: Mem.inject (update_meminj j (Mem.nextblock m_src0) (Mem.nextblock m_tgt0) 0) m_src1 m_tgt1>>) /\
        (<<AGREE: agree
                    (update_meminj j (Mem.nextblock m_src0) (Mem.nextblock m_tgt0) 0)
                    rs_src
                    rs_tgt>>).
  Proof.
    exists (_FillArgsParallel.fill_args_src_mem m_tgt0 m_tgt1 m_src0 vs (loc_arguments sg)).
    exists (_FillArgsParallel.fill_args_src_reg vs (loc_arguments sg)).
    destruct (Mem.alloc m_src0 0 (4 * size_arguments sg)) eqn:ALLOC.
    dup ALLOC. apply Mem.alloc_result in ALLOC0. clarify.

    inv ARGSRC. unfold extcall_arguments in *.
    dup ALC. apply Mem.alloc_result in ALC0. clarify.

    assert (INC : inject_incr j (update_meminj j (Mem.nextblock m_src0) (Mem.nextblock m_tgt0) 0)).
    { unfold update_meminj in *. ii. des_ifs; ss.
      exfalso. inv INJ. exploit mi_freeblocks.
      - instantiate (1:=(Mem.nextblock m_src0)).
        unfold Mem.valid_block. eapply Plt_strict.
      - ii. clarify. }

    splits.
    - econs; ss; eauto.
      + unfold extcall_arguments in *.
        assert (LENGTH: Datatypes.length vs = Datatypes.length (loc_arguments sg)).
        { erewrite inject_list_length; eauto.
          symmetry. eapply list_forall2_length; eauto. }
        exploit _FillArgsParallel.fill_args_src_reg_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply loc_arguments_one. }
        exploit _FillArgsParallel.fill_args_src_blk_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. }
        instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold _FillArgsParallel.fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss.
          exploit PERM; eauto.
      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0.
        econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          - split; i; exfalso.
            + eapply Mem.perm_alloc_3 in H1; eauto.
            + unfold _FillArgsParallel.fill_args_src_mem, Mem.perm in *. ss.
              rewrite PMap.gss in H1; eauto.
              eapply Mem.perm_unchanged_on_2 in H1; eauto.
              * eapply Mem.perm_alloc_3 in H1; eauto.
              * ss. des_ifs.
              * eapply Mem.valid_new_block; eauto.
          - transitivity (Mem.perm m_src0 b ofs k p).
            + symmetry. apply unchanged_on_perm; eauto.
              unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc in H0; eauto.
              eapply Plt_succ_inv in H0. des; clarify.
            + unfold Mem.perm; ss; eauto.
              rewrite PMap.gso; eauto. }
        { i. des_ifs.
          - rewrite PMap.gss.
            exfalso. exploit Mem.perm_alloc_3; try apply ALLOC; eauto.
          - rewrite PMap.gso; eauto.
            symmetry. apply unchanged_on_contents; eauto.
            eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss.
        eapply PERM; eauto.
    - inv INJ. inv mi_inj. unfold _FillArgsParallel.fill_args_src_mem, update_meminj in *.
      econs; ss; i.
      { econs; ss; i.
        - des_ifs.
          + unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss.
            zsimpl. eauto.
          + inv UNCH. eapply unchanged_on_perm.
            * des_ifs.
              exploit mi_mappedblocks; eauto.
              ii. unfold Mem.valid_block in *. ss.
              eapply Plt_strict; eauto.
            * exploit mi_mappedblocks; eauto.
              i. eapply Mem.valid_block_alloc; eauto.
            * eapply Mem.perm_alloc_1; eauto.
              unfold Mem.perm in *. ss.
              rewrite PMap.gsspec in *. des_ifs; ss. eauto.
        - des_ifs.
          + eapply Z.divide_0_r.
          + eapply mi_align; eauto.
            ii. unfold Mem.range_perm, Mem.perm in *; ss.
            rewrite PMap.gsspec in *. des_ifs; ss.
            eapply H0; eauto.
        - eapply memval_inject_incr; eauto.
          rewrite PMap.gsspec in *. des_ifs; ss.
          + hexploit _FillArgsParallel.fill_args_src_blk_inject; eauto.
            * erewrite inject_list_length; eauto.
              eapply Val_has_type_list_length; eauto.
            * eapply extcall_arguments_extcall_arg_in_stack; eauto.
            * instantiate (1:= ofs). rewrite Z.add_0_r. intros VINJ.
              eapply memval_inject_incr; eauto.
          + dup ALC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALC0. inv ALC0.
            exploit mi_memval; eauto.
            * unfold Mem.perm in *; ss.
              rewrite PMap.gsspec in *. des_ifs; ss. eauto.
            * { i. inv UNCH.
                rewrite unchanged_on_contents0.
                - rewrite unchanged_on_contents; eauto.
                  unfold Mem.perm in *; ss.
                  rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                - des_ifs.
                  unfold Mem.perm in *; ss.
                  rewrite PMap.gsspec in *. des_ifs; ss.
                  eapply mi_mappedblocks in H.
                  ii. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
                - exploit mi_perm; eauto.
                  + unfold Mem.perm in *; ss.
                    rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                  + i. eapply unchanged_on_perm; eauto. }
      }
      { unfold Mem.valid_block in *. ss. des_ifs.
        - exfalso. eapply H. eapply Plt_succ.
        - eapply mi_freeblocks. ii. eapply H. etrans; eauto. eapply Plt_succ. }
      { des_ifs.
        - eapply Mem.valid_new_block in ALC. unfold Mem.valid_block in *.
          rewrite <- NB. eauto.
        - exploit mi_mappedblocks; eauto.
          unfold Mem.valid_block in *.
          rewrite <- NB. i. etrans; eauto.
          erewrite (Mem.nextblock_alloc) with (m2 := m1); eauto.
          apply Plt_succ. }

      { ii. des_ifs; ss; clarify.
        - left. ii. clarify.
          exploit mi_mappedblocks; eauto. unfold Mem.valid_block. xomega.
        - left. ii. clarify.
          exploit mi_mappedblocks; eauto. unfold Mem.valid_block. xomega.
        - eapply mi_no_overlap with (b1 := b1) (b2 := b2); eauto.
          + unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss.
          + unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss. }
      { des_ifs.
        - set (Ptrofs.unsigned_range_2 ofs). lia.
        - eapply mi_representable; eauto.
          unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. }
      { des_ifs.
        - unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss.
          rewrite Z.add_0_r in *. eauto.
        - exploit mi_perm_inv; eauto.
          + inv UNCH. apply unchanged_on_perm in H0.
            * eapply Mem.perm_alloc_4; eauto.
              ii. clarify.
              exploit mi_mappedblocks; eauto.
              i. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
            * des_ifs.
              exploit mi_mappedblocks; eauto.
              ii. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
            * exploit mi_mappedblocks; eauto.
              i. unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc; eauto. etrans; eauto.
              apply Plt_succ.
          + i. unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss. }
    - hexploit _FillArgsParallel.fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto.
        eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto.
      + ii. cinv (H mr); econs; eauto.
  Qed.

  Theorem store_arguments_parallel_extends
          m_src0 m_tgt0 m_tgt1 rs_tgt vs vs' sg
          (TYP: Val.has_type_list vs' sg.(sig_args))
          (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
          (* (TYP: typechecked_args sg vs) *)
          (* (TYP: typechecked_args sg vs') *)
          (VALINJ: Val.lessdef_list vs vs')
          (EXTENDS: Mem.extends m_src0 m_tgt0)
          (ARGSRC: store_arguments m_tgt0 rs_tgt vs' sg m_tgt1)
    :
      exists m_src1 rs_src,
        (<<ARGTGT: store_arguments m_src0 rs_src vs sg m_src1>>) /\
        (<<EXTENDS: Mem.extends m_src1 m_tgt1>>) /\
        (<<AGREE: agree
                    inject_id
                    rs_src
                    rs_tgt>>).
  Proof.
    exists (_FillArgsParallel.fill_args_src_mem m_tgt0 m_tgt1 m_src0 vs (loc_arguments sg)).
    exists (_FillArgsParallel.fill_args_src_reg vs (loc_arguments sg)).

    destruct (Mem.alloc m_src0 0 (4 * size_arguments sg)) eqn:ALLOC.
    dup ALLOC. apply Mem.alloc_result in ALLOC0. clarify.

    inv ARGSRC. unfold extcall_arguments in *.
    dup ALC. apply Mem.alloc_result in ALC0. clarify.
    eapply val_inject_list_lessdef in VALINJ.

    splits; ss.

    - econs; ss; eauto.
      + unfold extcall_arguments in *.
        assert (LENGTH: Datatypes.length vs = Datatypes.length (loc_arguments sg)).
        { erewrite inject_list_length; eauto.
          symmetry. eapply list_forall2_length; eauto. }
        exploit _FillArgsParallel.fill_args_src_reg_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply loc_arguments_one. }
        exploit _FillArgsParallel.fill_args_src_blk_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. }
        instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold _FillArgsParallel.fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss.
          exploit PERM; eauto.
      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0.
        econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          - split; i; exfalso.
            + eapply Mem.perm_alloc_3 in H1; eauto.
            + unfold _FillArgsParallel.fill_args_src_mem, Mem.perm in *. ss.
              rewrite PMap.gss in H1; eauto.
              eapply Mem.perm_unchanged_on_2 in H1; eauto.
              * eapply Mem.perm_alloc_3 in H1; eauto.
              * ss. des_ifs.
              * eapply Mem.valid_new_block; eauto.
          - transitivity (Mem.perm m_src0 b ofs k p).
            + symmetry. apply unchanged_on_perm; eauto.
              unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc in H0; eauto.
              eapply Plt_succ_inv in H0. des; clarify.
            + unfold Mem.perm; ss; eauto.
              rewrite PMap.gso; eauto. }
        { i. des_ifs.
          - rewrite PMap.gss.
            exfalso. exploit Mem.perm_alloc_3; try apply ALLOC; eauto.
          - rewrite PMap.gso; eauto.
            symmetry. apply unchanged_on_contents; eauto.
            eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss.
        eapply PERM; eauto.

    - unfold _FillArgsParallel.fill_args_src_mem. inv EXTENDS. inv mext_inj. econs.
      + ss. rewrite mext_next. erewrite <- Mem.nextblock_alloc; eauto.
      + unfold inject_id in *.

        { econs; ss; i; clarify.
          - zsimpl.
            destruct (peq b2 (Mem.nextblock m_src0)); clarify.
            + unfold Mem.perm in *. ss.
              rewrite PMap.gsspec in *. des_ifs; ss. rewrite mext_next. eauto.
            + inv UNCH. eapply unchanged_on_perm.
              * des_ifs. eauto.
              * eapply Mem.perm_valid_block.
                eapply Mem.perm_alloc_1; eauto.
                eapply mi_perm; eauto.
                unfold Mem.perm in *. ss.
                rewrite PMap.gsspec in *. des_ifs; ss. eauto.
              * eapply Mem.perm_alloc_1; eauto.
                unfold Mem.perm in *. ss.
                rewrite PMap.gsspec in *. des_ifs; ss.
                exploit mi_perm; eauto.
                i. zsimpl. eauto.
          - eapply Z.divide_0_r.

          - rewrite PMap.gsspec in *. des_ifs; ss.
            + hexploit _FillArgsParallel.fill_args_src_blk_inject; eauto.
              * erewrite inject_list_length; eauto.
                eapply Val_has_type_list_length; eauto.
              * eapply extcall_arguments_extcall_arg_in_stack; eauto.
              * instantiate (2:= ofs). rewrite Z.add_0_r. intros VINJ.
                repeat rewrite mext_next in *. eauto.
            + exploit mi_memval; eauto.
              * unfold Mem.perm in *. ss.
                rewrite PMap.gsspec in *. des_ifs; ss. eauto.
              * zsimpl. i.
                { inv UNCH.
                  dup ALC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALC0. inv ALC0.
                  rewrite unchanged_on_contents; ss; eauto.
                  - rewrite unchanged_on_contents0; eauto.
                    unfold Mem.perm in *; ss.
                    rewrite PMap.gsspec in *. des_ifs; ss.
                    exploit mi_perm; eauto. zsimpl. eauto.
                  - des_ifs. eauto.
                  - eapply unchanged_on_perm0; eauto.
                    + eapply Mem.perm_valid_block.
                      exploit mi_perm; eauto.
                      * unfold Mem.perm in *; ss.
                        rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                    + exploit mi_perm; eauto.
                      * unfold Mem.perm in *; ss.
                        rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                      * zsimpl. eauto. }
        }
      + { ii. destruct (peq b (Mem.nextblock m_src0)); clarify.
          - unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss.
            rewrite <- mext_next. auto.
          - exploit mext_perm_inv; eauto.
            + inv UNCH. apply unchanged_on_perm in H.
              * eapply Mem.perm_alloc_4; eauto.
                ii. clarify. eauto.
              * des_ifs. eauto.
              * eapply Mem.perm_valid_block in H.
                unfold Mem.valid_block in *. rewrite NB. eauto.
            + i. unfold Mem.perm in *. ss.
              rewrite PMap.gsspec in *. des_ifs; ss. }
    - hexploit _FillArgsParallel.fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto.
        eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto.
      + ii. cinv (H mr); econs; eauto.
  Qed.

End STOREARGPRARALLEL.


Ltac extcall_simpl :=
  repeat match goal with
         | [ H: extcall_arg_pair _ _ _ (One _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (S _ _ _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (R _) _ |- _ ] => inv H
         end
.

Local Opaque Z.mul Z.sub Z.div.
Local Transparent size_arguments.
Local Transparent loc_arguments.

Module FillArgsProgress.

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

  Hint Unfold o_bind2.

  (* move to Conventions1C *)
  Lemma size_arguments_64_larger x y z tys
    :
      z <= size_arguments_64 tys x y z
  .
  Proof.
    ginduction tys; ss; i.
    - refl.
    - des_ifs; specialize (IHtys x y (z +2)); nia.
  Qed.

  Let fill_arguments_unchanged_on
      sp rs0 m0 args x y z rs1 m1 tys
      (LEN: length args = length tys)
      (FILL: fill_arguments sp rs0 m0 args (loc_arguments_64 tys x y z) = Some (rs1, m1))
    :
      (* <<UNCH: Mem.unchanged_on (brange sp 0 (4 * z)) m0 m1>> *)
      (<<UNCH: Mem.unchanged_on (fun b ofs => if eq_block b sp
                                              then ~ (4 * z <= ofs < 4 * size_arguments_64 tys x y z)
                                              else True) m0 m1>>)
  .
  Proof.
    ginduction tys; ss; i.
    { destruct args; ss; clarify. r. refl. }
    u in *. destruct args; ss; clarify.
    u in *. des_ifs_safe. destruct p. destruct r0; ss.
    - des_ifs; clarify; eauto.
    - des_ifs_safe.
      set (size_arguments_64_larger x y (z + 2) tys).
      exploit Mem.store_unchanged_on; eauto.
      { instantiate (1:= (fun b ofs =>
                            if eq_block b sp
                            then ~ 4 * pos <= ofs < 4 * pos + size_chunk (chunk_of_type ty)
                            else True)). i. ss. des_ifs.
      } i.
      des_ifs; exploit IHtys; eauto; i; ss;
        transitivity m; eapply Mem.unchanged_on_implies; eauto; i; ss; des_ifs; nia.
  Qed.


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
        * econs; eauto. econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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

          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }

          econs; eauto; cycle 1.
          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mint32)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }

          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
          (* { *)
          (*   hexploit BDD; try right; eauto. *)
          (*   { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. } *)
          (*   i; des. *)
          (*   exploit ACC; try right; eauto. i; ss; des. *)
          (*   generalize (typesize_pos ty); i. *)
          (*   split; try xomega. *)
          (* } *)

          eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mint32)); eauto.
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
        * econs; eauto. econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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

          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }

          econs; eauto; cycle 1.

          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat64)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
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
        * econs; eauto. econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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
          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          econs; eauto; cycle 1.
          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mint64)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
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
        * econs; eauto. econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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
          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }

          econs; eauto; cycle 1.
          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat32)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
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
        * econs; eauto. econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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
          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          econs; eauto; cycle 1.
          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many32)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
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
        * econs; eauto.
          econs; eauto; cycle 1.
          { i. clarify. eapply store_undef_memval_undefs; eauto.
            rewrite Ptrofs.unsigned_zero.
            { hexploit BDD; eauto. i; des. ss.
              exploit ACC; eauto. i; ss; des.
              split; try xomega. }
          }
          cbn. ss.
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
          assert (RANGE: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
          {
            hexploit BDD; try right; eauto.
            { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
            i; des.
            exploit ACC; try right; eauto. i; ss; des.
            generalize (typesize_pos ty); i.
            split; try xomega.
          }
          econs; eauto; cycle 1.
          { i. eapply memval_undefs_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many64)); cycle 1; eauto; clarify.
            - rewrite Ptrofs.unsigned_zero in *. ss.
              { locmap_tac.
                exploit Loc.in_notin_diff; eauto.
                { eapply in_regs_of_rpairs; eauto. ss. eauto. }
                intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
                u; ii. des; try xomega.
              }
            - rewrite Ptrofs.unsigned_zero. ss.
              eapply Mem.load_valid_access in H3.
              inv H3. ss.
              rewrite Ptrofs.add_zero_l in *.
              erewrite Ptrofs.unsigned_repr in *; ss.
            - eapply Mem.store_unchanged_on; eauto.
          }
          ss. cbn in *.
          rewrite Ptrofs.add_zero_l in *.
          rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
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
          sg m0 rs0 m1 sp targs
          (* (LEN: length args = length sg.(sig_args)) *)
          (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, sp))
          rs1 m2
          (TYP: Val.has_type_list targs sg.(sig_args))
          (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
          (* (LEN: length args = length sg.(sig_args)) *)
          (* (TYPIFY: typify_list args sg.(sig_args) = targs) *)
          (* (MAX: 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
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
    assert(LEN2: length targs = length (sig_args sg)).
    { clear - TYP. revert TYP. generalize (sig_args sg).
      induction targs; ss; i; des_ifs; ss.
      f_equal. eapply IHtargs. des. auto. }
    econs; eauto.
    - rr.
      eapply fill_arguments_spec_aux; ss; eauto.
      + ii. eapply loc_arguments_acceptable; eauto. unfold loc_arguments. des_ifs. eauto.
      + i. eapply loc_arguments_bounded; eauto.
    - eapply Mem.unchanged_on_implies.
      { eapply fill_arguments_unchanged_on; try apply FILL; eauto. }
      i. des_ifs.
    - generalize (loc_arguments_64 (sig_args sg) 0 0 0) m1 m2 rs0 rs1 FILL. clear.
      induction targs; i; ss; unfold o_bind2, o_bind, o_join, o_map, curry2 in *; des_ifs.
      + destruct p. exploit IHtargs; eauto.
      + destruct p. ss.
        exploit IHtargs; eauto. i. etrans; eauto.
        symmetry. eapply Mem.nextblock_store; eauto.
    - ii. eapply fill_arguments_perm; eauto. eauto with mem.
  Qed.

  Theorem fill_arguments_unchanged
          m1 rs0 sp targs locs
          rs1 m2
          (FILL: fill_arguments sp rs0 m1 targs locs = Some (rs1, m2))
    :
      <<PTRFREE: forall
        mr
        (NIN: ~ In (R mr) (regs_of_rpairs locs)),
        rs0 mr = rs1 mr>>.
  Proof.
    ginduction locs; ii; s.
    - destruct targs; ss; clarify.
    - destruct targs; ss; clarify.
      unfold o_bind, o_bind2, o_join, o_map, curry2, fst in *. ss.
      des_ifs; ss.
      + exploit IHlocs; try apply Heq0; ss; eauto.
        i.
        unfold Regmap.set; des_ifs.
        exfalso; eauto.
      + exploit IHlocs; try apply Heq0; ss; eauto.
  Qed.

End FillArgsProgress.


Require Import JunkBlock.

Theorem store_arguments_progress
        m0 tvs sg
        (TYP: Val.has_type_list tvs sg.(sig_args))
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
        n
  :
    exists rs m2,
      (<<STR: store_arguments m0 rs tvs sg m2>>) /\
      (<<PTRFREE:
         forall
           mr
           (NIN: ~ In (R mr) (regs_of_rpairs (loc_arguments sg))),
           is_junk_value m2 (assign_junk_blocks m2 n) (rs mr)>>)
.
Proof.
  destruct (Mem.alloc m0 0 (4 * size_arguments sg)) eqn:ALC.
  rename m into m1. rename b into blk.
  assert(LEN2: length tvs = length (sig_args sg)).
  { clear - TYP. revert TYP. generalize (sig_args sg).
    induction tvs; ss; i; des_ifs; ss.
    f_equal. eapply IHtvs. des. auto. }
  exploit (FillArgsProgress.fill_arguments_progress sg m0 (Regmap.init Vundef)); eauto. i; des.
  hexploit (FillArgsProgress.fill_arguments_unchanged); eauto. i.
  exploit (FillArgsProgress.fill_arguments_spec sg m0 (Regmap.init Vundef) m1 blk tvs); eauto.
  hexploit (FillArgsProgress.fill_arguments_unchanged); eauto. intros UNCH.
  esplits; eauto.
  ii. exploit UNCH; eauto. i. rewrite <- H1. ss.
Qed.
