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
Require Import Asm Mach mktac MemdataC AsmregsC StoreArguments.


Definition agree (j: meminj) (rs0 rs1: Mach.regset) : Prop :=
  forall mr, Val.inject j (rs0 mr) (rs1 mr).

Lemma typesize_chunk: forall ty,
    size_chunk (chunk_of_type ty) = 4 * (typesize ty).
Proof. destruct ty; ss. Qed.

Section STOREARGUMENTS_PROPERTY.

  Lemma extcall_arguments_same (rs0 rs1: Mach.regset) sp m sg args
        (ARGS: extcall_arguments rs0 m sp sg args)
        (SAME: forall r (IN: In (R r) (regs_of_rpairs (loc_arguments sg))), rs0 r = rs1 r):
      extcall_arguments rs1 m sp sg args.
  Proof.
    clear - ARGS SAME. unfold extcall_arguments in *.
    revert args ARGS SAME. generalize (loc_arguments sg). induction l; ss; i; inv ARGS; econs; eauto.
    - inv H1.
      + econs 1. inv H; eauto; try econs; eauto. erewrite SAME; econs; eauto.
      + inv H; inv H0;  econs; eauto; try erewrite SAME; eauto; (try by econs; eauto); ss; eauto.
    - eapply IHl; eauto. ii. eapply SAME. eapply in_app; eauto.
  Qed.

  Definition extcall_arg_in_reg (rs: regset) (l: rpair loc) (v: val) : Prop :=
    forall r (EQ: l = One (R r)), v = rs r.

  Definition extcall_arg_in_stack (m: ZMap.t memval) (lo: Z) (l: rpair loc) (v: val) : Prop :=
    forall ofs ty (EQ: l = One (S Outgoing ofs ty)),
      decode_val (chunk_of_type ty) (Mem.getN (size_chunk_nat (chunk_of_type ty)) (lo + 4 * ofs) m) = v.

  Lemma extcall_arguments_extcall_arg_in_reg
        rs m blk sg vs lo
        (SZ: 0 <= lo /\ lo + 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (ARGS: list_forall2
                 (extcall_arg_pair rs m (Vptr blk (Ptrofs.repr lo)))
                 (loc_arguments sg) vs):
      list_forall2 (extcall_arg_in_reg rs) (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg). generalize (@loc_arguments_ofs_bounded sg lo SZ).
    revert vs ARGS. induction (loc_arguments sg); ss; i; inv ARGS; econs.
    - ii. clarify. inv H3. inv H2. auto.
    - eapply IHl; eauto.
  Qed.

  Lemma extcall_arguments_extcall_arg_in_stack
        rs m blk sg vs lo
        (SZ: 0 <= lo /\ lo + 4 * size_arguments sg <= Ptrofs.max_unsigned)
        (ARGS: list_forall2
                 (extcall_arg_pair rs m (Vptr blk (Ptrofs.repr lo)))
                 (loc_arguments sg) vs):
      list_forall2
        (extcall_arg_in_stack (m.(Mem.mem_contents) !! blk) lo)
        (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg). generalize (@loc_arguments_ofs_bounded sg lo SZ).
    revert vs ARGS. induction (loc_arguments sg); ss; i; inv ARGS; econs.
    - ii. clarify. inv H3. inv H2. unfold load_stack in *. ss.
      Local Transparent Mem.load. unfold Mem.load in *. des_ifs.
      ss. rewrite Ptrofs.Ptrofs_add_repr. rewrite Ptrofs.unsigned_repr; eauto.
    - eapply IHl; eauto.
  Qed.

  Lemma extcall_arg_in_stack_in_reg_extcall_argument
        m blk m_blk rs vs sg
        (STACK: list_forall2
                  (extcall_arg_in_stack m_blk 0)
                  (loc_arguments sg) vs)
        (REGS: list_forall2
                 (extcall_arg_in_reg rs)
                 (loc_arguments sg) vs)
        (MBLK: m.(Mem.mem_contents) !! blk = m_blk)
        (PERM: Mem.range_perm m blk 0 (4 * size_arguments sg) Cur Freeable)
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned):
      list_forall2
        (extcall_arg_pair rs m (Vptr blk Ptrofs.zero)) (loc_arguments sg) vs.
  Proof.
    generalize (loc_arguments_acceptable sg).
    assert (SZ0: 0 <= 0 /\ 0 + 4 * size_arguments sg <= Ptrofs.max_unsigned) by lia.
    generalize (@loc_arguments_ofs_bounded sg 0 SZ0).
    assert (RANGE: forall ofs ty (In: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
               Mem.range_perm m blk (4 * ofs) (4 * (ofs + typesize ty)) Cur Freeable).
    { i. hexploit loc_arguments_bounded; eauto. ii. eapply PERM. split; try lia.
      hexploit loc_arguments_acceptable; eauto; cycle 1.
      - instantiate (1:= One (S Outgoing ofs ty)). i. inv H1. lia.
      - instantiate (1:= sg). generalize (loc_arguments_one sg).
        revert In. clear. induction (loc_arguments sg); ss.
        i. dup H. specialize (H _ (or_introl eq_refl)). unfold is_one in *. des_ifs. ss. des; clarify; eauto.
    }
    generalize (loc_arguments_one sg). revert vs STACK REGS RANGE.
    induction (loc_arguments sg); ss; i.
    - inv STACK. econs.
    - inv STACK. inv REGS. econs.
      + destruct a; cycle 1.
        { exfalso. hexploit H; eauto. }
        destruct r.
        * econs. exploit H7; eauto. i. clarify. econs.
        * destruct sl; try (by exfalso; exploit H1; eauto).
          econs. exploit H4; eauto. i. des. econs.
          { unfold load_stack, Mem.loadv in *. ss. unfold Mem.load. des_ifs.
            - rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr; eauto.
            - exfalso. apply n. unfold Mem.valid_access. split; ii.
              + eapply Mem.perm_implies; eauto.
                * eapply RANGE; eauto. rewrite Ptrofs.add_zero_l in *.
                  rewrite Ptrofs.unsigned_repr in *; try exploit H0; eauto. split; destruct ty; ss; try lia.
                * econs.
              + rewrite Ptrofs.add_zero_l in *. rewrite Ptrofs.unsigned_repr in *; try (by exploit H0; eauto).
                exploit H1; eauto. i. inv H2. destruct ty; ss; eapply Z.mul_divide_mono_l with (p := 4) in H5; eauto. }
      + eapply IHl; eauto. ii. eapply RANGE; eauto. eapply in_or_app; eauto.
  Qed.

  Lemma store_arguments_unchanged_on m0 m1 rs args sg
        (STORE: store_arguments m0 rs args sg m1):
      Mem.unchanged_on top2 m0 m1.
  Proof.
    inv STORE. dup ALC. eapply Mem.alloc_unchanged_on in ALC0.
    eapply Mem.unchanged_on_implies; eauto.
    - eapply Mem.unchanged_on_trans; eauto.
    - i. ss. des_ifs. exfalso. eapply Mem.fresh_block_alloc; eauto.
  Qed.

End STOREARGUMENTS_PROPERTY.



Module _FillArgsParallel.

  (* it's from AsmStepInj *)
  Lemma unsigned_add ofs delta
        (RANGE: delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned):
      Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))
      = Ptrofs.unsigned ofs + delta.
  Proof.
    rewrite Ptrofs.add_unsigned. replace (Ptrofs.unsigned (Ptrofs.repr delta)) with delta.
    * eapply Ptrofs.unsigned_repr; eauto. des. splits; eauto.
    * symmetry. eapply Ptrofs.unsigned_repr; eauto. des. splits; [extlia|].
      assert (Ptrofs.unsigned ofs >= 0); [|extlia].
      set (Ptrofs.unsigned_range ofs). des. extlia.
  Qed.

  Definition copy_memval (v: val) (mv: memval) : memval :=
    match v, mv with
    | Vundef, _ => Undef
    | _, Fragment _ q n => Fragment v q n
    | _, _ => mv
    end.

  Definition copy_list_memval (v: val): list memval -> list memval := map (copy_memval v).

  Lemma copy_list_memval_decode_undef vl vl'
        (COPY: copy_list_memval Vundef vl = vl'):
      vl' = repeat Undef (List.length vl).
  Proof.
    revert vl' COPY. induction vl; ss; i; clarify. f_equal. eapply IHvl; eauto.
  Qed.

  Lemma copy_list_memval_decode_pointer j vl vl' chunk v blk ofs
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
        (VALUE: v = Vptr blk ofs):
      decode_val chunk vl' = v.
  Proof.
    assert(H: DUMMY_PROP) by ss. clarify. inv INJ; ss.
    - unfold decode_val in H2. destruct vl; ss.
      + des_ifs.
      + des_ifs_safe.
        destruct m, chunk; ss; des_ifs_safe; cycle 10.
        { repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. }
        { destruct v; ss. }
        { repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify).
          unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. }
        all: des_ifs.
  Qed.

  Lemma copy_list_memval_decode j vl vl' chunk v
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
        (LENGTH: Nat.lt 0 (length vl)):
      decode_val chunk vl' = v.
  Proof.
    inv INJ; try (by rewrite H1; f_equal; apply eq_Forall2_eq; eapply Forall2_in_map;
      i; rewrite <- H1; destruct a; ss; f_equal; symmetry; eapply decode_fragment_all; eauto; ii; clarify).
    - eapply copy_list_memval_decode_pointer; eauto. rewrite <- H. econs; eauto.
    - exploit copy_list_memval_decode_undef. eauto. i. rewrite H. destruct vl; ss.
      + inv LENGTH.
      + unfold decode_val. des_ifs.
  Qed.

  Lemma copy_list_memval_inject j vl vl' chunk v
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl'):
      list_forall2 (memval_inject j) vl' vl.
  Proof.
    clarify. destruct v.
    { exploit copy_list_memval_decode_undef; eauto. i. rewrite H. eapply repeat_Undef_inject_any. }
    all: eapply Forall2_in_map; i; destruct a; ss; try econs;
      erewrite decode_fragment_all; eauto; ii; rewrite H in *; inv INJ.
  Qed.

  Definition fill_arg_src_reg (rs: regset) (arg: val) (loc: rpair loc): regset :=
    match loc with
    | One (R r) => rs#r <- arg
    | _ => rs
    end.

  Fixpoint fill_args_src_reg (args: list val) (locs: list (rpair loc)): regset :=
    match args, locs with
    | vhd::vtl, lhd::ltl => fill_arg_src_reg (fill_args_src_reg vtl ltl) vhd lhd
    | _, _ => fun _ => Vundef
    end.

  Lemma fill_args_src_reg_args args locs
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (ONES: forall l (IN: In l locs), is_one l)
        (LENGTH: length args = length locs):
      list_forall2 (extcall_arg_in_reg (fill_args_src_reg args locs)) locs args.
  Proof.
    revert NOREPEAT args LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv LENGTH. destruct a; inv NOREPEAT.
      + exploit IHlocs; eauto. i. unfold fill_arg_src_reg. des_ifs.
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
        (ARGS: list_forall2 (extcall_arg_in_reg rs_tgt) locs args_tgt):
      agree j (fill_args_src_reg args locs) rs_tgt.
  Proof.
    generalize dependent args. revert rs_tgt args_tgt ARGS. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss.
    - destruct args; ss. inv INJECT. inv LENGTH. inv ARGS.
      unfold fill_arg_src_reg. des_ifs; try eapply IHlocs; eauto.
      ii. unfold Regmap.set. des_ifs.
      + exploit H5; eauto. i. clarify.
      + eapply IHlocs; eauto.
  Qed.

  Definition fill_arg_src_blk (m_tgt m: ZMap.t memval) (lo_tgt lo: Z)
             (arg: val) (loc: rpair loc): ZMap.t memval :=
    match loc with
    | One (S Outgoing ofs ty) =>
      Mem.setN (copy_list_memval arg (Mem.getN (size_chunk_nat (chunk_of_type ty)) (lo_tgt + 4 * ofs) m_tgt)) (lo + 4 * ofs) m
    | _ => m
    end.

  Fixpoint fill_args_src_blk (m_tgt m: ZMap.t memval) (lo_tgt lo: Z)
           (args: list val) (locs: list (rpair loc)): ZMap.t memval :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_src_blk m_tgt (fill_args_src_blk m_tgt m lo_tgt lo vtl ltl) lo_tgt lo vhd lhd
    | _, _ => m
    end.

  Definition only_args_blk (m: ZMap.t memval) (locs: list loc) :=
    forall ofs,
      (<<UNDEF: ZMap.get ofs m = Undef >>) \/
      (<<INARGS: exists ofs0 ty v,
          (<<IN: In (S Outgoing ofs0 ty) locs>>) /\
          (<<RANGE: 4 * ofs0 <= ofs < 4 * ofs0 + size_chunk (chunk_of_type ty)>>) /\
          (<<LOAD:
             decode_val (chunk_of_type ty) (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * ofs0) m) = v>>) /\
          (<<VDEF: v <> Vundef>>)>>).

  Lemma only_args_blk_incr
        m a l
        (ONLY: only_args_blk m l):
      only_args_blk m (a::l).
  Proof.
    ii. specialize (ONLY ofs). des; auto. right. esplits; eauto. ss. auto.
  Qed.

  Lemma fill_args_src_blk_only_args m_tgt j args_tgt args locs lo_tgt
        (INJECT: Val.inject_list j args args_tgt)
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (LENGTH: length args = length locs)
        (ONES: forall l (IN: In l locs), is_one l)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt lo_tgt) locs args_tgt):
      only_args_blk
        (fill_args_src_blk m_tgt (ZMap.init Undef) lo_tgt 0 args locs) (regs_of_rpairs locs).
  Proof.
    generalize dependent args. revert m_tgt args_tgt ARGS NOREPEAT ONES. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss. ii. rewrite ZMap.gi. left. econs.
    - destruct args; ss. inv INJECT. inv LENGTH. inv ARGS.
      hexploit IHlocs; eauto.
      { ii. eapply loc_norepet_app; eauto. } intros ONLY.
      unfold fill_arg_src_blk. des_ifs; try (by eapply only_args_blk_incr; auto).
      + ss. ii.
        destruct (classic (4 * pos <= ofs < 4 * pos + Z.of_nat (size_chunk_nat (chunk_of_type ty)))).
        * assert (LEQ: size_chunk_nat (chunk_of_type ty) =
                       Datatypes.length (copy_list_memval v (Mem.getN (size_chunk_nat (chunk_of_type ty)) (lo_tgt + 4 * pos) m_tgt))).
          { unfold copy_list_memval. rewrite map_length.
            erewrite Mem.getN_length. auto. } exploit Mem.getN_in; eauto.
          rewrite LEQ at 1. rewrite Mem.getN_setN_same.
          instantiate (1:=fill_args_src_blk m_tgt (ZMap.init Undef) lo_tgt 0 args locs). i.
          destruct (classic (v = Vundef)).
          { clarify. unfold copy_list_memval, copy_memval in *.
            eapply list_in_map_inv in H2. des. ss. rewrite H2. left. econs. }
          { right. des. esplits; ss; eauto.
            - rewrite size_chunk_conv in *. auto.
            - erewrite copy_list_memval_decode; try eassumption.
              + exploit H5; eauto. i. rewrite H8. eauto.
              + rewrite LEQ at 2. symmetry. eapply Mem.getN_setN_same.
              + rewrite Mem.getN_length.
                exploit size_chunk_nat_pos. intros SZ. des. rewrite SZ. compute. omega. }
        * specialize (ONLY ofs). des.
          { left. erewrite Mem.setN_other; eauto. unfold copy_list_memval. erewrite map_length.
            erewrite Mem.getN_length. ii. clarify. }
          { right. esplits; ss; eauto. erewrite Mem.getN_setN_outside; eauto.
            - ii. clarify.
            - unfold copy_list_memval. erewrite map_length. erewrite Mem.getN_length.
              repeat rewrite <- size_chunk_conv in *. repeat rewrite typesize_chunk in *.
              set (typesize_pos ty0). set (typesize_pos ty).
              inv NOREPEAT. exploit Loc.in_notin_diff; eauto. i. ss. des; clarify; lia. }
      + ss. exploit ONES; eauto. i. clarify.
  Qed.

  Lemma fill_args_src_blk_inject m_tgt j args_tgt args locs lo_tgt lo
        (INJECT: Val.inject_list j args args_tgt)
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt lo_tgt) locs args_tgt):
      forall ofs, memval_inject
                    j
                    (ZMap.get (lo + ofs) (fill_args_src_blk m_tgt (ZMap.init Undef) lo_tgt lo args locs))
                    (ZMap.get (lo_tgt + ofs) m_tgt).
  Proof.
    generalize dependent args. revert m_tgt args_tgt ARGS. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss. rewrite ZMap.gi. econs.
    - destruct args; ss. inv INJECT. inv LENGTH. inv ARGS. unfold fill_arg_src_blk. des_ifs; try eapply IHlocs; eauto.
      + exploit IHlocs; eauto. instantiate (1:=ofs). intros INJ.
        { exploit Mem.setN_inj.
          - instantiate (3:=j).
            instantiate (2:=copy_list_memval v (Mem.getN (size_chunk_nat (chunk_of_type ty)) (lo_tgt + 4 * pos) m_tgt)).
            instantiate (1:=Mem.getN (size_chunk_nat (chunk_of_type ty)) (lo_tgt + 4 * pos) m_tgt).
            specialize (H5 pos ty eq_refl). des. clarify.
            { eapply copy_list_memval_inject; eauto. }
          - instantiate (4:=top1).
            instantiate (3:=fill_args_src_blk m_tgt (ZMap.init Undef) lo_tgt lo args locs).
            instantiate (1:=m_tgt).
            instantiate (1:=lo_tgt - lo).
            i. exploit IHlocs; eauto. instantiate (1:=q - lo). i.
            rpapply H2; f_equal; lia.
          - econs.
          - instantiate (2:= lo + ofs). instantiate (1:=lo + 4 * pos).
            repeat rewrite Z.add_0_r.
            i. rpapply H.
            { replace (lo + ofs + (lo_tgt - lo)) with (lo_tgt + ofs); try lia.
              replace (lo + 4 * pos + (lo_tgt - lo)) with (lo_tgt + 4 * pos); try lia.
              generalize ofs. clear - m_tgt. generalize (4 * pos). revert m_tgt. generalize (size_chunk_nat (chunk_of_type ty)).
              induction n; ss; i. repeat rewrite <- Z.add_assoc.
              replace (Mem.getN n (lo_tgt + (z + 1)) m_tgt) with
                  (Mem.getN n (lo_tgt + (z + 1)) (ZMap.set (lo_tgt + z) (ZMap.get (lo_tgt + z) m_tgt) m_tgt)).
              - rewrite <- IHn. rewrite ZMap.gsspec. des_ifs. rewrite e. auto.
              - clear IHn. generalize z m_tgt (z+1). induction n; ss; i. f_equal.
                + rewrite ZMap.gsspec. des_ifs. rewrite e. auto.
                + repeat rewrite <- Z.add_assoc. rewrite IHn. eauto. }
        }
  Qed.

  Lemma fill_args_src_blk_args m_tgt m j args_tgt args locs lo_tgt lo
        (INJECT: Val.inject_list j args args_tgt)
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt lo_tgt) locs args_tgt):
      list_forall2 (extcall_arg_in_stack (fill_args_src_blk m_tgt m lo_tgt lo args locs) lo) locs args.
  Proof.
    revert NOREPEAT args_tgt args ARGS INJECT LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv LENGTH. inv ARGS. inv INJECT.
      exploit IHlocs; eauto.
      { ii. eapply loc_norepet_app; eauto. }
      unfold fill_arg_src_blk. des_ifs; try (by econs; eauto; ii; inv EQ).
      + econs; eauto.
        { ii. inv EQ. specialize (H2 ofs ty0 eq_refl). des. clarify.
          assert (LEQ: size_chunk_nat (chunk_of_type ty0) =
                       Datatypes.length (copy_list_memval v (Mem.getN (size_chunk_nat (chunk_of_type ty0)) (lo_tgt + 4 * ofs) m_tgt))).
          { unfold copy_list_memval. rewrite list_length_map.
            rewrite Mem.getN_length. auto. }
          pattern (size_chunk_nat (chunk_of_type ty0)) at 1. rewrite LEQ. erewrite Mem.getN_setN_same.
          exploit copy_list_memval_decode; eauto.
          rewrite Mem.getN_length. destruct ty0; compute; lia.
        }
        { eapply list_forall2_lift; [| eauto].
          ii. clarify. specialize (H1 ofs ty0 eq_refl). des. clarify.
          erewrite Mem.getN_setN_outside; eauto. ss. inv NOREPEAT.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_one_in_rpair; eauto. } intros DIFF. ss.
          unfold copy_list_memval in *. erewrite map_length. rewrite Mem.getN_length.
          repeat rewrite <- size_chunk_conv. repeat rewrite typesize_chunk. des; clarify; lia.
        }
  Qed.

  Lemma fill_args_src_blk_default m_tgt m args locs lo_tgt lo :
      fst (fill_args_src_blk m_tgt m lo_tgt lo args locs) = fst m.
  Proof.
    revert m locs. induction args; ss; i. unfold fill_arg_src_blk. des_ifs; ss.
    rewrite Mem.setN_default. ss.
  Qed.

  Program Definition fill_args_src_mem (m_tgt0 m_tgt1 : mem) (m_src0: mem)
          (args: list val) (locs: list (rpair loc)) : mem :=
    Mem.mkmem
      (PMap.set
         (m_src0.(Mem.nextblock))
         (fill_args_src_blk
            (m_tgt1.(Mem.mem_contents) !! (m_tgt0.(Mem.nextblock)))
            (ZMap.init Undef) 0 0 args locs)
         (m_src0.(Mem.mem_contents)))
      (PMap.set
         (m_src0.(Mem.nextblock))
         (m_tgt1.(Mem.mem_access) !! (m_tgt0.(Mem.nextblock)))
         (m_src0.(Mem.mem_access)))
      (Pos.succ m_src0.(Mem.nextblock))
      _ _ _.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs; eapply Mem.access_max.
  Qed.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - exfalso. eapply H. eapply Plt_succ.
    - eapply Mem.nextblock_noaccess. ii. eapply H. etrans; eauto. eapply Plt_succ.
  Qed.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - rewrite fill_args_src_blk_default. eauto.
    - eapply Mem.contents_default.
  Qed.

  Definition encode_val' (chunk: memory_chunk) (v: val) : list memval :=
    if Val.eq v Vundef then repeat Undef (size_chunk_nat chunk)
    else encode_val chunk v.

  Lemma encode_val_length' chunk v:
      Datatypes.length (encode_val' chunk v) = size_chunk_nat chunk.
  Proof.
    unfold encode_val'. des_ifs.
    - eapply repeat_length.
    - eapply encode_val_length.
  Qed.

  Lemma decode_encode_val' ty v
        (TYP: Val.has_type v ty):
      decode_val (chunk_of_type ty) (encode_val' (chunk_of_type ty) v) = v.
  Proof.
    unfold encode_val'. des_ifs.
    { set (size_chunk_nat_pos (chunk_of_type ty)). des. rewrite e. ss.
      eapply decode_val_undef. }
    hexploit (decode_encode_val_general v (chunk_of_type ty) (chunk_of_type ty)). i.
    hexploit decode_encode_val_similar; eauto. i.
    rewrite H0 in *.
    hexploit Val.load_result_same; eauto.
  Qed.

  Definition fill_arg_blk (m: ZMap.t memval) (lo: Z)
             (arg: val) (loc: rpair loc): ZMap.t memval :=
    match loc with
    | One (S Outgoing ofs ty) => Mem.setN (encode_val' (chunk_of_type ty) arg) (lo + 4 * ofs) m
    | _ => m
    end.

  Fixpoint fill_args_blk (m: ZMap.t memval) (lo: Z)
           (args: list val) (locs: list (rpair loc)): ZMap.t memval :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_blk (fill_args_blk m lo vtl ltl) lo vhd lhd
    | _, _ => m
    end.

  Definition has_typed_loc (l: rpair loc) (v: val) :Prop :=
    match l with
    | One (S _ _ ty) => Val.has_type v ty
    | _ => True
    end.

  Lemma fill_args_blk_args m args locs lo
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (ONES: forall l (IN: In l locs), is_one l)
        (LENGTH: length args = length locs)
        (TYP: list_forall2 has_typed_loc locs args):
      list_forall2 (extcall_arg_in_stack (fill_args_blk m lo args locs) lo) locs args.
  Proof.
    revert NOREPEAT args ONES LENGTH TYP. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv LENGTH. inv TYP.
      exploit IHlocs; eauto.
      { ii. eapply loc_norepet_app; eauto. }
      unfold fill_arg_blk. des_ifs; try (by econs; eauto; ii; inv EQ).
      + i. econs; eauto.
        { ii. clarify.
          assert (LEQ: size_chunk_nat (chunk_of_type ty0) =
                       Datatypes.length (encode_val' (chunk_of_type ty0) v)).
          { rewrite encode_val_length'. auto. }
          rewrite LEQ at 1.
          erewrite Mem.getN_setN_same.
          eapply decode_encode_val'; eauto. }
        { eapply list_forall2_lift; [| eauto]. ii. clarify. specialize (H1 ofs ty0 eq_refl). des. clarify.
          erewrite Mem.getN_setN_outside; eauto. ss. inv NOREPEAT.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_one_in_rpair; eauto. } intros DIFF. ss.
          rewrite encode_val_length'. repeat rewrite <- size_chunk_conv. repeat rewrite typesize_chunk. des; clarify; lia.
        }
  Qed.

  Lemma fill_args_blk_only_args args locs
        (NOREPEAT: Loc.norepet (regs_of_rpairs locs))
        (LENGTH: length args = length locs)
        (ONES: forall l (IN: In l locs), is_one l)
        (TYP: list_forall2 has_typed_loc locs args):
      only_args_blk
        (fill_args_blk (ZMap.init Undef) 0 args locs) (regs_of_rpairs locs).
  Proof.
    generalize dependent args.
    revert NOREPEAT ONES. induction locs; ss; eauto; i.
    - inv LENGTH. destruct args; ss. ii. rewrite ZMap.gi. left. econs.
    - destruct args; ss. inv TYP. inv LENGTH.
      hexploit IHlocs; eauto.
      { ii. eapply loc_norepet_app; eauto. } intros ONLY.
      unfold fill_arg_blk. des_ifs; try (by eapply only_args_blk_incr; auto).
      + ss. ii. destruct (classic (4 * pos <= ofs < 4 * pos + Z.of_nat (size_chunk_nat (chunk_of_type ty)))).
        * assert (LEQ: size_chunk_nat (chunk_of_type ty) =
                       Datatypes.length (encode_val' (chunk_of_type ty) v)).
          { symmetry. eapply encode_val_length'. } exploit Mem.getN_in; eauto.
          rewrite LEQ at 1. rewrite Mem.getN_setN_same.
          instantiate (1:=fill_args_blk (ZMap.init Undef) 0 args locs). i.
          destruct (classic (v = Vundef)).
          { clarify. unfold encode_val' in *. des_ifs. eapply repeat_spec in H1. rewrite H1. left. econs. }
          { right. des. esplits; eauto.
            - ss. eauto.
            - rewrite size_chunk_conv in *. auto.
            - rewrite LEQ at 1. erewrite Mem.getN_setN_same. rewrite decode_encode_val'; eauto. }
        * specialize (ONLY ofs). des.
          { left. erewrite Mem.setN_other; eauto. rewrite encode_val_length'. ii. clarify. }
          { right. esplits; ss; eauto. erewrite Mem.getN_setN_outside; eauto.
            - ii. clarify.
            - rewrite encode_val_length'.
              repeat rewrite <- size_chunk_conv in *. repeat rewrite typesize_chunk in *.
              set (typesize_pos ty0). set (typesize_pos ty).
              inv NOREPEAT. exploit Loc.in_notin_diff; eauto. i. ss. des; clarify; lia. }
      + ss. exploit ONES; eauto. i. clarify.
  Qed.

  Lemma fill_args_blk_default m args locs lo:
      fst (fill_args_blk m lo args locs) = fst m.
  Proof.
    revert m locs. induction args; ss; i. unfold fill_arg_blk. des_ifs; ss.
    rewrite Mem.setN_default. ss.
  Qed.

  Program Definition fill_args_mem (m_src0: mem) (blk: block)
          (args: list val) (locs: list (rpair loc)) : mem :=
    Mem.mkmem
      (PMap.set
         blk
         (fill_args_blk (ZMap.init Undef) 0 args locs)
         (m_src0.(Mem.mem_contents)))
      (m_src0.(Mem.mem_access))
      (m_src0.(Mem.nextblock))
      _ _ _.
  Next Obligation.
  Proof. eapply Mem.access_max. Qed.
  Next Obligation.
  Proof. eapply Mem.nextblock_noaccess; auto. Qed.
  Next Obligation.
  Proof.
    rewrite PMap.gsspec. des_ifs.
    - rewrite fill_args_blk_default. eauto.
    - eapply Mem.contents_default.
  Qed.

End _FillArgsParallel.


Section STOREARGPRARALLEL.

  Theorem store_arguments_parallel_inject
          j m_src0 m_tgt0 m_tgt1 rs_tgt vs vs' sg
          (TYP: Val.has_type_list vs' sg.(sig_args))
          (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
          (* (TYP: typechecked_args sg vs) *)
          (* (TYP: typechecked_args sg vs') *)
          (VALINJ: Val.inject_list j vs vs')
          (INJ: Mem.inject j m_src0 m_tgt0)
          (ARGSRC: store_arguments m_tgt0 rs_tgt vs' sg m_tgt1):
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
      - instantiate (1:=(Mem.nextblock m_src0)). unfold Mem.valid_block. eapply Plt_strict.
      - ii. clarify. }

    splits.
    - econs; ss; eauto.
      + unfold extcall_arguments in *.
        assert (LENGTH: Datatypes.length vs = Datatypes.length (loc_arguments sg)).
        { erewrite inject_list_length; eauto. symmetry. eapply list_forall2_length; eauto. }
        exploit _FillArgsParallel.fill_args_src_reg_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply loc_arguments_one. }
        exploit _FillArgsParallel.fill_args_src_blk_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. lia. }
        instantiate (1:= 0). instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold _FillArgsParallel.fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss. exploit PERM; eauto.
      + ii. exploit _FillArgsParallel.fill_args_src_blk_only_args; eauto.
        * eapply loc_arguments_norepet.
        * erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
        * eapply loc_arguments_one.
        * eapply extcall_arguments_extcall_arg_in_stack; eauto. lia.
        * i. instantiate (1:=ofs) in H.
          unfold _FillArgsParallel.fill_args_src_mem. ss.
          Local Transparent Mem.load. unfold Mem.load. s.
          repeat rewrite PMap.gss. des; eauto. right.
          exploit loc_arguments_acceptable_2; eauto. i. inv H.
          hexploit loc_arguments_bounded; eauto. i.
          esplits; eauto. rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; cycle 1.
          { hexploit loc_arguments_bounded; eauto. i. set (typesize_pos ty). lia. }
          des_ifs. exfalso. apply n. unfold Mem.valid_access. split.
          { ii. unfold Mem.perm. ss. rewrite PMap.gss.
            eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply PERM.
            - erewrite typesize_chunk in *. set (typesize_pos ty). lia.
            - econs. }
          { clear - H1. destruct ty; ss; try apply Z.divide_factor_l.
            eapply Z.mul_divide_mono_l in H1. instantiate (1:=4) in H1. ss. }

      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0.
        econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          - split; i; exfalso.
            + eapply Mem.perm_alloc_3 in H1; eauto.
            + unfold _FillArgsParallel.fill_args_src_mem, Mem.perm in *. ss.
              rewrite PMap.gss in H1; eauto. eapply Mem.perm_unchanged_on_2 in H1; eauto.
              * eapply Mem.perm_alloc_3 in H1; eauto.
              * ss. des_ifs.
              * eapply Mem.valid_new_block; eauto.
          - transitivity (Mem.perm m_src0 b ofs k p).
            + symmetry. apply unchanged_on_perm; eauto.
              unfold Mem.valid_block in *. erewrite Mem.nextblock_alloc in H0; eauto.
              eapply Plt_succ_inv in H0. des; clarify.
            + unfold Mem.perm; ss; eauto.
              rewrite PMap.gso; eauto. }
        { i. des_ifs.
          - rewrite PMap.gss. exfalso. exploit Mem.perm_alloc_3; try apply ALLOC; eauto.
          - rewrite PMap.gso; eauto. symmetry. apply unchanged_on_contents; eauto.
            eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss. eapply PERM; eauto.
    - inv INJ. inv mi_inj. unfold _FillArgsParallel.fill_args_src_mem, update_meminj in *.
      econs; ss; i.
      { econs; ss; i.
        - des_ifs.
          + unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. zsimpl. eauto.
          + inv UNCH. eapply unchanged_on_perm.
            * des_ifs. exploit mi_mappedblocks; eauto.
              ii. unfold Mem.valid_block in *. ss. eapply Plt_strict; eauto.
            * exploit mi_mappedblocks; eauto. i. eapply Mem.valid_block_alloc; eauto.
            * eapply Mem.perm_alloc_1; eauto. unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
        - des_ifs.
          + eapply Z.divide_0_r.
          + eapply mi_align; eauto. ii. unfold Mem.range_perm, Mem.perm in *; ss.
            rewrite PMap.gsspec in *. des_ifs; ss. eapply H0; eauto.
        - eapply memval_inject_incr; eauto.
          rewrite PMap.gsspec in *. des_ifs; ss.
          + hexploit _FillArgsParallel.fill_args_src_blk_inject; eauto.
            * erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
            * eapply extcall_arguments_extcall_arg_in_stack; eauto. lia.
            * instantiate (1:= ofs). rewrite Z.add_0_r. intros VINJ. erewrite Z.add_0_l in *. auto.
          + dup ALC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALC0. inv ALC0.
            exploit mi_memval; eauto.
            * unfold Mem.perm in *; ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
            * { i. inv UNCH. rewrite unchanged_on_contents0.
                - rewrite unchanged_on_contents; eauto. unfold Mem.perm in *; ss.
                  rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                - des_ifs. unfold Mem.perm in *; ss.
                  rewrite PMap.gsspec in *. des_ifs; ss.
                  eapply mi_mappedblocks in H.
                  ii. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
                - exploit mi_perm; eauto.
                  + unfold Mem.perm in *; ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                  + i. eapply unchanged_on_perm; eauto. }
      }
      { unfold Mem.valid_block in *. ss. des_ifs.
        - exfalso. eapply H. eapply Plt_succ.
        - eapply mi_freeblocks. ii. eapply H. etrans; eauto. eapply Plt_succ. }
      { des_ifs.
        - eapply Mem.valid_new_block in ALC. unfold Mem.valid_block in *. rewrite <- NB. eauto.
        - exploit mi_mappedblocks; eauto. unfold Mem.valid_block in *.
          rewrite <- NB. i. etrans; eauto. erewrite (Mem.nextblock_alloc) with (m2 := m1); eauto.
          apply Plt_succ. }

      { ii. des_ifs; ss; clarify.
        - left. ii. clarify. exploit mi_mappedblocks; eauto. unfold Mem.valid_block. extlia.
        - left. ii. clarify. exploit mi_mappedblocks; eauto. unfold Mem.valid_block. extlia.
        - eapply mi_no_overlap with (b1 := b1) (b2 := b2); eauto.
          + unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss.
          + unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. }
      { des_ifs.
        - set (Ptrofs.unsigned_range_2 ofs). lia.
        - eapply mi_representable; eauto. unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. }
      { des_ifs.
        - unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. rewrite Z.add_0_r in *. eauto.
        - exploit mi_perm_inv; eauto.
          + inv UNCH. apply unchanged_on_perm in H0.
            * eapply Mem.perm_alloc_4; eauto. ii. clarify.
              exploit mi_mappedblocks; eauto. i. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
            * des_ifs. exploit mi_mappedblocks; eauto.
              ii. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
            * exploit mi_mappedblocks; eauto. i. unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc; eauto. etrans; eauto. apply Plt_succ.
          + i. unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. }
    - hexploit _FillArgsParallel.fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto. lia.
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
          (ARGSRC: store_arguments m_tgt0 rs_tgt vs' sg m_tgt1):
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
    eapply val_inject_list_lessdef in VALINJ. splits; ss.

    - econs; ss; eauto.
      + unfold extcall_arguments in *.
        assert (LENGTH: Datatypes.length vs = Datatypes.length (loc_arguments sg)).
        { erewrite inject_list_length; eauto. symmetry. eapply list_forall2_length; eauto. }
        exploit _FillArgsParallel.fill_args_src_reg_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply loc_arguments_one. }
        exploit _FillArgsParallel.fill_args_src_blk_args; eauto.
        { eapply loc_arguments_norepet. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. lia. }
        instantiate (1:=0). instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold _FillArgsParallel.fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss. exploit PERM; eauto.
      + ii. exploit _FillArgsParallel.fill_args_src_blk_only_args; eauto.
        * eapply loc_arguments_norepet.
        * erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
        * eapply loc_arguments_one.
        * eapply extcall_arguments_extcall_arg_in_stack; eauto. lia.
        * i. instantiate (1:=ofs) in H.
          unfold _FillArgsParallel.fill_args_src_mem. ss.
          Local Transparent Mem.load. unfold Mem.load. s.
          repeat rewrite PMap.gss. des; eauto. right.
          exploit loc_arguments_acceptable_2; eauto. i. inv H.
          hexploit loc_arguments_bounded; eauto. i.
          esplits; eauto. rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr; cycle 1.
          { hexploit loc_arguments_bounded; eauto. i. set (typesize_pos ty). lia. }
          des_ifs. exfalso. apply n. unfold Mem.valid_access. split.
          { ii. unfold Mem.perm. ss. rewrite PMap.gss.
            eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply PERM.
            - erewrite typesize_chunk in *. set (typesize_pos ty). lia.
            - econs. }
          { clear - H1. destruct ty; ss; try apply Z.divide_factor_l.
            eapply Z.mul_divide_mono_l in H1. instantiate (1:=4) in H1. ss. }
      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0. econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          - split; i; exfalso.
            + eapply Mem.perm_alloc_3 in H1; eauto.
            + unfold _FillArgsParallel.fill_args_src_mem, Mem.perm in *. ss.
              rewrite PMap.gss in H1; eauto. eapply Mem.perm_unchanged_on_2 in H1; eauto.
              * eapply Mem.perm_alloc_3 in H1; eauto.
              * ss. des_ifs.
              * eapply Mem.valid_new_block; eauto.
          - transitivity (Mem.perm m_src0 b ofs k p).
            + symmetry. apply unchanged_on_perm; eauto. unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc in H0; eauto. eapply Plt_succ_inv in H0. des; clarify.
            + unfold Mem.perm; ss; eauto. rewrite PMap.gso; eauto. }
        { i. des_ifs.
          - rewrite PMap.gss. exfalso. exploit Mem.perm_alloc_3; try apply ALLOC; eauto.
          - rewrite PMap.gso; eauto. symmetry. apply unchanged_on_contents; eauto.
            eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss. eapply PERM; eauto.

    - unfold _FillArgsParallel.fill_args_src_mem. inv EXTENDS. inv mext_inj. econs.
      + ss. rewrite mext_next. erewrite <- Mem.nextblock_alloc; eauto.
      + unfold inject_id in *.

        { econs; ss; i; clarify.
          - zsimpl. destruct (peq b2 (Mem.nextblock m_src0)); clarify.
            + unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. rewrite mext_next. eauto.
            + inv UNCH. eapply unchanged_on_perm.
              * des_ifs. eauto.
              * eapply Mem.perm_valid_block. eapply Mem.perm_alloc_1; eauto.
                eapply mi_perm; eauto. unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
              * eapply Mem.perm_alloc_1; eauto. unfold Mem.perm in *. ss.
                rewrite PMap.gsspec in *. des_ifs; ss. exploit mi_perm; eauto. i. zsimpl. eauto.
          - eapply Z.divide_0_r.

          - rewrite PMap.gsspec in *. des_ifs; ss.
            + hexploit _FillArgsParallel.fill_args_src_blk_inject; eauto.
              * erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
              * eapply extcall_arguments_extcall_arg_in_stack; eauto. lia.
              * instantiate (1:= ofs). erewrite Z.add_0_r. erewrite Z.add_0_l.
                intros VINJ. repeat rewrite mext_next in *. eauto.
            + exploit mi_memval; eauto.
              * unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
              * zsimpl. i.
                { inv UNCH. dup ALC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALC0. inv ALC0.
                  rewrite unchanged_on_contents; ss; eauto.
                  - rewrite unchanged_on_contents0; eauto. unfold Mem.perm in *; ss.
                    rewrite PMap.gsspec in *. des_ifs; ss. exploit mi_perm; eauto. zsimpl. eauto.
                  - des_ifs. eauto.
                  - eapply unchanged_on_perm0; eauto.
                    + eapply Mem.perm_valid_block. exploit mi_perm; eauto.
                      * unfold Mem.perm in *; ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                    + exploit mi_perm; eauto.
                      * unfold Mem.perm in *; ss. rewrite PMap.gsspec in *. des_ifs; ss. eauto.
                      * zsimpl. eauto. }
        }
      + { ii. destruct (peq b (Mem.nextblock m_src0)); clarify.
          - unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. rewrite <- mext_next. auto.
          - exploit mext_perm_inv; eauto.
            + inv UNCH. apply unchanged_on_perm in H.
              * eapply Mem.perm_alloc_4; eauto. ii. clarify. eauto.
              * des_ifs. eauto.
              * eapply Mem.perm_valid_block in H. unfold Mem.valid_block in *. rewrite NB. eauto.
            + i. unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs; ss. }
    - hexploit _FillArgsParallel.fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto. eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto. lia.
      + ii. cinv (H mr); econs; eauto.
  Qed.

End STOREARGPRARALLEL.


Require Import JunkBlock.

Lemma typify_has_typed_loc vs sg
      (TYP : Val.has_type_list vs (sig_args sg)):
    list_forall2 _FillArgsParallel.has_typed_loc (loc_arguments sg) vs.
Proof.
  unfold sig_args, loc_arguments in *. des_ifs. ss.
  generalize 0 at 1. generalize 0 at 1. generalize 0 at 1.
  revert TYP. clear. ginduction sig_args; ss.
  - i. destruct vs; clarify. econs.
  - i. destruct vs; clarify. ss. des. des_ifs; econs; eauto; try by econs.
Qed.

Theorem store_arguments_progress
        m0 tvs sg
        (TYP: Val.has_type_list tvs sg.(sig_args))
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
        n:
    exists rs m2,
      (<<STR: store_arguments m0 rs tvs sg m2>>) /\
      (<<PTRFREE:
         forall mr
           (NIN: ~ In (R mr) (regs_of_rpairs (loc_arguments sg))),
           is_junk_value m2 (assign_junk_blocks m2 n) (rs mr)>>).
Proof.
  destruct (Mem.alloc m0 0 (4 * size_arguments sg)) eqn:ALC.
  exists (fun mr =>
            if extcall_args_reg mr sg
            then (_FillArgsParallel.fill_args_src_reg tvs (loc_arguments sg)) mr else Vundef).
  exists (_FillArgsParallel.fill_args_mem m b tvs (loc_arguments sg)).
  splits.
  - econs; eauto.
    + eapply extcall_arguments_same.
      * eapply extcall_arg_in_stack_in_reg_extcall_argument.
        { eapply _FillArgsParallel.fill_args_blk_args.
          - eapply loc_arguments_norepet.
          - eapply loc_arguments_one.
          - eapply Val_has_type_list_length; auto.
          - eapply typify_has_typed_loc; eauto. }
        { eapply _FillArgsParallel.fill_args_src_reg_args.
          - eapply loc_arguments_norepet.
          - eapply loc_arguments_one.
          - eapply Val_has_type_list_length; auto. }
        { ss. rewrite PMap.gss. ss. }
        { eapply Mem_alloc_range_perm in ALC. unfold Mem.range_perm, Mem.perm in *. ss. }
        { auto. }
      * i. des_ifs.
    + ii. exploit _FillArgsParallel.fill_args_blk_only_args.
      * eapply loc_arguments_norepet.
      * eapply Val_has_type_list_length; eauto.
      * eapply loc_arguments_one.
      * eapply typify_has_typed_loc; eauto.
      * i. instantiate (1:=ofs) in H. ss.
        Local Transparent Mem.load. unfold Mem.load. s.
        repeat rewrite PMap.gss. des; eauto. right.
        exploit loc_arguments_acceptable_2; eauto. i. inv H.
        hexploit loc_arguments_bounded; eauto. i.
        esplits; eauto. rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; cycle 1.
        { hexploit loc_arguments_bounded; eauto. i. set (typesize_pos ty). lia. }
        des_ifs. exfalso. apply n0. unfold Mem.valid_access. split.
        { ii. unfold Mem.perm. ss. eapply Mem.perm_cur. eapply Mem.perm_implies; try eapply Mem.perm_alloc_2; eauto.
          - erewrite typesize_chunk in *. set (typesize_pos ty). lia.
          - econs. }
        { clear - H1. destruct ty; ss; try apply Z.divide_factor_l.
          eapply Z.mul_divide_mono_l in H1. instantiate (1:=4) in H1. ss. }
    + econs; ss; try refl. i. rewrite PMap.gsspec. des_ifs; ss. exfalso.
      eapply H. eapply Mem.perm_alloc_3; eauto.
    + eapply Mem_alloc_range_perm in ALC. unfold Mem.range_perm, Mem.perm in *. ss.
  - i. des_ifs.
Qed.
