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
Require Import Mach mktac.

Ltac my_tac :=
  match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] =>
    let name := fresh "A" in destruct x eqn:name; ss; subst;
                             try rewrite andb_true_iff in *; des; des_sumbool; subst
  end.

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

  Lemma longofwords_imply vh vl v
        (LONG: Val_longofwords' vh vl v)
    :
      Val.longofwords vh vl = v.
  Proof.
    inv LONG; clarify.
  Qed.

  Inductive store_arguments (m0: mem) (rs: Mach.regset) (vs: list val) (sg: signature) (m2: mem): Prop :=
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

End STOREARGUMENTS.

Inductive typechecked_args (sg: signature) (vs: list val) : Prop :=
| typechecked_args_intro
    (TYP: Val.has_type_list vs sg.(sig_args))
    (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
.

Lemma typecheck_typechecked_args vs sg tvs
      (TYP: typecheck vs sg tvs)
  :
    typechecked_args sg tvs.
Proof.
  inv TYP. econs; eauto.
  revert vs LEN. generalize (sig_args sg).
  induction l; ss; i.
  - destruct vs; clarify.
  - destruct vs; clarify. ss. inv LEN.
    split; eauto.
    unfold typify_list. ss.
    unfold Val.has_type, typify. des_ifs.
Qed.

Section FILLARG.

  Local Existing Instance Val.mi_normal.

  Definition agree (j: meminj) (rs0 rs1: Mach.regset) : Prop :=
    forall mr, Val.inject j (rs0 mr) (rs1 mr).

  Lemma list_map_injective A B (f: A -> B)
        (INJECTIVE: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
        l0 l1
        (LEQ: map f l0 = map f l1)
    :
      l0 = l1.
  Proof.
    revert l1 LEQ. induction l0; i; ss.
    - destruct l1; ss.
    - destruct l1; ss. inv LEQ. f_equal; eauto.
  Qed.

  Definition copy_memval (v: val) (mv: memval) : memval :=
    match v, mv with
    | Vundef, _ => Undef
    | _, Fragment _ q n => Fragment v q n
    | _, _ => mv
    end.

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
  Admitted.
  (*   unfold decode_val, Val.load_result in *. des_ifs. *)
  (*   - unfold proj_value in *. *)
  (*     des_ifs; repeat (repeat (apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*     all: eauto. *)
  (*     des_ifs. *)
  (*   - unfold proj_value in *. *)
  (*     des_ifs; repeat (repeat (apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*     all: eauto. *)
  (*     des_ifs. *)
  (* Qed. *)

  Definition copy_list_memval (v: val): list memval -> list memval := map (copy_memval v).

  Lemma Forall_in_map A B al (R: B -> Prop) (f: A -> B)
        (RMAP: forall a (IN: In a al), R (f a))
    :
      Forall R (map f al).
  Proof.
    induction al; econs; ss; eauto.
  Qed.

  Lemma Forall2_in_map A B al (R: B -> A -> Prop) (f: A -> B)
        (RMAP: forall a (IN: In a al), R (f a) a)
    :
      list_forall2 R (map f al) al.
  Proof.
    induction al; econs; ss; eauto.
  Qed.

  Lemma eq_Forall2_eq A (al0 al1 : list A)
    :
      list_forall2 eq al0 al1 <-> al0 = al1.
  Proof.
    revert al1. induction al0; ss; i; split; i; eauto.
    - inv H. eauto.
    - inv H. econs.
    - inv H. f_equal. eapply IHal0. eauto.
    - inv H. econs; eauto. eapply IHal0. eauto.
  Qed.

  Lemma copy_list_memval_decode_pointer j vl vl' chunk v blk ofs b
        (INJ: Val.inject j v (decode_val chunk vl))
        (COPY: copy_list_memval v vl = vl')
        (VALUE: v = Vptr blk ofs b)
    :
      decode_val chunk vl' = v.
  Proof.
  Admitted.
  (*   clarify. inv INJ; ss. *)
  (*   - unfold decode_val in H3. destruct vl; ss. *)
  (*     + des_ifs. *)
  (*     + des_ifs_safe. *)
  (*       destruct m, chunk; ss; des_ifs_safe. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*         unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. *)
  (*       * destruct v; ss. *)
  (*       * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*         unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. *)
  (*   - unfold decode_val in H3. destruct vl; ss. *)
  (*     + des_ifs_safe. *)
  (*       destruct m, chunk; ss; des_ifs_safe. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * des_ifs. *)
  (*       * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*         unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. *)
  (*       * destruct v; ss. *)
  (*       * repeat ((repeat apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify). *)
  (*         unfold decode_val; des_ifs. ss. unfold proj_sumbool, andb. des_ifs. *)
  (* Qed. *)

  Lemma copy_list_memval_decode_undef vl vl'
        (COPY: copy_list_memval Vundef vl = vl')
    :
      vl' = list_repeat (List.length vl) Undef.
  Proof.
    revert vl' COPY. induction vl; ss; i; clarify.
    f_equal. eapply IHvl; eauto.
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

  Definition fill_arg_src_blk (m_tgt m: ZMap.t memval) (arg: val) (loc: rpair loc)
    : ZMap.t memval :=
    match loc with
    | One (S Outgoing ofs ty) =>
      Mem.setN (copy_list_memval arg (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * ofs) m_tgt)) (4 * ofs) m
    | _ => m
    end.

  Definition fill_arg_src_reg (rs: regset) (arg: val) (loc: rpair loc)
    : regset :=
    match loc with
    | One (R r) =>
      rs#r <- arg
    | _ => rs
    end.

  Fixpoint fill_args_src_blk (m_tgt m: ZMap.t memval) (args: list val) (locs: list (rpair loc))
    : ZMap.t memval :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_src_blk m_tgt (fill_args_src_blk m_tgt m vtl ltl) vhd lhd
    | _, _ => m
    end.

  Fixpoint fill_args_src_reg (args: list val) (locs: list (rpair loc))
    : regset :=
    match args, locs with
    | vhd::vtl, lhd::ltl =>
      fill_arg_src_reg (fill_args_src_reg vtl ltl) vhd lhd
    | _, _ => fun _ => Vundef
    end.

  Definition extcall_arg_in_reg (rs: regset) (l: rpair loc) (v: val) : Prop :=
    forall r (EQ: l = One (R r)), v = rs r.

  Lemma list_forall2_lift A B (R0 R1: A -> B -> Prop) al bl
        (SAME: forall a (IN: In a al) b, R0 a b -> R1 a b)
        (FORALL: list_forall2 R0 al bl)
    :
      list_forall2 R1 al bl.
  Proof.
    generalize dependent bl. revert SAME.
    induction al; ss; i; inv FORALL; econs; eauto.
  Qed.

  Definition extcall_arg_in_stack (m: ZMap.t memval) (l: rpair loc) (v: val) : Prop :=
    forall ofs ty (EQ: l = One (S Outgoing ofs ty)),
      (<<LOAD:
         Some (decode_val (chunk_of_type ty) (Mem.getN (size_chunk_nat (chunk_of_type ty)) (4 * ofs) m)) = Some v>>) /\
      (<<UNDEFS: forall (UNDEF: v = Vundef),
          memval_undefs (chunk_of_type ty) m (4 * ofs)>>).

  Inductive range_no_overlap : list (rpair loc) -> Prop :=
  | range_no_overlap_nil:
      range_no_overlap []
  | range_no_overlap_cons
      hd tl
      (HD: forall ofs0 ofs1 ty0 ty1
                  (EQ: hd = One (S Outgoing ofs0 ty0))
                  (IN: In (One (S Outgoing ofs1 ty1)) tl),
          (4 * ofs0 + size_chunk (chunk_of_type ty0) <= 4 * ofs1) \/
          (4 * ofs1 + size_chunk (chunk_of_type ty1) <= 4 * ofs0))
      (ONTL: range_no_overlap tl)
    :
      range_no_overlap (hd::tl).

  Lemma fill_args_src_reg_args args locs
        (NOREPEAT: NoDup locs)
        (LENGTH: length args = length locs)
    :
      list_forall2 (extcall_arg_in_reg (fill_args_src_reg args locs)) locs args.
  Proof.
    revert NOREPEAT args LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv NOREPEAT. inv LENGTH.
      specialize (IHlocs H2 _ H0).
      unfold fill_arg_src_reg. des_ifs.
      + econs; eauto.
        * ii. inv EQ. rewrite Regmap.gss. auto.
        * eapply list_forall2_lift; [|eauto].
          { ii. clarify. unfold Regmap.set. des_ifs. eauto. }
      + econs; eauto. ii. inv EQ.
      + econs; eauto. ii. inv EQ.
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

  Lemma Forall_map A B la (R: B -> Prop) (f: A -> B)
        (RMAP: forall a, R (f a))
    :
      Forall R (map f la).
  Proof.
    induction la; econs; ss.
  Qed.

  Lemma fill_args_src_blk_args m_tgt m j args_tgt args locs
        (INJECT: Val.inject_list j args args_tgt)
        (NOOVERLAP: range_no_overlap locs)
        (LENGTH: length args = length locs)
        (ARGS: list_forall2 (extcall_arg_in_stack m_tgt) locs args_tgt)
    :
      list_forall2 (extcall_arg_in_stack (fill_args_src_blk m_tgt m args locs)) locs args.
  Proof.
    revert NOOVERLAP args_tgt args ARGS INJECT LENGTH. induction locs; ss; i.
    - destruct args; ss. econs.
    - destruct args; ss. inv NOOVERLAP. inv LENGTH.
      inv ARGS. inv INJECT.
      specialize (IHlocs ONTL _ _ H4 H7 H0).
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
            + i. rewrite H. auto.
          - ii. clarify. unfold memval_undefs in *.
            pattern (size_chunk_nat (chunk_of_type ty0)) at 1.
            rewrite LEQ.
            erewrite Mem.getN_setN_same.
            unfold copy_list_memval. unfold copy_memval. ss.
            eapply Forall_map.
            ii. econs.
        }
        { eapply list_forall2_lift; [| eauto].
          ii. clarify. specialize (H ofs ty0 eq_refl). des. clarify.
          split; i.
          - erewrite Mem.getN_setN_outside; eauto.
            specialize (HD _ _ _ _ eq_refl IN).
            unfold range, less1, copy_list_memval in *.
            erewrite map_length. rewrite Mem.getN_length.
            repeat rewrite <- size_chunk_conv. lia.
          - ii. unfold memval_undefs in *.
            erewrite Mem.getN_setN_outside; auto.
            specialize (HD _ _ _ _ eq_refl IN).
            unfold range, less1, copy_list_memval in *.
            erewrite map_length. rewrite Mem.getN_length.
            repeat rewrite <- size_chunk_conv. lia. }
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

  Lemma loc_norepet_app l0 l1
        (NOREPEAT: Loc.norepet (l0 ++ l1))
    :
      Loc.norepet l1.
  Proof.
    induction l0; ss.
    inv NOREPEAT. eauto.
  Qed.

  Lemma loc_in_not_not_in
        r l
        (IN: In (One r) l)
        (NIN: Loc.notin r (regs_of_rpairs l))
    :
      False.
  Proof.
    induction l; ss. des; clarify; ss; des.
    - destruct r; ss; des; clarify.
      + destruct ty; ss; lia.
      + destruct ty; ss; lia.
    - eapply IHl; eauto.
      destruct a; ss; des; eauto.
  Qed.

  Lemma nodup_loc_arguments sg:
    NoDup (loc_arguments sg).
  Proof.
    generalize (loc_arguments_one sg).
    generalize (loc_arguments_norepet sg). induction (loc_arguments sg); ss; i.
    - econs.
    - econs; eauto.
      + ii.
        destruct a.
        * eapply loc_in_not_not_in; eauto.
          ss. inv H. eauto.
        * exploit H0; eauto.
      + eapply IHl; eauto.
        eapply loc_norepet_app; eauto.
  Qed.

  Lemma in_one_in_rpair l (r: loc)
        (IN: In (One r) l)
    :
      In r (regs_of_rpairs l).
  Proof.
    induction l; ss; des; clarify.
    - destruct r; ss; eauto.
    - eapply in_or_app; eauto.
  Qed.

  Lemma loc_not_in_in_not l ll
    :
      Loc.notin l ll <-> (forall l0 (IN: In l0 ll), Loc.diff l l0).
  Proof.
    induction ll; ss; split; des; i; des; clarify; eauto.
    split; eauto.
  Qed.

  Lemma no_overlap_loc_arguments sg:
    range_no_overlap (loc_arguments sg).
  Proof.
    generalize (loc_arguments_one sg).
    generalize (loc_arguments_norepet sg). induction (loc_arguments sg); ss; i.
    - econs.
    - econs; eauto.
      + ii. clarify.
        inv H.
        eapply loc_not_in_in_not in H3; eauto.
        * instantiate (1:=S Outgoing ofs1 ty1) in H3.
          ss. des; clarify.
          -- destruct ty0, ty1; ss; try lia.
          -- destruct ty0, ty1; ss; try lia.
        * eapply in_one_in_rpair; eauto.
      + eapply IHl; eauto.
        eapply loc_norepet_app; eauto.
  Qed.

  Lemma loc_arguments_ofs_bounded
        sg
        (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
        ofs ty
        (IN: In (One (S Outgoing ofs ty)) (loc_arguments sg))
    :
      0 <= 4 * ofs <= Ptrofs.max_unsigned.
  Proof.
    hexploit loc_arguments_bounded.
    - instantiate (1:=sg). instantiate (1:=ty). instantiate (1:=ofs).
      revert ofs ty IN.
      induction (loc_arguments sg); ss; i.
      des; clarify; ss; eauto.
      eapply in_app_iff. right. eapply IHl; eauto.
    - i. split.
      + hexploit (loc_arguments_acceptable sg); eauto.
        intros ACCP. inv ACCP. lia.
      + destruct ty; ss; lia.
  Qed.

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



  Lemma sig_args_length sg
    :
      Datatypes.length (sig_args sg) = Datatypes.length (loc_arguments sg).
  Proof.
    unfold loc_arguments in *. des_ifs.
    generalize 0 at 1.
    generalize 0 at 1.
    generalize 0 at 1.
    induction (sig_args sg); ss; i.
    des_ifs; ss; f_equal; eauto.
  Qed.

  Lemma Val_has_type_list_length sg vs
        (TYP: Val.has_type_list vs (sig_args sg))
    :
      Datatypes.length vs = Datatypes.length (loc_arguments sg).
  Proof.
    rewrite <- sig_args_length.
    revert vs TYP. induction (sig_args sg); ss; i; destruct vs; ss.
    des.
    f_equal; eauto.
  Qed.

  Lemma store_arguments_parallel_inject
        j m_src0 m_tgt0 m_tgt1 rs_tgt vs vs' sg
        (* (TYP: typechecked_args sg vs) *)
        (TYP: typechecked_args sg vs')
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
    exists (fill_args_src_mem m_tgt0 m_tgt1 m_src0 vs (loc_arguments sg)).
    exists (fill_args_src_reg vs (loc_arguments sg)).
    destruct (Mem.alloc m_src0 0 (4 * size_arguments sg)) eqn:ALLOC.
    dup ALLOC. apply Mem.alloc_result in ALLOC0. clarify.

    inv ARGSRC. unfold extcall_arguments in *. inv TYP.
    dup ALC. apply Mem.alloc_result in ALC0. clarify.

    assert (INCR: inject_incr j (update_meminj j (Mem.nextblock m_src0) (Mem.nextblock m_tgt0) 0)).
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
        exploit fill_args_src_reg_args; eauto.
        { eapply nodup_loc_arguments. }
        exploit fill_args_src_blk_args; eauto.
        { eapply no_overlap_loc_arguments; eauto. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. }
        instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss.
          exploit PERM; eauto.
      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0.
        econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          transitivity (Mem.perm m_src0 b ofs k p).
          - symmetry. apply unchanged_on_perm; eauto.
            unfold Mem.valid_block in *.
            erewrite Mem.nextblock_alloc in H0; eauto.
            eapply Plt_succ_inv in H0. des; clarify.
          - unfold Mem.perm; ss; eauto.
            rewrite PMap.gso; eauto. }
        { i. des_ifs.
          rewrite PMap.gso; eauto.
          symmetry. apply unchanged_on_contents; eauto.
          eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss.
        eapply PERM; eauto.
    - inv INJ. inv mi_inj. unfold fill_args_src_mem, update_meminj in *.
      econs; ss; i.
      { econs; ss; i.
        - des_ifs.
          + unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss.
            zsimpl. eauto.
          + inv UNCH. eapply unchanged_on_perm.
            * des_ifs.
              exploit mi_mappedblocks; eauto.
              i. unfold Mem.valid_block in *. ss.
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
          + hexploit fill_args_src_blk_inject; eauto.
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
                  unfold Mem.valid_block in *. eapply Plt_strict; eauto.
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
              i. unfold Mem.valid_block in *. eapply Plt_strict; eauto.
            * exploit mi_mappedblocks; eauto.
              i. unfold Mem.valid_block in *.
              erewrite Mem.nextblock_alloc; eauto. etrans; eauto.
              apply Plt_succ.
          + i. unfold Mem.perm in *. ss.
            rewrite PMap.gsspec in *. des_ifs; ss. }
    - hexploit fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto.
        eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto.
      + ii. minv (H mr); econs; eauto.
  Qed.

  Lemma store_arguments_parallel_extends
        m_src0 m_tgt0 m_tgt1 rs_tgt vs vs' sg
        (* (TYP: typechecked_args sg vs) *)
        (TYP: typechecked_args sg vs')
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
    exists (fill_args_src_mem m_tgt0 m_tgt1 m_src0 vs (loc_arguments sg)).
    exists (fill_args_src_reg vs (loc_arguments sg)).

    destruct (Mem.alloc m_src0 0 (4 * size_arguments sg)) eqn:ALLOC.
    dup ALLOC. apply Mem.alloc_result in ALLOC0. clarify.

    inv ARGSRC. unfold extcall_arguments in *. inv TYP.
    dup ALC. apply Mem.alloc_result in ALC0. clarify.

    eapply val_inject_list_lessdef in VALINJ.

    splits; ss.

    - econs; ss; eauto.
      + unfold extcall_arguments in *.
        assert (LENGTH: Datatypes.length vs = Datatypes.length (loc_arguments sg)).
        { erewrite inject_list_length; eauto.
          symmetry. eapply list_forall2_length; eauto. }
        exploit fill_args_src_reg_args; eauto.
        { eapply nodup_loc_arguments. }
        exploit fill_args_src_blk_args; eauto.
        { eapply no_overlap_loc_arguments; eauto. }
        { eapply extcall_arguments_extcall_arg_in_stack; eauto. }
        instantiate (1:=ZMap.init Undef). intros STACK REGS.
        eapply extcall_arg_in_stack_in_reg_extcall_argument; eauto.
        * ss. rewrite PMap.gss. auto.
        * unfold fill_args_src_mem, Mem.range_perm, Mem.perm. ss. ii.
          rewrite PMap.gss.
          exploit PERM; eauto.
      + dup ALLOC. eapply Mem.alloc_unchanged_on with (P:=top2) in ALLOC0. inv ALLOC0.
        econs; ss; eauto.
        { erewrite Mem.nextblock_alloc; eauto. refl. }
        { i. des_ifs.
          transitivity (Mem.perm m_src0 b ofs k p).
          - symmetry. apply unchanged_on_perm; eauto.
            unfold Mem.valid_block in *.
            erewrite Mem.nextblock_alloc in H0; eauto.
            eapply Plt_succ_inv in H0. des; clarify.
          - unfold Mem.perm; ss; eauto.
            rewrite PMap.gso; eauto. }
        { i. des_ifs.
          rewrite PMap.gso; eauto.
          symmetry. apply unchanged_on_contents; eauto.
          eapply Mem.perm_alloc_4; eauto. }
      + eapply Mem.nextblock_alloc; eauto.
      + ii. unfold Mem.perm. ss. rewrite PMap.gss.
        eapply PERM; eauto.

    - unfold fill_args_src_mem. inv EXTENDS. inv mext_inj. econs.
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
            + hexploit fill_args_src_blk_inject; eauto.
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
    - hexploit fill_args_src_reg_agree.
      + eauto.
      + erewrite inject_list_length; eauto.
        eapply Val_has_type_list_length; eauto.
      + eapply extcall_arguments_extcall_arg_in_reg; eauto.
      + ii. minv (H mr); econs; eauto.
  Qed.

  Lemma extcall_args_callee_save_disjoint sg mr
        (EXT: In (R mr) (regs_of_rpairs (loc_arguments sg)))
    :
      ~ Conventions1.is_callee_save mr.
  Proof.
    destruct sg. ss.
    unfold loc_arguments in *.
    ss. replace Archi.ptr64 with true in *; eauto.
    assert (forall l mr p q r,
               In (R mr) (regs_of_rpairs (loc_arguments_64 l p q r)) ->
               ~ is_callee_save mr); eauto.
    induction l; ss; i; destruct a; des_ifs; ss; des; eauto; inv H; ss.
  Qed.

  Lemma list_forall2_nth_option_rel A B (R: A -> B -> Prop) (la: list A) (lb: list B)
    :
      list_forall2 R la lb <-> forall n, option_rel R (nth_error la n) (nth_error lb n).
  Proof.
    split; intros.
    - revert n.
      induction H; ss; i.
      + destruct n; ss; econs.
      + destruct n; ss. econs; eauto.
    - revert lb H. induction la; ss; i.
      + minv (H 0%nat). des_ifs. econs.
      + destruct lb.
        * minv (H 0%nat).
        * econs.
          -- minv (H 0%nat). eauto.
          -- eapply IHla. i.
             mset2 H (Datatypes.S n). ss.
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

End FILLARG.

Section ARGS.

  Lemma extcall_arg_imply
    :
      extcall_arg <5= Mach.extcall_arg.
  Proof.
    ii. inv PR; econs. eauto.
  Qed.

  Lemma extcall_arg_pair_imply
    :
      extcall_arg_pair <5= Mach.extcall_arg_pair.
  Proof.
    ii. inv PR.
    - eapply extcall_arg_imply in H. econs. eauto.
    - eapply extcall_arg_imply in H. eapply extcall_arg_imply in H0.
      eapply longofwords_imply in LONG. clarify. econs; eauto.
  Qed.

  Lemma extcall_arguments_imply
    :
      extcall_arguments <5= Mach.extcall_arguments.
  Proof.
    ii. unfold extcall_arguments, Mach.extcall_arguments in *.
    eapply list_forall2_imply; eauto.
    i. eapply extcall_arg_pair_imply. eauto.
  Qed.

End ARGS.

Ltac extcall_simpl :=
  repeat match goal with
         | [ H: extcall_arg_pair _ _ _ (One _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (S _ _ _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (R _) _ |- _ ] => inv H
         end
.

(* Inductive store_arguments (m0: mem) (rs: regset) (vs: list val) (sg: signature) (m2: mem): Prop := *)
(* | store_arguments_intro *)
(*     m1 blk *)
(*     (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, blk)) *)
(*     (VALS: extcall_arguments rs m2 (Vptr blk Ptrofs.zero true) sg vs) *)
(*     (UNCH: Mem.unchanged_on (fun b ofs => if eq_block b blk *)
(*                                           then (* ~ (0 <= ofs < 4 * size_arguments sg) *) False *)
(*                                           else True) m1 m2) *)
(*     (NB: m1.(Mem.nextblock) = m2.(Mem.nextblock)) *)
(*     (PERM: Mem.range_perm m2 blk 0 (4 * size_arguments sg) Cur Freeable) *)
(* . *)

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
          (TYP: typechecked_args sg targs)
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
    inv TYP.
    assert(LEN2: length targs = length (sig_args sg)).
    { clear - TYP0. revert TYP0. generalize (sig_args sg).
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
    - admit "ez - nextblock".
    - ii. eapply fill_arguments_perm; eauto. eauto with mem.
  Qed.

End FillArgs.

Theorem store_arguments_progress
        m0 tvs sg
        (TYP: typechecked_args sg tvs)
  :
    exists rs m2, <<STR: store_arguments m0 rs tvs sg m2>>
.
Proof.
  inv TYP.
  destruct (Mem.alloc m0 0 (4 * size_arguments sg)) eqn:ALC.
  rename m into m1. rename b into blk.
  assert(LEN2: length tvs = length (sig_args sg)).
  { clear - TYP0. revert TYP0. generalize (sig_args sg).
    induction tvs; ss; i; des_ifs; ss.
    f_equal. eapply IHtvs. des. auto. }
  exploit (FillArgs.fill_arguments_progress sg m0 (Regmap.init Vundef)); eauto. i; des.
  exploit (FillArgs.fill_arguments_spec sg m0 (Regmap.init Vundef) m1 blk tvs); eauto.
  econs; eauto.
Qed.
