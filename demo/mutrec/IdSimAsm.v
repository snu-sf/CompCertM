Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemInjInvC SimSymbDropInv.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.
Require Import Conventions1C.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import StoreArguments.
Require Import AsmStepInj IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import IdSimExtra AsmExtra IdSimExtra.

Require Import MatchSimModSemExcl.
Require Import Conventions1C.

Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.

Require Import mktac.

(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)

(* TODO it's from AsmgenproofC *)
Section FROMASMGEN.

  Definition set_regset (rs0 rs1: Mach.regset) (sg: signature) (mr: mreg) : val :=
    if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
    then rs1 mr
    else rs0 mr.

  Definition set_regset_undef (rs: Mach.regset) (sg: signature) (mr: mreg) : val :=
    if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
    then Vundef
    else rs mr.

End FROMASMGEN.

(* TODO it's from LowerBoundExtra *)
Section FROMLB.

  Definition extcall_args_reg (mr: mreg) (sg: signature):
    {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
    {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
  Proof.
    generalize (regs_of_rpairs (loc_arguments sg)). induction l.
    - ss. tauto.
    - ss. inv IHl; [tauto|].
      destruct a.
      + destruct (mreg_eq r mr); [clarify; eauto|].
        right. intros []; clarify.
      + right. intros []; clarify.
  Qed.

End FROMLB.

Lemma lessdef_commute j src0 src1 tgt0 tgt1
      (INJ0: Val.inject j src0 tgt0)
      (INJ1: Val.inject j src1 tgt1)
      (LESS: Val.lessdef src0 src1)
      (UNDEF: src0 = Vundef -> tgt0 = Vundef)
  :
    Val.lessdef tgt0 tgt1.
Proof.
  inv LESS.
  - inv INJ0; inv INJ1; ss; try econs.
    + clarify.
    + rewrite UNDEF; auto.
  - rewrite UNDEF; auto.
Qed.

Inductive wf_init_rs (sg: signature) (rs: regset) : Prop :=
| wf_init_rs_intro
    (RSPDEF: rs RSP <> Vundef)
    (TPTR: Val.has_type (rs RA) Tptr)
    (RADEF: rs RA <> Vundef)
.

Definition undef_bisim (rs_src rs_tgt: regset): Prop :=
  forall (r: mreg) (IN: Conventions1.is_callee_save r = true) (UNDEF: rs_src (to_preg r) = Vundef),
    rs_tgt (to_preg r) = Vundef.

Definition asm_init_rs (rs_src rs_tgt: Mach.regset)
           sg v_pc v_ra blk :=
  (((to_pregset (set_regset rs_src rs_tgt sg)) # PC <- v_pc)
     # RA <- v_ra)
    # RSP <- (Vptr blk Ptrofs.zero).

Lemma asm_init_rs_undef_bisim
      rs_src rs_tgt sg v_pc v_ra blk
  :
    undef_bisim (asm_init_rs rs_src (to_mregset rs_tgt) sg v_pc v_ra blk) rs_tgt.
Proof.
  ii. unfold asm_init_rs, to_pregset, set_regset, to_mregset, Pregmap.set, to_preg in *.
  des_ifs.
  - unfold preg_of in *; des_ifs.
  - unfold preg_of in *; des_ifs.
  - unfold preg_of in *; des_ifs.
  - rewrite to_preg_to_mreg in *. clarify.
    exfalso. exploit loc_args_callee_save_disjoint; eauto.
    apply NNPP. ii. rewrite <- loc_notin_not_in in H. eauto.
  - rewrite to_preg_to_mreg in *. clarify.
Qed.

(* move it to MemoryC after stablizing *)
Section TOMEMORYC.

  Lemma Z2Nat_range n:
    Z.of_nat (Z.to_nat n) = if (zle 0 n) then n else 0.
  Proof.
    des_ifs.
    - rewrite Z2Nat.id; eauto.
    - unfold Z.to_nat. des_ifs.
  Qed.

  Theorem Mem_unfree_parallel_inject
          j m1 m2 b ofs_src ofs_tgt sz m1' b' delta
          (INJECT: Mem.inject j m1 m2)
          (UNFREE: Mem_unfree m1 b (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sz) = Some m1')
          (VAL: ofs_tgt = Ptrofs.add ofs_src (Ptrofs.repr delta))
          (DELTA: j b = Some (b', delta))
          (ALIGN: forall ofs chunk p (PERM: forall ofs0 (BOUND: ofs <= ofs0 < ofs + size_chunk chunk),
                                         (Ptrofs.unsigned ofs_src) <= ofs0 < (Ptrofs.unsigned ofs_src + sz) \/ Mem.perm m1 b ofs0 Max p),
              (align_chunk chunk | delta))
          (REPRESENTABLE: forall ofs (PERM: Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
                                            Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty \/
                                            (Ptrofs.unsigned ofs_src) <= Ptrofs.unsigned ofs < (Ptrofs.unsigned ofs_src + sz) \/
                                            (Ptrofs.unsigned ofs_src) <= Ptrofs.unsigned ofs - 1 < (Ptrofs.unsigned ofs_src + sz)),
              delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned)
          (NOPERM: Mem_range_noperm m2 b' (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz))
    :
      exists m2',
        (<<UNFREE: Mem_unfree m2 b' (Ptrofs.unsigned ofs_tgt) (Ptrofs.unsigned ofs_tgt + sz) = Some m2'>>)
        /\ (<<INJECT: Mem.inject j m1' m2'>>).
  Proof.
    unfold Mem_unfree in UNFREE. des_ifs.
    assert (VALID: Plt b' (Mem.nextblock m2)).
    { exploit Mem.valid_block_inject_2; eauto. }
    unfold Mem_unfree in *. des_ifs. esplits; eauto. ss.
    assert (NOOVERLAP: forall b_src delta' ofs k p (DELTA: j b_src = Some (b', delta'))
                              (OFS: (Ptrofs.unsigned ofs_src) + delta <= ofs + delta' < Ptrofs.unsigned ofs_src + delta + sz)
                              (PERM: Mem.perm m1 b_src ofs k p),
               False).
    { i. exploit Mem.perm_inject; eauto. i. exploit NOPERM; eauto.
      - erewrite unsigned_add; eauto. eapply REPRESENTABLE; eauto. lia.
      - eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }

    econs; ss; eauto; i.

    - cinv (Mem.mi_inj _ _ _ INJECT).
      econs; ss; eauto; i.
      + destruct (peq b b1); clarify.
        * unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *. des_ifs_safe.
          des_ifs; clarify; eauto; try lia.
          { exploit Mem.perm_inject; eauto. i. exfalso. eapply NOPERM; eauto.
            eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }
          { exploit Mem.perm_inject; eauto. i. exfalso. eapply NOPERM; eauto.
            eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs. }
          { erewrite unsigned_add in *; eauto.
            - lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia. }
          { erewrite unsigned_add in *; eauto.
            - lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia. }
        * assert (Mem.perm m2 b2 (ofs + delta0) k p1).
          {
            exploit Mem.perm_inject; eauto. unfold Mem.perm in *. ss.
            rewrite PMap.gso in H0; eauto.
          }
          unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *.
          des_ifs. exfalso. exploit NOPERM; eauto.
          eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
      + ss. destruct (peq b1 b); clarify.
        { exploit ALIGN; eauto. i.
          exploit H0; eauto. unfold Mem.perm in *. ss. rewrite PMap.gss.
          unfold proj_sumbool. des_ifs; eauto. }
        { exploit Mem.mi_align.
          - eapply Mem.mi_inj. eauto.
          - eauto.
          - ii. exploit H0; eauto. unfold Mem.perm. ss. rewrite PMap.gso; eauto.
          - auto. }
      +
        unfold Mem.perm, proj_sumbool in *. ss.
        repeat rewrite PMap.gsspec in *. des_ifs; eauto.
        * rewrite Mem_setN_in_repeat; eauto; [econs|].
          rewrite Z2Nat.id; nia.
        * zsimpl. destruct (zlt 0 sz).
          { repeat rewrite Mem.setN_outside; cycle 1.
            { right. rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia.
              erewrite unsigned_add in *; eauto.
              - lia.
              - eapply REPRESENTABLE; eauto. lia.
              - eapply REPRESENTABLE; eauto. lia. }
            { rewrite length_list_repeat. rewrite Z2Nat_range. des_ifs; try lia. }
            eauto. }
          { repeat rewrite Mem.setN_outside; cycle 1.
            { rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia. }
            { rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia. }
            eauto. }
        * zsimpl. destruct (zlt 0 sz).
          { repeat rewrite Mem.setN_outside; cycle 1.
            { left. erewrite unsigned_add in *; eauto.
              - lia.
              - eapply REPRESENTABLE; eauto. lia.
              - eapply REPRESENTABLE; eauto. lia. }
            { rewrite length_list_repeat. rewrite Z2Nat_range. des_ifs; try lia. }
            eauto. }
          { repeat rewrite Mem.setN_outside; cycle 1.
            { rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia. }
            { rewrite length_list_repeat.
              rewrite Z2Nat_range. des_ifs; try nia. }
            eauto. }
        * repeat rewrite Mem.setN_outside; cycle 1.
          { rewrite length_list_repeat.
            rewrite Z2Nat_range. des_ifs; try nia. }
          repeat rewrite Mem.setN_outside; cycle 1.
          { rewrite length_list_repeat.
            rewrite Z2Nat_range. des_ifs; try nia. }
          eauto.
        * repeat rewrite Mem.setN_outside; cycle 1.
          { rewrite length_list_repeat.
            rewrite Z2Nat_range. des_ifs; try nia.
            apply NNPP. ii.
            exploit NOOVERLAP; eauto.
            erewrite unsigned_add in *; eauto.
            - lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia.
            - eapply REPRESENTABLE; eauto. lia. }
          eauto.

    - exploit Mem.mi_freeblocks; eauto.
    - exploit Mem.mi_mappedblocks; eauto.
    - ii. unfold Mem.perm in *. ss. apply imply_to_or. i. clarify.
      rewrite PMap.gsspec in *. unfold proj_sumbool in *. des_ifs; ss.
      + ii. exploit NOOVERLAP; eauto. nia.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
      + ii. exploit NOOVERLAP; eauto. nia.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
      + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
      + exploit Mem.mi_no_overlap; try apply H; eauto. i. des; clarify.
    - destruct (peq b0 b); clarify.
      + exploit REPRESENTABLE; eauto. unfold Mem.perm in *. ss. rewrite PMap.gss in *.
        unfold proj_sumbool in *. des_ifs; des; eauto; lia.
      + exploit Mem.mi_representable; eauto.
        unfold Mem.perm in *. ss. rewrite PMap.gso in *; eauto.
    - unfold Mem.perm, proj_sumbool in *. ss.
      rewrite PMap.gsspec in *.
      des_ifs; ss; eauto; (try by exploit Mem.mi_perm_inv; eauto); try by (left; try econs; try lia).
      { left. erewrite unsigned_add in *; eauto.
        - lia.
        - eapply REPRESENTABLE; eauto. lia.
        - eapply REPRESENTABLE; eauto. lia.
        - eapply REPRESENTABLE; eauto. lia. }
      { destruct (zlt 0 sz).
        - left. erewrite unsigned_add in *; eauto.
          + lia.
          + eapply REPRESENTABLE; eauto. lia.
          + eapply REPRESENTABLE; eauto. lia.
          + eapply REPRESENTABLE; eauto. lia.
        - lia. }
      { right. ii. exploit Mem.perm_inject; eauto. i.
        eapply NOPERM; eauto. }
  Qed.

End TOMEMORYC.

Definition junk_inj (m_src0 m_tgt0: mem) (j: meminj) (n: nat): meminj :=
  fun blk =>
    if plt blk (Mem.nextblock m_src0) then j blk
    else
      if plt blk (Mem.nextblock (JunkBlock.assign_junk_blocks m_src0 n)) then
        Some ((blk + (Mem.nextblock m_tgt0) - (Mem.nextblock m_src0))%positive, 0)
      else j blk.

Definition src_junk_val (m_src0 m_tgt0: mem) (n: nat) (v: val): val :=
  match v with
  | Vptr blk ofs =>
    if plt blk (Mem.nextblock m_tgt0) then Vundef
    else if plt blk (Mem.nextblock (JunkBlock.assign_junk_blocks m_tgt0 n)) then
           Vptr (blk + (Mem.nextblock m_src0) - (Mem.nextblock m_tgt0))%positive ofs
         else Vundef
  | _ => v
  end.

Lemma Plt_lemma a b c
      (LE: ~ Plt a b)
  :
    ~ Plt (a + c - b) c.
Proof.
  ii. unfold Plt in *.
  erewrite <- Pos.compare_lt_iff in H.
  erewrite <- Pos.add_compare_mono_r in H. instantiate (1:=b) in H.
  erewrite Pos.sub_add in H; [|xomega].
  rewrite Pos.add_comm in H. apply LE.
  erewrite -> Pos.compare_lt_iff in H.
  xomega.
Qed.

Lemma Plt_lemma2 a b c d
      (LE: ~ Plt a b)
      (LT: Plt a (b + d))
  :
    Plt (a + c - b) (c + d).
Proof.
  unfold Plt in *.
  erewrite <- Pos.compare_lt_iff in LT.
  erewrite <- Pos.add_compare_mono_r in LT. instantiate (1:=c) in LT.
  erewrite <- Pos.sub_compare_mono_r in LT.
  - instantiate (1:=b) in LT.
    erewrite -> Pos.compare_lt_iff in LT.
    rpapply LT. replace (b + d + c)%positive with (c + d + b)%positive.
    + rewrite Pos.add_sub. auto.
    + clear. xomega.
  - clear LT. xomega.
  - clear. xomega.
Qed.

Lemma src_junk_val_inj m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0)
      v
  :
    Val.inject (junk_inj m_src0 m_tgt0 j n) (src_junk_val m_src0 m_tgt0 n v) v.
Proof.
  unfold src_junk_val. des_ifs; eauto.
  econs.
  - unfold junk_inj. des_ifs.
    + apply Plt_lemma in p0; eauto. clarify.
    + instantiate (1:=0).
      replace (b + Mem.nextblock m_src0 - Mem.nextblock m_tgt0 + Mem.nextblock m_tgt0 - Mem.nextblock m_src0)%positive with b; auto.
      clear - n0. rewrite Pos.sub_add.
      * rewrite Pos.add_sub. auto.
      * xomega.
    + exfalso. rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs.
      apply n2. eapply Plt_lemma2 in p; eauto.
  - symmetry. eapply Ptrofs.add_zero.
Qed.

Lemma src_junk_val_junk m_src0 m_tgt0 n v
      (JUNK: JunkBlock.is_junk_value m_tgt0 (JunkBlock.assign_junk_blocks m_tgt0 n) v)
  :
    JunkBlock.is_junk_value
      m_src0 (JunkBlock.assign_junk_blocks m_src0 n)
      (src_junk_val m_src0 m_tgt0 n v).
Proof.
  unfold JunkBlock.is_junk_value, src_junk_val in *. des_ifs. des.
  split.
  - ii. unfold Mem.valid_block in *. eapply Plt_lemma; eauto.
  - unfold Mem.valid_block.
    rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs.
    eapply Plt_lemma2; eauto.
Qed.

Definition set_regset_junk
           (m_src0 m_tgt0: mem) (n: nat)
           (rs0 rs1: Mach.regset) (sg: signature) (mr: mreg) : val :=
  if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
  then src_junk_val m_src0 m_tgt0 n (rs1 mr)
  else rs0 mr.

Lemma junk_inj_incr m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0)
  :
    inject_incr j (junk_inj m_src0 m_tgt0 j n).
Proof.
  ii. unfold junk_inj. des_ifs. exfalso. eapply Mem.valid_block_inject_1 in H; eauto.
Qed.

Lemma assign_junk_blocks_parallel_inject m_src0 m_tgt0 j n
      (INJ: Mem.inject j m_src0 m_tgt0)
  :
    Mem.inject
      (junk_inj m_src0 m_tgt0 j n)
      (JunkBlock.assign_junk_blocks m_src0 n)
      (JunkBlock.assign_junk_blocks m_tgt0 n).
Proof.
  dup INJ. inv INJ. unfold junk_inj.
  econs; [inv mi_inj; econs|..]; i; repeat rewrite JunkBlock.assign_junk_blocks_perm in *.
  - des_ifs; eauto. eapply Mem.perm_valid_block in H0. exfalso. eauto.
  - unfold Mem.range_perm in *. repeat rewrite JunkBlock.assign_junk_blocks_perm in *.
    des_ifs; eauto. apply Z.divide_0_r.
  - des_ifs.
    + eapply memval_inject_incr; [..|eapply junk_inj_incr; eauto].
      exploit mi_memval; eauto. i. rpapply H1; eauto.
      * eapply Mem.unchanged_on_contents; eauto.
        { eapply JunkBlock.assign_junk_blocks_unchanged_on. } ss.
      * eapply Mem.unchanged_on_contents; eauto.
        { eapply JunkBlock.assign_junk_blocks_unchanged_on. } ss.
    + eapply Mem.perm_valid_block in H0. exfalso. eauto.
    + eapply Mem.perm_valid_block in H0. exfalso. eauto.
  - des_ifs.
    + exploit Mem.valid_block_unchanged_on;
        try apply JunkBlock.assign_junk_blocks_unchanged_on.
      * eauto.
      * eauto.
    + destruct (j b) as [[]|] eqn:DELTA; auto. exfalso.
      eapply Mem.valid_block_inject_1 in DELTA; try apply INJ0; eauto.
  - des_ifs.
    + eapply Mem.valid_block_unchanged_on;
        try apply JunkBlock.assign_junk_blocks_unchanged_on; eauto.
    + unfold Mem.valid_block.
      rewrite JunkBlock.assign_junk_blocks_nextblock in *. des_ifs.
      eapply Plt_lemma2; eauto.
    + exfalso. eapply Mem.valid_block_inject_1 in H; eauto.
  - ii. repeat rewrite JunkBlock.assign_junk_blocks_perm in *. des_ifs; eauto.
    + exfalso. eapply Mem.perm_valid_block in H2. eauto.
    + exfalso. eapply Mem.perm_valid_block in H3. eauto.
    + exfalso. eapply Mem.perm_valid_block in H2. eauto.
    + exfalso. eapply Mem.perm_valid_block in H3. eauto.
    + exfalso. eapply Mem.perm_valid_block in H3. eauto.
  - set (Ptrofs.unsigned_range_2 ofs). des_ifs; des; eauto; lia.
  - des_ifs; eauto. zsimpl. exfalso.
    eapply Mem.perm_valid_block in H0.
    unfold Mem.valid_block in *. eapply Plt_lemma; eauto.
Qed.


Section INJINV.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv top1 top1.
Local Instance SimSymbP: SimSymb.class SimMemP := SimSymbDropInv.SimSymbDrop.

Lemma SimSymbDrop_match_globals F `{HasExternal F} V sm0 skenv_src skenv_tgt (p: AST.program F V)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 bot1 skenv_src skenv_tgt)
  :
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0.(SimMemInjInv.minj)).
Proof.
  inv SIMSKE. econs.
  - i. unfold SkEnv.revive in *. exists d_src.
    apply Genv_map_defs_def in FINDSRC. des.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
    des_ifs_safe.
    apply Genv.invert_find_symbol in Heq0.
    exploit SIMDEF; try apply FIND; eauto. i. des. clarify.
    esplits; eauto.
    exploit Genv_map_defs_def_inv; try apply DEFTGT.
    i. rewrite H0.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
    erewrite Genv.find_invert_symbol.
    + rewrite Heq1; eauto.
    + exploit SIMSYMB1; eauto. i. des. eauto.
  - i. unfold SkEnv.revive in *.
    rewrite Genv_map_defs_symb in FINDSRC.
    exploit SIMSYMB2; try apply FINDSRC; eauto.
Qed.

Lemma SimSymbDrop_symbols_inject sm0 ss_link skenv_src skenv_tgt
      (SIMSKELINK: SimSymbDropInv.sim_skenv sm0 ss_link skenv_src skenv_tgt)
  :
    symbols_inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) skenv_src skenv_tgt.
Proof.
  inv SIMSKELINK. econs; esplits; ss; i.
  - unfold Genv.public_symbol, proj_sumbool.
    rewrite PUB in *. des_ifs; ss.
    + exploit SIMSYMB3; eauto. i. des. clarify.
    + exploit SIMSYMB2; eauto. i. des. clarify.
  - exploit SIMSYMB1; eauto. i. des. eauto.
  - exploit SIMSYMB2; eauto.
    { unfold Genv.public_symbol, proj_sumbool in *. des_ifs. eauto. }
    i. des. eauto.
  - unfold Genv.block_is_volatile, Genv.find_var_info.
    destruct (Genv.find_def skenv_src b1) eqn:DEQ.
    + exploit SIMDEF; eauto. i. des. clarify.
      rewrite DEFTGT. eauto.
    + des_ifs_safe. exfalso. exploit SIMDEFINV; eauto.
      i. des. clarify.
Qed.

Lemma match_globals_find_funct F V (ge_src ge_tgt: Genv.t F V) j fptr_src fptr_tgt d
      (FINDSRC: Genv.find_funct ge_src fptr_src = Some d)
      (GENV: meminj_match_globals eq ge_src ge_tgt j)
      (FPTR: Val.inject j fptr_src fptr_tgt)
  :
    Genv.find_funct ge_tgt fptr_tgt = Some d.
Proof.
  inv GENV. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
  inv FPTR. exploit DEFLE; eauto. i. des. clarify. des_ifs.
Qed.

Lemma SimSymbDrop_find_None F `{HasExternal F} V (p: AST.program F V)
      sm0 skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimSymbDropInv.sim_skenv sm0 bot1 skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0.(SimMemInjInv.minj)) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef)
  :
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. exfalso.
  unfold SkEnv.revive in *. ss.
  apply Genv_map_defs_def in Heq. des.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
  des_ifs_safe.
  apply Genv.invert_find_symbol in Heq0.
  inv SIMSKE. ss. inv FPTR; clarify.
  exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
  erewrite Integers.Ptrofs.add_zero in H4. clarify.
    exploit Genv_map_defs_def_inv; try apply DEFSRC.
  i. revert FINDSRC. rewrite H0.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
  erewrite Genv.find_invert_symbol.
  - rewrite Heq1; eauto. i. des_ifs.
  - exploit SIMSYMB3; eauto. i. des.
    assert (blk_src = b1).
    { exploit DISJ; eauto. }
    clarify.
Qed.


Inductive match_states
          (skenv_link_tgt: SkEnv.t)
          (ge_src ge_tgt: genv)
          (sm_init : SimMem.t)
  : nat-> AsmC.state -> AsmC.state -> SimMem.t -> Prop :=
| match_states_intro
    j init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : SimMem.t)
    (AGREE: AsmStepInj.agree j rs_src rs_tgt)
    (AGREEINIT: AsmStepInj.agree j init_rs_src init_rs_tgt)
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MCOMPATINJ: j = sm0.(SimMemInjInv.minj).(SimMemInj.inj))
    (MWF: SimMem.wf sm0)
    (UNDEF: undef_bisim init_rs_src init_rs_tgt)
    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITSRC: wf_init_rs fd.(fn_sig) init_rs_src)
    (WFINITTGT: wf_init_rs fd.(fn_sig) init_rs_tgt)
    (RAWF: Genv.find_funct skenv_link_tgt (init_rs_tgt RA) = None)
    (RSPDELTA: forall blk_src ofs (RSPSRC: init_rs_src RSP = Vptr blk_src ofs),
        exists blk_tgt,
          (j blk_src = Some (blk_tgt, 0)))
  :
    match_states
      skenv_link_tgt
      ge_src ge_tgt sm_init 0
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0
.


Inductive has_footprint
          (skenv_link_src skenv_link_tgt: SkEnv.t)
  :
    AsmC.state -> AsmC.state -> SimMem.t -> Prop :=
| has_foot_print_intro
    blk0 blk1_src blk1_tgt ofs_src ofs_tgt
    (init_rs_src init_rs_tgt rs0_src rs0_tgt: regset)
    m_src m_tgt (sm0: SimMem.t) sg
    (FPTR: rs0_src # PC = Vptr blk0 Ptrofs.zero)
    (SIG: exists skd, skenv_link_src.(Genv.find_funct) (Vptr blk0 Ptrofs.zero)
                      = Some skd /\ SkEnv.get_sig skd = sg)
    (RSPSRC: rs0_src RSP = Vptr blk1_src ofs_src)
    (RSPTGT: rs0_tgt RSP = Vptr blk1_tgt ofs_tgt)
    (FREEABLESRC: Mem.range_perm (sm0.(SimMem.src)) blk1_src (ofs_src.(Ptrofs.unsigned))
                                 (ofs_src.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                 Cur Freeable)
    (FREEABLETGT: Mem.range_perm (sm0.(SimMem.tgt)) blk1_tgt (ofs_tgt.(Ptrofs.unsigned))
                                 (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                 Cur Freeable)
    (VALIDSRC: Mem.valid_block sm0.(SimMem.src) blk1_src)
    (VALIDTGT: Mem.valid_block sm0.(SimMem.tgt) blk1_tgt)

    (MLEEXCLWF: sm0.(SimMemInjInv.minj).(SimMemInj.tgt_external) <2= (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))


  :
    has_footprint skenv_link_src skenv_link_tgt
                  (mkstate init_rs_src (State rs0_src m_src))
                  (mkstate init_rs_tgt (State rs0_tgt m_tgt))
                  sm0
.

Inductive mle_excl
          (skenv_link_src skenv_link_tgt: SkEnv.t)
  : AsmC.state -> AsmC.state -> SimMem.t
    -> SimMem.t -> Prop :=
| mle_excl_intro
    blk0 sg
    blk1_src ofs_src
    (init_rs_src rs0_src: regset) m_unused_src
    blk1_tgt ofs_tgt
    (init_rs_tgt rs0_tgt: regset) m_unused_tgt
    (FPTR: rs0_src # PC = Vptr blk0 Ptrofs.zero)
    (SIG: exists skd, skenv_link_src.(Genv.find_funct) (Vptr blk0 Ptrofs.zero)
                      = Some skd /\ SkEnv.get_sig skd = sg)
    (RSPSRC: rs0_src RSP = Vptr blk1_src ofs_src)
    (RSPTGT: rs0_tgt RSP = Vptr blk1_tgt ofs_tgt)
    (mrel0 mrel1: SimMem.t)
    (INCR: inject_incr mrel0.(SimMemInjInv.minj).(SimMemInj.inj) mrel1.(SimMemInjInv.minj).(SimMemInj.inj))

    (SRCUNCHANGED: Mem.unchanged_on mrel0.(SimMemInjInv.minj).(SimMemInj.src_external) mrel0.(SimMem.src) mrel1.(SimMem.src))

    (TGTUNCHANGED: Mem.unchanged_on
                     ((mrel0.(SimMemInjInv.minj).(SimMemInj.tgt_external))
                        /2\
                        (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))
                     mrel0.(SimMem.tgt) mrel1.(SimMem.tgt))

    (SRCPARENTEQ: mrel0.(SimMemInjInv.minj).(SimMemInj.src_external) = mrel1.(SimMemInjInv.minj).(SimMemInj.src_external))
    (SRCPARENTEQNB: mrel0.(SimMemInjInv.minj).(SimMemInj.src_parent_nb) = mrel1.(SimMemInjInv.minj).(SimMemInj.src_parent_nb))
    (TGTPARENTEQ: mrel0.(SimMemInjInv.minj).(SimMemInj.tgt_external) /2\
                                                 (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))) = mrel1.(SimMemInjInv.minj).(SimMemInj.tgt_external))
    (TGTPARENTEQNB: mrel0.(SimMemInjInv.minj).(SimMemInj.tgt_parent_nb) = mrel1.(SimMemInjInv.minj).(SimMemInj.tgt_parent_nb))
    (FROZEN: SimMemInj.frozen mrel0.(SimMemInjInv.minj).(SimMemInj.inj) mrel1.(SimMemInjInv.minj).(SimMemInj.inj) (mrel0.(SimMemInjInv.minj).(SimMemInj.src_parent_nb))
                                                                          (mrel0.(SimMemInjInv.minj).(SimMemInj.tgt_parent_nb)))

    (MAXSRC: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(SimMem.src) b)
        (UNFREE: ~ brange blk1_src (ofs_src.(Ptrofs.unsigned)) (ofs_src.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                   b ofs)
      ,
        <<MAX: Mem.perm mrel1.(SimMem.src) b ofs Max <1= Mem.perm mrel0.(SimMem.src) b ofs Max>>)
    (MAXTGT: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(SimMem.tgt) b)
        (UNFREE: ~ brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                   b ofs)
      ,
        <<MAX: Mem.perm mrel1.(SimMem.tgt) b ofs Max <1= Mem.perm mrel0.(SimMem.tgt) b ofs Max>>)
    (MINVEQSRC: SimMemInjInv.mem_inv_src mrel0 = SimMemInjInv.mem_inv_src mrel1)
    (MINVEQTGT: SimMemInjInv.mem_inv_tgt mrel0 = SimMemInjInv.mem_inv_tgt mrel1)
  :
    mle_excl
      skenv_link_src skenv_link_tgt
      (mkstate init_rs_src (State rs0_src m_unused_src))
      (mkstate init_rs_tgt (State rs0_tgt m_unused_tgt))
      mrel0 mrel1
.




Lemma asm_inj_inv_drop
      (asm: Asm.program)
      (WF: Sk.wf asm.(module))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1).
    econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with
      (match_states :=
         match_states
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm))
      (match_states_at := top4)
      (has_footprint := has_footprint skenv_link_src skenv_link_tgt)
      (sidx := unit)
      (mle_excl := mle_excl skenv_link_src skenv_link_tgt); ss; eauto; ii.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - inv MLE. inv MLE0. inv FOOT. inv MLEEXCL.
    ss. econs; ss; eauto; [econs; ss; eauto|..].
    + etrans; eauto.
    + eapply Mem.unchanged_on_trans; eauto.
      rewrite SRCPARENTEQ. eauto.
    + des. des_ifs. rewrite FPTR in *. rewrite RSPTGT in *. clarify.
      eapply Mem.unchanged_on_trans; eauto.
      rewrite TGTPARENTEQ in *.
      eapply Mem.unchanged_on_implies; eauto.
      ii. ss. splits; eauto.
    + etrans; eauto.
    + etrans; eauto.
    + etrans; eauto.
      rewrite TGTPARENTEQ in *. des. des_ifs. clarify.
      rewrite FPTR in *. clarify.
      rewrite RSPTGT in *. clarify.
      clear - TGTPARENTEQ0 MLEEXCLWF.
      extensionality blk.
      extensionality ofs.
      rewrite <- TGTPARENTEQ0.
      eapply propositional_extensionality. split; auto; tauto.
    + etrans; eauto.
    + inv FROZEN. inv FROZEN0.
      econs; ss; eauto.
      i. des.
      destruct (SimMemInj.inj sm1.(SimMemInjInv.minj) b_src) eqn:EQ.
      * destruct p.
        exploit NEW_IMPLIES_OUTSIDE; eauto.
        eapply INCR0 in EQ. clarify.
      * exploit NEW_IMPLIES_OUTSIDE0; eauto.
        rewrite SRCPARENTEQNB.
        rewrite TGTPARENTEQNB.
        eauto.

    + ii. des. des_ifs. clarify.
      destruct (classic (brange blk1_src0 (Ptrofs.unsigned ofs_src0)
                                (Ptrofs.unsigned ofs_src0 + 4 * size_arguments (SkEnv.get_sig skd)) b ofs)).
      {
        unfold brange in *. des. clarify.
        eapply Mem.perm_cur. des_ifs.
        rewrite RSPSRC in *. clarify.
        rewrite FPTR in *. clarify.
        exploit FREEABLESRC; splits; eauto.
        eapply Mem.perm_implies; eauto. econs.
      }
      eapply MAXSRC; eauto.
      eapply MAXSRC0; eauto.
      inv SRCUNCHANGED.
      unfold Mem.valid_block.
      eapply Plt_Ple_trans; eauto.
    + ii. des. des_ifs. clarify.
      destruct (classic (brange blk1_tgt0 (Ptrofs.unsigned ofs_tgt0)
                                (Ptrofs.unsigned ofs_tgt0 + 4 * size_arguments (SkEnv.get_sig skd)) b ofs)).
      {
        unfold brange in *. des. clarify.
        eapply Mem.perm_cur. des_ifs.
        rewrite RSPTGT in *. clarify.
        rewrite FPTR in *. clarify.
        exploit FREEABLETGT; splits; eauto.
        eapply Mem.perm_implies; eauto. econs.
      }
      eapply MAXTGT; eauto.
      eapply MAXTGT0; eauto.
      inv TGTUNCHANGED.
      unfold Mem.valid_block.
      eapply Plt_Ple_trans; eauto.
    + etrans; eauto.
    + etrans; eauto.

  - exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv SIMARGS. destruct args_src, args_tgt, sm_arg. destruct minj. ss. clarify.
    inv INITTGT. ss. inv TYP. inv MWF. inv WF0. ss.
    inv STORE. des.
    exploit store_arguments_parallel_inject; [..| eauto |]; eauto.
    + eapply typify_has_type_list; eauto.
    + eapply inject_list_typify_list; try eassumption.
      erewrite inject_list_length; eauto.
    + i. des.

      eexists (AsmC.mkstate (((to_pregset (set_regset_junk m_src1 m0 n rs_src (to_mregset rs) (fn_sig fd))) # PC <- fptr)
                               # RA <- (src_junk_val m_src1 m0 n (rs RA)))
                            # RSP <- (Vptr (Mem.nextblock src) Ptrofs.zero)
                            (Asm.State _ (JunkBlock.assign_junk_blocks m_src1 n))). econs; ss.

      assert (INCR: inject_incr
                      inj
                      (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0)).
      { ii. unfold update_meminj. des_ifs.
        exfalso. inv PUBLIC. exploit mi_freeblocks.
        - eapply Plt_strict.
        - i. clarify.
      }

      assert (MLE:
                SimMemInj.le'
                  (SimMemInj.mk
                     src tgt inj src_external tgt_external
                     src_parent_nb tgt_parent_nb)
                  (SimMemInj.mk
                     (JunkBlock.assign_junk_blocks m_src1 n)
                     (JunkBlock.assign_junk_blocks m0 n)
                     (junk_inj m_src1 m0 (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0) n)
                     src_external tgt_external
                     src_parent_nb tgt_parent_nb)).
      { econs; ss; eauto.
        - etrans.
          + eauto.
          + eapply junk_inj_incr; eauto.
        - etrans.
          + i. exploit store_arguments_unchanged_on; try apply ARGTGT; eauto. i. eapply Mem.unchanged_on_implies; eauto. ss.
          + eapply Mem.unchanged_on_implies;
              try apply JunkBlock.assign_junk_blocks_unchanged_on; ss.
        - etrans.
          + i. exploit store_arguments_unchanged_on; try apply H; eauto.
            i. eapply Mem.unchanged_on_implies; eauto. ss.
          + eapply Mem.unchanged_on_implies;
              try apply JunkBlock.assign_junk_blocks_unchanged_on; ss.
        - econs; ss; eauto. i. des.
          unfold junk_inj, update_meminj in *. des_ifs; ss. split.
          + red. etrans; eauto. eapply store_arguments_unchanged_on in ARGTGT.
            eapply Mem.unchanged_on_nextblock in ARGTGT. clear - ARGTGT n0. xomega.
          + red. etrans; eauto. eapply store_arguments_unchanged_on in H.
            eapply Mem.unchanged_on_nextblock in H. clear - H n0. etrans; eauto.
            clear - n0. hexploit Plt_lemma; eauto. instantiate (1:=Mem.nextblock m0).
            remember (b_src + Mem.nextblock m0 - Mem.nextblock m_src1)%positive.
            clear Heqp. xomega.
        - ii. erewrite JunkBlock.assign_junk_blocks_perm in *.
          eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
          eapply unchanged_on_perm in PR; eauto.
        - ii. erewrite JunkBlock.assign_junk_blocks_perm in *.
          eapply store_arguments_unchanged_on in H. inv H.
          eapply unchanged_on_perm in PR; eauto. }

      esplits; eauto.
      {
        econs; ss; eauto.
        - instantiate (1:=fd). inv SAFESRC. ss. des.
          exploit match_globals_find_funct; eauto. i.
          setoid_rewrite FINDF in H1. clarify.

        - econs; eauto.
          erewrite inject_list_length; eauto.
        - econs; eauto.
          inv ARGTGT.
          econs; try eassumption; eauto.
          eapply extcall_arguments_same; eauto. i.
          unfold Pregmap.set, to_mregset, to_pregset, to_preg.
          erewrite to_preg_to_mreg.
          des_ifs; clarify; ss.
          * unfold preg_of in *; des_ifs.
          * unfold preg_of in *; des_ifs.
          * unfold preg_of in *; des_ifs.
          * unfold set_regset_junk. des_ifs; clarify; eauto.
            exfalso. eapply Loc.notin_not_in in n3. eauto.

        - assert (JUNK: JunkBlock.is_junk_value m0 (JunkBlock.assign_junk_blocks m0 n) (rs RA)).
          { apply NNPP. ii. exploit PTRFREE; eauto. i. des; ss. }
          split.
          + unfold Pregmap.set, src_junk_val. des_ifs.
          + unfold Pregmap.set, src_junk_val. des_ifs; ss; des; eauto.

        - unfold Pregmap.set. des_ifs. unfold src_junk_val, JunkBlock.is_junk_value in *.
          des_ifs. ii. clarify. apply n1.
          assert (PLT: Plt (b + Mem.nextblock m_src1 - Mem.nextblock m0) (Mem.nextblock m_src1)).
          { eapply Plt_Ple_trans; eauto.
            inv SIMSKENV. inv SIMSKELINK. ss.
            eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
            clear - SRCLE BOUNDSRC unchanged_on_nextblock. xomega. }
          exfalso. eapply Plt_lemma; eauto.
        - i. unfold Pregmap.set in *. des_ifs; eauto.
          { exploit PTRFREE.
            - ii. eapply src_junk_val_junk in H1; eauto.
            - i. des; clarify. }
          left.
          unfold to_pregset, set_regset_junk, to_mregset in *. des_ifs; ss.
          + exploit PTRFREE.
            * ii. eapply src_junk_val_junk in H1; eauto.
            * i. erewrite to_mreg_some_to_preg in *; eauto. des; ss.
              clarify. esplits; eauto.
          + esplits; eauto. erewrite loc_notin_not_in in n3. tauto.
      }
      { instantiate (1:=SimMemInjInv.mk _ _ _). econs; ss; eauto. }
      {
        assert (AGREE0 :
                  AsmStepInj.agree (junk_inj m_src1 m0
                                             (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0) n)
                                   ((((to_pregset (set_regset_junk m_src1 m0 n rs_src (to_mregset rs) (fn_sig fd)))
                                        # PC <- fptr) # RA <- (src_junk_val m_src1 m0 n (rs RA))) # RSP <-
                                                                                                  (Vptr (Mem.nextblock src) Ptrofs.zero)) rs).
        { ii.
          unfold Pregmap.set, to_mregset, to_pregset, to_preg.
          des_ifs; ss; eauto.
          - eapply val_inject_incr; try apply junk_inj_incr; eauto.
            unfold update_meminj. rewrite H0. econs; des_ifs. ss.
          - eapply src_junk_val_inj; eauto.
          - eapply val_inject_incr; [|eauto].
            etrans; eauto. apply junk_inj_incr; eauto.
          - unfold set_regset_junk. des_ifs.
            + erewrite to_mreg_preg_of; eauto. eapply src_junk_val_inj; eauto.
            + eapply val_inject_incr; [|eauto].
              * apply junk_inj_incr; eauto.
              * specialize (AGREE m). unfold to_mregset in *.
                erewrite to_mreg_preg_of in *; eauto. }

        assert (MWF: SimMemInj.wf'
                       {|
                         SimMemInj.src := JunkBlock.assign_junk_blocks m_src1 n;
                         SimMemInj.tgt := JunkBlock.assign_junk_blocks m0 n;
                         SimMemInj.inj := junk_inj m_src1 m0
                                                   (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0) n;
                         SimMemInj.src_external := src_external;
                         SimMemInj.tgt_external := tgt_external;
                         SimMemInj.src_parent_nb := src_parent_nb;
                         SimMemInj.tgt_parent_nb := tgt_parent_nb |}).
        {
          econs; ss; auto.
          + eapply assign_junk_blocks_parallel_inject; eauto.
          + ii. unfold SimMemInj.src_private, SimMemInj.tgt_private, update_meminj, junk_inj in *. ss.
            eapply SRCEXT in PR. des.
            splits; eauto.
            * unfold loc_unmapped. des_ifs; ss; exfalso.
              { eapply Plt_strict. eauto. }
              { apply n0. clear p. eapply Plt_Ple_trans; eauto.
                inv ARGTGT. eapply Mem.nextblock_alloc in ALC.
                rewrite ALC in *. rewrite <- NB. clear. xomega. }
              { apply n0. inv ARGTGT. rewrite <- NB.
                apply Mem.nextblock_alloc in ALC. rewrite ALC in *. clear. xomega. }
            * eapply Mem.valid_block_unchanged_on; try apply JunkBlock.assign_junk_blocks_unchanged_on.
              exploit store_arguments_unchanged_on; try apply ARGTGT; eauto. i.
              eapply Mem.valid_block_unchanged_on; eauto.
          + ii. unfold SimMemInj.src_private, SimMemInj.tgt_private, junk_inj, update_meminj in *. ss.
            eapply TGTEXT in PR. des.
            splits; eauto.
            * unfold loc_out_of_reach in *.
              ii. des_ifs; ss.
              { eapply Plt_strict. eauto. }
              { rewrite JunkBlock.assign_junk_blocks_perm in *.
                eapply PR; eauto.
                eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
                eapply unchanged_on_perm; eauto.
                eapply Mem.valid_block_inject_1; eauto. }
              { rewrite JunkBlock.assign_junk_blocks_perm in *.
                eapply Mem.perm_valid_block in H2. eauto. }
              { apply n0. inv ARGTGT. rewrite <- NB.
                apply Mem.nextblock_alloc in ALC. rewrite ALC in *. clear. xomega. }
              { rewrite JunkBlock.assign_junk_blocks_perm in *.
                eapply Mem.perm_valid_block in H2. eauto. }
            * eapply Mem.valid_block_unchanged_on in PR0; cycle 1;
                try eapply store_arguments_unchanged_on; eauto.
              eapply Mem.valid_block_unchanged_on;
                try apply JunkBlock.assign_junk_blocks_unchanged_on; eauto.
          + etrans; eauto. etrans.
            * eapply Mem.unchanged_on_nextblock.
              eapply store_arguments_unchanged_on. eauto.
            * eapply Mem.unchanged_on_nextblock.
              apply JunkBlock.assign_junk_blocks_unchanged_on.
          + etrans; eauto. etrans.
            * eapply Mem.unchanged_on_nextblock.
              eapply store_arguments_unchanged_on. eauto.
            * eapply Mem.unchanged_on_nextblock.
              apply JunkBlock.assign_junk_blocks_unchanged_on. }

        econs; ss.
        - exploit SimMemInjInv.le_inj_wf_wf; eauto; ss.

        - unfold to_pregset, set_regset, Pregmap.set. ii.
          rewrite to_preg_to_mreg in *. des_ifs.
          + apply f_equal with (f:=to_mreg) in e.
            rewrite to_preg_to_mreg in  e. ss.
          + apply f_equal with (f:=to_mreg) in e.
            rewrite to_preg_to_mreg in  e. ss.
          + unfold set_regset_junk in *. des_ifs.
            * assert (JUNK: JunkBlock.is_junk_value m0 (JunkBlock.assign_junk_blocks m0 n) (rs (to_preg r))).
              { apply NNPP. ii. exploit PTRFREE; eauto. i. des; clarify.
                erewrite to_preg_to_mreg in MR. clarify.
                eapply Loc.notin_not_in; eauto. }
              unfold src_junk_val in *. des_ifs_safe.
              unfold JunkBlock.is_junk_value in *.
              unfold to_mregset in *. rewrite Heq in *.
              unfold Mem.valid_block in *. exfalso. des. des_ifs.
            * erewrite loc_notin_not_in in n3. apply NNPP in n3.
              apply loc_args_callee_save_disjoint in n3. exfalso. eauto.
        - instantiate (1:=fd). inv SAFESRC. ss. des.
          exploit match_globals_find_funct; eauto. i.
          setoid_rewrite FINDF in H1. clarify.

        - econs; ss.
          + unfold Pregmap.set. des_ifs. unfold src_junk_val. des_ifs.
          + unfold Pregmap.set. des_ifs. unfold src_junk_val.
            assert (JUNK: JunkBlock.is_junk_value m0 (JunkBlock.assign_junk_blocks m0 n) (rs RA)).
            { apply NNPP. ii. exploit PTRFREE; eauto. i. des; clarify. }
            clear - RADEF JUNK.
            unfold JunkBlock.is_junk_value, Mem.valid_block in *. des_ifs; des; eauto.

        - econs; ss. ii. congruence.

        - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
          eapply Genv.genv_defs_range in Heq0. exfalso. eapply RANOTFPTR; eauto.
        - unfold Pregmap.set. des_ifs. ii. clarify. unfold junk_inj, update_meminj.
          des_ifs; eauto.
      }

  - exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv TYP. inv SIMARGS. ss.
    eapply asm_initial_frame_succeed; eauto.
    + apply inject_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + exploit match_globals_find_funct; eauto.

  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. cinv INJPC.
    assert (delta = 0).
    { clear EXTERNAL. unfold Genv.find_funct_ptr in *. des_ifs.
      inv SIMSKELINK.
      exploit SIMDEF; eauto.
      i. des. eauto. }
    clarify. psimpl. ss.
    exploit extcall_arguments_inject; eauto.
    { inv MWF. inv WF0. eauto. }
    i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

    exploit Mem_free_parallel'; eauto.
    { inv MWF. eauto. } i. des.
    destruct sm0.
    exploit SimMemInjInv.le_inj_wf_wf; eauto; ss. i.
    eexists (Args.mk (Vptr b2 _) _ _).
    esplits; eauto; ss; i.
    + econs; auto.
      * exploit SimSymbDrop_find_None; try eassumption.
        { unfold Genv.find_funct. des_ifs. eauto. }
        { clarify. }
        { rewrite <- H2. ss. }
      * esplits; eauto.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv SIMSKELINK.
        exploit SIMDEF; try apply Heq1; eauto. i. des. clarify.
        rewrite DEFTGT. eauto.
      * instantiate (1:=Ptrofs.add ofs (Ptrofs.repr delta)).
        destruct (zlt 0 (size_arguments (SkEnv.get_sig skd))).
        { inv MWF. inv WF0. exploit Mem.mi_representable; eauto.
          - right.
            instantiate (1:=Ptrofs.add ofs (Ptrofs.repr (4 * size_arguments (SkEnv.get_sig skd)))).
            eapply Mem.perm_cur.
            eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
            rewrite unsigned_add.
            + clear - ARGSRANGE l. lia.
            + clear- ARGSRANGE.
              set (size_arguments_above (SkEnv.get_sig skd)).
              set (Ptrofs.unsigned_range_2 ofs). lia.
          - repeat rewrite unsigned_add.
            + lia.
            + exploit Mem.mi_representable; eauto. left.
              eapply Mem.perm_cur.
              eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
              clear - ARGSRANGE l. lia.
            + clear- ARGSRANGE.
              set (size_arguments_above (SkEnv.get_sig skd)).
              set (Ptrofs.unsigned_range_2 ofs). lia. }
        { set (Ptrofs.unsigned_range_2 (Ptrofs.add ofs (Ptrofs.repr delta))). lia. }
      * eauto.
      * eauto.
      * clear - AGREE TPTR RADEF. splits.
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      * inv MWF. inv WF0. i. erewrite Mem.address_inject; eauto; cycle 1.
        { eapply Mem.free_range_perm; eauto.
          set (size_chunk_pos chunk). lia. }
        eapply Z.divide_add_r; eauto.
        inv PUBLIC.
        inv mi_inj. exploit mi_align; eauto.
        eapply Mem.free_range_perm in FREE.
        intros ofs0 RANGE.
        exploit FREE; eauto.
        -- instantiate (1:=ofs0).
           instantiate (1:=Ptrofs.unsigned ofs) in RANGE.
           nia.
        -- i.
           eapply Mem.perm_cur_max.
           eapply Mem.perm_implies; eauto. econs.
      * eauto.
    + econs; s; eauto.
      * eapply val_inject_incr; cycle 1; eauto.
        inv MLE. eauto.
      * eapply val_inject_list_incr; cycle 1; eauto.
        inv MLE. eauto.
    + inv MWF. inv WF0. econs; ss; eauto.
      * eapply Mem.free_range_perm in FREE. eauto.
      * eapply Mem.free_range_perm in FREETGT. auto.
      * eapply Mem.valid_block_inject_1; eauto.
      * eapply Mem.valid_block_inject_2; eauto.
      * ii. unfold brange in *. ss. des. clarify.
        eapply TGTEXT in PR.
        unfold SimMemInj.tgt_private, loc_out_of_reach in *. ss. des.
        eapply PR; eauto.
        exploit Mem.free_range_perm; try apply FREE; eauto.
        -- instantiate (1:=x1 - delta).
           dup H5. erewrite Mem.address_inject in H5; eauto; cycle 1.
           { eapply Mem.free_range_perm; eauto. lia. }
           erewrite Mem.address_inject in H6; eauto; cycle 1.
           { eapply Mem.free_range_perm; eauto. lia. }
           lia.
        -- i. eapply Mem.perm_cur_max; eauto.
           eapply Mem.perm_implies; eauto. econs.

  - (** ******************* after external **********************************)
    destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC.
    inv SIMRET.
    cinv (AGREE RSP); rewrite RSRSP in *; ss.
    des.
    unfold Genv.find_funct in FINDF, SIG. des_ifs. ss.

    destruct sm_arg, sm0, sm_ret. ss.
    inv MWF0. inv WF0. inv MWF. inv WF0. rewrite MEMSRC in *.
    assert (PERMRET: forall ofs, Mem.perm (SimMemInj.src minj1) blk ofs Max <1= Mem.perm (SimMemInj.src minj0) blk ofs Max).
    { inv MLE. inv MLE1. inv MLE0. inv MLE. ss. ii. eapply MAXSRC; eauto.
      - eapply Mem.valid_block_inject_1; eauto.
      - eapply MAXSRC0; eauto.
        + eapply Mem.valid_block_unchanged_on; eauto.
          eapply Mem.valid_block_inject_1; eauto. }
    exploit Mem_unfree_parallel_inject; eauto.
    { inv MLE0. inv MLE1. inv MLE. inv MLE0. ss. eauto. }
    { inv HISTORY. ss. ii. eapply Mem.mi_align; eauto.
      - eapply Mem.mi_inj; eauto.
      - ii. exploit PERM; eauto. i. des.
        + instantiate (1:=p). eapply Mem.perm_implies; cycle 1.
          { instantiate (1:=Freeable). econs. }
          inv CALLSRC. rewrite RSRSP in *. clarify.
          eapply Mem.perm_cur. exploit Mem.free_range_perm; eauto.
          des. unfold Genv.find_funct in SIG, SIG0, EXTERNAL.
          des_ifs. rewrite Heq in *. clarify.
        + exploit PERMRET; eauto. }
    { inv HISTORY. ss. inv MLE. inv MLE0. inv CALLSRC.
      rewrite RSRSP in *. unfold Genv.find_funct in SIG, SIG0, EXTERNAL.
      des_ifs. rewrite Heq in *.
      des; clarify; ss. hexploit Mem.free_range_perm; try eassumption. i.
      eapply Mem.mi_representable; try apply PUBLIC; eauto. des.
      - exploit PERMRET; eauto.
      - exploit PERMRET; eauto.
      - left. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
      - right. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs. }
    { inv MLE0. inv MLE1. cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      inv HISTORY. inv CALLTGT. ss. des.
      unfold Genv.find_funct in SIG, SIG0, EXTERNAL. des_ifs.
      rewrite RSP in *. inv SIMARGS. ss. clarify.
      ii. apply MAXTGT in H; cycle 1.
      { inv MLE. inv MLE1. eapply Mem.valid_block_unchanged_on; eauto.
        eapply Mem.valid_block_inject_2; eauto. }
      exploit Mem_free_noperm; eauto. inv MATCH. ss.
      assert (skd = skd0); [|clarify; lia].
      inv SIMSKENV. ss. inv SIMSKELINK. clear - Heq FPTR AGREE0 SIMDEF SIG SIG0.
      unfold Genv.find_funct_ptr in *. des_ifs_safe.
      cinv (AGREE0 PC); rewrite Heq in *; clarify.
      rewrite FPTR in *. clarify.
      exploit SIMDEF; eauto. i. des. clarify. }
    i. des. rewrite <- MEMSRC in *.

    esplits; ss.
    + instantiate (1:=SimMemInjInv.mk
                        (SimMemInj.mk
                           m1 m2' (SimMemInj.inj minj1) _ _ _ _) _ _).
      econs; ss; eauto.
      * eapply Mem.unchanged_on_implies.
        { rewrite <- MEMSRC. eapply Mem_unfree_unchanged_on; eauto. }
        ii. unfold brange in *. des. clarify.
        inv MWFAFTR. ss. inv WF0. ss.
        eapply SRCEXT1 in H.
        unfold SimMemInj.src_private, loc_unmapped in *. ss. des.
        inv MLE. inv MLE1. inv MLE0. inv MLE. ss.
        eapply INCR in H2.
        eapply INCR0 in H2.
        rewrite H2 in *. clarify.
      * eapply Mem.unchanged_on_implies.
        { rewrite <- MEMTGT in *. eapply Mem_unfree_unchanged_on; eauto. }
        ii. unfold brange in *. des. clarify.
        eapply H6. split; auto.
      * econs; ss; eauto. i. des. clarify.
      * ii. exploit Mem_unfree_unchanged_on; try apply UNFREE; eauto. i.
        inv H. rewrite MEMSRC in *.
        eapply unchanged_on_perm; eauto.
      * ii. exploit Mem_unfree_unchanged_on; try apply H; eauto. i.
        inv H.
        eapply unchanged_on_perm; eauto.
    + i. ss. splits.
      {
        instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
        - instantiate (1:=SkEnv.get_sig skd). esplits; eauto.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
          cinv (AGREE PC); rewrite Heq in *; clarify.
          inv SIMSKENV. ss. inv SIMSKELINK. exploit SIMDEF; eauto.
          i. des. clarify. des_ifs.
        - eauto.
        - rewrite MEMTGT in *. instantiate (1:=m2').
          rewrite <- UNFREE0. f_equal.
      }

      {
        econs; try assumption.
        - instantiate (1:=SimMemInj.inj minj1).
          ii. inv MLE. inv MLE2. inv MLE0. inv MLE. ss.
          unfold set_pair, Pregmap.set, loc_external_result, map_rpair.
          des_ifs; ss; eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
          -- eapply Val.loword_inject. eauto.
          -- eapply Val.hiword_inject. eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
        - ii. inv MLE. inv MLE2. inv MLE0. inv MLE. ss. eauto.
        - eauto.
        - ss.
        - ss.
        - unfold SimMemInj.unlift' in *. ss.
          econs; ss; eauto; [econs; ss; eauto |..].
           + inv MWFAFTR. inv WF0. ss.
            rewrite MEMSRC in *.
            unfold SimMemInj.src_private in *. ss.
            etrans; eauto.
            ii; splits; des; eauto.
            clear - UNFREE PR0.
            eapply Mem.valid_block_unchanged_on; eauto.
            eapply Mem_unfree_unchanged_on; eauto.
          + unfold SimMemInj.lift' in *. inv HISTORY. ss.
            rewrite MEMSRC in *.
            (* clear - MLE MLE0 MLE1 MWF MWF0 MWF1 MLEAFTR MWFAFTR UNFREE H CALLSRC CALLTGT H2. *)
            ii. unfold SimMemInj.tgt_private, loc_out_of_reach. ss. splits.
            *
              (* ii. des. eapply PR0. *)
              (* inv MLE0. inv MLE3. inv MWF. inv WF0. ss. *)
              (* eapply TGTEXT1 in PR. *)

              (* assert (NINV: ~ mem_inv_tgt x0). *)
              (* { *)
              (*   (* rewrite MINVEQTGT. *) *)
              (*   ii. *)
              (*   inv MLE1. ss. inv MLE0. ss. *)
              (*   exploit INVRANGETGT0; eauto. i. des. *)
              (*   exploit H4; eauto. *)
              (*   clear - H0. *)

              (* assert (PR1: SimMemInj.tgt_private minj1 x0 x1). *)
              (* { inv MLE1. ss. inv MLE0. ss. *)
              (*   clear - TGTPARENTEQ TGTEXT0 PR. *)
              (*   rewrite <- TGTPARENTEQ in *. *)


              (* clear - TGTEXT0 PR. *)
              (* eapply TGTEXT0 in PR. *)
              (* unfold SimMemInj.tgt_private in *. des. *)
              (* unfold loc_out_of_reach in *. *)
              (* hexploit PR; eauto. *)

              (* ii. *)
              (* dup UNFREE. eapply Mem_unfree_unchanged_on in UNFREE. inv UNFREE. *)

              (* apply NNPP. ii. exploit unchanged_on_perm; eauto. *)
              (* -- instantiate (1:=x1-delta0). instantiate (1:=b1). *)
              (*    ii. eapply H4. *)
              (*    unfold brange in *. des. clarify. split. *)
              (*    ++ inv MLE1. ss. exploit INCR0; eauto. i. clarify. *)
              (*    ++ inv MLE1. ss. dup H2. apply INCR0 in H2. rewrite H2 in *. clarify. *)
              (*       inv CALLSRC. inv MATCH. rewrite RSP in *. clarify. *)
              (*       erewrite Mem.address_inject; try eapply PUBLIC; eauto. *)
              (*       { clear - H6 H7. lia. } *)
              (*       { eapply Mem.free_range_perm; eauto. *)
              (*         des. clarify. *)
              (*         assert (skd = skd0); [|clarify; lia]. *)
              (*         inv SIMSKENV. ss. inv SIMSKELINK. clear - Heq FPTR AGREE0 SIMDEF SIG SIG0. *)
              (*         unfold Genv.find_funct_ptr in *. des_ifs_safe. *)
              (*         cinv (AGREE0 PC); rewrite Heq in *; clarify. } *)
              (* -- eapply Mem.valid_block_inject_1; eauto. *)
              (* -- i. des. eauto. *)

              admit "wait".

            * unfold SimMemInj.valid_blocks, Mem.valid_block.
              erewrite <- Mem_nextblock_unfree; eauto. des.
              inv MLE0. inv MLE3. ss. inv TGTUNCHANGED. eapply Plt_Ple_trans; eauto.
              inv MWF. inv WF0. eapply TGTEXT1 in PR. unfold SimMemInj.tgt_private in *. des. eauto.
          + inv MWFAFTR. inv WF0. ss.
            rewrite MEMSRC in *.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
          + inv MWFAFTR. inv WF0. ss.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
          + ii. admit "wait".
          + ii. admit "wait".
        - unfold Genv.find_funct. rewrite Heq0. des_ifs. eauto.
        - eauto.
        - eauto.
        - ii. exploit RSPDELTA; eauto. i. des.
          inv MLE1. inv MLE2. ss. apply INCR in H. eexists; eauto.
      }

  - (** ******************* final **********************************)

    exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv MATCH. inv FINALSRC. inv MWF.

    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
    destruct sm0.
    exploit Mem_free_parallel'; eauto.
    { instantiate (3:=Ptrofs.zero). zsimpl. psimpl. eauto. }
    i. des.
    exploit SimMemInjInv.le_inj_wf_wf; eauto; ss.
    { econs; eauto. }
    { ss. }
    { ss. } intros MINVWF.

    assert (delta = 0).
    { exploit RSPDELTA; eauto. i. des. clarify. }
    clarify. ss. zsimpl.

    esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H UNDEF.
        inv WFINITSRC.
        eapply lessdef_commute; eauto.
      * des. esplits; eauto.
        eapply match_globals_find_funct; eauto.
      * unfold external_state in *.
        des_ifs_safe. exfalso.
        cinv (AGREE PC); try rewrite Heq in *; clarify; eauto.
        { des_ifs. clear RANOTFPTR.
          unfold Genv.find_funct, Genv.find_funct_ptr in INITSIG, Heq2, Heq0.
          des_ifs_safe.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq3. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq5.
          inv SIMSKENV. inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
          exploit Genv_map_defs_def_inv; try apply DEFSRC.
          i. revert Heq2. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq6; eauto. clarify.
          - exploit SIMSYMB3; eauto. i. des.
            rewrite BLKSRC. f_equal.
            exploit DISJ; eauto. }
         { rewrite <- H2 in *. inv WFINITSRC. eauto. }
      * inv WFINITSRC. inv WFINITTGT.
        unfold Val.has_type in TPTR. des_ifs.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
        -- ss. clear RANOTFPTR. des_ifs.
           cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
      * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        cinv (AGREE RSP); rewrite RSRSP in *; clarify.
    + econs; ss. eapply val_inject_incr; cycle 1; eauto.
      inv MLE. eauto.
    + econs; ss.

  - left; i.
    esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + exists O.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        cinv MWF. inv SIMSKENV. destruct st0. ss. clarify.

        exploit asm_step_preserve_injection; eauto.
        { exploit SimSymbDrop_match_globals; eauto.
          intros MATCH. inv MATCH. econs; ss; i; eauto.
          exploit DEFLE; eauto. i. des. clarify. esplits; eauto. }
        { eapply symbols_inject_weak_imply.
          eapply SimSymbDrop_symbols_inject; eauto. }
        { inv WF0. eauto. }

        i. des.
        eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).

        exploit SimMemInjInv.unchanged_on_mle; eauto.
        { ii. eapply asm_step_max_perm; eauto. }
        { ii. eapply asm_step_max_perm; eauto. }
        i. des.

        esplits; eauto.
        - left. econs; cycle 1.
          + apply star_refl.
          + symmetry. apply E0_right.
          + econs.
            * apply AsmC.modsem_determinate.
            * econs; ss; eauto.
        - econs; ss; eauto.
          + eapply agree_incr; eauto.
          + i. exploit RSPDELTA; eauto. i. des. esplits; eauto.
      }
Qed.

End INJINV.
