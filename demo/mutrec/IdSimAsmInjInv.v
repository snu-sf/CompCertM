Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemInjInv.
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
Require Import IdSimExtra.

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

(* TODO move it to AsmExtra *)
Lemma asm_initial_frame_succeed (asm: Asm.program) args skenv_link fd
      (ARGS: Datatypes.length args.(Args.vs) = Datatypes.length (sig_args fd.(fn_sig)))
      (SIZE: 4 * size_arguments fd.(fn_sig) <= Ptrofs.max_unsigned)
      (SIG: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig asm)) asm) (args.(Args.fptr)) =
            Some (Internal fd))
  :
    exists st_init, initial_frame skenv_link asm args st_init.
Proof.
  exploit StoreArguments.store_arguments_progress; eauto.
  { eapply typify_has_type_list; eauto. }
  instantiate (1:=0%nat). instantiate (1:=args.(Args.m)). i. des. destruct args. ss.
  eexists (AsmC.mkstate ((to_pregset (set_regset_undef rs fd.(fn_sig)))
                           #PC <- fptr
                           #RA <- Vnullptr
                           #RSP <- (Vptr (Mem.nextblock m) Ptrofs.zero))
                        (Asm.State _ m2)).
  inv STR.
  econs; eauto; ss.
  - econs; ss. econs; eauto.
    eapply extcall_arguments_same; eauto.
    i. unfold to_mregset, to_pregset.
    rewrite Pregmap.gso; cycle 1.
    { unfold to_preg, preg_of. des_ifs. }
    rewrite Pregmap.gso; cycle 1.
    { unfold to_preg, preg_of. des_ifs. }
    rewrite Pregmap.gso; cycle 1.
    { unfold to_preg, preg_of. des_ifs. }
    rewrite to_preg_to_mreg.
    unfold set_regset_undef. des_ifs. exfalso.
    eapply Loc.notin_not_in in n. eauto.
  - instantiate (1:=0%nat). eauto.
  - intros pr. unfold JunkBlock.is_junk_value, to_pregset, set_regset_undef, Pregmap.set.
    des_ifs; ss; eauto.
    ii. left. esplits; eauto. erewrite loc_notin_not_in in n2. tauto.
Qed.

Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInv.SimMemInjInv P.

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
    (MCOMPATINJ: j = sm0.(SimMemInjInv.inj))
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

    (SRCNBLE: Ple mrel0.(SimMemInjInv.src).(Mem.nextblock) mrel1.(SimMemInjInv.src).(Mem.nextblock))
    (TGTNBLE: Ple mrel0.(SimMemInjInv.tgt).(Mem.nextblock) mrel1.(SimMemInjInv.tgt).(Mem.nextblock))
    (INCR: inject_incr mrel0.(SimMemInjInv.inj) mrel1.(SimMemInjInv.inj))
    (FROZEN: inject_separated
               (mrel0.(SimMemInjInv.inj)) (mrel1.(SimMemInjInv.inj))
               (mrel0.(SimMemInjInv.src)) (mrel0.(SimMemInjInv.tgt)))
    (MINVEQ: mrel0.(SimMemInjInv.mem_inv) = mrel1.(SimMemInjInv.mem_inv))

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
  :
    mle_excl
      skenv_link_src skenv_link_tgt
      (mkstate init_rs_src (State rs0_src m_unused_src))
      (mkstate init_rs_tgt (State rs0_tgt m_unused_tgt))
      mrel0 mrel1
.

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

Lemma asm_inj_inv
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
  { instantiate (1:=bot1). econs; ss; i; clarify. }
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

  - inv MLE. inv FOOT. inv MLEEXCL.
    ss. econs; ss; eauto.
    + etrans; eauto.
    + etrans; eauto.
    + etrans; eauto.
    + ii. destruct (SimMemInjInv.inj sm1 b1) eqn:EQ.
      * destruct p. dup EQ. eapply INCR0 in EQ. clarify.
        exploit FROZEN; eauto.
      * exploit FROZEN0; eauto. i. des. split; auto.
        { ii. eapply H1. eapply Plt_Ple_trans; eauto. }
        { ii. eapply H2. eapply Plt_Ple_trans; eauto. }
    + etrans; eauto.

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
      eapply Plt_Ple_trans; eauto.

  - inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
    inv INITTGT. ss. inv TYP. inv MWF. ss.
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
        exfalso. exploit Mem.valid_block_inject_1; eauto.
        eapply Plt_strict.
      }
      esplits; eauto.
      {
        econs; ss; eauto.
        - instantiate (1:=fd). inv SAFESRC. ss. des.
          admit "genv".
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
            clear - BOUNDSRC unchanged_on_nextblock. xomega. }
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

      {

        instantiate (1:=SimMemInjInv.mk
                          (JunkBlock.assign_junk_blocks m_src1 n) (JunkBlock.assign_junk_blocks m0 n)
                          (junk_inj m_src1 m0 (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0) n)
                          _).
        econs; ss; auto.
        - etrans.
          + eapply Mem.unchanged_on_nextblock.
            eapply store_arguments_unchanged_on; eauto.
          + eapply Mem.unchanged_on_nextblock.
            eapply JunkBlock.assign_junk_blocks_unchanged_on.
        - etrans.
          + eapply Mem.unchanged_on_nextblock.
            eapply store_arguments_unchanged_on; eauto.
          + eapply Mem.unchanged_on_nextblock.
            eapply JunkBlock.assign_junk_blocks_unchanged_on.
        - etrans.
          + eauto.
          + eapply junk_inj_incr; eauto.
        - ii. unfold junk_inj, update_meminj in *. des_ifs; ss.
          + split; eapply Plt_strict.
          + split.
            * ii. eapply n0. eapply Mem.valid_block_unchanged_on; eauto.
              eapply store_arguments_unchanged_on; eauto.
            * ii.
              eapply store_arguments_unchanged_on in H.
              eapply Mem.unchanged_on_nextblock in H.
              hexploit Plt_lemma; eauto. instantiate (1:=Mem.nextblock m0).
              ii. eapply H3.
              eapply Plt_Ple_trans; eauto.
          + split; eapply Plt_strict.

        - ii. erewrite JunkBlock.assign_junk_blocks_perm in *.
          eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
          eapply unchanged_on_perm in PR; eauto.
        - ii. erewrite JunkBlock.assign_junk_blocks_perm in *.
          eapply store_arguments_unchanged_on in H. inv H.
          eapply unchanged_on_perm in PR; eauto.
      }

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

        econs; ss.
        - econs; ss; auto.
          + eapply assign_junk_blocks_parallel_inject; eauto.
          + eapply SimMemInjInv.unchanged_on_invariant; eauto.
            * ii. eapply INVRANGE; eauto. apply 0.
            * eapply Mem.unchanged_on_implies.
              { etrans.
                - eapply store_arguments_unchanged_on; eauto.
                - eapply JunkBlock.assign_junk_blocks_unchanged_on; eauto. }
              ss.
          + ii. exploit INVRANGE; eauto. i. des.
            split.
            * unfold junk_inj, update_meminj. ii. des_ifs.
              { eapply Plt_strict; eauto. }
              { erewrite JunkBlock.assign_junk_blocks_perm in H4.
                exploit H1; eauto.
                eapply Mem.perm_unchanged_on_2; eauto.
                - instantiate (1:=top2).
                  eapply store_arguments_unchanged_on; eauto.
                - ss.
                - inv ARGTGT. eapply Mem.nextblock_alloc in ALC.
                  rewrite NB in *. rewrite ALC in p.
                  clear - p n0. unfold Mem.valid_block. xomega. }
              { erewrite JunkBlock.assign_junk_blocks_perm in H4.
                eapply Mem.perm_valid_block in H4. clarify. }
              { eapply n0. clear - ARGTGT. inv ARGTGT.
                rewrite <- NB. eapply Mem.nextblock_alloc in ALC.
                rewrite ALC. xomega. }
              { eapply Mem.perm_valid_block in H4. clarify. }
            * exploit INVRANGE; eauto. i. des.
              eapply Mem.valid_block_unchanged_on; eauto.
              { etrans.
                - eapply store_arguments_unchanged_on; eauto.
                - eapply JunkBlock.assign_junk_blocks_unchanged_on; eauto. }

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
          admit "genv".

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

  - des. inv SAFESRC. inv TYP. inv SIMARGS. ss.
    eapply asm_initial_frame_succeed; eauto.
    + apply inject_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + admit "genv".

  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. cinv INJPC.
    assert (delta = 0).
    { admit "genv". }
    clarify. psimpl. ss.
    exploit extcall_arguments_inject; eauto.
    { inv MWF. eauto. }
    i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

    exploit Mem_free_parallel_inject'; eauto.
    { inv MWF. eauto. } i. des.

    exploit SimMemInjInv.unchanged_on_mle; eauto.
    { ii. clarify. }
    { eapply Mem.free_unchanged_on; eauto.
      ii. unfold loc_unmapped in *. clarify. }
    { eapply Mem.free_unchanged_on; eauto.
      ii. exploit H0; eauto. eapply Mem.perm_cur. eapply Mem.perm_implies.
      - eapply Mem.free_range_perm; eauto. i.
        admit "somehow".
      - econs. }
    { ii. eapply Mem.perm_free_3; eauto. }
    { ii. eapply Mem.perm_free_3; eauto. } i. des.

    eexists (Args.mk (Vptr b2 _) _ _).
    exists (SimMemInjInv.mk m1 m2' (SimMemInjInv.inj sm0) (SimMemInjInv.mem_inv sm0)).
    esplits; eauto; ss; i.
    + econs; auto.
      * admit "genv".
      * esplits; eauto. instantiate (1:=skd).
        admit "genv".
      * instantiate (1:=Ptrofs.add ofs (Ptrofs.repr delta)).
        destruct (zlt 0 (size_arguments (SkEnv.get_sig skd))).
        { inv MWF. exploit Mem.mi_representable; eauto.
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
      * inv MWF. i. erewrite Mem.address_inject; eauto; cycle 1.
        { eapply Mem.free_range_perm; eauto.
          set (size_chunk_pos chunk). lia. }
        eapply Z.divide_add_r; eauto.
        inv WF0.
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
    + inv MWF. econs; ss; eauto.
      * eapply Mem.free_range_perm in FREE. eauto.
      * eapply Mem.free_range_perm in FREE0. auto.
      * eapply Mem.valid_block_inject_1; eauto.
      * eapply Mem.valid_block_inject_2; eauto.

  - (** ******************* after external **********************************)
    destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC.
    inv SIMRET.
    cinv (AGREE RSP); rewrite RSRSP in *; ss.
    des.
    unfold Genv.find_funct in FINDF, SIG. des_ifs. ss.

    inv MWF0. inv MWF. rewrite MEMSRC in *.
    assert (PERMRET: forall ofs, Mem.perm (SimMemInjInv.src sm_ret) blk ofs Max <1= Mem.perm (SimMemInjInv.src sm0) blk ofs Max).
    { inv MLE. inv MLE0. ii. eapply MAXSRC; eauto.
      - eapply Mem.valid_block_inject_1; eauto.
      - eapply MAXSRC0; eauto.
        + unfold Mem.valid_block.
          eapply Plt_Ple_trans; try apply SRCNBLE.
          eapply Mem.valid_block_inject_1; eauto. }
    exploit Mem_unfree_parallel_inject; eauto.
    { inv MLE0. inv MLE. ss. eauto. }
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
      eapply Mem.mi_representable; try apply WF0; eauto. des.
      - exploit PERMRET; eauto.
      - exploit PERMRET; eauto.
      - left. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
      - right. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs. }
    { inv MLE0. cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      inv HISTORY. inv CALLTGT. ss. des.
      unfold Genv.find_funct in SIG, SIG0, EXTERNAL. des_ifs.
      rewrite RSP in *. inv SIMARGS. ss. clarify.
      ii. apply MAXTGT in H; cycle 1.
      { inv MLE. unfold Mem.valid_block.
        eapply Plt_Ple_trans; eauto.
        eapply Mem.valid_block_inject_2; eauto. }
      exploit Mem_free_noperm; eauto. inv MATCH. ss.
      assert (skd = skd0); [|clarify; lia].
      admit "genv". }
    i. des. rewrite <- MEMSRC in *.

    esplits; ss.
    + instantiate (1:=SimMemInjInv.mk m1 m2' (SimMemInjInv.inj sm_ret) _).
      econs; ss; eauto.
      * rewrite <- MEMSRC. erewrite Mem_nextblock_unfree; eauto. refl.
      * erewrite Mem_nextblock_unfree; eauto. refl.
      * ii. clarify.
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
          admit "genv".
        - eauto.
        - rewrite MEMTGT in *. instantiate (1:=m2').
          rewrite <- UNFREE0. f_equal.
      }

      {
        econs; try assumption.
        - instantiate (1:=SimMemInjInv.inj sm_ret).
          ii. inv MLE. inv MLE0.
          unfold set_pair, Pregmap.set, loc_external_result, map_rpair.
          des_ifs; ss; eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
          -- eapply Val.loword_inject. eauto.
          -- eapply Val.hiword_inject. eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
        - ii. inv MLE. inv MLE0. eauto.
        - eauto.
        - ss.
        - ss.
        - econs; ss; eauto.
          + eapply SimMemInjInv.unchanged_on_invariant; eauto.
            * ii. eapply INVRANGE0; eauto.
            * eapply Mem.unchanged_on_implies.
              { eapply Mem_unfree_unchanged_on; eauto. }
              { ii. destruct H3. clarify.
                eapply INVRANGE; eauto.
                - inv MLE1. ss. rewrite MINVEQ. auto.
                - inv HISTORY. ss. inv CALLSRC. ss.
                  admit "user FREE". }
          + i. admit "use MWFAFTR".
        - unfold Genv.find_funct. rewrite Heq0. des_ifs. eauto.
        - eauto.
        - eauto.
        - ii. exploit RSPDELTA; eauto. i. des.
          inv MLE1. ss. apply INCR in H. eexists; eauto.
      }

  - (** ******************* final **********************************)

    inv MATCH. inv FINALSRC. inv MWF.

    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
    exploit Mem_free_parallel_inject'; eauto.
    { instantiate (3:=Ptrofs.zero). zsimpl. psimpl. eauto. }
    i. des.

    assert (delta = 0).
    { exploit RSPDELTA; eauto. i. des. clarify. }
    clarify. ss. zsimpl.

    eexists (SimMemInjInv.mk _ _ _ _). esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H UNDEF.
        inv WFINITSRC.
        eapply lessdef_commute; eauto.
      * des. esplits; eauto.
        admit "genv".
      * unfold external_state in *.
        des_ifs_safe. exfalso.
        cinv (AGREE PC); try rewrite Heq in *; clarify; eauto.
        { admit "genv". }
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
    + econs; ss.
    + econs; ss.
      * erewrite <- Mem.nextblock_free; eauto. refl.
      * erewrite <- Mem.nextblock_free; eauto. refl.
      * ii. clarify.
      * ii. eapply Mem.perm_free_3; eauto.
      * ii. eapply Mem.perm_free_3; eauto.
    + econs; ss; eauto.
      * eapply SimMemInjInv.unchanged_on_invariant; eauto.
        { ii. eapply INVRANGE; eauto. apply 0. }
        { eapply Mem.free_unchanged_on; eauto.
          ii. exploit INVRANGE; eauto. i. des.
          exploit H3; eauto. admit "ez - use FREE0.". }
      * i. admit "ez - use FREE".

  - left; i.
    esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + exists O.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss. destruct st0.
        cinv MWF. exploit asm_step_preserve_injection; eauto.
        { instantiate (1:=SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm).
          admit "genv". }
        { inv SIMSKENV. ss.
          eapply symbols_inject_weak_imply.
          eapply SimMemInjInv.skenv_inject_symbols_inject; eauto. }

        i. des.
        exploit SimMemInjInv.unchanged_on_mle; eauto.
        { ii. eapply asm_step_max_perm; eauto. }
        { ii. eapply asm_step_max_perm; eauto. }
        i. des.

        eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).
        eexists.
        esplits.
        - left. econs; cycle 1.
          + apply star_refl.
          + symmetry. apply E0_right.
          + econs.
            * apply AsmC.modsem_determinate.
            * econs; ss; eauto.
        - eauto.
        - econs; ss; eauto.
          + eapply agree_incr; eauto.
          + i. exploit RSPDELTA; eauto. i. des. esplits; eauto.
      }
      Unshelve. apply 0. apply 0. apply 0.
Qed.

End INJINV.
