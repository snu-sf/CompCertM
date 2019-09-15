Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import sflib.

Require Import MutrecHeader IntegersC.
Require Import MutrecB MutrecBspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SoundTop.
Require SimMemInjC SimMemInjInv SimMemInjInvC.
Require Mach.
Require Import AsmC AsmregsC Conventions1C MemoryC AsmExtra StoreArgumentsProps.

Set Implicit Arguments.


Definition memoized_inv: SimMemInjInv.memblk_invariant :=
  SimMemInjInv.memblk_invarant_mk
    (fun mem =>
       exists i,
         (<<VINDEX: mem Mint32 0 = Some (Vint i)>>) /\
         (<<VSUM: mem Mint32 (size_chunk Mint32) = Some (Vint (sum i))>>))
    (fun chunk ofs p =>
       (chunk = Mint32 /\ ofs = 0 /\ p = Writable) \/
       (chunk = Mint32 /\ ofs = (size_chunk Mint32) /\ p = Writable)).

Local Instance SimMemMemoizedB: SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Lemma memoized_inv_store_le i v_ind v_sum blk ofs0 ofs1 m_tgt0 m_tgt1
      (sm0 sm1: SimMemInjInv.t')
      (MWF: SimMem.wf sm0)
      (INVAR: sm0.(SimMemInjInv.mem_inv_tgt) blk)
      (OFSI: ofs0 = 0)
      (OFSV: ofs1 = size_chunk Mint32)
      (INDEX: v_ind = Vint i)
      (SUM: v_sum = Vint (sum i))
      (STR0: Mem.store Mint32 sm0.(SimMemInjInv.minj).(SimMemInj.tgt) blk ofs0 v_ind = Some m_tgt0)
      (STR1: Mem.store Mint32 m_tgt0 blk ofs1 v_sum = Some m_tgt1)
      (MREL: sm1 = SimMemInjInv.mk
                     (SimMemInjC.update
                        (sm0.(SimMemInjInv.minj))
                        (sm0.(SimMemInjInv.minj).(SimMemInj.src))
                        m_tgt1
                        (sm0.(SimMemInjInv.minj).(SimMemInj.inj)))
                     sm0.(SimMemInjInv.mem_inv_src)
                     sm0.(SimMemInjInv.mem_inv_tgt))
  :
    (<<MLE: SimMem.le sm0 sm1>>) /\
    (<<MWF: SimMem.wf sm1>>).
Proof.
  unfold SimMemInjC.update in *. clarify. ss.
  inv MWF. inv WF. split.
  - econs; ss; eauto. econs; ss; eauto.
    + refl.
    + etrans.
      * eapply Mem.store_unchanged_on; eauto.
        ii. exploit INVRANGETGT; eauto. i. des.
        exfalso. eauto.
      * eapply Mem.store_unchanged_on; eauto.
        ii. exploit INVRANGETGT; eauto. i. des.
        exfalso. eauto.
    + eapply SimMemInj.frozen_refl. + eapply SimMemInj.frozen_refl.
    + ii. eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_2; eauto.
  - econs; ss; eauto.
    + econs; ss; eauto.
      * eapply MemoryC.private_unchanged_inject; eauto; cycle 1.
        { instantiate (1:=~2
                        loc_out_of_reach (SimMemInj.inj (SimMemInjInv.minj sm0))
                        (SimMemInj.src (SimMemInjInv.minj sm0))). ss. }
        etrans.
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGETGT; eauto. }
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGETGT; eauto. }
      * etrans; eauto.
        unfold SimMemInj.tgt_private, SimMemInj.valid_blocks in *. ss.
        ii. des. split; auto. eapply Mem.store_valid_block_1; eauto.
        eapply Mem.store_valid_block_1; eauto.
      * rpapply TGTLE. etrans.
        { eapply Mem.nextblock_store; eauto. }
        { eapply Mem.nextblock_store; eauto. }
    + ii. exploit SATTGT; eauto. i. inv H. des. des_ifs.
      * assert (Mem.valid_access m_tgt1 Mint32 blk0 0 Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          hexploit PERMISSIONS; ss; eauto. }
        assert (Mem.valid_access m_tgt1 Mint32 blk0 (size_chunk Mint32) Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          hexploit PERMISSIONS; ss; eauto. }
        econs.
        { ii. ss. des; clarify; eauto. }
        { destruct (peq blk blk0).
          { clarify. exists (i). des_ifs. split.
            - erewrite Mem.load_store_other; try apply STR1; eauto.
              + erewrite Mem.load_store_same; eauto. ss.
              + ss. right. left. refl.
            - erewrite Mem.load_store_same; eauto. ss. }
          { ss. des. exists i0. split.
            - erewrite Mem.load_store_other; try apply STR1; eauto.
              erewrite Mem.load_store_other; try apply STR0; eauto.
            - erewrite Mem.load_store_other; try apply STR1; eauto.
              erewrite Mem.load_store_other; try apply STR0; eauto. }
        }
Qed.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (MutrecBspec.module).
Let md_tgt: Mod.t := (AsmC.module prog).
Hypothesis (INCL: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
(* Let ge := (SkEnv.project skenv_link md_src.(Mod.sk)). *)
(* Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)). *)

Let tge := (skenv_link.(SkEnv.project) prog.(Sk.of_program fn_sig)).(SkEnv.revive) prog.
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimMemInjInvC.mk symbol_memoized md_src md_tgt) sm_link.

Inductive well_saved (initstk stk: block)
  : regset -> regset -> mem -> Prop :=
| well_saved_intro
    (init_rs rs: regset) m
    (INITSIG: tge.(Genv.find_funct) (init_rs # PC) = Some (Internal func_g))
    (INITRSPVAL: init_rs RSP = Vptr initstk Ptrofs.zero)
    (RANOTFPTR: forall blk ofs (RAVAL: init_rs RA = Vptr blk ofs),
        ~ Plt blk (Genv.genv_next skenv_link))
    (RSPVAL: rs RSP = Vptr stk Ptrofs.zero)
    (STKPERM: Mem.range_perm m stk 0 24 Cur Freeable)
    (RASAVED: Mem.loadv Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.repr 16)) = Some (init_rs RA))
    (RSPSAVED: Mem.loadv Mptr m (Val.offset_ptr (rs RSP) Ptrofs.zero) = Some (init_rs RSP))
    (REGSAVED: forall mr (CALLEESAVE: Conventions1.is_callee_save mr)
                      (INREG: mr <> Machregs.BX), init_rs mr.(to_preg) = rs mr.(to_preg))
    (REGSAVEDSTK: Mem.loadv Many64 m (Val.addl (rs RSP) (Vlong (Int64.repr 8))) = Some (init_rs RBX))
  :
    well_saved
      initstk stk
      init_rs rs m.

Lemma well_saved_keep init_rs initstk stk rs0 rs1 m0 m1
      (SAVED: well_saved
                initstk stk
                init_rs rs0 m0)
      (REGSAME: forall mr (CALLEESAVE: Conventions1.is_callee_save mr)
                       (INREG: mr <> Machregs.BX),
          rs0 mr.(to_preg) = rs1 mr.(to_preg))
      (RSPSAME: rs0 RSP = rs1 RSP)
      (UNCHSTK: Mem.unchanged_on
                   (fun blk _ => blk = stk) m0 m1)
  :
    well_saved
      initstk stk
      init_rs rs1 m1.
Proof.
  inv SAVED. rewrite RSPVAL in *. ss. econs; eauto.
  - ii. eapply Mem.perm_unchanged_on; [apply UNCHSTK|..]; ss; eauto.
  - rewrite <- RSPSAME. ss. erewrite Mem.load_unchanged_on; eauto. ss.
  - rewrite <- RSPSAME. ss. erewrite Mem.load_unchanged_on; eauto. ss.
  - ii. erewrite REGSAVED; eauto.
  - ii. rewrite <- RSPSAME. ss. des_ifs. ss.
    erewrite Mem.load_unchanged_on; eauto. ss.
Qed.

Inductive curr_pc (v: val) (ofs: ptrofs): Prop :=
| curr_pc_intro
    blk
    (RSPC: v = Vptr blk ofs)
    (FINDF: Genv.find_funct_ptr tge blk = Some (Internal func_g))
.

Require Import mktac.

Inductive match_states (sm_init: SimMem.t)
  :
    nat -> MutrecBspec.state -> AsmC.state -> SimMem.t -> Prop :=
| match_states_initial
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (PRIV: forall
           blk_src blk_tgt delta
           (DETLA: sm0.(SimMemInjInv.minj).(SimMemInj.inj) blk_src = Some (blk_tgt, delta)),
           blk_tgt <> stk)
    (NOTEXT: forall
        ofs,
        ~ sm0.(SimMemInjInv.minj).(SimMemInj.tgt_external) stk ofs)
    (NINV: ~ sm0.(SimMemInjInv.mem_inv_tgt) stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 2))
    (ARG: rs RDI = Vint i)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (IDX: (idx > 9)%nat)
  :
    match_states sm_init idx (Callstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0

| match_states_at_external
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (PRIV: forall
           blk_src blk_tgt delta
           (DETLA: sm0.(SimMemInjInv.minj).(SimMemInj.inj) blk_src = Some (blk_tgt, delta)),
           blk_tgt <> stk)
    (NOTEXT: forall
        ofs,
        ~ sm0.(SimMemInjInv.minj).(SimMemInj.tgt_external) stk ofs)
    (NINV: ~ sm0.(SimMemInjInv.mem_inv_tgt) stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 12))
    (ARG: rs RBX = Vint i)
    (FARG: rs RDI = Vint (Int.sub i (Int.repr 1)))
    (RANGE: 0 < i.(Int.intval) < MAX)
    (IDX: (idx > 6)%nat)
  :
    match_states sm_init idx (Interstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0

| match_states_after_external
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (PRIV: forall
        blk_src blk_tgt delta
        (DETLA: sm0.(SimMemInjInv.minj).(SimMemInj.inj) blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (NOTEXT: forall
        ofs,
        ~ sm0.(SimMemInjInv.minj).(SimMemInj.tgt_external) stk ofs)
    (NINV: ~ sm0.(SimMemInjInv.mem_inv_tgt) stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 13))
    (ARG: rs RBX = Vint i)
    (SUM: rs RAX = Vint (sum (Int.sub i Int.one)))
    (RANGE: 0 < i.(Int.intval) < MAX)
    (IDX: (idx > 3)%nat)
  :
    match_states sm_init idx (Returnstate (sum i) m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt))sm0

| match_states_final
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (PRIV: forall
        blk_src blk_tgt delta
        (DETLA: sm0.(SimMemInjInv.minj).(SimMemInj.inj) blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (NOTEXT: forall
        ofs,
        ~ sm0.(SimMemInjInv.minj).(SimMemInj.tgt_external) stk ofs)
    (NINV: ~ sm0.(SimMemInjInv.mem_inv_tgt) stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 20))
    (ARG: rs RAX = Vint i)
    (IDX: (idx >= 2)%nat)
  :
    match_states sm_init idx (Returnstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0
.

Lemma f_blk_exists
  :
    exists f_blk,
      (<<FINDF: Genv.find_symbol
                  (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog)
                  f_id = Some f_blk>>)
      /\
      (<<FINDF: Genv.find_funct_ptr
                  (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog)
                  f_blk = None>>)
      /\
      (<<FINDF: exists skd, Genv.find_funct_ptr skenv_link f_blk = Some skd /\
                            Some (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default true) = Sk.get_csig skd>>)
.
Proof.
  exploit (prog_defmap_norepet prog f_id); eauto.
  { unfold prog_defs_names. ss. repeat (econs; eauto).
    - ii; ss; des; ss.
    - ii; ss; des; ss. }
  { ss. eauto. }
  intro T; des.
  destruct ((prog_defmap (Sk.of_program fn_sig prog)) ! f_id) eqn:DMAP; clarify.
  exploit SkEnv.project_impl_spec; eauto. intro PROJ.
  assert(PREC: SkEnv.genv_precise
                 (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog)
                 prog).
  { eapply SkEnv.project_revive_precise; ss; et. }
  inv PREC.
  exploit (P2GE f_id); eauto. i; des. des_ifs.
  rename b into f_blk.
  eexists. splits; et.
  { unfold Genv.find_funct_ptr. des_ifs. }
  (* exploit (@SkEnv.project_revive_precise _ _ skenv_link); eauto. *)
  { inv INCL.
    exploit (Sk.of_program_prog_defmap prog fn_sig); et. rewrite DMAP. intro S. ss.

    remember ((prog_defmap (Sk.of_program fn_sig prog)) ! f_id) as U in *.
    destruct U eqn:V; try (by ss). inv S. inv H1.

    exploit DEFS; eauto. i; des.
    assert(blk = f_blk).
    { inv PROJ. exploit SYMBKEEP; et.
      - instantiate (1:= f_id). unfold defs. des_sumbool. ss. et.
      - i. rewrite SYMB0 in *. clear - SYMB H. unfold SkEnv.revive in *. rewrite Genv_map_defs_symb in *. ss.
        rewrite SYMB in *. des. clarify.
    }
    clarify. inv MATCH.
    esplits; eauto.
    - unfold Genv.find_funct_ptr. rewrite DEF0. et.
    - ss. des_ifs. clear - H. inv H; ss.
    - ss.
  }
Qed.


(* from DempProof *)
Lemma E0_double:
  E0 = E0 ** E0.
Proof. auto. Qed.
Hint Resolve E0_double.

Lemma match_states_lxsim
      sm_init idx st_src0 st_tgt0 sm0
      (SIMSK: SimSymb.sim_skenv
                sm0 (SimMemInjInvC.mk symbol_memoized md_src md_tgt)
                (SkEnv.project skenv_link (Sk.of_program fn_sig prog))
                (SkEnv.project skenv_link (Sk.of_program fn_sig prog)))
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsimL (md_src skenv_link) (md_tgt skenv_link)
                   (fun st => unit -> exists su m_init, SoundTop.sound_state su m_init st)
                   (top3) (fun _ _ => SimMem.le)
                   sm_init (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  destruct (Genv.find_symbol
              ((skenv_link.(SkEnv.project) prog.(Sk.of_program fn_sig)).(SkEnv.revive) prog)
              _memoized) as [b_memo|] eqn:BLK; cycle 1.
  { exfalso. clear - INCL BLK. inversion INCL; subst.
    exploit DEFS; eauto.
    - instantiate (2:=_memoized). ss.
    - i. des.
      exploit SkEnv.project_impl_spec. eapply INCL. i. inv H. ss.
      exploit SYMBKEEP. instantiate (1:=_memoized). ss. i.
      rr in H. rewrite <- H in *.
      assert (Genv.find_symbol (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog) _memoized = Some blk).
      { ss. } clarify. }

  revert_until tge.
  pcofix CIH.
  i. pfold.
  generalize f_blk_exists; et. i; des.
  inv MATCH.

  (* initial *)
  - intros _. inv CURRPC.

    assert (CMP: compare_ints
                   (Val.and (rs RDI) (rs RDI)) Vzero
                   (rs # RBX <- (rs RDI)) # PC <- (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                   (SimMemInj.tgt sm0.(SimMemInjInv.minj)) ZF = if (Int.eq_dec i Int.zero) then Vtrue else Vfalse).
    { unfold compare_ints, nextinstr, Val.cmpu.
      repeat (rewrite Pregmap.gso; [| clarify; fail]).
      repeat rewrite Pregmap.gss.
      rewrite ARG. ss. rewrite Int.and_idem.
      exploit Int.eq_spec; eauto. i. des_ifs. }
    destruct (classic (i = Int.zero)).

    (* i = Int.zero *)
    + clarify. econs 1. i. econs.
      * split; ii.
        { inv H. inv H0. }
        { inv H. inv H0. }
      * i. ss. inv STEPSRC; ss.

        esplits.
        { left. econs; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                rewrite Pregmap.gss.
                rewrite Pregmap.gso; clarify.
                rewrite RSPC. ss.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                rewrite RSPC. ss.
              + des_ifs.
              + ss.
                unfold nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                rewrite RSPC. ss. rewrite CMP. ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                rewrite Pregmap.gss. ss.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr_nf, undef_regs, nextinstr. ss.
              + des_ifs.
              + ss. }

          econs 1.
        }

        { refl. }

        { right. eapply CIH; eauto. econs 4; eauto.
          - eapply well_saved_keep; eauto.
            + unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
              to_preg, preg_of, compare_ints, Pregmap.set.
              ii. des_ifs.
            + refl.

          - ss.
            unfold nextinstr_nf, nextinstr, undef_regs.
            repeat rewrite Pregmap.gss. econs; eauto.

          - ss.
            unfold nextinstr_nf, nextinstr, undef_regs.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss.
            unfold Vzero. rewrite sum_recurse. des_ifs. }

      * econs; ss.
        { ii. inv H; ss.
          eexists. inv H0. econs. }
        { ii. inv H; ss; nia. }

    (* i <> Int.zero *)
    + cinv MWF. ss.
      assert (INVAR: SimMemInjInv.mem_inv_tgt sm0 b_memo).
      { inv SIMSK. ss. inv INJECT.
        eapply INVCOMPAT; eauto. ss. }
      exploit SATTGT; eauto. intros SAT0. inv SAT0. ss.
      des. rename i0 into x.
      assert (CMP0:
                nextinstr
                  (compare_ints
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInj.tgt sm0.(SimMemInjInv.minj))) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x) RBX)
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInj.tgt sm0.(SimMemInjInv.minj))) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x) RAX)
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInj.tgt sm0.(SimMemInjInv.minj))) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x))
                     (SimMemInj.tgt sm0.(SimMemInjInv.minj))) ZF =
                if (Int.eq_dec x i) then Vtrue else Vfalse).
      { unfold compare_ints at 1.
        unfold nextinstr_nf, undef_regs, nextinstr.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss. ss.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss. ss.
        unfold Val.cmpu, Val.of_optbool, Val.cmpu_bool. ss.
        unfold compare_ints.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss.
        rewrite ARG.
        exploit Int.eq_spec; eauto. i. des_ifs. }

      destruct (Int.eq_dec x i).

      (* already memoized *)
      { clarify. econs 2. i. splits.
        - econs 2.
          + split.
            * apply star_one. ss. econs 1.
            * eapply Ord.lift_idx_spec. eauto.
          + refl.
          + left. pfold. intros _. econs 1. i. econs 2.

            * esplits.
              {
                econs; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      rewrite Pregmap.gss.
                      rewrite Pregmap.gso; clarify.
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss.
                      unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss. rewrite CMP. des_ifs.
                      exfalso. unfold Vfalse in *. clarify. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss. psimpl.
                      replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
                      { unfold Int64.zero.
                        exploit Ptrofs.of_int64_to_int64; eauto. }
                      rewrite VINDEX. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. rewrite CMP0. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss.
                      replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.of_int64 Int64.zero))) with 4; cycle 1.
                      { exploit Ptrofs.of_int64_to_int64; eauto. }
                      rewrite VSUM. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 1.
              }

              { eapply Ord.lift_idx_spec. eauto. }

            * refl.

            * right. eapply CIH; eauto.
              econs 4; eauto.
              { eapply well_saved_keep; eauto.
                - unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
                  to_preg, preg_of, compare_ints, Pregmap.set.
                  destruct mr; ss.
                - refl. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss. ss. econs; eauto. }
              { omega. }

        - i. ss. esplits; eauto.
          instantiate (1:=AsmC.mkstate _ (Asm.State _ _)). econs; ss.
          econs; eauto.
          + des_ifs.
          + ss. }

      (* not memoized *)
      { clarify. econs 2. i. splits.
        - econs 2.
          + split.
            * apply star_one. ss. econs 2.
              exploit Int.eq_false. eapply H. ii.
              unfold Int.eq in H0. des_ifs.
            * eapply Ord.lift_idx_spec. eauto.
          + refl.
          + left. pfold. intros _. econs 1. i. econs 2.

            * esplits.
              {
                econs; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      rewrite Pregmap.gss.
                      rewrite Pregmap.gso; clarify.
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss.
                      unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss. rewrite CMP.
                      simpl. des_ifs.
                      unfold Vfalse in *. clarify. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss. psimpl.
                      replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
                      { unfold Int64.zero.
                        exploit Ptrofs.of_int64_to_int64; eauto. }
                      rewrite VINDEX. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. rewrite CMP0. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 1.
              }

              { eapply Ord.lift_idx_spec. eauto. }

            * refl.

            * right. eapply CIH; eauto.
              econs 2; eauto.
              { eapply well_saved_keep; eauto.
                - unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
                  to_preg, preg_of, compare_ints, Pregmap.set.
                  destruct mr; ss.
                - refl. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss. ss. econs; eauto. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                unfold compare_ints.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                rewrite ARG. ss. f_equal.
                rewrite Int.add_zero_l.
                rewrite Int.add_signed. rewrite Int.sub_signed. ss. }
              { exploit Int.eq_false. eapply H. i.
                unfold Int.eq in H0.
                rewrite Int.unsigned_zero in H0.
                des_ifs. split; eauto. destruct i. ss. omega. }

        - i. ss. esplits; eauto.
          instantiate (1:=AsmC.mkstate _ (Asm.State _ _)). econs; ss.
          econs; eauto.
          + des_ifs.
          + ss. }

  - intros _. inv CURRPC.
    econs 1. i. econs 2.
    { split.
      - instantiate (1:=AsmC.mkstate _ _). apply plus_one. split.
        + eapply modsem_determinate; eauto.
        + ss. econs; ss. econs; eauto.
          * des_ifs.
          * ss.
      - eapply Ord.lift_idx_spec. eauto. }
    { refl. }

    left. pfold. intros _. econs 3; eauto.
    + econs; eauto. econs; eauto.
    + ii.

      hexploit Mem.range_perm_free.
      { instantiate (1:=0).
        instantiate (1:=0).
        instantiate (1:=stk).
        instantiate (1:=SimMem.tgt sm0).
        ii. lia. } intros [m_tgt FREE].


      cinv MWF.
      hexploit (@SimMemInjInvC.unchanged_on_mle
                  SimMemInjInv.top_inv memoized_inv sm0
                  sm0.(SimMemInjInv.minj).(SimMemInj.src) m_tgt sm0.(SimMemInjInv.minj).(SimMemInj.inj)); ss; eauto.
      { eapply private_unchanged_inject; eauto.
        - cinv WF0. eauto.
        - instantiate (1:=~2
                        loc_out_of_reach (SimMemInj.inj (SimMemInjInv.minj sm0))
                        (SimMemInj.src (SimMemInjInv.minj sm0))).
          eapply Mem.free_unchanged_on; eauto.
          ii. omega.
        - ss. }
      { ii. clarify. }
      { refl. }
      { eapply Mem.free_unchanged_on; eauto. ii. omega. }
      { ii. eapply Mem.perm_free_3; eauto. }
      i. des.

      cinv SAVED. inv ATSRC.
      eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _).
      esplits; eauto.
      * econs; ss; eauto.
        instantiate (1:=Vptr g_fptr Ptrofs.zero).
        inv SIMSK. inv SIMSKENV. inv INJECT. ss.
        econs. eapply DOMAIN; eauto.
        exploit Genv.genv_symb_range. unfold Genv.find_symbol in *. eauto.
        i. ss. ii.
        exploit INVCOMPAT; eauto. i. rewrite <- H0 in H. ss.
        rewrite Ptrofs.add_zero_l. ss.
      * econs 1; eauto.
        { repeat rewrite Pregmap.gss. ss.
          unfold Genv.symbol_address.
          assert (Genv.find_symbol
                    (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog) f_id = Some g_fptr) by ss.
          rewrite H. ss. }
        { unfold Genv.find_funct. des_ifs.
          unfold Genv.find_funct_ptr. des_ifs.
          unfold Genv.find_def in Heq. ss.
          do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *.
          des_ifs.
          exploit Genv.find_invert_symbol. eauto. i. rewrite H in *.
          unfold o_bind in Heq. ss. clarify.
          destruct (Genv.invert_symbol skenv_link g_fptr) eqn:SYMB.
          unfold o_bind in Heq0. ss. des_ifs.
          exploit SkEnv.project_impl_spec. eapply INCL. i. inv H0. ss.
          destruct ((prog_defmap (Sk.of_program fn_sig prog)) ! i0) eqn:DMAP; ss.
          assert (defs (Sk.of_program fn_sig prog) i0).
          { rewrite <- defs_prog_defmap. eauto. }
          exploit SYMBKEEP; eauto. i. rr in H1.
          clarify. exploit Genv.invert_find_symbol. eapply SYMB. i.
          rewrite <- H1 in H2. exploit Genv.find_invert_symbol; eauto. i.
          rewrite H3 in *. clarify.
          unfold o_bind in Heq0. ss. }
        { destruct ((prog_defmap (Sk.of_program fn_sig prog)) ! f_id) eqn:DMAP; clarify.
          assert (DEFS0: defs (Sk.of_program fn_sig prog) f_id).
          { rewrite <- defs_prog_defmap. eauto. }
          exploit SkEnv.project_impl_spec. eapply INCL. i. inv H.
          inv INCL.
          exploit DEFS; eauto. i. des.
          exploit SYMBKEEP; eauto. i. rr in H.
          rewrite H in *. rewrite FINDG in *. ss. clarify.
          inv MATCH. ss. inv H1; des_ifs; esplits; try rewrite Genv.find_funct_ptr_iff; eauto; ss. }
        { split; ss.
          - repeat (rewrite Pregmap.gso; [| clarify; fail]).
            rewrite Pregmap.gss. rewrite RSPC. ss.
          - repeat (rewrite Pregmap.gso; [| clarify; fail]).
            rewrite Pregmap.gss. rewrite RSPC. ss. }
        { econs; eauto.
          - econs; eauto. ss.
            rpapply extcall_arg_reg. ss.
          - econs. }
        { zsimpl. psimpl. inv WF.
          rewrite Genv.find_funct_ptr_iff in FINDF1.
          eapply WFPARAM in FINDF1. generalize (size_arguments_above (Sk.get_sig skd)); i. etrans; eauto. xomega. }
        { ii. apply Z.divide_0_r. }
        { ss. }

      * i. inv AFTERSRC. ss. inv SIMRETV; ss.
        exploit Mem_unfree_suceeds.
        { instantiate (1:=stk).
          instantiate (1:=SimMemInj.tgt sm_ret.(SimMemInjInv.minj)).
          inv MLE1. inv MLE2. ss.
          unfold Mem.valid_block. eapply Plt_Ple_trans; eauto.
          - eapply Mem.perm_valid_block; eauto.
            eapply STKPERM; eauto. instantiate (1:=0). lia.
          - erewrite <- Mem.nextblock_free; eauto.
            eapply Mem.unchanged_on_nextblock; eauto. } i. des.
        exploit Mem_unfree_right_inject; try apply UNFR; eauto.
        { inv MWF1. inv WF1. eauto. }
        { instantiate (1:=0). instantiate (1:=0). ii. lia. } intros INJ.
        eapply SimMemInjInvC.unlift_wf in MWF1; try apply MLE1; eauto.
        dup MLE1. eapply SimMemInjInvC.unlift_spec in MLE1; eauto.
        exploit SimMemInjInvC.unchanged_on_mle; eauto.
        { ss. ii. clarify. }
        { refl. }
        { eapply Mem.unchanged_on_implies.
          - eapply Mem_unfree_unchanged_on; eauto.
          - unfold brange. ii. des. lia. }
        { ii. eapply Mem_unfree_unchanged_on; eauto.
          unfold brange. ii. des. lia. } i. des.
        eexists.
        eexists (SimMemInjInv.mk
                   (SimMemInj.mk
                      (SimMemInj.src sm_ret.(SimMemInjInv.minj))
                      m1 _ _ _ _ _ _ _) _ _).
        esplits; ss.
        { econs; ss; eauto.
          - instantiate (1:=mksignature [AST.Tint] (Some AST.Tint) cc_default true).
            assert (SYMBREV: Genv.find_symbol
                               (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) prog) f_id = Some g_fptr) by ss.
            unfold Genv.symbol_address. rewrite SYMBREV. ss. des_ifs.
            destruct ((prog_defmap (Sk.of_program fn_sig prog)) ! f_id) eqn:DMAP; clarify.
            assert (DEFS0: defs (Sk.of_program fn_sig prog) f_id).
            { rewrite <- defs_prog_defmap. eauto. }
            exploit SkEnv.project_impl_spec. eapply INCL. i. inv H.
            inv INCL. exploit DEFS; eauto.
          - unfold size_arguments. des_ifs. ss. psimpl. eauto. }
        { etrans; eauto. refl. }
        { right. eapply CIH; eauto.
          { exploit SimSymb.mle_preserves_sim_skenv; ss; cycle 1; eauto.
            etrans; eauto. etrans; eauto. }
          econs 3; ss; eauto.
          - etrans; eauto. etrans; eauto. etrans; eauto.
          - eapply well_saved_keep; eauto.
            + unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
              to_preg, preg_of, compare_ints, Pregmap.set.
              destruct mr; ss.
            + etrans.
              { eapply Mem.free_unchanged_on; eauto. clear. ii. lia. }
              etrans.
              { inv MLE2. ss. inv MLE4. ss.
                eapply Mem.unchanged_on_implies; eauto.
                ii. clarify. split; auto. split; ss; auto.
                ii. eapply PRIV; eauto. }
              { eapply Mem.unchanged_on_implies; eauto.
                - eapply Mem_unfree_unchanged_on; eauto.
                - clear. ii. destruct H1. lia. }
          - inv MLE1. ss. inv MLE4. ss. ii. clarify.
            destruct (SimMemInj.inj (SimMemInjInv.minj sm0) blk_src) eqn:BLK0.
            + destruct p. dup BLK0. eapply INCR in BLK0.
              clarify. hexploit PRIV; eauto.
            + inv MLE2. ss. inv MLE1. ss. inv FROZEN0.
              exploit NEW_IMPLIES_OUTSIDE; eauto. i. des.
              inv SAVED. eapply (Plt_strict stk).
              eapply Plt_Ple_trans; eauto.
              eapply Mem.nextblock_free in FREE. rewrite FREE.
              eapply Mem.perm_valid_block; eauto.
              eapply STKPERM; eauto. instantiate (1:=0). clear. lia.
          - repeat rewrite Pregmap.gss. rewrite RSPC.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss. ss. econs; eauto.
          - unfold set_pair, loc_external_result, loc_result. des_ifs_safe. ss.
            clarify.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss. inv RETV; eauto. }

  - intros _. econs 1. i. cinv CURRPC.

    cinv MWF. ss.
    assert (INVAR: SimMemInjInv.mem_inv_tgt sm0 b_memo).
    { inv SIMSK. ss. inv INJECT.
      eapply INVCOMPAT; eauto. ss. }
    hexploit SATTGT; eauto. intros SAT0.
    specialize (SAT0 _ INVAR). destruct SAT0. des. des_ifs_safe.

    hexploit Mem.valid_access_store.
    { eapply PERMISSIONS. ss. left. eauto. } intros [m_tgt0 STR0].
    hexploit Mem.valid_access_store.
    { eapply Mem.store_valid_access_1; eauto.
      eapply PERMISSIONS. ss. right. eauto. } intros [m_tgt1 STR1].

    hexploit memoized_inv_store_le; try refl; eauto.
    instantiate (1:=i) in STR0. i. des.

    econs 2.

    + split.
      * econs 1; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + des_ifs.
            + ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss.
              unfold exec_store, Mem.storev, eval_addrmode. ss.
              des_ifs_safe. unfold Genv.symbol_address. rewrite BLK.
              psimpl. unfold nextinstr at 1.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite ARG.
              replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
              { unfold Int64.zero.
                exploit Ptrofs.of_int64_to_int64; eauto. }
              rewrite STR0.
              ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss.
              unfold exec_store, Mem.storev, eval_addrmode. ss.
              des_ifs_safe. unfold Genv.symbol_address. rewrite BLK.
              psimpl. unfold nextinstr_nf at 1.
              unfold undef_regs. unfold nextinstr at 1 2.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss. rewrite SUM.
              replace
                (Val.add (Vint (sum (Int.sub i Int.one))) (Vint (Int.add i (Int.repr 0))))
                with (Vint (sum i)); cycle 1.
              { rewrite sum_recurse with (i := i). des_ifs; cycle 1.
                - unfold Val.add. rewrite Int.add_zero. auto.
                - rewrite Z.eqb_eq in Heq0. omega. }
              rewrite STR1. ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss. unfold goto_label.
              unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss. }

        econs 1; eauto.

      * eapply Ord.lift_idx_spec. eauto.

    + eauto.

    + right. eapply CIH; eauto.
      { exploit SimSymb.mle_preserves_sim_skenv; ss; cycle 1; eauto. }
      econs 4; ss; eauto.

      * etrans; eauto.

      * eapply well_saved_keep; eauto.
        { unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
          to_preg, preg_of, compare_ints, Pregmap.set.
          destruct mr; ss. }
        { etrans.
          - eapply Mem.store_unchanged_on; eauto. ii. clarify.
          - eapply Mem.store_unchanged_on; eauto. ii. clarify. }

      * repeat rewrite Pregmap.gss. econs; eauto.

  - intros _. econs 1; eauto. intros _.
    inv CURRPC. inv SAVED.
    hexploit Mem.range_perm_free.
    { eapply STKPERM. } intros [m2 FREE1].
    hexploit Mem.range_perm_free.
    { instantiate (1:=0).
      instantiate (1:=0).
      instantiate (1:=initstk).
      instantiate (1:=m2).
      ii. omega. } intros [m4 FREE2].

    cinv MWF. destruct sm0 as [sm0 minv_src minv_tgt].
    exploit SimMemInj.free_right; eauto.
    { ii. split; eauto.
      - ii. exploit PRIV; eauto.
      - eapply Mem.perm_valid_block. eauto. } i. des. clarify.
    exploit SimMemInj.free_right; eauto.
    { clear. ii. lia. }
    { clear. ii. lia. } i. des. clarify.

    econs 2.
    + split.
      * econs 1; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + des_ifs.
            + ss. unfold exec_load, eval_addrmode, eval_addrmode64.
              des_ifs_safe. ss.
              rewrite Int64.add_zero_l. rewrite REGSAVEDSTK. ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss. unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RASAVED. rewrite RSPSAVED. rewrite RSPVAL.
              psimpl. zsimpl. rewrite FREE1. ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              rewrite RSPC. ss.
            + des_ifs.
            + ss. }

        econs 1.

      * eapply Ord.lift_idx_spec. eauto.

    + instantiate (1:=SimMemInjInv.mk sm1 _ _). econs; ss; eauto.

    + left. pfold. intros _. econs 4; ss.
      * instantiate (1:=SimMemInjInv.mk sm2 _ _). econs; ss; eauto.
        etrans; eauto. etrans; eauto. inv MLE. eauto.
      * hexploit (@SimMemInjInv.le_inj_wf_wf SimMemInjInv.top_inv memoized_inv sm0 sm2); ss; eauto.
        { etrans; eauto. }
        { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
          - ii. exploit INVRANGETGT; eauto. i. des.
            inv MWF. inv WF1. eapply Plt_Ple_trans; eauto.
          - etrans.
            + eapply Mem.free_unchanged_on; eauto.
            + eapply Mem.free_unchanged_on; eauto. clear. ii. lia. }
        { destruct sm_init. inv MLE. ss. clarify. }
      * econs; ss; eauto.
        { repeat rewrite Pregmap.gss.
          repeat (rewrite Pregmap.gso; [| clarify; fail]).
          repeat rewrite Pregmap.gss.
          unfold external_state. ss. des_ifs. exfalso.
          unfold Genv.find_funct_ptr in *. des_ifs_safe.
          eapply Genv.genv_defs_range in Heq1.
          eapply RANOTFPTR; eauto. }
        { unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
          exfalso. exploit RANOTFPTR; eauto. eapply Genv.genv_defs_range; eauto. }
        { unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
          to_preg, preg_of, compare_ints, Pregmap.set in *.
          ii. specialize (REGSAVED mr).
          des_ifs; eapply Val.lessdef_same; try apply REGSAVED; eauto; clarify. }
        { ss. }
      * econs; ss.
        { repeat (rewrite Pregmap.gso; [| clarify; fail]).
          rewrite ARG. econs. }
        { rewrite MSRC0. eauto. }

        Unshelve. all: ss; eauto. apply Ptrofs.zero. apply Ptrofs.zero.
        apply Ptrofs.zero. apply Ptrofs.zero. econs.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply sim_mod_sem_implies.
  eapply ModSemPair.simL_intro with (has_footprint := top3) (mle_excl := fun _ _ => SimMem.le).
  { i. eapply SoundTop.sound_state_local_preservation. }
  { i. eapply Preservation.local_preservation_noguarantee_weak; eauto. eapply SoundTop.sound_state_local_preservation. }
  { ii; ss. r. etrans; eauto. }
  i. ss. esplits; eauto.

  - i. des. inv SAFESRC. instantiate (1:=unit).
    esplits; eauto.
    + refl.
    + econs; eauto.
    + instantiate (1:= (Ord.lift_idx lt_wf 15%nat)).
      inv SIMARGS; ss. inv INITTGT; ss.
      inv TYP. ss. clarify.
      assert (FD: fd = func_g).
      { inv VALS. inv H1. inv H3. inv FPTR0. ss.
        des_ifs.
        inv SIMSKENV. inv SIMSKE. inv INJECT. ss.
        exploit IMAGE; eauto.
        { exploit Genv.genv_symb_range.
          unfold Genv.find_symbol in SYMB. eauto. i. ss. eauto. }
        ii. des. subst. clarify.
        unfold Genv.find_funct in FINDF. ss. des_ifs.
        rewrite Genv.find_funct_ptr_iff in FINDF.
        unfold Genv.find_def in FINDF. ss.
        do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *.
        des_ifs.
        destruct (Genv.invert_symbol
             (SkEnv.project skenv_link (Sk.of_program fn_sig prog)) b) eqn:SKENVSYMB; ss.
        unfold o_bind in FINDF. ss.
        exploit Genv.find_invert_symbol. eauto. i.
        rewrite H in *. clarify.
        destruct ((prog_defmap prog) ! g_id) eqn:DMAP; ss. clarify. } clarify.

      unfold Genv.find_funct in FINDF. des_ifs.

      cinv STORE. des. ss.
      destruct (Mem.alloc (JunkBlock.assign_junk_blocks m0 n) 0 24) as [m2 stk] eqn:ALLOC.
      hexploit Mem.valid_access_store.
      { eapply Mem.valid_access_implies.
        - instantiate (4:=Mptr).
          eapply Mem.valid_access_alloc_same.
          + eauto.
          + instantiate (1:=Ptrofs.unsigned Ptrofs.zero). ss.
          + unfold Mptr. des_ifs.
          + apply Z.divide_0_r.
        - econs. } intros [m3 STR0].
      hexploit Mem.valid_access_store.
      { eapply Mem.valid_access_implies.
        - instantiate (4:=Mptr).
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.valid_access_alloc_same.
          + eauto.
          + instantiate (1:=Ptrofs.unsigned (Ptrofs.repr 16)). ss.
          + unfold Mptr. des_ifs.
          + rewrite align_chunk_Mptr. des_ifs. exists 2. ss.
        - econs. } intros [m4 STR1].
      hexploit Mem.valid_access_store.
      { eapply Mem.valid_access_implies.
        - instantiate (4:=Many64).
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.valid_access_alloc_same.
          + eauto.
          + instantiate (1:=Ptrofs.unsigned (Ptrofs.repr 8)). ss.
          + unfold Mptr. des_ifs.
          + ss. exists 2. auto.
        - econs. } intros [m5 STR2].

      destruct sm_arg as [sm_arg minv_src minv_tgt].

      assert (UNCH0: Mem.unchanged_on top2 (SimMemInj.tgt sm_arg) (JunkBlock.assign_junk_blocks m0 n)).
      { ss. etrans.
        { eapply store_arguments_unchanged_on; eauto. }
        { eapply JunkBlock.assign_junk_blocks_unchanged_on; eauto. } }

      assert (STKOUTSIDE0: ~ Mem.valid_block sm_arg.(SimMemInj.tgt) stk).
      { ii. eapply Mem.fresh_block_alloc in ALLOC. eapply ALLOC.
        eapply Mem.valid_block_unchanged_on; eauto. }

      assert (UNCH: Mem.unchanged_on top2 (SimMemInj.tgt sm_arg) m5).
      { ss. etrans; eauto.
        eapply Mem.unchanged_on_implies with (P:=fun blk ofs => blk <> stk); cycle 1.
        { ii. clarify. eapply Mem.fresh_block_alloc; eauto. } etrans.
        { eapply Mem.unchanged_on_implies with (P:=top2); ss.
          eapply Mem.alloc_unchanged_on; eauto. } etrans.
        { eapply Mem.store_unchanged_on; eauto. } etrans.
        { eapply Mem.store_unchanged_on; eauto. } etrans.
        { eapply Mem.store_unchanged_on; eauto. } refl. }

      assert (STKOUTSIDE1: forall blk_src blk_tgt ofs_src,
                 sm_arg.(SimMemInj.inj) blk_src = Some (blk_tgt, ofs_src)
                 -> blk_tgt <> stk).
      { inv MWF. inv WF0. ss.
        ii. clarify. exploit Mem.valid_block_inject_2; eauto. }

      assert (STKOUTSIDE2: forall ofs, ~ SimMemInj.tgt_external sm_arg stk ofs).
      { ii. inv MWF. inv WF0. ss. eapply TGTEXT in H. destruct H. clarify. }

      set (sm1:=SimMemInjInv.mk
                  (SimMemInjC.update
                     sm_arg
                     (SimMemInj.src sm_arg)
                     (m5)
                     (SimMemInj.inj sm_arg)) minv_src minv_tgt).

      assert (MLE: SimMemInjInv.le' (SimMemInjInv.mk sm_arg minv_src minv_tgt) sm1).
      { econs; ss; eauto. econs; ss; eauto.
        - refl.
        - eapply Mem.unchanged_on_implies; eauto; ss.
        - eapply SimMemInj.frozen_refl. - eapply SimMemInj.frozen_refl.
        - ii. eapply Mem.perm_unchanged_on_2; eauto; ss. }

      assert (MWF1: SimMem.wf sm1).
      { inv MLE. ss. cinv MWF. cinv WF0. ss.
        eapply SimMemInjInv.le_inj_wf_wf; eauto; ss.
        - hexploit (@SimMemInjC.parallel_gen sm_arg (SimMemInj.src sm_arg) m5); eauto.
          + eapply private_unchanged_inject; eauto.
          + ii. clarify.
          + refl.
          + eapply Mem.unchanged_on_implies; eauto; ss.
          + ii. eapply Mem.perm_unchanged_on_2; eauto; ss.
          + i. des. eauto.
        - eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
          + ii. exploit INVRANGETGT; eauto. i. des. eapply Plt_Ple_trans; eauto.
          + eapply Mem.unchanged_on_implies; eauto; ss. }

      rename Heq into RSPC.
      pfold. intros _. econs 1. intros _. econs 2.
      * split.
        {
          econs 1; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + des_ifs.
              + ss. rewrite ALLOC. psimpl. rewrite STR0. rewrite STR1. ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                rewrite RSPC. ss.
              + des_ifs.
              + ss. unfold exec_store, eval_addrmode, eval_addrmode64. ss.
                des_ifs_safe. psimpl. unfold nextinstr.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                replace (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned (Int64.repr 8)))) with 8; ss.
                rewrite STR2. ss. }
          econs 1.
        }
        { eapply Ord.lift_idx_spec. eauto. }
      * eauto.
      * left. unfold MutrecBspec.module in *.
        eapply match_states_lxsim; eauto.
        { inv SIMSKENV. eapply SimMemInjInvC.sim_skenv_inj_lepriv; eauto. hexploit SimMem.pub_priv; et. }
        { ss. econs; ss; eauto.
          - econs; ss; eauto.
            + rewrite RSPC. eauto.
            + ii. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
              eapply Mem_alloc_range_perm; eauto.
            + psimpl. erewrite Mem.load_store_other; eauto; cycle 1.
              { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. }
              erewrite Mem.load_store_same; eauto.
              f_equal. erewrite <- Val.load_result_same; eauto. ss.
            + psimpl. erewrite Mem.load_store_other; eauto; cycle 1.
              { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. }
              erewrite Mem.load_store_other; eauto; cycle 1.
              { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. }
              erewrite Mem.load_store_same; eauto.
              f_equal. rewrite H1. ss.
            + ii. unfold is_callee_save, nextinstr_nf, nextinstr, undef_regs,
              to_preg, preg_of, compare_ints, Pregmap.set. des_ifs.
            + unfold Mem.loadv. psimpl. des_ifs_safe.
              replace (Ptrofs.unsigned (Ptrofs.of_int64 (Int64.repr 8))) with 8; ss.
              erewrite Mem.load_store_same; eauto; ss.
          - ii. inv MWF. ss. inv WF0. exploit INVRANGETGT; eauto.
            i. des. eapply (Plt_strict stk). eapply Plt_Ple_trans; eauto.
            etrans; eauto. clear - STKOUTSIDE0.
            unfold Mem.valid_block in *. xomega.
          - unfold nextinstr_nf, undef_regs, nextinstr.
            repeat rewrite Pregmap.gss.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss.
            rewrite RSPC. ss. econs; eauto.
          - unfold nextinstr_nf, undef_regs, nextinstr.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            inv H0. inv VALS. inv H4. inv H2. ss. unfold typify_list, typify in *.
            ss. des_ifs; ss. inv VALS0.
            unfold loc_arguments in *. des_ifs. inv H5. inv H3; ss.
            inv H; ss. clarify.
          - omega. }

  - (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss. clarify.

    exploit asm_initial_frame_succeed; eauto.
    + instantiate (1:=func_g). ss.
      eapply inject_list_length in VALS. des. rewrite <- VALS. ss.
    + ss.
    + ss.
      inv VALS. inv H1. inv H3. inv FPTR0. ss.
      des_ifs.
      inv SIMSKENV. inv SIMSKE. inv INJECT. ss.
      exploit IMAGE; eauto.
      { exploit Genv.genv_symb_range.
        unfold Genv.find_symbol in SYMB. eauto. i. ss. eauto. }
      ii. des. subst. clarify.

      rewrite Genv.find_funct_ptr_iff in *.
      unfold Genv.find_def in *; ss.
      do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *.
      des_ifs.
      exploit Genv.find_invert_symbol. eauto. i.
      rewrite H in *. clarify.
    + ss.
Unshelve. apply 0. apply 0.
Qed.


End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (MutrecBspec.module) (AsmC.module prog) (SimMemInjInvC.mk symbol_memoized (MutrecBspec.module) (AsmC.module prog)))
.
Proof.
  econs; ss.
  - econs; ss. i. inv SS. esplits; ss; eauto.
    + econs; ss.
      ii. econs.
      * ii. ss. des; clarify.
        { econs.
          - ii. eapply PERM; eauto. ss. lia.
          - apply Z.divide_0_r. }
        { econs.
          - ii. eapply PERM; eauto. ss. lia.
          - ss. exists 1. eauto. }
      * ss. des. exists Int.zero. esplits; eauto.
        rewrite sum_recurse. des_ifs.
    + ii. des; clarify.
    + ii. destruct H. eapply in_prog_defmap in PROG.
      ss. unfold update_snd in PROG. ss.
      des; clarify; inv DROP; ss.
      des; clarify.
  - ii. ss.
    inv SIMSKENVLINK. inv SIMSKENV.
    eapply sim_modsem; eauto.
Qed.
