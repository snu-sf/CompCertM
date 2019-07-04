Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemInjInvC.
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
Require Import AsmExtra IdSimExtra IdSimAsmExtra IdSimInvExtra.

Require Import MatchSimModSemExcl2.
Require Import Conventions1C.

Require Import mktac.


Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.



Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv top1 P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.

Local Existing Instance SoundTop.Top.

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

Lemma asm_inj_id_drop
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
  eapply MatchSimModSemExcl2.match_states_sim with
      (match_states :=
         match_states
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm))
      (match_states_at := top4)
      (sidx := unit); ss; eauto; ii.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - (** ******************* initial **********************************)
    destruct sm_arg as [sm_arg mem_inv_src mem_inv_tgt].
    dup MWF. rename MWF0 into MINVWF.
    destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.
    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv SIMARGS. destruct args_src, args_tgt. ss. clarify.
    inv INITTGT. ss. inv TYP. inv STORE.

    exploit store_arguments_parallel; eauto.
    { eapply typify_has_type_list; eauto. }
    { exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
      i. des. inv WFTGT. eapply WFPARAM in H1. ss. }
    { eapply inject_list_typify_list; try eassumption.
      erewrite inject_list_length; eauto. } i. des.
    hexploit (assign_junk_blocks_parallel n); eauto. i. des.
    eexists (AsmC.mkstate (((to_pregset (set_regset_junk (SimMemInj.src sm1) m0 n rs_src (to_mregset rs) (fn_sig fd))) # PC <- fptr)
                             # RA <- (src_junk_val (SimMemInj.src sm1) m0 n (rs RA)))
                          # RSP <- (Vptr (Mem.nextblock (SimMemInj.src sm_arg)) Ptrofs.zero)
                          (Asm.State _ _)).
    hexploit (@SimMemInjInv.le_inj_wf_wf top1 P sm_arg sm0); eauto.
    { etrans; eauto. }
    { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
      - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
      - eapply Mem.unchanged_on_implies with (P:=top2); ss. etrans.
        + eapply store_arguments_unchanged_on; eauto.
        + rewrite <- MTGT. rewrite MTGT0.
          eapply JunkBlock.assign_junk_blocks_unchanged_on. } intros MWFINV1.

    eexists (SimMemInjInv.mk sm0 _ _). esplits; eauto.
    { econs; ss; eauto.
      - instantiate (1:=fd). inv SAFESRC. ss. des.
        exploit match_globals_find_funct; eauto. i.
        setoid_rewrite FINDF in H1. clarify.
      - econs; eauto. erewrite inject_list_length; eauto.
      - inv ARGTGT. econs; ss; eauto.
        econs; try eassumption; eauto.
        eapply extcall_arguments_same; eauto. i.
        unfold Pregmap.set, to_mregset, to_pregset, to_preg.
        erewrite to_preg_to_mreg. des_ifs; clarify; ss.
        + unfold preg_of in *; des_ifs.
        + unfold preg_of in *; des_ifs.
        + unfold preg_of in *; des_ifs.
        + unfold set_regset_junk. des_ifs; clarify; eauto.
          exfalso. eapply Loc.notin_not_in in n3. eauto.
      - assert (JUNK: JunkBlock.is_junk_value m0 (JunkBlock.assign_junk_blocks m0 n) (rs RA)).
        { apply NNPP. ii. exploit PTRFREE; eauto. i. des; ss. }
        split.
        + unfold Pregmap.set, src_junk_val. des_ifs.
        + unfold Pregmap.set, src_junk_val. des_ifs; ss; des; eauto.
      - unfold Pregmap.set. des_ifs. unfold src_junk_val, JunkBlock.is_junk_value in *.
        des_ifs. ii. clarify. apply n1.
        assert (PLT: Plt (b + Mem.nextblock (SimMemInj.src sm1) - Mem.nextblock (SimMemInj.tgt sm1)) (Mem.nextblock (SimMemInj.src sm1))).
        { eapply Plt_Ple_trans; eauto.
          inv SIMSKENV. inv SIMSKELINK. ss. inv MLE. inv MWF.
          etrans; eauto. etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto. }
        exfalso. eapply Plt_lemma; eauto.
      - i. unfold Pregmap.set in *. des_ifs; eauto.
        { exploit PTRFREE.
          - ii. eapply src_junk_val_junk in H1; eauto.
          - i. des; clarify. } left.
        unfold to_pregset, set_regset_junk, to_mregset in *. des_ifs; ss.
        + exploit PTRFREE.
          * ii. eapply src_junk_val_junk in H1; eauto.
          * i. erewrite to_mreg_some_to_preg in *; eauto. des; ss.
            clarify. esplits; eauto.
        + esplits; eauto. erewrite loc_notin_not_in in n3. tauto. }

    { econs; ss; eauto. etrans; eauto. }

    { assert (AGREE0:
                AsmStepInj.agree
                  (SimMemInj.inj sm0)
                  (((to_pregset (set_regset_junk (SimMemInj.src sm1) m0 n rs_src (to_mregset rs) (fn_sig fd)))
                      # PC <- fptr) # RA <- (src_junk_val (SimMemInj.src sm1) m0 n (rs RA))) # RSP <-
                  (Vptr (Mem.nextblock (SimMemInj.src sm_arg)) Ptrofs.zero) rs).
      { ii. unfold Pregmap.set, to_mregset, to_pregset, to_preg.
        inv MLE0. des_ifs; ss; eauto.
        - eapply val_inject_incr; eauto. rewrite INJ.
          unfold update_meminj. rewrite H0. econs; des_ifs. ss.
        - rewrite MINJ. eapply src_junk_val_inj; eauto. inv MWF0. eauto.
        - inv MLE. eapply val_inject_incr; eauto.
        - unfold set_regset_junk. des_ifs.
          + erewrite to_mreg_preg_of; eauto. rewrite MINJ.
            eapply src_junk_val_inj; eauto. inv MWF0. eauto.
          + eapply val_inject_incr; eauto. rewrite INJ in *.
            specialize (AGREE m). unfold to_mregset in *.
            erewrite to_mreg_preg_of in *; eauto. }
      econs; eauto.
      - rewrite <- MTGT. auto.

      - unfold to_pregset, set_regset, Pregmap.set. ii.
        rewrite to_preg_to_mreg in *. des_ifs.
        + apply f_equal with (f:=to_mreg) in e.
          rewrite to_preg_to_mreg in  e. ss.
        + apply f_equal with (f:=to_mreg) in e.
          rewrite to_preg_to_mreg in  e. ss.
        + unfold set_regset_junk in *. des_ifs.
          * assert (JUNK: JunkBlock.is_junk_value (SimMemInj.tgt sm1) (JunkBlock.assign_junk_blocks (SimMemInj.tgt sm1) n) (rs (to_preg r))).
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
          assert (JUNK: JunkBlock.is_junk_value (SimMemInj.tgt sm1) (JunkBlock.assign_junk_blocks (SimMemInj.tgt sm1) n) (rs RA)).
          { apply NNPP. ii. exploit PTRFREE; eauto. i. des; clarify. }
          clear - RADEF JUNK.
          unfold JunkBlock.is_junk_value, Mem.valid_block in *. des_ifs; des; eauto.
      - econs; ss. ii. congruence.
      - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
        eapply Genv.genv_defs_range in Heq0. exfalso. eapply RANOTFPTR; eauto.
      - unfold Pregmap.set. des_ifs. ii. clarify. rewrite MINJ. rewrite INJ.
        unfold junk_inj, update_meminj. des_ifs; eauto. }

  - (** ******************* safe **********************************)
    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv TYP. inv SIMARGS. ss.
    eapply asm_initial_frame_succeed; eauto.
    + apply inject_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
      i. des. inv WFSRC. eapply WFPARAM in H. ss.
    + exploit match_globals_find_funct; eauto.

  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC. inv MATCH.
    destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
    dup MWF. rename MWF0 into MINVWF.
    destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.

    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. cinv INJPC.
    assert (delta = 0).
    { psimpl. inv SIMSKELINK. ss. inv INJECT. exploit IMAGE; eauto.
      - left. clear - SIG. unfold Genv.find_funct_ptr in *.
        des_ifs. eapply Genv.genv_defs_range; eauto.
      - i. des. eauto. }
    clarify. psimpl. ss.
    exploit extcall_arguments_inject; eauto.
    { inv MWF. eauto. }
    i. des. cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

    exploit Mem_free_parallel'; eauto. i. des.
    hexploit (@SimMemInjInv.le_inj_wf_wf top1 P sm0 sm1); eauto.
    { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
      - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
      - eapply Mem.free_unchanged_on; eauto. ii.
        exploit INVRANGETGT; eauto. i. des. exploit H5; eauto.
        eapply Mem.perm_cur. eapply Mem.perm_implies.
        + eapply Mem.free_range_perm; eauto.
          instantiate (1:=Ptrofs.unsigned ofs + delta). lia.
        + econs. } intros MWFINV0.

    eexists (Args.mk (Vptr b2 _) _ _). eexists (SimMemInjInv.mk sm1 _ _).
    esplits; eauto; ss; i.
    + econs; auto.
      * instantiate (2:=Ptrofs.add ofs (Ptrofs.repr delta)).
        destruct (zlt 0 (size_arguments (SkEnv.get_sig skd))).
        { inv MWF. exploit Mem.mi_representable; eauto.
          - right.
            instantiate (1:=Ptrofs.add ofs (Ptrofs.repr (4 * size_arguments (SkEnv.get_sig skd)))).
            eapply Mem.perm_cur.
            eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
            rewrite unsigned_add.
            + clear - ARGSRANGE l. lia.
            + clear- ARGSRANGE. set (size_arguments_above (SkEnv.get_sig skd)).
              set (Ptrofs.unsigned_range_2 ofs). lia.
          - repeat rewrite unsigned_add. i. des.
            + instantiate (1:=(SkEnv.get_sig skd)). lia.
            + exploit Mem.mi_representable; eauto. left. eapply Mem.perm_cur.
              eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
              clear - ARGSRANGE l. lia.
            + clear - ARGSRANGE.
              set (size_arguments_above (SkEnv.get_sig skd)).
              set (Ptrofs.unsigned_range_2 ofs). lia. }
        { set (Ptrofs.unsigned_range_2 (Ptrofs.add ofs (Ptrofs.repr delta))). lia. }
      * exploit SimSymbIdInv_find_None; try eassumption.
        { unfold Genv.find_funct. des_ifs. eauto. }
        { clarify. }
        { rewrite <- H2. ss. }
      * clear - H3 SIG SIMSKELINK.
        inv SIMSKELINK. ss. inv INJECT. inv SIMSKENV.
        unfold Genv.find_funct_ptr in *. des_ifs_safe.
        exploit IMAGE; eauto.
        { left. eapply Genv.genv_defs_range; eauto. }
        { i. des. clarify. rewrite Heq. esplits; eauto. }
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
        inv PUBLIC. inv mi_inj. exploit mi_align; eauto.
        eapply Mem.free_range_perm in FREE.
        intros ofs0 RANGE. exploit FREE; eauto.
        -- instantiate (1:=ofs0). instantiate (1:=Ptrofs.unsigned ofs) in RANGE. nia.
        -- i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. econs.
      * eauto.
    + inv MLE. econs; s; eauto.

  - (** ******************* after external **********************************)
    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } instantiate (1:=asm). intros GEMATCH.
    inv MATCH. inv AFTERSRC. inv SIMRET. inv HISTORY.
    inv CALLSRC. inv CALLTGT. inv SIMARGS.
    rewrite RSRSP in *. rewrite FPTR in *. des. ss. des_ifs. clarify.
    cinv (AGREE Asm.RSP); rewrite RSRSP in *; ss; clarify; rewrite RSP0 in *; clarify.

    assert (SKD: skd1 = skd).
    { inv SIMSKENV. inv SIMSKELINK. ss. inv INJECT.
      cinv (AGREE PC); rewrite FPTR in *; clarify. eauto.
      exploit IMAGE; eauto.
      - left. clear - SIG0. unfold Genv.find_funct_ptr in *.
        des_ifs. eapply Genv.genv_defs_range; eauto.
      - rewrite FPTR0 in *. clear - SIG0 SIG1 SIMSKENVLINK H1.
        i. des. clarify. inv SIMSKENVLINK. inv SIMSKENV. clarify. } clarify.

    hexploit (@Mem_unfree_parallel P sm0 sm_arg sm_ret); eauto.
    { rewrite MEMSRC in *. eauto. }

    i. des. esplits; eauto. i.
    esplits; ss; eauto.

    + econs; ss; eauto.
      * esplits; eauto. rewrite FPTR0. eauto.
      * eauto. rewrite MEMTGT in *. eauto.
    + dup MLE2. rename MLE4 into MINVLE2.
      destruct MLE2 as [MLE2 MINVEQSRC2 MINVEQTGT2].
      econs; try refl; eauto.
      * clarify. inv MLE2. ii.
        unfold set_pair, Pregmap.set, loc_external_result, map_rpair.
        des_ifs; ss; eauto.
        { rewrite MINJ. eauto. }
        { unfold regset_after_external. des_ifs; ss; eauto. }
        { rewrite MINJ. eapply Val.loword_inject. eauto. }
        { rewrite MINJ. eapply Val.hiword_inject. eauto. }
        { unfold regset_after_external. des_ifs; ss; eauto. }
      * inv MLE2. eapply agree_incr; eauto.
      * inv MLE2. i. exploit RSPDELTA; eauto. i. des. esplits; eauto.

  - (** ******************* final **********************************)

    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv MATCH. inv FINALSRC.

    destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
    dup MWF. rename MWF0 into MINVWF.
    destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.

    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
    exploit Mem_free_parallel'; eauto.
    { instantiate (3:=Ptrofs.zero). zsimpl. psimpl. eauto. }
    i. des.
    hexploit (@SimMemInjInv.le_inj_wf_wf top1 P sm0 sm1); eauto.
    { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
      - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
      - eapply Mem.free_unchanged_on; eauto.
        ii. exploit INVRANGETGT; eauto. i. des. exploit H3; eauto.
        eapply Mem.perm_cur. eapply Mem.perm_implies.
        + eapply Mem.free_range_perm; eauto.
          instantiate (1:=delta). lia.
        + econs. } intros MWFINV0.

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
      * clear - EXTERNAL AGREE SIMSKENVLINK SIMSKENV WFINITSRC RSRA.
        unfold external_state, Genv.find_funct, Genv.find_funct_ptr in *.
        cinv (AGREE PC); eauto.
        { rewrite <- H0 in *. des_ifs_safe.
          inv SIMSKENV. ss. inv SIMSKELINK. ss. inv SIMSKENV.
          inv INJECT. exploit IMAGE; eauto.
          - right. eapply Genv.genv_defs_range in Heq0. ss.
          - i. des. clarify. rewrite Heq0 in *. clarify. }
        { exfalso. rewrite <- H1 in *. inv WFINITSRC. eauto. }
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
   + econs; ss; eauto.

  - (** ******************* step **********************************)
    left; i.
    esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + exists O.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        inv SIMSKENV. destruct st0. ss. clarify.
        destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
        dup MWF. rename MWF0 into MINVWF.
        destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.

        exploit asm_step_preserve_injection; eauto.
        { exploit SimSymbIdInv_match_globals; eauto.
          intros MATCH. inv MATCH. econs; ss; i; eauto.
          exploit DEFLE; eauto. i. des. clarify. esplits; eauto. }
        { eapply symbols_inject_weak_imply.
          exploit SimMemInjInvC.skenv_inject_symbols_inject; eauto. }
        { cinv MWF. eauto. }

        i. des.
        eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).

        exploit SimMemInjC.parallel_gen; eauto.
        { ii. eapply asm_step_max_perm; eauto. }
        { ii. eapply asm_step_max_perm; eauto. }
        i. des.
        hexploit SimMemInjInv.le_inj_wf_wf; eauto.
        { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
          - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
          - eapply Mem.unchanged_on_implies; eauto.
            i. exploit INVRANGETGT; eauto. i. des. eauto. } intros MWFINV0.
        eexists (SimMemInjInv.mk _ _ _).

        esplits; eauto.
        - left. econs; cycle 1.
          + apply star_refl.
          + symmetry. apply E0_right.
          + econs.
            * apply AsmC.modsem_determinate.
            * econs; ss; eauto.
        - econs; ss; eauto.
        - econs; ss; eauto.
          + eapply agree_incr; eauto.
          + i. exploit RSPDELTA; eauto. i. des. esplits; eauto.
      }
      Unshelve. all: apply 0.
Qed.

End INJINV.
