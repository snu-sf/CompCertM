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
From compcertr Require Import Events Integers Conventions.
Require Import Preservation.
Require Import LocationsC.
Require Import Conventions1C.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import StoreArguments StoreArgumentsProps.
Require Import AsmStepInj IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import AsmExtra IdSimExtra IdSimAsmExtra IdSimInvExtra.

Require Import MatchSimModSemExcl2.
Require Import Conventions1C.

Require Import mktac.

From compcertr Require Import AST.

Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.



Section INJINV.

Variable P: SimMemInjInv.memblk_invariant.

Local Instance SimMemP: SimMem.class := SimMemInjInvC.SimMemInjInv SimMemInjInv.top_inv P.
Local Instance SimSymbP: SimSymb.class SimMemP := SimMemInjInvC.SimSymbIdInv P.
Local Existing Instance SoundTop.Top.

Lemma asm_inj_inv_id
      (asm: Asm.program)
      (WF: Sk.wf (module asm))
  :
    exists mp,
      (<<SIM: ModPair.sim mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=SimMemInjInvC.mk bot1 _ _).
  econs; ss; i.
  { econs; ss; i; clarify. }
  eapply MatchSimModSemExcl2.match_states_sim with
      (match_states :=
         @match_states
           SimMemInjInv.top_inv P
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
    inv SIMARGS.
    { ss. clarify.
      inv INITTGT; clarify. ss. inv TYP. cinv STORE.

      exploit store_arguments_parallel; eauto.
      { eapply typify_has_type_list; eauto. }
      { exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto. i. des.
        inv WFTGT. rpapply WFPARAM; eauto; ss. }
      { eapply inject_list_typify_list; try eassumption.
        erewrite inject_list_length; eauto. } i. des.
      hexploit (assign_junk_blocks_parallel n); eauto. i. des.
      eexists (AsmC.mkstate (((to_pregset (set_regset_junk (SimMemInj.src sm1) m0 n rs_src (to_mregset rs) (fn_sig fd))) # PC <- fptr_src)
                               # RA <- (src_junk_val (SimMemInj.src sm1) m0 n (rs RA)))
                            # RSP <- (Vptr (Mem.nextblock (SimMemInj.src sm_arg)) Ptrofs.zero)
                            (Asm.State _ _)).
    hexploit (@SimMemInjInv.le_inj_wf_wf SimMemInjInv.top_inv P sm_arg sm0); eauto.
    { etrans; eauto. }
    { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
      - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
      - eapply Mem.unchanged_on_implies with (P:=top2); ss. etrans.
        + eapply store_arguments_unchanged_on; eauto.
        + rewrite <- MTGT. rewrite MTGT0.
          eapply JunkBlock.assign_junk_blocks_unchanged_on. } intros MWFINV1.

    eexists (SimMemInjInv.mk sm0 _ _). esplits; eauto.
      { econs; ss; eauto.
        - inv SAFESRC; clarify. ss. des.
          exploit match_globals_find_funct; eauto. i.
          setoid_rewrite FINDF in H. clarify.
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
            rewrite NBSRC.
            etrans; eauto. etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto. }
          exfalso. eapply Plt_lemma; eauto.
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
        - i. unfold Pregmap.set in *. des_ifs; eauto.
          { exploit PTRFREE.
            - ii. eapply src_junk_val_junk in H; eauto.
            - i. des; clarify. } left.
          unfold to_pregset, set_regset_junk, to_mregset in *. des_ifs; ss.
          + exploit PTRFREE.
            * ii. eapply src_junk_val_junk in H; eauto.
            * i. erewrite to_mreg_some_to_preg in *; eauto. des; ss.
              clarify. esplits; eauto.
          + esplits; eauto. erewrite loc_notin_not_in in n3. tauto. }

      { econs; ss; eauto. etrans; eauto. }

      { assert (AGREE0:
                  AsmStepInj.agree
                    (SimMemInj.inj sm0)
                    (((to_pregset (set_regset_junk (SimMemInj.src sm1) m0 n rs_src (to_mregset rs) (fn_sig fd)))
                        # PC <- fptr_src) # RA <- (src_junk_val (SimMemInj.src sm1) m0 n (rs RA))) # RSP <-
                    (Vptr (Mem.nextblock (SimMemInj.src sm_arg)) Ptrofs.zero) rs).
        { ii. unfold Pregmap.set, to_mregset, to_pregset, to_preg.
          inv MLE0. des_ifs; ss; eauto.
          - eapply val_inject_incr; eauto. rewrite INJ.
            unfold update_meminj. rewrite H1. econs; des_ifs. ss.
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

        - instantiate (1:=fd). inv SAFESRC; clarify. ss. des.
          exploit match_globals_find_funct; eauto. i.
          setoid_rewrite FINDF in H. clarify.
        - econs.
          + econs; eauto.
            * unfold Pregmap.set. des_ifs.
            * unfold Pregmap.set. des_ifs. unfold src_junk_val. des_ifs.
            * unfold Pregmap.set. des_ifs. unfold src_junk_val.
              assert (JUNK: JunkBlock.is_junk_value (SimMemInj.tgt sm1) (JunkBlock.assign_junk_blocks (SimMemInj.tgt sm1) n) (rs RA)).
              { apply NNPP. ii. exploit PTRFREE; eauto. i. des; clarify. }
              clear - RADEF JUNK.
              unfold JunkBlock.is_junk_value, Mem.valid_block in *. des_ifs; des; eauto.
          + econs; ss. ii. congruence.
          + { unfold to_pregset, set_regset, Pregmap.set. ii.
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
                  apply loc_args_callee_save_disjoint in n3. exfalso. eauto. }
          + ss.
        - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
          eapply Genv.genv_defs_range in Heq0. exfalso. eapply RANOTFPTR; eauto.
        - unfold Pregmap.set. des_ifs. ii. clarify. rewrite MINJ. rewrite INJ.
          unfold junk_inj, update_meminj. des_ifs; eauto. }
    }
    { ss. inv INITTGT; clarify. ss.
      hexploit (assign_junk_blocks_parallel n); eauto. i. des.

      eexists (AsmC.mkstate
                 (rs_src # RA <- (src_junk_val (SimMemInj.src sm_arg) (SimMemInj.tgt sm_arg) n ra))
                 (Asm.State
                    (rs_src # RA <- (src_junk_val (SimMemInj.src sm_arg) (SimMemInj.tgt sm_arg) n ra))
                    (SimMemInj.src sm1))).
      esplits; eauto.
      - econs 2; ss; eauto.
        + inv SAFESRC; clarify. ss. des.
          exploit match_globals_find_funct; eauto.
          * eapply RS.
          * i. setoid_rewrite FINDF in H. clarify.
        + unfold Pregmap.set. des_ifs. unfold src_junk_val.
          des_ifs; split; ss; eauto; des; clarify.
        + unfold src_junk_val. des_ifs. i. clarify. ii. apply n0.
          assert (PLT: Plt (b + Mem.nextblock (SimMemInj.src sm_arg) - Mem.nextblock (SimMemInj.tgt sm_arg)) (Mem.nextblock (SimMemInj.src sm_arg))).
          { eapply Plt_Ple_trans; eauto.
            inv SIMSKENV. inv SIMSKELINK. ss. inv MLE. inv MWF.
            rewrite NBSRC. etrans; eauto. }
          exfalso. eapply Plt_lemma; eauto.
        + rewrite MSRC. eapply src_junk_val_junk; eauto.
      - instantiate (1:=SimMemInjInv.mk sm1 _ _). econs; ss.
      - cinv MWF. econs; eauto; simpl.
        + eapply AsmStepInj.agree_step; eauto.
          * eapply agree_incr; try apply RS; eauto.
            rewrite MINJ. eapply junk_inj_incr; eauto.
          * rewrite MINJ. eapply src_junk_val_inj; eauto.
        + eapply AsmStepInj.agree_step; eauto.
          * eapply agree_incr; try apply RS; eauto.
            rewrite MINJ. eapply junk_inj_incr; eauto.
          * rewrite MINJ. eapply src_junk_val_inj; eauto.
        + hexploit (@SimMemInjInv.le_inj_wf_wf SimMemInjInv.top_inv P sm_arg sm1); eauto.
          eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
          { ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto. }
          { eapply Mem.unchanged_on_implies with (P:=top2); ss. rewrite MTGT.
            eapply JunkBlock.assign_junk_blocks_unchanged_on. }
        + rewrite Pregmap.gso; clarify.
          inv SAFESRC; clarify. ss. des.
          exploit match_globals_find_funct; eauto.
          * eapply RS.
          * i. setoid_rewrite FINDF in H. clarify. eauto.
        + econs 2; eauto.
          * unfold src_junk_val. econs; eauto; rewrite Pregmap.gss.
            { des_ifs. }
            { des_ifs; clarify; ss; des; clarify. }
          * econs; eauto; rewrite Pregmap.gss.
        + rewrite Pregmap.gss. unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs.
          eapply Genv.genv_defs_range in Heq. exfalso. eapply RANOTFPTR; eauto.
        + i. des. clarify. }

  - (** ******************* safe **********************************)
    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH. des.
    inv SAFESRC.
    { inv TYP. inv SIMARGS; clarify. ss.
      eapply asm_initial_frame_succeed; eauto.
      + apply inject_list_length in VALS.
        transitivity (Datatypes.length vs_src); eauto.
      + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
        i. des. inv WFSRC. eapply WFPARAM in H; eauto.
      + exploit match_globals_find_funct; eauto. }
    { inv SIMARGS; clarify. ss.
      eapply asm_initial_frame_succeed_asmstyle; eauto.
      exploit match_globals_find_funct; eauto. eapply RS. }

  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC.
    { inv MATCH.
      destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
      dup MWF. rename MWF0 into MINVWF.
      destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.
      des; ss; clarify. des_ifs.
      set (INJPC:= AGREE PC). cinv INJPC; rewrite <- H1 in *; ss; clarify.
      assert (delta = 0).
      { psimpl. inv SIMSKELINK. ss. inv INJECT. exploit IMAGE; eauto. rewrite <- H0 in *.
        - left. ss. clear - SIG. unfold Genv.find_funct_ptr in *.
          des_ifs. eapply Genv.genv_defs_range; eauto.
        - i. des. eauto. }
      clarify. psimpl. ss.
      exploit extcall_arguments_inject; eauto.
      { inv MWF. eauto. }
      i. des. cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

      exploit SimMemInjC.Mem_free_parallel'; eauto. i. des.
      hexploit (@SimMemInjInv.le_inj_wf_wf SimMemInjInv.top_inv P sm0 sm1); eauto.
      { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
        - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
        - eapply Mem.free_unchanged_on; eauto. ii.
          exploit INVRANGETGT; eauto. i. des. exploit H6; eauto.
          eapply Mem.perm_cur. eapply Mem.perm_implies.
          + eapply Mem.free_range_perm; eauto.
            instantiate (1:=Ptrofs.unsigned ofs + delta). lia.
          + econs. } intros MWFINV0.

      eexists (Args.mk (Vptr b2 _) _ _). eexists (SimMemInjInv.mk sm1 _ _).
      esplits; eauto; ss; i.
      + econs; auto.
        * eauto.
        * exploit SimSymbIdInv_find_None; try eassumption.
          { ii. rewrite H in *. ss. }
          { unfold Genv.find_funct. des_ifs. }
        * esplits; eauto. inv SIMSKELINK. inv INJECT. inv SIMSKENV. ss.
          rewrite <- H0 in *. inv INJPC. exploit IMAGE; eauto.
          { left. eapply Genv.genv_defs_range; eauto. ss.
            unfold Genv.find_funct_ptr in *. clear EXTERNAL. des_ifs; eauto. }
          { i. des. clarify. }
        * clear - AGREE TPTR RADEF. splits.
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        * eauto.
        * eauto.
        * destruct (zlt 0 (size_arguments sg)).
          { inv MWF. exploit Mem.mi_representable; eauto.
            - right.
              instantiate (1:=Ptrofs.add ofs (Ptrofs.repr (4 * size_arguments sg))).
              eapply Mem.perm_cur.
              eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
              rewrite unsigned_add.
              + clear - ARGSRANGE l. lia.
              + clear- ARGSRANGE. set (size_arguments_above sg).
                set (Ptrofs.unsigned_range_2 ofs). lia.
            - repeat rewrite unsigned_add. i. des.
              + lia.
              + exploit Mem.mi_representable; eauto. left. eapply Mem.perm_cur.
                eapply Mem.perm_implies; try eapply Mem.free_range_perm; eauto; [|econs].
                clear - ARGSRANGE l. lia.
              + clear - ARGSRANGE.
                set (size_arguments_above sg).
                set (Ptrofs.unsigned_range_2 ofs). lia. }
          { set (Ptrofs.unsigned_range_2 (Ptrofs.add ofs (Ptrofs.repr delta))). lia. }
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
      + inv MLE. econs; s; eauto. rewrite H0. rewrite H1. eauto.
    }
    { ss. inv MATCH.
      des; ss; clarify. des_ifs.
      set (INJPC:= AGREE PC). cinv INJPC; rewrite <- H1 in *; ss; clarify.
      assert (delta = 0).
      { psimpl. inv SIMSKELINK. ss. inv INJECT. exploit IMAGE; eauto. rewrite <- H0 in *.
        - left. ss. clear - SIG. unfold Genv.find_funct_ptr in *.
          des_ifs. eapply Genv.genv_defs_range; eauto.
        - i. des. eauto. } clarify. psimpl. ss.
      exists (Args.Asmstyle rs_tgt (SimMemInj.tgt sm0.(SimMemInjInv.minj))). esplits; eauto.
      - econs 2; eauto.
        + exploit SimSymbIdInv_find_None; try eassumption.
          { ii. rewrite H in *. ss. }
          { unfold Genv.find_funct. des_ifs. }
        + esplits; eauto. inv SIMSKELINK. inv INJECT. inv SIMSKENV. ss.
          rewrite <- H0 in *. inv INJPC. exploit IMAGE; eauto.
          { left. eapply Genv.genv_defs_range; eauto. ss.
            unfold Genv.find_funct_ptr in *. clear EXTERNAL. des_ifs; eauto. }
          { i. des. clarify. rewrite <- H1 in *. auto. }
        + clear - AGREE TPTR RADEF. splits.
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      - econs 2; eauto.
      - refl. }

  - (** ******************* after external **********************************)
    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } instantiate (1:=asm). intros GEMATCH.
    inv MATCH. inv AFTERSRC.
    { inv SIMRET; clarify. inv HISTORY; clarify.
      inv CALLSRC; clarify; cycle 1.
      { ss. des. clarify. }
      inv CALLTGT; clarify; cycle 1.
      { ss. des. clarify. ss. inv SIMARGS; clarify. } inv SIMARGS; clarify.
      rewrite RSRSP in *. des. ss. des_ifs. clarify.
      cinv (AGREE Asm.RSP); rewrite RSRSP in *; ss; clarify; rewrite RSP0 in *; clarify.

      assert (SKD: skd1 = skd).
      { inv SIMSKENV. inv SIMSKELINK. ss. inv INJECT.
        cinv (AGREE PC); rewrite <- H1 in *; clarify. eauto.
        exploit IMAGE; eauto.
        - left. rewrite <- H0 in *. ss. clear - SIG0. unfold Genv.find_funct_ptr in *.
          des_ifs. eapply Genv.genv_defs_range; eauto.
        - i. des. clarify. inv SIMSKENVLINK. inv SIMSKENV. clarify.
          rewrite <- H0 in *. ss. des_ifs. } clarify.

      hexploit (@Mem_unfree_parallel P sm0 sm_arg sm_ret); eauto.

      i. des. esplits; eauto. i.
      esplits; ss; eauto.

      + econs; ss; eauto.
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
    }
    { inv SIMRET; clarify. inv HISTORY; clarify.
      inv CALLSRC; clarify.
      { ss. des. clarify. }
      inv CALLTGT; clarify.
      { ss. des. clarify. ss. inv SIMARGS; clarify. } inv SIMARGS; clarify. ss.
      exists (SimMemInjInvC.unlift' sm_arg sm_ret).
      eexists. eexists (AsmC.mkstate _ (Asm.State _ _)). esplits; eauto.
      - etrans; eauto.
      - clear - MLE0. inv MLE0. inv MLE. ss. econs; ss; eauto. eapply SimMemInj.frozen_refl.
      - i. esplits; eauto.
        + econs 2; eauto.
        + exploit SimMemInjInvC.unlift_wf; try apply MLE0; eauto. i. inv MLE2.
          cinv MLE3. ss.
          econs; try apply H; auto; eauto.
          * eapply AsmStepInj.agree_step; eauto.
          * eapply AsmStepInj.agree_incr; eauto.
          * i. exploit RSPDELTA; eauto. i. des. eauto. }

  - (** ******************* final **********************************)

    exploit SimSymbIdInv_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv MATCH. inv FINALSRC.
    {
      destruct sm0 as [sm0 mem_inv_src mem_inv_tgt].
      dup MWF. rename MWF0 into MINVWF.
      destruct MWF as [MWF SATSRC SATTGT INVRANGESRC INVRANGETGT]. ss.
      cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      exploit SimMemInjC.Mem_free_parallel'; eauto.
      { instantiate (3:=Ptrofs.zero). zsimpl. psimpl. eauto. }
      i. des.
      hexploit (@SimMemInjInv.le_inj_wf_wf SimMemInjInv.top_inv P sm0 sm1); eauto.
      { eapply SimMemInjInv.private_unchanged_on_invariant; eauto.
        - ii. exploit INVRANGETGT; eauto. i. des. inv MWF. eapply Plt_Ple_trans; eauto.
        - eapply Mem.free_unchanged_on; eauto.
          ii. exploit INVRANGETGT; eauto. i. des. exploit H3; eauto.
          eapply Mem.perm_cur. eapply Mem.perm_implies.
          + eapply Mem.free_range_perm; eauto.
            instantiate (1:=delta). lia.
          + econs. } intros MWFINV0.

      assert (delta = 0).
      { rewrite FINDF in *. clarify. exploit RSPDELTA; eauto. i. des. clarify. }
      clarify. ss. zsimpl.

      esplits; ss; eauto.
      + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
        econs; ss; ii; eauto.
        * des. esplits; eauto.
          eapply match_globals_find_funct; eauto.
        * inv WFINITRS; clarify. clear - EXTERNAL AGREE SIMSKENVLINK SIMSKENV WFINITSRC RSRA.
          unfold external_state, Genv.find_funct, Genv.find_funct_ptr in *.
          cinv (AGREE PC); eauto.
          { rewrite <- H0 in *. des_ifs_safe.
            inv SIMSKENV. ss. inv SIMSKELINK. ss. inv SIMSKENV.
            inv INJECT. exploit IMAGE; eauto.
            - right. eapply Genv.genv_defs_range in Heq0. ss.
            - i. des. clarify. rewrite Heq0 in *. clarify. }
          { exfalso. rewrite <- H1 in *. inv WFINITSRC. eauto. }
        * inv WFINITRS; clarify. inv WFINITSRC. inv WFINITTGT.
          unfold Val.has_type in TPTR. des_ifs.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
          -- ss. clear RANOTFPTR. des_ifs.
             cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
        * specialize (CALLEESAVE _ H).
          specialize (AGREEINIT (to_preg mr0)).
          specialize (AGREE (to_preg mr0)). inv WFINITRS; clarify.
          clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H UNDEF.
          inv WFINITSRC.
          eapply lessdef_commute; eauto.
        * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
          cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      + econs; ss. eapply val_inject_incr; cycle 1; eauto.
        inv MLE. eauto.
      + econs; ss; eauto.
    }
    { exists sm0. exists (Retv.Asmstyle rs_tgt sm0.(SimMemInjInv.minj).(SimMemInj.tgt)).
      esplits; ss; eauto.
      + econs 2; ss; ii; eauto.
        * des. esplits; eauto.
          eapply match_globals_find_funct; eauto.
        * des.
          inv WFINITRS; clarify. clear - EXTERNAL AGREE SIMSKENVLINK SIMSKENV WFINITSRC RSRA.
          unfold external_state, Genv.find_funct, Genv.find_funct_ptr in *.
          cinv (AGREE PC); eauto.
          { rewrite <- H0 in *. des_ifs_safe.
            inv SIMSKENV. ss. inv SIMSKELINK. ss. inv SIMSKENV.
            inv INJECT. exploit IMAGE; eauto.
            - right. eapply Genv.genv_defs_range in Heq0. ss.
            - i. des. clarify. rewrite Heq0 in *. clarify. }
          { exfalso. rewrite <- H1 in *. inv WFINITSRC. eauto. }
        * des. des_ifs. clarify.
          inv WFINITRS; clarify. inv WFINITSRC. inv WFINITTGT.
          unfold Val.has_type in TPTR. des_ifs.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
          -- ss. clear RANOTFPTR. des_ifs.
             cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
      + econs 2; ss.
      + refl. }

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
