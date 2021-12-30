Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemId SimMemExt.
From compcertr Require SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
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

Require Import AsmregsC Conventions1C.
Require Import MatchSimModSemExcl2 MatchSimModSem.
Require Import StoreArguments StoreArgumentsProps.
Require Import AsmStepInj AsmStepExt IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import AsmExtra IdSimExtra.
Require Import IdSimAsmExtra.

Require Import mktac.

From compcertr Require Import AST.

Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.


(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)

Lemma asm_id
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>).
Proof.
  eapply any_id; eauto.
Qed.

Section LOCALPRIV.

  Variable skenv_link: SkEnv.t.

  Inductive sound_state (su: Sound.t): AsmC.state -> Prop :=
  | sound_state_intro
      (init_rs rs0: regset) m0
      (RS: forall pr, UnreachC.val' su (rs0#pr))
      (MEM: UnreachC.mem' su m0)
      (* (INIT: forall pr, UnreachC.val' su (init_rs#pr)) *)
      (WF: Sound.wf su)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next)):
      sound_state su (mkstate init_rs (State rs0 m0)).

  Inductive has_footprint: AsmC.state -> Sound.t -> mem -> Prop :=
  | has_footprint_intro
      su0 blk1 ofs
      init_rs (rs0: regset) m_unused m1 sg
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC)
                        = Some skd /\ Sk.get_csig skd = Some sg)
      (RSP: rs0 RSP = Vptr blk1 ofs)
      (FREEABLE: Mem.range_perm m1 blk1 (Ptrofs.unsigned (ofs))
                                (Ptrofs.unsigned (ofs) + 4 * (size_arguments sg))
                                Cur Freeable)
      (VALID: Mem.valid_block m1 blk1)
      (PUB: ~ su0.(Unreach.unreach) blk1):
      has_footprint (mkstate init_rs (State rs0 m_unused)) su0 m1
  | has_footprint_asmstyle
      su0 init_rs (rs0: regset) m_unused m1
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC)
                        = Some skd /\ Sk.get_csig skd = None)
    :
      has_footprint (mkstate init_rs (State rs0 m_unused)) su0 m1.

  Inductive mle_excl: AsmC.state -> Sound.t -> mem -> mem -> Prop :=
  | mle_excl_intro
      init_rs rs0 m_unused (su0: Unreach.t) m0 m1
      blk1 sg ofs1
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC)
                        = Some skd /\ Sk.get_csig skd = Some sg)
      (RSP: rs0 RSP = Vptr blk1 ofs1)
      UNFR
      (UNFRDEF: UNFR = (brange blk1 (Ptrofs.unsigned ofs1)
                                           (Ptrofs.unsigned (ofs1) + 4 * (size_arguments sg))))
      (PERM: forall blk ofs
          (VALID: (Mem.valid_block m0) blk)
          (UNFREE: ~ UNFR blk ofs),
          (Mem.perm m1) blk ofs Max <1= (Mem.perm m0) blk ofs Max)
      (UNCH: Mem.unchanged_on (~2 UNFR) m0 m1):
      mle_excl (mkstate init_rs (State rs0 m_unused)) su0 m0 m1
  | mle_excl_asmstyle
      init_rs rs0 m_unused (su0: Unreach.t) m0 m1
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC)
                        = Some skd /\ Sk.get_csig skd = None)
      (MEM: m0 = m1):
      mle_excl (mkstate init_rs (State rs0 m_unused)) su0 m0 m1.

  Lemma unreach_free su m0 m1 blk lo hi
        (MEM: UnreachC.mem' su m0)
        (FREE: Mem.free m0 blk lo hi = Some m1):
      UnreachC.mem' su m1.
  Proof.
    inv MEM. exploit Mem.free_unchanged_on; eauto.
    { instantiate (1:=~2 brange blk lo hi). ii. eauto. } intros UNCH.
    econs.
    - ii. eapply SOUND; eauto.
      + eapply Mem.perm_free_3; eauto.
      + erewrite <- Mem.unchanged_on_contents; eauto.
        * unfold brange. ii. des. clarify. eapply Mem_free_noperm; eauto.
          apply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
        * eapply Mem.perm_free_3; eauto.
    - ii. eapply BOUND in PR. eapply Mem.valid_block_unchanged_on; eauto.
    - etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    - etrans; eauto. symmetry. eapply Mem.nextblock_free; eauto.
  Qed.

  Lemma unreach_unfree su m0 m1 blk lo hi
        (MEM: UnreachC.mem' su m0)
        (UNFREE: Mem_unfree m0 blk lo hi = Some m1):
      UnreachC.mem' su m1.
  Proof.
    inv MEM. exploit Mem_unfree_unchanged_on; eauto. intros UNCH. econs.
    - ii. assert (NIN: ~ brange blk lo hi blk0 ofs).
      { unfold brange. ii. des. clarify. unfold Mem_unfree in *. des_ifs. ss.
        rewrite PMap.gss in PTR. rewrite Mem_setN_in_repeat in PTR; clarify.
        rewrite Z2Nat_range. des_ifs; lia. }
      eapply SOUND; eauto.
      + eapply Mem.perm_unchanged_on_2; eauto; ss. eapply Mem.perm_valid_block in PERM.
        eapply Mem_nextblock_unfree in UNFREE. unfold Mem.valid_block in *. rewrite UNFREE. auto.
      + erewrite <- Mem.unchanged_on_contents; eauto.
        * eapply Mem.perm_unchanged_on_2; eauto; ss. eapply Mem.perm_valid_block in PERM.
          eapply Mem_nextblock_unfree in UNFREE. unfold Mem.valid_block in *. rewrite UNFREE. auto.
    - ii. eapply BOUND in PR. eapply Mem.valid_block_unchanged_on; eauto.
    - etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    - etrans; eauto. eapply Mem_nextblock_unfree; eauto.
  Qed.

  Lemma asm_unreach_local_preservation
        asm
        (INCL: SkEnv.includes skenv_link (Sk.of_program fn_sig asm))
        (SKENVWF : SkEnv.wf skenv_link):
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link asm) sound_state>>.
  Proof.
    esplits. eapply local_preservation_strong_horizontal_excl_spec with (lift := UnreachC.le') (sound_state := (sound_state)); eauto.
    instantiate (1:= AsmC.get_mem).
    eapply local_preservation_strong_horizontal_excl_intro with
        (has_footprint := has_footprint)
        (mle_excl := mle_excl); ii; ss; eauto.
    { eapply UnreachC.liftspec; et. }
    - (* FOOTEXCL *)
      inv MLE. inv FOOT.
      { inv MLEEXCL; cycle 1.
        { des. clarify. }
        ss. des. rewrite RSP in *. clarify. econs; et.
        + i.
          destruct (classic (brange blk0
                                    (Ptrofs.unsigned ofs1)
                                    (Ptrofs.unsigned ofs1 + 4 * size_arguments sg) blk ofs)).
          * rr in H. des; clarify. eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem.
          * eapply PERM; et.
            eapply PERM0; et.
            eapply Mem.valid_block_unchanged_on; et.
        + i. r. eapply RO; et.
          erewrite <- Mem.loadbytes_unchanged_on_1; et.
          * eapply Mem.valid_block_unchanged_on; et.
          * ii. inv H0. eapply RO0; et. eapply Mem.perm_cur.
            eapply Mem.perm_implies with Freeable; eauto with mem.
        + eapply Mem_unchanged_on_trans_strong; et.
          eapply Mem.unchanged_on_implies; try apply PRIV0; et.
          u. i; des; clarify; ss.
      }
      { inv MLEEXCL.
        { des. clarify. }
        econs; eauto. }

    - (* init *)

      inv INIT.
      { ss. des. inv WF. inv STORE.

        (* inv SUARG. des. ss. inv WF. *)
        (* inv INIT. inv STORE. *)
        eexists (Unreach.mk
                   (Unreach.unreach su_arg)
                   (Unreach.ge_nb su_arg)
                   (Mem.nextblock (JunkBlock.assign_junk_blocks m0 n))).
        assert (UNCH: Mem.unchanged_on
                        top2
                        m_arg
                        (JunkBlock.assign_junk_blocks m0 n)).
        { etrans.
          - eapply store_arguments_unchanged_on; eauto.
          - eapply Mem.unchanged_on_implies.
            + eapply JunkBlock.assign_junk_blocks_unchanged_on.
            + ss. }

        inv MEM.
        assert (NBLE: Plt (Unreach.nb su_arg) (Mem.nextblock (JunkBlock.assign_junk_blocks m0 n))).
        { rewrite NB. eapply Plt_Ple_trans.
          - instantiate (1:=Mem.nextblock m0).
            inv H. eapply Mem.nextblock_alloc in ALC.
            rewrite <- NB0. rewrite ALC. extlia.
          - rewrite JunkBlock.assign_junk_blocks_nextblock. des_ifs; extlia. }

        esplits; ss.
        + econs; ss. split; ss. apply Plt_Ple; auto.
        + inv TYP.

          assert (SOUNDIMPLY: forall blk (SOUNDV: ~ Unreach.unreach su_arg blk /\
                                                  (blk < Unreach.nb su_arg)%positive),
                     ~ Unreach.unreach su_arg blk /\
                     (blk < Mem.nextblock (JunkBlock.assign_junk_blocks m0 n))%positive).
          { ii. des. split; auto. etrans; eauto. }

          assert (SURS: forall pr,
                     UnreachC.val'
                       (Unreach.mk
                          (Unreach.unreach su_arg)
                          (Unreach.ge_nb su_arg)
                          (Mem.nextblock (JunkBlock.assign_junk_blocks m0 n)))
                       (rs pr)).
          {
            ii. ss. apply NNPP. intros NSOUND. exploit PTRFREE.
            - instantiate (1:=pr). unfold JunkBlock.is_junk_value. des_ifs. ii.
              des. apply not_and_or in NSOUND. des; eauto.
              apply NNPP in NSOUND. apply WFHI in NSOUND.
              rewrite NB in *. apply H1. clear H2.
              eapply Mem.valid_block_unchanged_on; eauto.
              eapply store_arguments_unchanged_on; eauto.
            - i. des.
              + dup H. eapply store_arguments_unchanged_on in H1.
                eapply Mem.unchanged_on_nextblock in H1. apply NSOUND. apply SOUNDIMPLY.
                inv H.
                clear - VALS0 ARG MR PTR VALS NB H1 SOUNDIMPLY.
                unfold typify_list, Sound.vals, Mach.extcall_arguments in *.
                revert VALS pr PTR mr MR ARG VALS0.
                generalize (loc_arguments_one (fn_sig fd)).
                generalize (loc_arguments (fn_sig fd)).
                generalize (sig_args (fn_sig fd)).

                induction vs_arg; ss.
                * ii. inv VALS. inv VALS0. ss.
                * ii. des_ifs; inv VALS0; ss. inv VALS.
                  exploit H; eauto. i. destruct a1; ss. des.
                  { clarify. inv H4. inv H7. unfold to_mregset in *.
                    erewrite to_mreg_some_to_preg in *; eauto.
                    unfold typify in *. des_ifs; rewrite PTR in *; clarify.
                    exploit H3; eauto. }
                  { eapply IHvs_arg; eauto. }
              + clarify. rewrite PTR in *. exploit VAL; eauto.
              + clarify. rewrite PTR in *. clarify. eapply NSOUND. split.
                * ii. apply WFHI in H0. rewrite NB in *. eapply Plt_strict; eauto.
                * rewrite NB in *. auto.
          }

          econs; ss.
          * econs; ss.
            { i. rewrite JunkBlock.assign_junk_blocks_perm in PERM.
              erewrite Mem.unchanged_on_contents; cycle 1.
              - apply JunkBlock.assign_junk_blocks_unchanged_on.
              - ss.
              - ss.
              - destruct (peq blk (Mem.nextblock m_arg)).
                + clarify. inv H.
                  exploit Mem.alloc_result; eauto. i. clarify.
                  assert (RANGE: 0 <= ofs < 4 * size_arguments (fn_sig fd)).
                  { apply NNPP. ii.
                    rewrite <- Mem.unchanged_on_perm in PERM; eauto.
                    - eapply Mem.perm_alloc_3 in PERM; eauto.
                    - ss. des_ifs.
                    - apply Mem.perm_valid_block in PERM. unfold Mem.valid_block.
                      rewrite NB0. eauto. }
                  assert (UnreachC.memval'
                            su_arg
                            (ZMap.get ofs (Mem.mem_contents m0) !! (Mem.nextblock m_arg))).
                  { ii. exploit ONLYARGS; eauto. rewrite PTR.
                    clarify. ss. i. des.
                    - inv UNDEF.
                    - exploit forall2_in_exists; eauto.
                      + instantiate (1:= One (S Outgoing ofs1 ty)).
                        eapply in_regs_of_rpairs_inv in IN.
                        des. dup IN. eapply LocationsC.loc_arguments_one in IN.
                        unfold is_one in *. des_ifs. inv IN0; auto. inv H.
                      + i. des. inv SAT. inv H1.
                        unfold Mach.load_stack, Stacklayout.fe_ofs_arg in *.
                        ss. psimpl. zsimpl. clarify.
                        rewrite Ptrofs.unsigned_repr in *; cycle 1.
                        { eapply loc_arguments_acceptable_2 in IN.
                          exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
                          i. des. ss. clarify. inv SKENVWF; ss.
                          eapply WFPARAM in H; ss. red in H. inv IN. lia. }
                        Local Transparent Mem.load.
                        unfold Mem.load in H4. des_ifs.
                        exploit MemdataC.decode_fragment_all; eauto.
                        * rewrite <- PTR.
                          eapply Mem.getN_in.
                          erewrite <- size_chunk_conv. eauto.
                        * i. rewrite <- H in *.
                          unfold typify_list in IN0.
                          revert VALS IN0.
                          generalize (sig_args (fn_sig fd)). clear.
                          induction vs_arg; ss.
                          i. des_ifs. ss. des.
                          { unfold typify in *. des_ifs. clear h. ss.
                            inv VALS. ss. exploit H1; eauto. }
                          { inv VALS. eauto. }
                  }
                  ii. ss. eapply SOUNDIMPLY. exploit H; eauto.

                + assert (VALID: Mem.valid_block m_arg blk).
                  { apply Mem.perm_valid_block in PERM. unfold Mem.valid_block in *.
                    inv H. rewrite <- NB0 in *. eapply Mem.nextblock_alloc in ALC.
                    rewrite ALC in *. clear - PERM n0. extlia. }
                  exploit store_arguments_unchanged_on; eauto. intros UNCH0.
                  erewrite Mem.unchanged_on_contents; eauto.
                  * ii. ss. eapply SOUNDIMPLY. eapply SOUND; eauto.
                    eapply Mem.unchanged_on_perm; eauto. ss.
                  * ss.
                  * eapply Mem.unchanged_on_perm; eauto. ss.
            }
            { ii. apply WFHI in PR. rewrite NB in *.
              unfold Mem.valid_block. etrans; eauto. }
            { etrans; eauto. apply Plt_Ple. rewrite NB in *. auto. }

          * econs; ss. ii. apply WFHI in PR. eapply Plt_Ple_trans; eauto.
            apply Plt_Ple. auto.
          * inv SKENV. ss.
        + econs; ss.
          * i. eapply Mem.unchanged_on_perm; eauto. ss.
          * i. erewrite <- Mem.loadbytes_unchanged_on_1; et. i. ss.
          * eapply Mem.unchanged_on_implies; eauto. ss.
      }
      { set (su_new := Unreach.mk
                         su_arg.(Unreach.unreach) su_arg.(Unreach.ge_nb) (Mem.nextblock (JunkBlock.assign_junk_blocks m_arg n))).
        set (UNCH := JunkBlock.assign_junk_blocks_unchanged_on m_arg n).
        assert (HLE: Unreach.hle su_arg su_new).
        { unfold su_new. ss. unfold Unreach.hle. esplits; ss; eauto.
          des. inv MEM. rewrite NB. eapply Mem.unchanged_on_nextblock; eauto. }
        esplits; eauto.
        - unfold Sound.args in *. des. econs; ss; eauto.
          + i. unfold Pregmap.set; des_ifs; eauto.
            * ii. clarify. ss. hexploit RANOTFPTR; eauto. i. des. split; ss.
              ii. des. inv WF. eapply WFHI in H0. inv MEM. rewrite NB in *. eauto.
            * hexploit Sound.hle_val; eauto.
          + inv MEM. econs; ss.
            * i. rewrite JunkBlock.assign_junk_blocks_perm in *.
              erewrite Mem.unchanged_on_contents; eauto; ss.
              unfold su_new. ii. ss. clarify. exploit SOUND; eauto.
              i. des. split; auto. eapply Plt_Ple_trans; eauto. rewrite NB.
              eapply Mem.unchanged_on_nextblock; eauto.
            * ii. eapply Mem.valid_block_unchanged_on; eauto.
            * etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
          + inv WF. unfold su_new. econs; ss; eauto.
            i. eapply Plt_Ple_trans; eauto. inv MEM. rewrite NB.
            eapply Mem.unchanged_on_nextblock; eauto.
          + inv SKENV. ss.
        - ss. econs; eauto.
          + rewrite JunkBlock.assign_junk_blocks_perm in *. eauto.
          + i. erewrite <- Mem.loadbytes_unchanged_on_1; et. i. ss.
          + eapply Mem.unchanged_on_implies; eauto; ss. }

    (* step *)
    - inv STEP. des. destruct st0, st1. ss. clarify. destruct st, st0. ss.

      hexploit asm_step_preserve_injection; try apply STEP0.
      { instantiate (1:=UnreachC.to_inj su0 (Mem.nextblock m)).
        unfold UnreachC.to_inj, Mem.flat_inj in *. econs; ss; i.
        - unfold UnreachC.to_inj, Mem.flat_inj in *. des_ifs. esplits; eauto.
        - inv SUST. esplits; eauto. des_ifs.
          + eapply Genv.genv_symb_range in FINDSRC. ss.
            exfalso. inv WF. eapply WFLO in Heq. rewrite SKE in *. extlia.
          + eapply Genv.genv_symb_range in FINDSRC. ss. exfalso. apply n.
            inv MEM. rewrite SKE in *. eapply Plt_Ple_trans; eauto. }
      { inv SUST. eapply symbols_inject_weak_imply.
        instantiate (1:=skenv_link). unfold symbols_inject. esplits; ss.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. des_ifs; ss.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. esplits; eauto. des_ifs.
          + eapply Genv.genv_symb_range in H0. ss.
            exfalso. ss. inv WF. eapply WFLO in Heq. rewrite SKE in *. extlia.
          + eapply Genv.genv_symb_range in H0. ss. exfalso. apply n.
            inv MEM. rewrite SKE in *. eapply Plt_Ple_trans; eauto.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. des_ifs.
      }

      { instantiate (1:= r). ii. inv SUST. inv MEM. rewrite <- NB. eapply UnreachC.unreach_to_inj_val; eauto. }
      { eapply UnreachC.to_inj_mem. inv SUST. eauto. }

      i. des. inv SUST. inv MEM.
      assert (MNB: Ple (Mem.nextblock m) (Mem.nextblock m0)).
      { eapply Mem.unchanged_on_nextblock; eauto. }

      exists (Unreach.mk (fun blk => if j1 blk then false else plt blk (Mem.nextblock m0))
                         (Unreach.ge_nb su0)
                         (Mem.nextblock m0)).
      assert (HLE: Unreach.hle
                     su0 (Unreach.mk
                            (fun blk => if j1 blk then false else plt blk (Mem.nextblock m0))
                            (Unreach.ge_nb su0)
                            (Mem.nextblock m0))).
      { eapply Unreach.hle_update; [..|refl]; ss; rewrite NB in *; eauto; i.
        destruct (if Unreach.unreach su0 blk then None else Mem.flat_inj (Mem.nextblock m) blk) eqn: BEQ.
        - destruct p. dup BEQ. eapply INCR in BEQ0. des_ifs.
        - destruct (j1 blk) as [[]|] eqn: BEQ0.
          + specialize (SEP _ _ _ BEQ BEQ0). des. des_ifs.
          + unfold Mem.flat_inj, proj_sumbool in *. des_ifs. extlia. }
      assert (SOUNDV: forall v_src v_tgt (INJ: Val.inject j1 v_src v_tgt),
                 UnreachC.val' (Unreach.mk
                                  (fun blk => if j1 blk then false else plt blk (Mem.nextblock m0))
                                  (Unreach.ge_nb su0)
                                  (Mem.nextblock m0)) v_src).
      { ii. ss. clarify. inv INJ0. inv WF. rewrite NB in *.
        destruct (if Unreach.unreach su0 blk then None else Mem.flat_inj (Mem.nextblock m) blk) eqn: BEQ.
        - destruct p. dup BEQ. eapply INCR in BEQ0.
          unfold Mem.flat_inj in *; des_ifs; esplits; eauto. eapply Plt_Ple_trans; eauto.
        - specialize (SEP _ _ _ BEQ H1). des.
          unfold Mem.flat_inj in *; des_ifs; esplits; eauto.
          + eapply Plt_Ple_trans; eauto.
          + eapply Mem.valid_block_inject_1; eauto.
      }
      esplits; eauto.
      + econs; ss; eauto.
        * inv WF. rewrite NB in *. econs; ss; i.
          { ii. ss. clarify. unfold proj_sumbool in *. des_ifs.
            - destruct p. esplits; eauto. eapply Mem.valid_block_inject_1; eauto.
            - destruct p. esplits; eauto. eapply Mem.valid_block_inject_1; eauto.
            - exfalso. destruct p0.
              exploit Mem.mi_memval; eauto. eapply Mem.mi_inj; eauto. i.
              rewrite PTR in *. inv H. inv H1. clarify.
            - exfalso. eapply n0. eapply Mem.perm_valid_block; eauto.
            - exfalso. destruct p.
              exploit Mem.mi_memval; eauto. eapply Mem.mi_inj; eauto. i.
              rewrite PTR in *. inv H. inv H1. clarify.
            - exfalso. eapply n1. eapply Mem.perm_valid_block; eauto. }
          { ii. des_ifs; eauto. unfold proj_sumbool in *. des_ifs. }
          { etrans; eauto. }
        * inv WF. rewrite NB in *. econs; ss.
          { i. des_ifs; eauto.
            destruct (if Unreach.unreach su0 x0
                      then None else Mem.flat_inj (Mem.nextblock m) x0) as [[]|]eqn:EQ.
            - apply INCR in EQ. clarify.
            - unfold Mem.flat_inj in *. des_ifs; eauto. etrans; eauto. extlia. }
          { i. unfold proj_sumbool in *. des_ifs; eauto. }
      + econs; ss; eauto; i.
        * exploit asm_step_max_perm; try apply STEP0; eauto.
        * exploit asm_step_readonly; try apply STEP0; eauto.
          i. eapply unchanged_ro_readonly; et.
        * eapply Mem.unchanged_on_implies; eauto.
          ii. unfold flip in *. ss. esplits; eauto.
          unfold loc_unmapped. unfold UnreachC.to_inj. des_ifs.

    - (* call *)
      inv AT; ss.
      {

        assert(SUARGS: UnreachC.args' su0 (Args.mk (rs PC) vs m1)).
        {
          inv SUST. r. splits; ss.
          + rewrite Forall_forall. i.
            exploit extcall_arguments_inject; eauto.
            { instantiate (1:= rs).
              instantiate (1:=UnreachC.to_inj su0 (Mem.nextblock m0)). ii.
              ss. specialize (RS pr). ss. unfold UnreachC.val' in *.
              destruct (rs pr); try by econs.
              exploit RS; eauto. i. des. econs.
              - unfold UnreachC.to_inj, Mem.flat_inj. des_ifs. exfalso. apply n.
                inv MEM. rewrite NB in *. eauto.
              - psimpl. auto. }
            { eapply UnreachC.to_inj_mem. eauto. }
            i. des. clear - ARGINJ H MEM.
            revert H args2 ARGINJ. induction vs; ss. i. inv ARGINJ. des; eauto.
            clarify. ii. clarify. inv H2. unfold UnreachC.to_inj, Mem.flat_inj in *.
            des_ifs. esplits; eauto. inv MEM. rewrite NB. auto.
          + eapply unreach_free; eauto. }
        exploit (@UnreachC.greatest_ex su0 (Args.mk (rs PC) vs m1)); ss; eauto.
        { unfold UnreachC.args' in *. des. exists su0. esplits; eauto. refl. }
        i; des.
        des_ifs. clear_tac.
        splits; [..|exists su_gr; esplits]; eauto.
        + (* mle *)
          inv SUST.
          exploit RS; eauto. intro SU; des.
          eapply Unreach.free_mle; eauto.
        + (* footprint *)
          des_ifs. des. clarify. econs; eauto.
          * eapply Mem.free_range_perm; et.
          * inv SUST. exploit RS; try apply RSP; eauto. i. des.
            unfold Mem.valid_block. inv MEM. rewrite <- NB. auto.
          * inv SUST. specialize (RS Asm.RSP). eapply RS; et.
        + eapply GR.
        + eapply GR.
        + eapply GR.
        + eapply GR.
        + eapply GR. esplits; eauto. refl.
        + (* K *)
          ii. inv AFTER; cycle 1; ss.
          { exfalso. des. clarify. }
          assert (sg = sg0).
          { des. clarify. } clarify.
          rename retv_m into m2.
          assert(GRARGS: Sound.args su_gr (Args.mk (rs PC) vs m1)).
          { rr in GR. des. ss. }
          assert(LEOLD: Unreach.hle_old su_gr su_ret).
          { eapply Unreach.hle_hle_old; et. rr in GRARGS. des. ss. }
          set (su1 := Unreach.mk (fun blk =>
                                    if plt blk (Mem.nextblock m0)
                                    then su0.(Unreach.unreach) blk
                                    else su_ret.(Unreach.unreach) blk
                                 )
                                 su0.(Unreach.ge_nb) m2.(Mem.nextblock)).
          exists su1.
          assert(HLEA: Sound.hle su0 su1).
          { unfold su1. rr. ss.
            inv SUST. inv MEM. rewrite NB in *.
            esplits; et.
            - ii. des_ifs.
            - inv MLE. etrans.
              + eapply Mem.unchanged_on_nextblock. eapply Mem.free_unchanged_on; eauto.
                instantiate (1:=bot2). ss.
              + eapply Mem.unchanged_on_nextblock. eauto.
          }
          assert(LEA: UnreachC.le' su0 su1).
          { rr in GR. des. unfold su1.
            rr. ss. esplits; eauto.
            ii. des_ifs. eapply LEOLD; eauto. eapply LE0; eauto.
          }
          assert(LEB: UnreachC.le' su1 su_ret).
          { rr in GR. des. unfold su1.
            rr. ss. esplits; eauto.
            - ii. des_ifs. eapply LEOLD; eauto. eapply LE0; eauto.
            - rr in LE. des. rr in LE0. des. congruence.
          }
          esplits; eauto; cycle 1.
          { (* unfree mle_excl *)
            des. clarify. ss. des_ifs. clear_tac.
            econs; et.
            - ii. eapply Mem_unfree_unchanged_on; et.
            - eapply Mem_unfree_unchanged_on; et.
              (* u. ii; des; ss; clarify. *)
              (* rr in H. eapply H. *)
          }
          (* { inv SUST. inv MEM. rr. split; ss. ii. des_ifs. apply BOUND in PR. unfold Mem.valid_block in *. ss. } *)
          inv SUST.
          generalize (loc_external_result_one sg0); intro ONE.
          destruct (loc_external_result sg0) eqn:T; ss. clear_tac.
          unfold Pregmap.set.
          (* sound_state *)
          Local Opaque PregEq.eq.
          econs; ss; eauto.
          { i.
            set pr as PR.
            des_ifs.
            - (* PC *)
              eapply (@Sound.hle_val UnreachC.Unreach); ss; et.
            - (* retv *)
              move RETV at bottom. rr in RETV. des. ss.
              eapply UnreachC.val_le; eauto.
              unfold su1. ss. inv MEM0. rewrite NB. refl.
            - (* others *)
              eapply (@Sound.hle_val UnreachC.Unreach); ss; et.
              unfold regset_after_external. des_ifs.
          }
          { bar. move RETV at bottom. rr in RETV. des. ss.
            assert(UnreachC.mem' su1 m2).
            { inv MEM0. econs; ss; eauto; cycle 1.
              - ii. eapply BOUND. des_ifs. eapply LEB. eapply LEA. ss.
              - inv LEA. inv LEB. rewrite H0. rewrite H2. eauto.
              - i.
                destruct (classic (Unreach.unreach su_ret blk0)); cycle 1.
                { hexploit SOUND; eauto. i.
                  eapply UnreachC.memval_le; et. unfold su1. ss. Unreach.nb_tac. extlia.
                }
                rename H into SURET.
                des_ifs.
                assert(HLE: forall
                          blk
                          (OLD: Plt blk (Mem.nextblock m0))
                          (NEW: Unreach.unreach su_ret blk)
                        ,
                          <<OLD: Unreach.unreach su_gr blk>>).
                { ii. rr in LEOLD. des. eapply OLD0. esplits; et.
                  clear - OLD GR FREE. inv GR. des. inv H1. ss. des.
                  inv MEM. rewrite NB. eapply Plt_Ple_trans; eauto.
                  erewrite <- Mem.nextblock_free; eauto. refl. }
                exploit HLE; et. intro SUGR; des.
                assert(UNCH: (ZMap.get ofs1 (Mem.mem_contents m2) !! blk0)
                             = (ZMap.get ofs1 (Mem.mem_contents m1) !! blk0)).
                { inv MLE. eapply Mem.unchanged_on_contents; eauto.
                  - eapply PRIV; et.
                    unfold Mem.valid_block. erewrite Mem.nextblock_free; eauto. }

                move SUARGS at bottom. rr in SUARGS. des. ss. inv MEM0.
                erewrite UNCH.
                hexploit SOUND0; et.
                { inv MLE. eapply PRIV; et.
                  unfold Mem.valid_block. erewrite Mem.nextblock_free; eauto. }
                i; des.
                remember su1 as su1new. clear - p HLEA H.
                ii. exploit H; eauto. i. des. inv HLEA. des. split.
                + rewrite <- H2; eauto.
                + eapply Plt_Ple_trans; eauto. }
            eapply unreach_unfree; eauto.
          }
          { (* WF *)
            inv WF. unfold su1. econs; ss; et.
            - i. des_ifs; et.
              inv MEM. extlia.
            - i. des_ifs; et.
              { clear - p FREE MLE. inv MLE. eapply Plt_Ple_trans; eauto.
                etrans; eapply Mem.unchanged_on_nextblock; eauto.
                eapply Mem.free_unchanged_on; eauto. instantiate (1:=bot2). ss. }
              rr in RETV. des. ss. inv WF0. inv MEM1. Unreach.nb_tac. eapply WFHI0; et.
          }
      }
      { inv SUST. esplits; eauto; ss.
        - refl.
        - econs 2. eauto.
        - refl.
        - i. inv AFTER.
          { des. clarify. }
          ss. des. esplits; eauto.
          + econs; eauto.
            * i. unfold Pregmap.set. des_ifs.
              { eapply (@Sound.hle_val UnreachC.Unreach); ss; et. }
              { eapply REGSET. }
            * rewrite <- SKE. unfold Unreach.hle in *. des. auto.
          + econs 2; eauto. }

    - (* return *)
      inv SUST. inv FINAL.
      { ss. clarify.
        exists su0. esplits; eauto.
        { refl. }
        { rr. ss. esplits; ss; et.
          eapply unreach_free; eauto.
        }
        eapply Unreach.free_mle; eauto.
        rewrite <- RSRSP in *. eapply RS; eauto. }
      { esplits; ss; eauto.
        - refl.
        - refl. }
  Qed.

End LOCALPRIV.

Lemma asm_ext_unreach
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>).
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto. instantiate (1:=(SimSymbId.mk (module asm) (module asm))). econs; ss; eauto.
  ii. inv SSLE. clear_tac. fold SkEnv.t in skenv_link_src.
  hexploit (asm_unreach_local_preservation INCLSRC WFSRC); eauto. i; des.

  eapply match_states_sim with
      (match_states :=
         match_states_ext skenv_link_tgt
                          (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
                          (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm)); eauto; ss.
  - apply unit_ord_wf.

  - (* init bsim *)
    ii. inv SIMSKENV. ss.
    inv SIMARGS.
    { destruct sm_arg. ss. clarify.
      inv INITTGT; cycle 1.
      { des. clarify. } clarify.
      ss. inv TYP. rewrite val_inject_list_lessdef in *.
      inv STORE. des.
      exploit store_arguments_parallel_extends; [..| eauto |]; eauto.
      + eapply typify_has_type_list; eauto.
      + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
        i. des. inv WFTGT. eapply WFPARAM in H1; eauto; ss.
      + ss. rewrite val_inject_list_lessdef in *.
        eapply inject_list_typify_list; try eassumption.
        erewrite inject_list_length; eauto.
      + i. des.
        eexists (AsmC.mkstate (asm_init_rs
                                 rs_src (to_mregset rs)
                                 (fn_sig fd) fptr_src (rs RA) (Mem.nextblock src))
                              (Asm.State _ (JunkBlock.assign_junk_blocks m_src1 n))).
        esplits; eauto.
        { econs; ss; eauto.
          - rewrite SIMSKENVLINK in *. cinv FPTR; ss; clarify; eauto.
            exfalso. inv SAFESRC; clarify. rewrite <- H4 in *. ss.
          - inv SIMSKENVLINK. unfold asm_init_rs, to_pregset, Pregmap.set. des_ifs.
          - econs; eauto. erewrite inject_list_length; eauto.
          - econs; eauto. inv ARGTGT. econs; eauto.
            eapply extcall_arguments_same; eauto. i.
            unfold asm_init_rs, Pregmap.set, to_mregset, to_pregset, to_preg.
            erewrite to_preg_to_mreg.
            des_ifs; clarify; ss.
            * unfold preg_of in *; des_ifs.
            * unfold preg_of in *; des_ifs.
            * unfold preg_of in *; des_ifs.
            * unfold set_regset. des_ifs; clarify; eauto.
              exfalso. eapply Loc.notin_not_in in n3. eauto.
          - intros pr. unfold asm_init_rs, to_pregset, Pregmap.set, set_regset.
            des_ifs; eauto; ss.
            + ii. exploit PTRFREE; eauto.
              * instantiate (1:=RA). revert PTR.
                unfold JunkBlock.is_junk_value, Mem.valid_block.
                repeat rewrite JunkBlock.assign_junk_blocks_nextblock.
                replace (Mem.nextblock m_src1) with (Mem.nextblock m0); auto.
                symmetry. eapply Mem.mext_next; eauto.
              * ss.
            + ii. exploit PTRFREE.
              * instantiate (1:=pr). ii. apply PTR. unfold to_mregset.
                erewrite to_mreg_some_to_preg; eauto. revert H1.
                unfold JunkBlock.is_junk_value, Mem.valid_block.
                repeat rewrite JunkBlock.assign_junk_blocks_nextblock.
                replace (Mem.nextblock m_src1) with (Mem.nextblock m0); auto.
                symmetry. eapply Mem.mext_next; eauto.
              * i. des; eauto. clarify. eauto.
            + ii. left. esplits; eauto. rewrite loc_notin_not_in in n3. tauto. }
        { assert (AGREE0 :
                    AsmStepExt.agree
                      (asm_init_rs
                         rs_src (to_mregset rs)
                         (fn_sig fd) fptr_src (rs RA) (Mem.nextblock src)) rs).
          { ii.
            unfold asm_init_rs, Pregmap.set, to_mregset, set_regset, to_pregset, to_preg, inject_id, set_regset in *.
            des_ifs; ss; eauto; try rewrite val_inject_id in *; eauto.
            - rewrite H0. erewrite Mem.mext_next; eauto.
            - apply to_mreg_some_to_preg in Heq. unfold to_preg in *.
              rewrite Heq in *. eauto.
            - specialize (AGREE m). rewrite val_inject_id in *.
              apply to_mreg_some_to_preg in Heq. unfold to_preg in *.
              rewrite Heq in *. eauto. }
          instantiate (1:=SimMemExt.mk _ _).
          econs; ss.
          - eapply JunkBlock.assign_junk_block_extends; eauto.
          - unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
            rewrite SIMSKENVLINK in *. inv FPTR; ss; clarify; eauto.
            exfalso. inv SAFESRC. clarify. rewrite <- H4 in *. ss. clarify.
          - econs.
            + unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
            + econs; ss. ii. rewrite H0 in *. clarify.
            + eapply asm_init_rs_undef_bisim.
            + ss.
          - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
            hexploit RANOTFPTR; eauto. i. exfalso. eapply H1.
            eapply Genv.genv_defs_range; eauto. }
    }
    { ss. inv INITTGT.
      { exfalso. des. clarify. } clarify.
      exists (AsmC.mkstate
                (rs_src # RA <- ra)
                (Asm.State (rs_src # RA <- ra) (JunkBlock.assign_junk_blocks (SimMemExt.src sm_arg) n))).
      eexists (SimMemExt.mk _ _).
      exploit JunkBlock.assign_junk_block_extends; eauto. intros EXTEND.
      esplits; eauto.
      - econs 2; eauto; ss.
        + rewrite SIMSKE in *. cinv (RS PC); clarify.
          * rewrite H2. auto.
          * des. inv SAFESRC; des; clarify. rewrite <- H1 in *. ss.
        + i. clarify. hexploit RANOTFPTR; eauto. rewrite SIMSKELINK. auto.
        + unfold JunkBlock.is_junk_value in *. des_ifs. des. split.
          * erewrite Mem.valid_block_extends; eauto.
          * erewrite Mem.valid_block_extends; eauto.
      - econs; ss.
        + eapply agree_step; eauto.
        + eapply agree_step; eauto.
        + rewrite Pregmap.gso; clarify. rewrite SIMSKE. eauto. cinv (RS PC).
          * rewrite H2. eauto.
          * des. inv SAFESRC; des; clarify. rewrite <- H1 in *. ss.
        + des. econs 2; eauto.
          * econs.
            { rewrite Pregmap.gss. eauto. }
            { rewrite Pregmap.gss. eauto. }
          * econs.
            { rewrite Pregmap.gss. eauto. }
            { rewrite Pregmap.gss. eauto. }
        + rewrite Pregmap.gss. rewrite <- SIMSKELINK in *.
          unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs.
          eapply Genv.genv_defs_range in Heq. exfalso. eapply RANOTFPTR; eauto. }

  - ii. des. inv SAFESRC.
    { inv TYP. inv SIMARGS; clarify.
      eapply asm_initial_frame_succeed; eauto.
      + ss. apply lessdef_list_length in VALS.
        transitivity (Datatypes.length vs_src); eauto.
      + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
        i. des. inv WFSRC. eapply WFPARAM in H; eauto.
      + inv SIMSKENVLINK. cinv FPTR; eauto.
        rewrite <- H1 in *. ss. }
    { inv SIMARGS; clarify.
      eapply asm_initial_frame_succeed_asmstyle; eauto.
      inv SIMSKENVLINK. cinv (RS PC); eauto. rewrite <- H1 in *. ss. }

  - ii. inv MATCH. ss.

  - (** ******************* at external **********************************)
    ii. inv SIMSKENV. inv CALLSRC.
    { inv MATCH.
      des; ss; clarify. des_ifs.
      set (INJPC:= AGREE PC). inv INJPC; cycle 1.
      { rewrite <- H0 in *. ss. }
      unfold inject_id in *. clarify. psimpl.
      exploit extcall_arguments_extends; try apply AGREE; eauto. i. des.
      cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.
      exploit Mem.free_parallel_extends; eauto. i. des.
      eexists (Args.mk (rs_tgt PC) _ _). eexists (SimMemExt.mk _ _).
      esplits; eauto; ss; i.
      + econs; eauto.
        * rewrite SIMSKENVLINK in *. rewrite <- H1. auto.
        * esplits; eauto. rewrite SIMSKENVLINK in *. rewrite <- H1. ss.
        * clear - AGREE TPTR RADEF. splits.
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      + econs; ss.
      + instantiate (1:=top4). ss. }
    { ss. inv MATCH. des; ss; clarify.
      set (INJPC:= AGREE PC). inv INJPC; cycle 1.
      { rewrite <- H0 in *. ss. }
      exists (Args.Asmstyle rs_tgt (SimMemExt.tgt sm0)). esplits; eauto.
      - econs; ss; eauto.
        + rewrite <- H1. rewrite SIMSKE in *. auto.
        + rewrite <- H1. rewrite SIMSKELINK in *. eauto.
        + cinv (AGREE RA); clarify. exfalso. eauto.
      - econs 2; eauto. }

  - ii. destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC.
    { inv SIMRET; ss.
      cinv (AGREE RSP); rewrite RSRSP in *; ss. des.
      unfold Genv.find_funct in FINDF. unfold Genv.find_funct in SIG. des_ifs. ss.
      exploit Mem_unfree_parallel_extends; try apply MWF; eauto. i. des.
      unfold inject_id in *. clarify.
      esplits; ss.
      + i. ss. splits.
        { instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
          - instantiate (1:=sg). esplits; eauto.
            unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
            cinv (AGREE PC); rewrite Heq in *; clarify.
            inv SIMSKENV. ss. inv SIMSKELINK. psimpl. des_ifs.
          - eauto.
          - instantiate (1:=m2').
            rewrite <- UNFREE0. f_equal; psimpl; auto. }
      + { instantiate (1:=SimMemExt.mk _ _).
          econs; try assumption; ss.
          - apply agree_step; eauto.
            unfold set_pair. des_ifs; repeat (eapply agree_step; eauto).
            + eapply regset_after_external_extends; eauto.
            + eapply regset_after_external_extends; eauto.
            + eapply Val.hiword_lessdef; eauto.
            + eapply Val.loword_lessdef; eauto.
          - unfold Genv.find_funct. rewrite Heq0. des_ifs. eauto.
          - eauto. }
    }
    { inv SIMRET; ss. exists sm_ret. exists tt.
      eexists (AsmC.mkstate _ (State _ _)). esplits; ss; eauto.
      - econs 2; ss. inv SIMSKENV. ss. rewrite SIMSKELINK in *.
        cinv (AGREE PC); eauto. rewrite <- H1 in *. ss. des. clarify.
      - clarify. econs; eauto.
        apply agree_step; eauto. }

  - (** ******************* final **********************************)
    i. inv MATCH. inv FINALSRC.
    {
      cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl. ss.
      exploit Mem.free_parallel_extends; eauto. i. des.
      unfold inject_id in *. clarify.
      eexists (SimMemExt.mk _ _). esplits; ss; eauto.
      + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        econs; ss; ii; eauto.
        * des. esplits; eauto.
          rewrite SIMSKENVLINK in *. specialize (AGREEINIT PC).
          inv AGREEINIT; clarify; ss. rewrite <- H3 in *. ss.
        * unfold external_state in *. rewrite SIMSKENVLINK in *.
          des_ifs_safe. exfalso.
          specialize (AGREE PC). inv AGREE.
          { rewrite H5 in *. rewrite Heq in *. des_ifs. }
          { inv WFINITRS; ss; clarify. inv WFINITSRC.
            rewrite <- H3 in *. eauto. }
        * inv WFINITRS; clarify. inv WFINITSRC. inv WFINITTGT.
          unfold Val.has_type in TPTR. des_ifs.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
        * specialize (CALLEESAVE _ H1).
          specialize (AGREEINIT (to_preg mr0)).
          specialize (AGREE (to_preg mr0)).
          inv WFINITRS; clarify.
          clear - CALLEESAVE AGREEINIT AGREE WFINITSRC H1 UNDEF. inv WFINITSRC.
          eapply lessdef_commute; try eassumption.
          -- rewrite <- val_inject_lessdef. eassumption.
          -- rewrite <- val_inject_lessdef. eassumption.
          -- eauto.
        * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
          cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      + econs; ss.
    }
    { exists sm0. exists (Retv.Asmstyle rs_tgt (SimMemExt.tgt sm0)). ss.
      esplits; eauto.
      - econs 2; eauto.
        + inv SIMSKENV. ss. rewrite <- SIMSKE.
          cinv (AGREEINIT PC); ss. rewrite <- H1 in *. ss.
        + unfold external_state in *. rewrite SIMSKENVLINK in *.
          des_ifs_safe. exfalso.
          specialize (AGREE PC). inv AGREE.
          { rewrite H1 in *. rewrite Heq in *. des_ifs. }
          { des. rewrite <- H0 in *. ss. des_ifs.
            inv WFINITRS; ss; clarify. inv WFINITSRC. eauto. }
        + des. clarify. inv WFINITRS; clarify.
          inv WFINITSRC. cinv (AGREE PC); clarify.
          * cinv (AGREEINIT RA); ss. exfalso. eauto.
          * rewrite <- H1 in *. exfalso. eauto.
      - econs 2; eauto. }

  - left. ii. esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + exists tt.
      inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss. destruct st0. ss. clarify.
      exploit asm_step_preserve_extension; try apply STEP; eauto. i. des.
      rewrite SIMSKENVLINK in *. esplits; auto.
      -- left. econs; [|econs 1|symmetry; eapply E0_right]. econs.
         { apply AsmC.modsem_determinate. }
         instantiate (1:=AsmC.mkstate _ _).
         econs; ss; eauto.
      -- instantiate (1:=SimMemExt.mk _ _). econs; ss; eauto.
Qed.

(* It's ***exactly*** same as asm_ext_sound *)
Lemma asm_ext_top
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>).
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto. instantiate (1:=(SimSymbId.mk (module asm) (module asm))). econs; ss; eauto.
  ii. inv SSLE. clear_tac. fold SkEnv.t in skenv_link_src.

  eapply match_states_sim with
      (match_states :=
         match_states_ext
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm)); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    instantiate (1:=top3). econs; ss.
    { ii. esplits; eauto. instantiate (1:=tt). rr. des_ifs.
      esplits; eauto. unfold Sound.vals. rewrite Forall_forall. ii; ss. }
    { ii. esplits; eauto. rr. esplits; eauto. des_ifs. }

  - (* init bsim *)
    ii. inv SIMSKENV. ss.
    inv SIMARGS.
    { destruct sm_arg. ss. clarify.
      inv INITTGT; cycle 1.
      { des. clarify. } clarify.
      ss. inv TYP. rewrite val_inject_list_lessdef in *.
      inv STORE. des.
      exploit store_arguments_parallel_extends; [..| eauto |]; eauto.
      + eapply typify_has_type_list; eauto.
      + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
        i. des. inv WFTGT. eapply WFPARAM in H1; eauto; ss.
      + ss. rewrite val_inject_list_lessdef in *.
        eapply inject_list_typify_list; try eassumption.
        erewrite inject_list_length; eauto.
      + i. des.
        eexists (AsmC.mkstate (asm_init_rs
                                 rs_src (to_mregset rs)
                                 (fn_sig fd) fptr_src (rs RA) (Mem.nextblock src))
                              (Asm.State _ (JunkBlock.assign_junk_blocks m_src1 n))).
        esplits; eauto.
        { econs; ss; eauto.
          - rewrite SIMSKENVLINK in *. cinv FPTR; ss; clarify; eauto.
            exfalso. inv SAFESRC; clarify. rewrite <- H4 in *. ss.
          - inv SIMSKENVLINK. unfold asm_init_rs, to_pregset, Pregmap.set. des_ifs.
          - econs; eauto. erewrite inject_list_length; eauto.
          - econs; eauto. inv ARGTGT. econs; eauto.
            eapply extcall_arguments_same; eauto. i.
            unfold asm_init_rs, Pregmap.set, to_mregset, to_pregset, to_preg.
            erewrite to_preg_to_mreg.
            des_ifs; clarify; ss.
            * unfold preg_of in *; des_ifs.
            * unfold preg_of in *; des_ifs.
            * unfold preg_of in *; des_ifs.
            * unfold set_regset. des_ifs; clarify; eauto.
              exfalso. eapply Loc.notin_not_in in n3. eauto.
          - intros pr. unfold asm_init_rs, to_pregset, Pregmap.set, set_regset.
            des_ifs; eauto; ss.
            + ii. exploit PTRFREE; eauto.
              * instantiate (1:=RA). revert PTR.
                unfold JunkBlock.is_junk_value, Mem.valid_block.
                repeat rewrite JunkBlock.assign_junk_blocks_nextblock.
                replace (Mem.nextblock m_src1) with (Mem.nextblock m0); auto.
                symmetry. eapply Mem.mext_next; eauto.
              * ss.
            + ii. exploit PTRFREE.
              * instantiate (1:=pr). ii. apply PTR. unfold to_mregset.
                erewrite to_mreg_some_to_preg; eauto. revert H1.
                unfold JunkBlock.is_junk_value, Mem.valid_block.
                repeat rewrite JunkBlock.assign_junk_blocks_nextblock.
                replace (Mem.nextblock m_src1) with (Mem.nextblock m0); auto.
                symmetry. eapply Mem.mext_next; eauto.
              * i. des; eauto. clarify. eauto.
            + ii. left. esplits; eauto. rewrite loc_notin_not_in in n3. tauto. }
        { assert (AGREE0 :
                    AsmStepExt.agree
                      (asm_init_rs
                         rs_src (to_mregset rs)
                         (fn_sig fd) fptr_src (rs RA) (Mem.nextblock src)) rs).
          { ii.
            unfold asm_init_rs, Pregmap.set, to_mregset, set_regset, to_pregset, to_preg, inject_id, set_regset in *.
            des_ifs; ss; eauto; try rewrite val_inject_id in *; eauto.
            - rewrite H0. erewrite Mem.mext_next; eauto.
            - apply to_mreg_some_to_preg in Heq. unfold to_preg in *.
              rewrite Heq in *. eauto.
            - specialize (AGREE m). rewrite val_inject_id in *.
              apply to_mreg_some_to_preg in Heq. unfold to_preg in *.
              rewrite Heq in *. eauto. }
          instantiate (1:=SimMemExt.mk _ _).
          econs; ss.
          - eapply JunkBlock.assign_junk_block_extends; eauto.
          - unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
            rewrite SIMSKENVLINK in *. inv FPTR; ss; clarify; eauto.
            exfalso. inv SAFESRC. clarify. rewrite <- H4 in *. ss. clarify.
          - econs.
            + unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
            + econs; ss. ii. rewrite H0 in *. clarify.
            + eapply asm_init_rs_undef_bisim.
            + ss.
          - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
            hexploit RANOTFPTR; eauto. i. exfalso. eapply H1.
            eapply Genv.genv_defs_range; eauto. }
    }
    { ss. inv INITTGT.
      { exfalso. des. clarify. } clarify.
      exists (AsmC.mkstate
                (rs_src # RA <- ra)
                (Asm.State (rs_src # RA <- ra) (JunkBlock.assign_junk_blocks (SimMemExt.src sm_arg) n))).
      eexists (SimMemExt.mk _ _).
      exploit JunkBlock.assign_junk_block_extends; eauto. intros EXTEND.
      esplits; eauto.
      - econs 2; eauto; ss.
        + rewrite SIMSKE in *. cinv (RS PC); clarify.
          * rewrite H2. auto.
          * des. inv SAFESRC; des; clarify. rewrite <- H1 in *. ss.
        + i. clarify. hexploit RANOTFPTR; eauto. rewrite SIMSKELINK. auto.
        + unfold JunkBlock.is_junk_value in *. des_ifs. des. split.
          * erewrite Mem.valid_block_extends; eauto.
          * erewrite Mem.valid_block_extends; eauto.
      - econs; ss.
        + eapply agree_step; eauto.
        + eapply agree_step; eauto.
        + rewrite Pregmap.gso; clarify. rewrite SIMSKE. eauto. cinv (RS PC).
          * rewrite H2. eauto.
          * des. inv SAFESRC; des; clarify. rewrite <- H1 in *. ss.
        + des. econs 2; eauto.
          * econs.
            { rewrite Pregmap.gss. eauto. }
            { rewrite Pregmap.gss. eauto. }
          * econs.
            { rewrite Pregmap.gss. eauto. }
            { rewrite Pregmap.gss. eauto. }
        + rewrite Pregmap.gss. rewrite <- SIMSKELINK in *.
          unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs.
          eapply Genv.genv_defs_range in Heq. exfalso. eapply RANOTFPTR; eauto. }

  - ii. des. inv SAFESRC.
    { inv TYP. inv SIMARGS; clarify.
      eapply asm_initial_frame_succeed; eauto.
      + ss. apply lessdef_list_length in VALS.
        transitivity (Datatypes.length vs_src); eauto.
      + exploit SkEnv.revive_incl_skenv; try eapply FINDF; eauto.
        i. des. inv WFSRC. eapply WFPARAM in H; eauto.
      + inv SIMSKENVLINK. cinv FPTR; eauto.
        rewrite <- H1 in *. ss. }
    { inv SIMARGS; clarify.
      eapply asm_initial_frame_succeed_asmstyle; eauto.
      inv SIMSKENVLINK. cinv (RS PC); eauto. rewrite <- H1 in *. ss. }

  - ii. inv MATCH. ss.

  - (** ******************* at external **********************************)
    ii. inv SIMSKENV. inv CALLSRC.
    { inv MATCH.
      des; ss; clarify. des_ifs.
      set (INJPC:= AGREE PC). inv INJPC; cycle 1.
      { rewrite <- H0 in *. ss. }
      unfold inject_id in *. clarify. psimpl.
      exploit extcall_arguments_extends; try apply AGREE; eauto. i. des.
      cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.
      exploit Mem.free_parallel_extends; eauto. i. des.
      eexists (Args.mk (rs_tgt PC) _ _). eexists (SimMemExt.mk _ _).
      esplits; eauto; ss; i.
      + econs; eauto.
        * rewrite SIMSKENVLINK in *. rewrite <- H1. auto.
        * esplits; eauto. rewrite SIMSKENVLINK in *. rewrite <- H1. ss.
        * clear - AGREE TPTR RADEF. splits.
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      + econs; ss.
      + instantiate (1:=top4). ss. }
    { ss. inv MATCH. des; ss; clarify.
      set (INJPC:= AGREE PC). inv INJPC; cycle 1.
      { rewrite <- H0 in *. ss. }
      exists (Args.Asmstyle rs_tgt (SimMemExt.tgt sm0)). esplits; eauto.
      - econs; ss; eauto.
        + rewrite <- H1. rewrite SIMSKE in *. auto.
        + rewrite <- H1. rewrite SIMSKELINK in *. eauto.
        + cinv (AGREE RA); clarify. exfalso. eauto.
      - econs 2; eauto. }

  - ii. destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC.
    { inv SIMRET; ss.
      cinv (AGREE RSP); rewrite RSRSP in *; ss. des.
      unfold Genv.find_funct in FINDF. unfold Genv.find_funct in SIG. des_ifs. ss.
      exploit Mem_unfree_parallel_extends; try apply MWF; eauto. i. des.
      unfold inject_id in *. clarify.
      esplits; ss.
      + i. ss. splits.
        { instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
          - instantiate (1:=sg). esplits; eauto.
            unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
            cinv (AGREE PC); rewrite Heq in *; clarify.
            inv SIMSKENV. ss. inv SIMSKELINK. psimpl. des_ifs.
          - eauto.
          - instantiate (1:=m2').
            rewrite <- UNFREE0. f_equal; psimpl; auto. }
      + { instantiate (1:=SimMemExt.mk _ _).
          econs; try assumption; ss.
          - apply agree_step; eauto.
            unfold set_pair. des_ifs; repeat (eapply agree_step; eauto).
            + eapply regset_after_external_extends; eauto.
            + eapply regset_after_external_extends; eauto.
            + eapply Val.hiword_lessdef; eauto.
            + eapply Val.loword_lessdef; eauto.
          - unfold Genv.find_funct. rewrite Heq0. des_ifs. eauto.
          - eauto. }
    }
    { inv SIMRET; ss. exists sm_ret. exists tt.
      eexists (AsmC.mkstate _ (State _ _)). esplits; ss; eauto.
      - econs 2; ss. inv SIMSKENV. ss. rewrite SIMSKELINK in *.
        cinv (AGREE PC); eauto. rewrite <- H1 in *. ss. des. clarify.
      - clarify. econs; eauto.
        apply agree_step; eauto. }

  - (** ******************* final **********************************)
    i. inv MATCH. inv FINALSRC.
    {
      cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl. ss.
      exploit Mem.free_parallel_extends; eauto. i. des.
      unfold inject_id in *. clarify.
      eexists (SimMemExt.mk _ _). esplits; ss; eauto.
      + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        econs; ss; ii; eauto.
        * des. esplits; eauto.
          rewrite SIMSKENVLINK in *. specialize (AGREEINIT PC).
          inv AGREEINIT; clarify; ss. rewrite <- H3 in *. ss.
        * unfold external_state in *. rewrite SIMSKENVLINK in *.
          des_ifs_safe. exfalso.
          specialize (AGREE PC). inv AGREE.
          { rewrite H5 in *. rewrite Heq in *. des_ifs. }
          { inv WFINITRS; ss; clarify. inv WFINITSRC.
            rewrite <- H3 in *. eauto. }
        * inv WFINITRS; clarify. inv WFINITSRC. inv WFINITTGT.
          unfold Val.has_type in TPTR. des_ifs.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
          -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
             cinv (AGREE PC); rewrite RSRA in *; clarify.
        * specialize (CALLEESAVE _ H1).
          specialize (AGREEINIT (to_preg mr0)).
          specialize (AGREE (to_preg mr0)).
          inv WFINITRS; clarify.
          clear - CALLEESAVE AGREEINIT AGREE WFINITSRC H1 UNDEF. inv WFINITSRC.
          eapply lessdef_commute; try eassumption.
          -- rewrite <- val_inject_lessdef. eassumption.
          -- rewrite <- val_inject_lessdef. eassumption.
          -- eauto.
        * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
          cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      + econs; ss.
    }
    { exists sm0. exists (Retv.Asmstyle rs_tgt (SimMemExt.tgt sm0)). ss.
      esplits; eauto.
      - econs 2; eauto.
        + inv SIMSKENV. ss. rewrite <- SIMSKE.
          cinv (AGREEINIT PC); ss. rewrite <- H1 in *. ss.
        + unfold external_state in *. rewrite SIMSKENVLINK in *.
          des_ifs_safe. exfalso.
          specialize (AGREE PC). inv AGREE.
          { rewrite H1 in *. rewrite Heq in *. des_ifs. }
          { des. rewrite <- H0 in *. ss. des_ifs.
            inv WFINITRS; ss; clarify. inv WFINITSRC. eauto. }
        + des. clarify. inv WFINITRS; clarify.
          inv WFINITSRC. cinv (AGREE PC); clarify.
          * cinv (AGREEINIT RA); ss. exfalso. eauto.
          * rewrite <- H1 in *. exfalso. eauto.
      - econs 2; eauto. }

  - left. ii. esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + exists tt.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        destruct st0. ss. clarify.
        exploit asm_step_preserve_extension; try apply STEP; eauto. i. des.
        rewrite SIMSKENVLINK in *.
        esplits; auto.
        - left. econs; [|econs 1|symmetry; eapply E0_right]. econs.
          { apply AsmC.modsem_determinate. }
          instantiate (1:=AsmC.mkstate _ _).
          econs; ss; eauto.
        - instantiate (1:=SimMemExt.mk _ _). econs; ss; eauto.
      }
Unshelve. apply tt.
Qed.

Inductive match_states
          (skenv_link_tgt: SkEnv.t)
          (ge_src ge_tgt: genv)
  : nat-> AsmC.state -> AsmC.state -> (@SimMem.t SimMemInjC.SimMemInj) -> Prop :=
| match_states_intro
    j init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : @SimMem.t SimMemInjC.SimMemInj)
    (AGREE: AsmStepInj.agree j rs_src rs_tgt)
    (AGREEINIT: AsmStepInj.agree j init_rs_src init_rs_tgt)
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MCOMPATINJ: j = sm0.(SimMemInj.inj))
    (MWF: SimMem.wf sm0)
    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITRS: wf_init_rss fd.(fn_sig) init_rs_src init_rs_tgt)
    (RAWF: Genv.find_funct skenv_link_tgt (init_rs_tgt RA) = None)
    (RSPDELTA: forall (SIG: sig_cstyle fd.(fn_sig) = true)
                      blk_src ofs (RSPSRC: init_rs_src RSP = Vptr blk_src ofs),
        exists blk_tgt,
          (j blk_src = Some (blk_tgt, 0))):
    match_states
      skenv_link_tgt
      ge_src ge_tgt 0
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0.

Lemma asm_inj_drop_bot
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = (SimSymbDrop.mk bot1 (module asm) (module asm))>>).
Proof.
  eexists (ModPair.mk _ _ _); s. esplits; eauto. econs; ss; i.
  { econs; ss; i; clarify. inv WF. auto. }
  eapply MatchSimModSemExcl2.match_states_sim with
      (match_states :=
         match_states skenv_link_tgt
                      (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
                      (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm))
      (match_states_at := top4)
      (sidx := unit); ss; eauto; ii.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  (** ******************* initial **********************************)
  - exploit SimSymbDrop_match_globals.
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
      exists sm0. esplits; eauto.

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

      { etrans; eauto. }

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
      - cinv MWF. econs; eauto.
        + eapply AsmStepInj.agree_step; eauto.
          * eapply agree_incr; try apply RS; eauto.
            rewrite MINJ. eapply junk_inj_incr; eauto.
          * rewrite MINJ. eapply src_junk_val_inj; eauto.
        + eapply AsmStepInj.agree_step; eauto.
          * eapply agree_incr; try apply RS; eauto.
            rewrite MINJ. eapply junk_inj_incr; eauto.
          * rewrite MINJ. eapply src_junk_val_inj; eauto.
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
    exploit SimSymbDrop_match_globals.
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
      des; ss; clarify. des_ifs.
      set (INJPC:= AGREE PC). cinv INJPC; rewrite <- H1 in *; ss; clarify.
      assert (delta = 0).
      { rewrite <- H0 in *. ss. unfold Genv.find_funct_ptr in *.
        clear EXTERNAL. des_ifs.
        inv SIMSKELINK. exploit SIMDEF; eauto. i. des. eauto. }
      clarify. psimpl. ss.
      exploit extcall_arguments_inject; eauto.
      { inv MWF. eauto. }
      i. des. cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

      exploit SimMemInjC.Mem_free_parallel'; eauto. i. des.
      eexists (Args.mk (Vptr b2 _) _ _). exists sm1.
      esplits; eauto; ss; i.
      + econs; auto.
        * eauto.
        * exploit SimSymbDrop_find_None; try eassumption.
          { ii. rewrite H in *. ss. }
          { unfold Genv.find_funct. des_ifs. }
        * esplits; eauto. unfold Genv.find_funct, Genv.find_funct_ptr in *.
          des_ifs_safe. inv SIMSKELINK. des_ifs_safe.
          exploit SIMDEF; try apply Heq2; eauto. i. des. clarify.
          rewrite DEFTGT. eauto.
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
      { rewrite <- H0 in *. ss. unfold Genv.find_funct_ptr in *.
        clear EXTERNAL. des_ifs.
        inv SIMSKELINK. exploit SIMDEF; eauto. i. des. eauto. }
      clarify. psimpl. ss.
      exists (Args.Asmstyle rs_tgt (SimMemInj.tgt sm0)). esplits; eauto.
      - econs 2; eauto.
        + exploit SimSymbDrop_find_None; try eassumption.
          { ii. rewrite H in *. ss. }
          { unfold Genv.find_funct. des_ifs. }
        + esplits; eauto. unfold Genv.find_funct, Genv.find_funct_ptr in *.
          des_ifs_safe. inv SIMSKELINK. des_ifs_safe.
          exploit SIMDEF; try apply Heq2; eauto. i. des. clarify.
          rewrite DEFTGT. eauto.
        + clear - AGREE TPTR RADEF. splits.
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
          { rename TPTR into TPTR0. unfold Tptr in *.
            des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      - econs 2; eauto.
      - refl. }

  (** ******************* after external **********************************)
  - exploit SimSymbDrop_match_globals.
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
      { inv SIMSKENV. inv SIMSKELINK. ss.
        clear - AGREE FPTR SIG0 SIG1 SIMDEFINV.
        cinv (AGREE PC); rewrite <- H1 in *; clarify.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
        exploit SIMDEFINV; eauto.
        i. des. clarify. } clarify.

      hexploit (@Mem_unfree_parallel sm0 sm_arg sm_ret); eauto.

      i. des. esplits; eauto. i.
      esplits; ss; eauto.

      + econs; ss; eauto.
      + econs; try refl; eauto.
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
      exists (SimMemInj.unlift' sm_arg sm_ret).
      eexists. eexists (AsmC.mkstate _ (Asm.State _ _)). esplits; eauto.
      - etrans; eauto.
      - clear - MLE0. inv MLE0. ss. econs; ss; eauto. eapply SimMemInj.frozen_refl.
      - i. esplits; eauto.
        + econs 2; eauto.
        + exploit SimMemInj.unlift_wf; try apply MLE0; eauto. i. inv MLE2.
          econs; try apply H; auto; eauto.
          * eapply AsmStepInj.agree_step; eauto.
          * eapply AsmStepInj.agree_incr; eauto.
          * i. exploit RSPDELTA; eauto. i. des. eauto. }

  (** ******************* final **********************************)
  - exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv MATCH. inv FINALSRC.
    {
      cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      exploit SimMemInjC.Mem_free_parallel'; eauto.
      { instantiate (3:=Ptrofs.zero). zsimpl. psimpl. eauto. }
      i. des.

      assert (delta = 0).
      { rewrite FINDF in *. clarify. exploit RSPDELTA; eauto. i. des. clarify. }
      clarify. ss. zsimpl.

      esplits; ss; eauto.
      + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
        econs; ss; ii; eauto.
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
          { rewrite <- H2 in *. inv WFINITRS; clarify. inv WFINITSRC. eauto. }
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
    }
    { exists sm0. exists (Retv.Asmstyle rs_tgt sm0.(SimMemInj.tgt)).
      esplits; ss; eauto.
      + econs 2; ss; ii; eauto.
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
            apply Genv.invert_find_symbol in Heq4.
            inv SIMSKENV. inv SIMSKE. ss.
            exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
            exploit Genv_map_defs_def_inv; try apply DEFSRC.
            i. revert Heq2. rewrite H.
            unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
            erewrite Genv.find_invert_symbol.
            - rewrite Heq5; eauto. clarify.
            - exploit SIMSYMB3; eauto. i. des.
              rewrite BLKSRC. f_equal.
              exploit DISJ; eauto. }
          { rewrite <- H1 in *. ss. des. des_ifs. clarify.
            inv WFINITRS; clarify. inv WFINITSRC. congruence. }
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

  (** ******************* step **********************************)
  - left; i. esplits; ss; i.
    + apply AsmC.modsem_receptive.
    + { exists O. inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss. inv SIMSKENV. destruct st0. ss. clarify.

        exploit asm_step_preserve_injection; eauto.
        { exploit SimSymbDrop_match_globals; eauto. intros MATCH. inv MATCH.
          econs; ss; i; eauto. exploit DEFLE; eauto. i. des. clarify. esplits; eauto. }
        { eapply symbols_inject_weak_imply.
          eapply SimSymbDrop_symbols_inject; eauto. }
        { cinv MWF. eauto. }

        i. des. eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).

        exploit SimMemInjC.parallel_gen; eauto.
        { ii. eapply asm_step_max_perm; eauto. }
        { ii. eapply asm_step_max_perm; eauto. }
        i. des. esplits; eauto.
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

Lemma asm_inj_drop
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>).
Proof.
  exploit asm_inj_drop_bot; eauto. i. des. eauto.
Qed.

Lemma asm_inj_id
      (asm: Asm.program)
      (WF: Sk.wf (module asm)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = (AsmC.module asm)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = (AsmC.module asm)>>).
Proof.
  eapply sim_inj_drop_bot_id; eauto. apply asm_inj_drop_bot; auto.
Qed.
