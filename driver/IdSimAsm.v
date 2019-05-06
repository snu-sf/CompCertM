Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AsmC.
Require SimMemId SimMemExt SimMemInj.
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
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import StoreArguments.
Require Import AsmStepInj AsmStepExt IntegersC.
Require Import Coq.Logic.PropExtensionality.


Set Implicit Arguments.


Local Opaque Z.mul Z.add Z.sub Z.div.

Require Import mktac.

(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)

Lemma asm_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  intro GENV; des.
  inv SIMSKENVLINK.

  eapply match_states_sim with (index := unit)
                               (sound_state := SoundTop.sound_state)
                               (match_states := fun sm_arg idx st_src0 st_tgt0 sm =>
                                                  st_src0 = st_tgt0 /\ SimMem.wf sm)
                               (match_states_at := top4); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eapply SoundTop.sound_state_local_preservation; eauto.
  - (* init bsim *)
    ii. des. exists st_init_tgt. inv SAFESRC. econs; ss; eauto.
    esplits; ss; eauto.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  - (* init progress *)
    ii. des.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
    exists st_init_src. inv SAFESRC. econs; ss; eauto.
  - (* call wf *)
    ii; des; ss.
  - (* call fsim *)
    ii; des; ss.
    destruct sm0; ss. clarify.
    eexists _, (SimMemId.mk _ _); ss. esplits; eauto.
    econs; ss; eauto.
  - (* after fsim *)
    ii; des; ss.
    destruct sm_ret; ss. clarify. clear_tac.
    destruct retv_src, retv_tgt; ss. inv SIMRET. ss. clarify.
    esplits; eauto.
  - (* final fsim *)
    ii; des; ss. clarify.
    destruct retv_src; ss.
    exists (SimMemId.mk m m).
    esplits; ss; eauto.
  - (* step fsim *)
    left; i.
    ii; ss. des. clarify. clear_tac.
    esplits; eauto.
    { admit "ez - receptive". }
    ii; des. esplits; eauto. left. apply plus_one. econs; eauto.
    { admit "ez - determinate". }
Unshelve.
  all: ss.
Qed.

Inductive sound_state (skenv: SkEnv.t) (su: Sound.t) (m_init: mem): AsmC.state -> Prop :=
| sound_state_intro
    init_rs rs0 m0
    (MLE: Unreach.mle su m_init m0)
    (RS: forall pr, UnreachC.val' su (rs0#pr))
    (MEM: UnreachC.mem' su m0)
    (INIT: forall pr, UnreachC.val' su (init_rs#pr))
    (WF: forall blk (PRIV: su.(Unreach.unreach) blk) (PUB: Plt blk su.(Unreach.ge_nb)), False)
    (SKE: su.(Unreach.ge_nb) = skenv.(Genv.genv_next))
  :
    sound_state skenv su m_init (mkstate init_rs (State rs0 m0))
.

Module TRIAL2.
Section TRIAL2.

  Variable skenv_link: SkEnv.t.

  Inductive sound_state (su: Sound.t): AsmC.state -> Prop :=
  | sound_state_intro
      (init_rs rs0: regset) m0
      (RS: forall pr, UnreachC.val' su (rs0#pr))
      (MEM: UnreachC.mem' su m0)
      (INIT: forall pr, UnreachC.val' su (init_rs#pr))
      (WF: Sound.wf su)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state su (mkstate init_rs (State rs0 m0))
  .

  Inductive has_footprint: AsmC.state -> Sound.t -> mem -> Prop :=
  | has_footprint_intro
      su0
      blk0 blk1 ofs
      init_rs (rs0: regset) m_unused m1 sg
      (FPTR: rs0 # PC = Vptr blk0 Ptrofs.zero)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr blk0 Ptrofs.zero)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSP: rs0 RSP = Vptr blk1 ofs)
      (FREEABLE: Mem.range_perm m1 blk1 (ofs.(Ptrofs.unsigned))
                                (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                Cur Freeable)
      (VALID: Mem.valid_block m1 blk1)
      (PUB: ~ su0.(Unreach.unreach) blk1)
    :
      has_footprint (mkstate init_rs (State rs0 m_unused)) su0 m1
  .

  Inductive mle_excl: AsmC.state -> Sound.t -> mem -> mem -> Prop :=
  | mle_excl_intro
      init_rs rs0 m_unused (su0: Unreach.t) m0 m1
      blk0 blk1 sg ofs1
      (FPTR: rs0 # PC = Vptr blk0 Ptrofs.zero)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr blk0 Ptrofs.zero)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSP: rs0 RSP = Vptr blk1 ofs1)
      UNFR
      (UNFRDEF: UNFR = (brange blk1 ofs1.(Ptrofs.unsigned)
                                           (ofs1.(Ptrofs.unsigned) + 4 * (size_arguments sg))))
      (PERM: forall
          blk ofs
          (VALID: m0.(Mem.valid_block) blk)
          (UNFREE: ~ UNFR blk ofs)
        ,
          m1.(Mem.perm) blk ofs Max <1= m0.(Mem.perm) blk ofs Max)
      (UNCH: Mem.unchanged_on (~2 UNFR) m0 m1)
    :
      mle_excl (mkstate init_rs (State rs0 m_unused)) su0 m0 m1
  .

  (* TODO: move to proper place *)
  Lemma loc_external_result_one
        sg
    :
      is_one (loc_external_result sg)
  .
  Proof.
    unfold loc_external_result. generalize (loc_result_one sg); i.
    destruct (loc_result sg) eqn:T; ss.
  Qed.

  Lemma unreach_free su m0 m1 blk lo hi
        (MEM: UnreachC.mem' su m0)
        (FREE: Mem.free m0 blk lo hi = Some m1)
    :
      UnreachC.mem' su m1.
  Proof.
    inv MEM. exploit Mem.free_unchanged_on; eauto.
    { instantiate (1:=~2 brange blk lo hi). ii. eauto. } intros UNCH.
    econs.
    - ii. eapply SOUND; eauto.
      + eapply Mem.perm_free_3; eauto.
      + erewrite <- Mem.unchanged_on_contents; eauto.
        * unfold brange. ii. des. clarify.
          eapply Mem_free_noperm; eauto.
          apply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
        * eapply Mem.perm_free_3; eauto.
    - ii. eapply BOUND in PR. eapply Mem.valid_block_unchanged_on; eauto.
    - etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    - etrans; eauto. symmetry. eapply Mem.nextblock_free; eauto.
  Qed.

  Lemma unreach_unfree su m0 m1 blk lo hi
        (MEM: UnreachC.mem' su m0)
        (UNFREE: Mem_unfree m0 blk lo hi = Some m1)
    :
      UnreachC.mem' su m1.
  Proof.
    inv MEM. exploit Mem_unfree_unchanged_on; eauto. intros UNCH.
    econs.
    - ii. assert (NIN: ~ brange blk lo hi blk0 ofs).
      { unfold brange. ii. des. clarify.
        unfold Mem_unfree in *. des_ifs. ss.
        rewrite PMap.gss in PTR. rewrite Mem_setN_in_repeat in PTR; clarify.
        rewrite Z2Nat_range. des_ifs; lia. }
      eapply SOUND; eauto.
      + eapply Mem.perm_unchanged_on_2; eauto; ss.
        eapply Mem.perm_valid_block in PERM.
        eapply Mem_nextblock_unfree in UNFREE. unfold Mem.valid_block in *.
        rewrite UNFREE. auto.
      + erewrite <- Mem.unchanged_on_contents; eauto.
        * eapply Mem.perm_unchanged_on_2; eauto; ss.
          eapply Mem.perm_valid_block in PERM.
          eapply Mem_nextblock_unfree in UNFREE. unfold Mem.valid_block in *.
          rewrite UNFREE. auto.
    - ii. eapply BOUND in PR. eapply Mem.valid_block_unchanged_on; eauto.
    - etrans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
    - etrans; eauto. eapply Mem_nextblock_unfree; eauto.
  Qed.

  (* Lemma inject_list_Forall_inject j vs0 vs1 *)
  (*   : *)
  (*     Val.inject_list j vs0 vs1 <-> Forall2 (Val.inject j) vs0 vs1. *)
  (* Proof. *)
  (*   revert vs1. induction vs0; ss; i; split. *)
  (*   - intros H; inv H. econs. *)
  (*   - intros H; inv H. econs. *)
  (*   - intros H; inv H. econs; eauto. eapply IHvs0; eauto. *)
  (*   - intros H; inv H. econs; eauto. eapply IHvs0; eauto. *)
  (* Qed. *)

  (* Lemma forall2_in_exists A B (P: A -> B -> Prop) la lb *)
  (*       (ALL: list_forall2 P la lb) *)
  (*       a *)
  (*       (IN: In a la) *)
  (*   : *)
  (*     exists b, (<<IN: In b lb>>) /\ (<<SAT: P a b>>). *)
  (* Proof. *)
  (*   revert la lb ALL a IN. induction la; ss. *)
  (*   i. inv ALL. des. *)
  (*   - clarify. esplits; eauto. econs. auto. *)
  (*   - eapply IHla in H3; eauto. des. esplits; eauto. econs 2. auto. *)
  (* Qed. *)

  Lemma asm_unreach_local_preservation
        asm
    :
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link asm) sound_state>>
  .
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_excl_spec with (sound_state := (sound_state)); eauto.
    instantiate (1:= AsmC.get_mem).
    eapply local_preservation_strong_horizontal_excl_intro with
        (has_footprint := has_footprint)
        (mle_excl := mle_excl); ii; ss; eauto.
    - (* FOOTEXCL *)
      inv MLE. inv FOOT. inv MLEEXCL. ss. des. rewrite FPTR in *. rewrite RSP in *. clarify. econs; et.
      + i.
        destruct (classic (brange blk3
                                  (Ptrofs.unsigned ofs1)
                                  (Ptrofs.unsigned ofs1 + 4 * size_arguments (SkEnv.get_sig skd0)) blk ofs)).
        * rr in H. des; clarify. eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem.
        * eapply PERM; et.
          eapply PERM0; et.
          eapply Mem.valid_block_unchanged_on; et.
      + des_ifs. clear_tac.
        eapply Mem_unchanged_on_trans_strong; et.
        eapply Mem.unchanged_on_implies; try apply RO0; et.
        i. des.
        esplits; et.
        { u. i; des; clarify. r in H. eapply H. eapply Mem.perm_implies with Freeable; eauto with mem. }
      + eapply Mem_unchanged_on_trans_strong; et.
        eapply Mem.unchanged_on_implies; try apply PRIV0; et.
        u. i; des; clarify; ss.

    - (* init *)
      inv SUARG. des. ss. inv WF.
      inv INIT. inv STORE.
      eexists (Unreach.mk
                 (Unreach.unreach su_arg)
                 (Unreach.ge_nb su_arg)
                 (Mem.nextblock (JunkBlock.assign_junk_blocks m0 n))).
      assert (UNCH: Mem.unchanged_on
                        (SimMemInj.valid_blocks (Args.m args))
                        (Args.m args)
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
          inv H0. eapply Mem.nextblock_alloc in ALC.
          rewrite <- NB0. rewrite ALC. xomega.
        - rewrite JunkBlock.assign_junk_blocks_nextblock. des_ifs; xomega. }

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
            rewrite NB in *. apply H2. clear H3.
            eapply Mem.valid_block_unchanged_on; eauto.
            eapply store_arguments_unchanged_on; eauto.
          - i. des.
            + dup H0. eapply store_arguments_unchanged_on in H2.
              eapply Mem.unchanged_on_nextblock in H2. apply NSOUND. apply SOUNDIMPLY.
              inv H0.
              clear - VALS0 ARG MR PTR VALS NB H2 SOUNDIMPLY.
              unfold typify_list, Sound.vals, extcall_arguments in *.
              revert VALS pr PTR mr MR ARG VALS0.
              generalize (loc_arguments_one (fn_sig fd)).
              generalize (loc_arguments (fn_sig fd)).
              generalize (sig_args (fn_sig fd)).

              induction (Args.vs args); ss.
              * ii. inv VALS. inv VALS0. inv ARG.
              * ii. des_ifs; inv VALS0; ss. inv VALS.
                exploit H; eauto. i. destruct a1; ss. des.
                { clarify. inv H4. inv H7. unfold to_mregset in *.
                  erewrite to_mreg_some_to_preg in *; eauto.
                  unfold typify in *. des_ifs; rewrite PTR in *; clarify.
                  exploit H3; eauto. }
                { eapply IHl; eauto. }
            + clarify. rewrite PTR in *. rewrite <- RSPC in *. exploit H; eauto.
            + clarify. rewrite PTR in *. clarify. eapply NSOUND. split.
              * ii. apply WFHI in H1. rewrite NB in *. eapply Plt_strict; eauto.
              * rewrite NB in *. auto.
        }


        econs; ss.
        * econs; ss.
          { i. rewrite JunkBlock.assign_junk_blocks_perm in PERM.
            erewrite Mem.unchanged_on_contents; cycle 1.
            - apply JunkBlock.assign_junk_blocks_unchanged_on.
            - ss.
            - ss.
            - destruct (peq blk (Mem.nextblock (Args.m args))).
              + clarify. inv H0.
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
                          (ZMap.get ofs (Mem.mem_contents m0) !! (Mem.nextblock (Args.m args)))).
                * admit "it doesn't hold!!!!".

                * ii. ss. eapply SOUNDIMPLY. exploit H0; eauto.

              + assert (VALID: Mem.valid_block (Args.m args) blk).
                { apply Mem.perm_valid_block in PERM. unfold Mem.valid_block in *.
                  inv H0. rewrite <- NB0 in *. eapply Mem.nextblock_alloc in ALC.
                  rewrite ALC in *. clear - PERM n0. xomega. }
                exploit store_arguments_unchanged_on; eauto. intros UNCH0.
                erewrite Mem.unchanged_on_contents; eauto.
                * ii. ss. eapply SOUNDIMPLY. eapply SOUND; eauto.
                  eapply Mem.unchanged_on_perm; eauto.
                * eapply Mem.unchanged_on_perm; eauto.
          }
          { ii. apply WFHI in PR. rewrite NB in *.
            unfold Mem.valid_block. etrans; eauto. }
          { etrans; eauto. apply Plt_Ple. rewrite NB in *. auto. }
        * econs; ss. ii. apply WFHI in PR. eapply Plt_Ple_trans; eauto.
          apply Plt_Ple. auto.
        * inv SKENV. ss.
      + econs; ss.
        * i. eapply Mem.unchanged_on_perm; eauto.
        * eapply Mem.unchanged_on_implies; eauto.
        * eapply Mem.unchanged_on_implies; eauto.

    - (* step *)

      inv STEP. des. destruct st0, st1. ss. clarify. destruct st, st0. ss.

      hexploit asm_step_preserve_injection; try apply STEP0.
      { instantiate (1:= SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig asm)) asm).
        instantiate (1:=UnreachC.to_inj su0 (Mem.nextblock m)).
        ii. ss. des_ifs. unfold UnreachC.to_inj, Mem.flat_inj in *. des_ifs.
        esplits; eauto.
      }
      { inv SUST. ii. ss. esplits; eauto.
        unfold UnreachC.to_inj, Mem.flat_inj in *. des_ifs.
        - eapply Genv.genv_symb_range in FINDSRC. ss.
          exfalso. ss. inv WF. eapply WFLO in Heq. rewrite SKE in *. xomega.
        - eapply Genv.genv_symb_range in FINDSRC. ss. exfalso. apply n.
          inv MEM. rewrite SKE in *. eapply Plt_Ple_trans; eauto. }
      { inv SUST. eapply symbols_inject_weak_imply.
        instantiate (1:=skenv_link). unfold symbols_inject. esplits; ss.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. des_ifs; ss.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. esplits; eauto. des_ifs.
          + eapply Genv.genv_symb_range in H0. ss.
            exfalso. ss. inv WF. eapply WFLO in Heq. rewrite SKE in *. xomega.
          + eapply Genv.genv_symb_range in H0. ss. exfalso. apply n.
            inv MEM. rewrite SKE in *. eapply Plt_Ple_trans; eauto.
        - unfold UnreachC.to_inj, Mem.flat_inj. ii. des_ifs.
      }

      { instantiate (1:= r). ii.
        inv SUST. ss. specialize (RS pr). ss. unfold UnreachC.val' in *.
        destruct (r pr); try by econs.
        exploit RS; eauto. i. des. econs.
        - unfold UnreachC.to_inj, Mem.flat_inj. des_ifs. exfalso. apply n.
          inv MEM. rewrite NB in *. eauto.
        - psimpl. auto.
      }

      { eapply UnreachC.to_inj_mem. inv SUST. eauto. }

      i. des. inv SUST. inv MEM.
      assert (MNB: Ple (Mem.nextblock m) (Mem.nextblock m0)).
      { eapply Mem.unchanged_on_nextblock; eauto. }

      exists (Unreach.mk (fun blk => if j1 blk then false
                                     else plt blk (Mem.nextblock m0))
                         (Unreach.ge_nb su0)
                         (Mem.nextblock m0)).
      assert (HLE: Unreach.hle
                     su0 (Unreach.mk
                            (fun blk => if j1 blk then false
                                        else plt blk (Mem.nextblock m0))
                            (Unreach.ge_nb su0)
                            (Mem.nextblock m0))).
      { eapply Unreach.hle_update; [..|refl]; ss; rewrite NB in *; eauto; i.
        destruct (if Unreach.unreach su0 blk then None else Mem.flat_inj (Mem.nextblock m) blk) eqn: BEQ.
        - destruct p. dup BEQ. eapply INCR in BEQ0. des_ifs.
        - destruct (j1 blk) as [[]|] eqn: BEQ0.
          + specialize (SEP _ _ _ BEQ BEQ0). des. des_ifs.
          + unfold Mem.flat_inj, proj_sumbool in *. des_ifs. xomega. }
      assert (SOUNDV: forall v_src v_tgt (INJ: Val.inject j1 v_src v_tgt),
                 UnreachC.val' (Unreach.mk
                                  (fun blk => if j1 blk then false
                                              else plt blk (Mem.nextblock m0))
                                  (Unreach.ge_nb su0)
                                  (Mem.nextblock m0)) v_src).
      { ii. ss. clarify. inv INJ0. inv WF. rewrite NB in *.
        destruct (if Unreach.unreach su0 blk then None else Mem.flat_inj (Mem.nextblock m) blk) eqn: BEQ.
        - destruct p. dup BEQ. eapply INCR in BEQ0.
          unfold Mem.flat_inj in *; des_ifs; esplits; eauto.
          eapply Plt_Ple_trans; eauto.
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
        * i. eapply UnreachC.Unreach_obligation_3; eauto.
        * inv WF. rewrite NB in *. econs; ss.
          { i. des_ifs; eauto.
            destruct (if Unreach.unreach su0 x0
                      then None
                      else Mem.flat_inj (Mem.nextblock m) x0) as [[]|]eqn:EQ.
            - apply INCR in EQ. clarify.
            - unfold Mem.flat_inj in *. des_ifs; eauto. etrans; eauto. xomega. }
          { i. unfold proj_sumbool in *. des_ifs; eauto. }
      + econs; ss; eauto; i.
        * exploit asm_step_max_perm; try apply STEP0; eauto.
        * exploit asm_step_readonly; try apply STEP0; eauto.
        * eapply Mem.unchanged_on_implies; eauto.
          ii. unfold flip in *. ss. esplits; eauto.
          unfold loc_unmapped. unfold UnreachC.to_inj. des_ifs.

    - (* call *)
      inv AT. ss.
      assert(SUARGS: UnreachC.args' su0 (Args.mk (Vptr blk0 Ptrofs.zero) vs m1)).
      {
        inv SUST. r. splits; ss.
        + rewrite <- FPTR. eapply RS; et.
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
      exploit (@Sound.greatest_ex _ su0 (Args.mk (Vptr blk0 Ptrofs.zero) vs m1)); ss; eauto.
      { exists su0. esplits; eauto. refl. }
      i; des.
      des_ifs. clear_tac.
      esplits; eauto.
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
      + (* K *)
        ii. inv AFTER. ss.
        destruct retv; ss. rename m into m2.
        assert(GRARGS: Sound.args su_gr (Args.mk (Vptr blk0 Ptrofs.zero) vs m1)).
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
          des. clarify. rewrite FPTR in *. ss. des_ifs. clear_tac.
          econs; et.
          - ii. eapply Mem_unfree_unchanged_on; et.
          - eapply Mem_unfree_unchanged_on; et.
            (* u. ii; des; ss; clarify. *)
            (* rr in H. eapply H. *)
        }
        (* { inv SUST. inv MEM. rr. split; ss. ii. des_ifs. apply BOUND in PR. unfold Mem.valid_block in *. ss. } *)
        inv SUST.
        generalize (loc_external_result_one sg); intro ONE.
        destruct (loc_external_result sg) eqn:T; ss. clear_tac.
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
              destruct (classic (Unreach.unreach su_ret blk2)); cycle 1.
              { hexploit SOUND; eauto. i.
                eapply UnreachC.memval_le; et. unfold su1. ss. Unreach.nb_tac. xomega.
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
              assert(UNCH: (ZMap.get ofs1 (Mem.mem_contents m2) !! blk2)
                           = (ZMap.get ofs1 (Mem.mem_contents m1) !! blk2)).
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
        { i. eapply (@Sound.hle_val UnreachC.Unreach); ss; et. }
        { (* WF *)
          inv WF. unfold su1. econs; ss; et.
          - i. des_ifs; et.
            inv MEM. xomega.
          - i. des_ifs; et.
            { clear - p FREE MLE. inv MLE. eapply Plt_Ple_trans; eauto.
              etrans; eapply Mem.unchanged_on_nextblock; eauto.
              eapply Mem.free_unchanged_on; eauto. instantiate (1:=bot2). ss. }
            rr in RETV. des. ss. inv WF. inv MEM0. Unreach.nb_tac. eapply WFHI0; et.
        }

    - (* return *)
      inv SUST. inv FINAL. ss. clarify.
      exists su0. esplits; eauto.
      { refl. }
      { rr. ss. esplits; ss; et.
        eapply unreach_free; eauto.
      }
      eapply Unreach.free_mle; eauto.
      exploit INIT; eauto. i; des. ss.
  Qed.

End TRIAL2.
End TRIAL2.

Let asm_ext_unreach_lxsim: forall
    asm skenv_link
    m_src0 m_tgt0
    (GENV: Genv.match_genvs (match_globdef (fun _ : AST.program fundef unit => eq) eq asm)
                            (SkEnv.revive (SkEnv.project skenv_link asm.(Sk.of_program fn_sig)) asm)
                            (SkEnv.revive (SkEnv.project skenv_link asm.(Sk.of_program fn_sig)) asm))
    m_src1 m_tgt1
    st_init_src st_init_tgt
  ,
    <<LXSIM: @lxsim (modsem skenv_link asm) (modsem skenv_link asm)
                    (SimMemExt.SimMemExt)
                    (fun st => exists su m_init, sound_state skenv_link su m_init st)
                    (SimMemExt.mk m_src0 m_tgt0) (lift_idx unit_ord_wf tt) st_init_src st_init_tgt
                    (SimMemExt.mk m_src1 m_tgt1)>>
.
Proof.
  i. revert_until m_tgt1.
  pcofix CIH. ii. pfold.
Abort.

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

Inductive match_states_ext
          (skenv_link_tgt : SkEnv.t)
          (ge_src ge_tgt: genv)
          (sm_init : @SimMem.t SimMemExt.SimMemExt)
  : unit -> AsmC.state -> AsmC.state -> (@SimMem.t SimMemExt.SimMemExt) -> Prop :=
| match_states_ext_intro
    init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : @SimMem.t SimMemExt.SimMemExt)
    (AGREE: AsmStepExt.agree rs_src rs_tgt)
    (AGREEINIT: AsmStepExt.agree init_rs_src init_rs_tgt)
    (* (INJ: Mem.extends m_src m_tgt) *)
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (UNDEF: undef_bisim init_rs_src init_rs_tgt)
    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITSRC: wf_init_rs fd.(fn_sig) init_rs_src)
    (WFINITTGT: wf_init_rs fd.(fn_sig) init_rs_tgt)
    (RAWF: Genv.find_funct skenv_link_tgt (init_rs_tgt RA) = None)
  :
    match_states_ext
      skenv_link_tgt
      ge_src ge_tgt sm_init tt
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0
.

Require Import Conventions1C.

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

Lemma asm_ext_unreach
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto. instantiate (1:=tt).
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  fold SkEnv.t in skenv_link_src.
  hexploit (TRIAL2.asm_unreach_local_preservation skenv_link_src asm); eauto. i; des.

  eapply match_states_sim with
      (match_states :=
         match_states_ext
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm)); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eauto.

  - (* init bsim *)
    ii. inv SIMSKENV. ss.
    inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
    inv INITTGT. ss. inv TYP. rewrite val_inject_list_lessdef in *.
    inv STORE. des.
    exploit store_arguments_parallel_extends; [..| eauto |]; eauto.
    + eapply typify_has_type_list; eauto.
    + rewrite val_inject_list_lessdef in *.
      eapply inject_list_typify_list; try eassumption.
      erewrite inject_list_length; eauto.
    + i. des.
      eexists (AsmC.mkstate (asm_init_rs
                               rs_src (to_mregset rs)
                               (fn_sig fd) fptr (rs RA) (Mem.nextblock src))
                            (Asm.State _ (JunkBlock.assign_junk_blocks m_src1 n))).
      esplits; eauto.
      { econs; ss; eauto.
        - rewrite SIMSKENVLINK in *. cinv FPTR; ss; clarify; eauto.
          exfalso. inv SAFESRC. ss.
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
        - inv SIMSKENVLINK. unfold asm_init_rs, to_pregset, Pregmap.set. des_ifs.
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
                       (fn_sig fd) fptr (rs RA) (Mem.nextblock src)) rs).
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
        - eapply asm_init_rs_undef_bisim.
        - unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
          rewrite SIMSKENVLINK in *. inv FPTR; ss; clarify; eauto.
          exfalso. inv SAFESRC. clarify.
        - econs; ss. ii. rewrite H0 in *. clarify.
        - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
          hexploit RANOTFPTR; eauto. i. exfalso. eapply H1.
          eapply Genv.genv_defs_range; eauto. }

  - ii. des. inv SAFESRC. inv TYP.
    eapply asm_initial_frame_succeed; eauto.
    + inv SIMARGS. ss. apply lessdef_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + inv SIMSKENVLINK. inv SIMARGS. ss. inv FPTR; ss.
      rewrite <- H0 in *. ss.

  - ii. inv MATCH. ss.

  - (** ******************* at external **********************************)
    ii. inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. inv INJPC.
    unfold inject_id in *. clarify. psimpl.
    exploit extcall_arguments_extends; try apply AGREE; eauto. i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.
    exploit Mem.free_parallel_extends; eauto. i. des.
    eexists (Args.mk (Vptr blk0 _) _ _). eexists (SimMemExt.mk _ _).
    esplits; eauto; ss; i.
    + econs; eauto.
      * rewrite SIMSKENVLINK in *. ss.
      * esplits; eauto. rewrite SIMSKENVLINK in *. ss.
      * clear - AGREE TPTR RADEF. splits.
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
    + econs; ss.
    + instantiate (1:=top4). ss.

  - ii. destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC. inv SIMRET.
    cinv (AGREE RSP); rewrite RSRSP in *; ss. des.
    unfold Genv.find_funct in FINDF. unfold Genv.find_funct in SIG. des_ifs. ss.
    rewrite MEMSRC in *. exploit Mem_unfree_parallel_extends; try apply MWF; eauto.
    i. des. rewrite <- MEMSRC in *.
    unfold inject_id in *. clarify.
    esplits; ss.
    + i. ss. splits.
      { instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
        - instantiate (1:=SkEnv.get_sig skd). esplits; eauto.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
          cinv (AGREE PC); rewrite Heq in *; clarify.
          inv SIMSKENV. ss. inv SIMSKELINK. psimpl. des_ifs.
        - eauto.
        - rewrite MEMTGT in *. instantiate (1:=m2').
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
        - eauto.
        - eauto. }

  - (** ******************* final **********************************)
    i. inv MATCH. inv FINALSRC.
    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl. ss.
    exploit Mem.free_parallel_extends; eauto. i. des.
    unfold inject_id in *. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H1).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H1 UNDEF. inv WFINITSRC.
        eapply lessdef_commute; try eassumption.
        -- rewrite <- val_inject_lessdef. eassumption.
        -- rewrite <- val_inject_lessdef. eassumption.
        -- eauto.
      * des. esplits; eauto.
        rewrite SIMSKENVLINK in *. specialize (AGREEINIT PC).
        inv AGREEINIT; clarify; ss. rewrite <- H3 in *. ss.
      * unfold external_state in *. rewrite SIMSKENVLINK in *.
        des_ifs_safe. exfalso.
        specialize (AGREE PC). inv AGREE.
        { rewrite H5 in *. rewrite Heq in *. des_ifs. }
        { inv WFINITSRC. rewrite <- H3 in *. eauto. }
      * inv WFINITSRC. inv WFINITTGT.
        unfold Val.has_type in TPTR. des_ifs.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
      * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        cinv (AGREE RSP); rewrite RSRSP in *; clarify.
    + econs; ss.

  - left. ii. esplits; ss; i.
    + admit "receptive".
    + exists tt.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        destruct st0. ss. clarify.
        exploit asm_step_preserve_extension; try apply STEP; eauto. i. des.
        rewrite SIMSKENVLINK in *.
        esplits; auto.
        - left. econs; [|econs 1|symmetry; eapply E0_right]. econs.
          { admit "determinate". }
          instantiate (1:=AsmC.mkstate _ _).
          econs; ss; eauto.
        - instantiate (1:=SimMemExt.mk _ _). econs; ss; eauto.
      }
Qed.

(* It's ***exactly*** same as asm_ext_sound *)
Lemma asm_ext_top
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto. instantiate (1:=tt).
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  fold SkEnv.t in skenv_link_src.

  eapply match_states_sim with
      (match_states :=
         match_states_ext
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm)); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    instantiate (1:=top3). econs; ss.  ii. exists tt. esplits; ss.

  - (* init bsim *)
    ii. inv SIMSKENV. ss.
    inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
    inv INITTGT. ss. inv TYP. rewrite val_inject_list_lessdef in *.
    inv STORE. des.
    exploit store_arguments_parallel_extends; [..| eauto |]; eauto.
    + eapply typify_has_type_list; eauto.
    + rewrite val_inject_list_lessdef in *.
      eapply inject_list_typify_list; try eassumption.
      erewrite inject_list_length; eauto.
    + i. des.
      eexists (AsmC.mkstate (asm_init_rs
                               rs_src (to_mregset rs)
                               (fn_sig fd) fptr (rs RA) (Mem.nextblock src))
                            (Asm.State _ (JunkBlock.assign_junk_blocks m_src1 n))).
      esplits; eauto.
      { econs; ss; eauto.
        - rewrite SIMSKENVLINK in *. cinv FPTR; ss; clarify; eauto.
          exfalso. inv SAFESRC. ss.
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
        - inv SIMSKENVLINK. unfold asm_init_rs, to_pregset, Pregmap.set. des_ifs.
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
                       (fn_sig fd) fptr (rs RA) (Mem.nextblock src)) rs).
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
        - eapply asm_init_rs_undef_bisim.
        - unfold asm_init_rs, to_pregset, set_regset, Pregmap.set. des_ifs.
          rewrite SIMSKENVLINK in *. inv FPTR; ss; clarify; eauto.
          exfalso. inv SAFESRC. clarify.
        - econs; ss. ii. rewrite H0 in *. clarify.
        - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def. des_ifs.
          hexploit RANOTFPTR; eauto. i. exfalso. eapply H1.
          eapply Genv.genv_defs_range; eauto. }

  - ii. des. inv SAFESRC. inv TYP.
    eapply asm_initial_frame_succeed; eauto.
    + inv SIMARGS. ss. apply lessdef_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + inv SIMSKENVLINK. inv SIMARGS. ss. inv FPTR; ss.
      rewrite <- H0 in *. ss.

  - ii. inv MATCH. ss.

  - (** ******************* at external **********************************)
    ii. inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. inv INJPC.
    unfold inject_id in *. clarify. psimpl.
    exploit extcall_arguments_extends; try apply AGREE; eauto. i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.
    exploit Mem.free_parallel_extends; eauto. i. des.
    eexists (Args.mk (Vptr blk0 _) _ _). eexists (SimMemExt.mk _ _).
    esplits; eauto; ss; i.
    + econs; eauto.
      * rewrite SIMSKENVLINK in *. ss.
      * esplits; eauto. rewrite SIMSKENVLINK in *. ss.
      * clear - AGREE TPTR RADEF. splits.
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
    + econs; ss.
    + instantiate (1:=top4). ss.

  - ii. destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC. inv SIMRET.
    cinv (AGREE RSP); rewrite RSRSP in *; ss. des.
    unfold Genv.find_funct in FINDF. unfold Genv.find_funct in SIG. des_ifs. ss.
    rewrite MEMSRC in *. exploit Mem_unfree_parallel_extends; try apply MWF; eauto.
    i. des. rewrite <- MEMSRC in *.
    unfold inject_id in *. clarify.
    esplits; ss.
    + i. ss. splits.
      { instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
        - instantiate (1:=SkEnv.get_sig skd). esplits; eauto.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
          cinv (AGREE PC); rewrite Heq in *; clarify.
          inv SIMSKENV. ss. inv SIMSKELINK. psimpl. des_ifs.
        - eauto.
        - rewrite MEMTGT in *. instantiate (1:=m2').
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
        - eauto.
        - eauto. }

  - (** ******************* final **********************************)
    i. inv MATCH. inv FINALSRC.
    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl. ss.
    exploit Mem.free_parallel_extends; eauto. i. des.
    unfold inject_id in *. clarify.
    eexists (SimMemExt.mk _ _). esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H1).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H1 UNDEF. inv WFINITSRC.
        eapply lessdef_commute; try eassumption.
        -- rewrite <- val_inject_lessdef. eassumption.
        -- rewrite <- val_inject_lessdef. eassumption.
        -- eauto.
      * des. esplits; eauto.
        rewrite SIMSKENVLINK in *. specialize (AGREEINIT PC).
        inv AGREEINIT; clarify; ss. rewrite <- H3 in *. ss.
      * unfold external_state in *. rewrite SIMSKENVLINK in *.
        des_ifs_safe. exfalso.
        specialize (AGREE PC). inv AGREE.
        { rewrite H5 in *. rewrite Heq in *. des_ifs. }
        { inv WFINITSRC. rewrite <- H3 in *. eauto. }
      * inv WFINITSRC. inv WFINITTGT.
        unfold Val.has_type in TPTR. des_ifs.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
      * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        cinv (AGREE RSP); rewrite RSRSP in *; clarify.
    + econs; ss.

  - left. ii. esplits; ss; i.
    + admit "receptive".
    + exists tt.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        destruct st0. ss. clarify.
        exploit asm_step_preserve_extension; try apply STEP; eauto. i. des.
        rewrite SIMSKENVLINK in *.
        esplits; auto.
        - left. econs; [|econs 1|symmetry; eapply E0_right]. econs.
          { admit "determinate". }
          instantiate (1:=AsmC.mkstate _ _).
          econs; ss; eauto.
        - instantiate (1:=SimMemExt.mk _ _). econs; ss; eauto.
      }
Qed.


Inductive match_states
          (skenv_link_tgt: SkEnv.t)
          (ge_src ge_tgt: genv)
          (sm_init : @SimMem.t SimMemInjC.SimMemInj)
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
    AsmC.state -> AsmC.state -> @SimMem.t SimMemInjC.SimMemInj -> Prop :=
| has_foot_print_intro
    blk0 blk1_src blk1_tgt ofs_src ofs_tgt
    (init_rs_src init_rs_tgt rs0_src rs0_tgt: regset)
    m_src m_tgt (sm0: @SimMem.t SimMemInjC.SimMemInj) sg
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

    (MLEEXCLWF: sm0.(SimMemInj.tgt_external) <2= (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))


  :
    has_footprint skenv_link_src skenv_link_tgt
                  (mkstate init_rs_src (State rs0_src m_src))
                  (mkstate init_rs_tgt (State rs0_tgt m_tgt))
                  sm0
.

Inductive mle_excl
          (skenv_link_src skenv_link_tgt: SkEnv.t)
  : AsmC.state -> AsmC.state -> (@SimMem.t SimMemInjC.SimMemInj)
    -> (@SimMem.t SimMemInjC.SimMemInj) -> Prop :=
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
    (mrel0 mrel1: @SimMem.t SimMemInjC.SimMemInj)
    (INCR: inject_incr mrel0.(SimMemInj.inj) mrel1.(SimMemInj.inj))

    (SRCUNCHANGED: Mem.unchanged_on mrel0.(SimMemInj.src_external) mrel0.(SimMem.src) mrel1.(SimMem.src))

    (TGTUNCHANGED: Mem.unchanged_on
                     ((mrel0.(SimMemInj.tgt_external))
                        /2\
                        (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))
                     mrel0.(SimMem.tgt) mrel1.(SimMem.tgt))

    (SRCPARENTEQ: mrel0.(SimMemInj.src_external) = mrel1.(SimMemInj.src_external))
    (SRCPARENTEQNB: mrel0.(SimMemInj.src_parent_nb) = mrel1.(SimMemInj.src_parent_nb))
    (TGTPARENTEQ: mrel0.(SimMemInj.tgt_external) /2\
                                                 (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))) = mrel1.(SimMemInj.tgt_external))
    (TGTPARENTEQNB: mrel0.(SimMemInj.tgt_parent_nb) = mrel1.(SimMemInj.tgt_parent_nb))
    (FROZEN: SimMemInj.frozen mrel0.(SimMemInj.inj) mrel1.(SimMemInj.inj) (mrel0.(SimMemInj.src_parent_nb))
                                                                          (mrel0.(SimMemInj.tgt_parent_nb)))

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


Require Import MatchSimModSemExcl.
Require Import Conventions1C.

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

Lemma asm_inj_drop_bot
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = bot1>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { admit "add condition". }
  eapply match_states_sim with
      (match_states :=
         match_states
           skenv_link_tgt
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm))
      (match_states_at := top4)
      (has_footprint := has_footprint skenv_link_src skenv_link_tgt)
      (mle_excl := mle_excl skenv_link_src skenv_link_tgt); ss; eauto; ii.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - inv MLE. inv FOOT. inv MLEEXCL.
    ss. econs; ss; eauto.
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
      destruct (SimMemInj.inj sm1 b_src) eqn:EQ.
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

  - inv SIMSKENV. ss.
    inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
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
        exfalso. inv PUBLIC. exploit mi_freeblocks.
        - eapply Plt_strict.
        - i. clarify.
      }
      esplits; eauto.
      {
        econs; ss; eauto.
        - instantiate (1:=fd).
          unfold Genv.find_funct in *. des_ifs_safe.
          cinv FPTR; ss; clarify; cycle 1.
          {
            exfalso. inv SAFESRC. ss.
          }

          assert (delta = 0).
          {
            unfold Genv.find_funct_ptr, SkEnv.revive in *. des_ifs.
            eapply Genv_map_defs_def in Heq0. des.
            inv SIMSKE. exploit SIMDEFINV; eauto. i. des. eauto.
          }
          clarify. psimpl. des_ifs.
          unfold Genv.find_funct_ptr in *. des_ifs_safe.
          clear - INCLSRC INCLTGT SIMSKENVLINK SIMSKE SIMSKELINK Heq0 H5.

          {
            (* genv *)
            unfold SkEnv.revive in *. ss.
            apply Genv_map_defs_def in Heq0. des.
            unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
            des_ifs_safe.
            apply Genv.invert_find_symbol in Heq0.
            inv SIMSKE. ss.
            exploit SIMDEFINV; eauto. i. des. clarify.
            exploit Genv_map_defs_def_inv; try apply DEFSRC.
            i. rewrite H. ss.
            unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
            erewrite Genv.find_invert_symbol. rewrite Heq1; eauto.
            exploit SIMSYMB3; eauto. i. des.
            assert (blk_src = b1).
            { exploit DISJ; eauto. }
            clarify.
          }

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
            inv SIMSKELINK. ss.
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

      {

        instantiate (1:=SimMemInj.mk
                          (JunkBlock.assign_junk_blocks m_src1 n) (JunkBlock.assign_junk_blocks m0 n)
                          (junk_inj m_src1 m0 (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0) n)
                          _ _ _ _).
        econs; ss; auto.
        - etrans.
          + eauto.
          + eapply junk_inj_incr; eauto.
        - etrans.
          + i. exploit store_arguments_unchanged_on; try apply ARGTGT; eauto. i. eapply Mem.unchanged_on_implies; eauto.
          + eapply Mem.unchanged_on_implies;
              try apply JunkBlock.assign_junk_blocks_unchanged_on; ss.
        - etrans.
          + i. exploit store_arguments_unchanged_on; try apply H; eauto.
            i. eapply Mem.unchanged_on_implies; eauto.
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
                - eapply Mem.valid_block_inject_1; eauto.
                - eapply Mem.valid_block_inject_1; eauto. }
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
              apply JunkBlock.assign_junk_blocks_unchanged_on.

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
        - instantiate (1:= fd).
          inv SAFESRC. ss.
          unfold to_pregset, set_regset, Pregmap.set. des_ifs.

          clear - FINDF FINDF0 FPTR SIMSKE.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. inv FPTR.
          unfold SkEnv.revive in *.
          apply Genv_map_defs_def in Heq2. des.
          apply Genv_map_defs_def in Heq0. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in *.
          des_ifs_safe. apply Genv.invert_find_symbol in Heq2.
          inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
          exploit SIMSYMB1; eauto. i. des.
          apply Genv.find_invert_symbol in BLKTGT. clarify.

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

  - ii. des. inv SAFESRC. inv TYP.
    eapply asm_initial_frame_succeed; eauto.
    + inv SIMARGS. ss. apply inject_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); eauto.
    + (* genv *)
      inv SIMSKENV. ss. inv SIMSKE. ss.
      unfold Genv.find_funct in *. des_ifs_safe. inv SIMARGS.
      inv FPTR; try rewrite Heq in *; clarify.
      unfold Genv.find_funct_ptr in *. des_ifs_safe.
      unfold SkEnv.revive in *. ss.
      apply Genv_map_defs_def in Heq0. des.
      unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
      des_ifs_safe.
      apply Genv.invert_find_symbol in Heq1.
      exploit SIMDEF; eauto. i. des. clarify.
      des_ifs_safe.
      exploit Genv_map_defs_def_inv; try apply DEFTGT.
      i. rewrite H. ss.
      unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
      erewrite Genv.find_invert_symbol. rewrite Heq2; eauto.
      exploit SIMSYMB1; eauto. i. des. eauto.

  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. inv INJPC.
    assert (delta = 0).
    {
      clear EXTERNAL. unfold Genv.find_funct_ptr in *. des_ifs.
      inv SIMSKELINK.
      exploit SIMDEF; eauto.
      i. des. eauto.
    }
    clarify. psimpl. ss.
    exploit extcall_arguments_inject; eauto.
    { inv MWF. eauto. }
    i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.

    exploit Mem_free_parallel'; eauto. i. des.
    eexists (Args.mk (Vptr b2 _) _ _). exists sm1.
    esplits; eauto; ss; i.
    + econs; eauto.
      * {
          (* genv *)
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. exfalso.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq3.
          inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.

          exploit Genv_map_defs_def_inv; try apply DEFSRC.
          i. revert EXTERNAL. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq4; eauto. i. clarify.
          - exploit SIMSYMB3; eauto. i. des.
            assert (blk_src = blk0).
            { exploit DISJ; eauto. }
            clarify.
        }
      * esplits; eauto.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv SIMSKELINK.
        exploit SIMDEF; try apply Heq1; eauto. i. des. clarify.
        rewrite DEFTGT. eauto.
      * clear - AGREE TPTR RADEF. splits.
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      * inv MWF. i. erewrite Mem.address_inject; eauto; cycle 1.
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
    + econs; s; eauto.
      * eapply val_inject_incr; cycle 1; eauto.
        inv MLE. eauto.
      * eapply val_inject_list_incr; cycle 1; eauto.
        inv MLE. eauto.
    + inv MWF. econs; ss; eauto.
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
           dup H0. erewrite Mem.address_inject in H0; eauto; cycle 1.
           { eapply Mem.free_range_perm; eauto. lia. }
           erewrite Mem.address_inject in H5; eauto; cycle 1.
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

    inv MWF0. inv MWF. rewrite MEMSRC in *.
    assert (PERMRET: forall ofs, Mem.perm (SimMemInj.src sm_ret) blk ofs Max <1= Mem.perm (SimMemInj.src sm0) blk ofs Max).
    { inv MLE. inv MLE0. ii. eapply MAXSRC; eauto.
      - eapply Mem.valid_block_inject_1; eauto.
      - eapply MAXSRC0; eauto.
        + eapply Mem.valid_block_unchanged_on; eauto.
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
      eapply Mem.mi_representable; try apply PUBLIC; eauto. des.
      - exploit PERMRET; eauto.
      - exploit PERMRET; eauto.
      - left. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs.
      - right. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. econs. }
    { inv MLE0. cinv (AGREE RSP); rewrite RSRSP in *; clarify.
      inv HISTORY. inv CALLTGT. ss. des.
      unfold Genv.find_funct in SIG, SIG0, EXTERNAL. des_ifs.
      rewrite RSP in *. inv SIMARGS. ss. clarify.
      ii. apply MAXTGT in H; cycle 1.
      { inv MLE. eapply Mem.valid_block_unchanged_on; eauto.
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
    + instantiate (1:=SimMemInj.mk m1 m2' (SimMemInj.inj sm_ret) _ _ _ _).
      econs; ss; eauto.
      * eapply Mem.unchanged_on_implies.
        { rewrite <- MEMSRC. eapply Mem_unfree_unchanged_on; eauto. }
        ii. unfold brange in *. des. clarify.
        inv MWFAFTR. ss.
        eapply SRCEXT1 in H.
        unfold SimMemInj.src_private, loc_unmapped in *. ss. des.
        inv MLE. inv MLE0.
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
        - instantiate (1:=SimMemInj.inj sm_ret).
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
        - unfold SimMemInj.unlift' in *. ss.
          econs; ss; eauto.
          + inv MWFAFTR.
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
            * ii. des. eapply PR0.
              inv MLE0. inv MWF. ss.
              eapply TGTEXT1 in PR.
              rewrite TGTPARENTEQ in *.
              eapply TGTEXT0 in PR.
              unfold SimMemInj.tgt_private in *. des.
              unfold loc_out_of_reach in *.
              hexploit PR; eauto.

              ii.
              dup UNFREE. eapply Mem_unfree_unchanged_on in UNFREE. inv UNFREE.

              apply NNPP. ii. exploit unchanged_on_perm; eauto.
              -- instantiate (1:=x1-delta0). instantiate (1:=b1).
                 ii. eapply H4.
                 unfold brange in *. des. clarify. split.
                 ++ inv MLE1. ss. exploit INCR0; eauto. i. clarify.
                 ++ inv MLE1. ss. dup H2. apply INCR0 in H2. rewrite H2 in *. clarify.
                    inv CALLSRC. inv MATCH. rewrite RSP in *. clarify.
                    erewrite Mem.address_inject; try eapply PUBLIC; eauto.
                    { clear - H6 H7. lia. }
                    { eapply Mem.free_range_perm; eauto.
                      des. clarify.
                      assert (skd = skd0); [|clarify; lia].
                      inv SIMSKENV. ss. inv SIMSKELINK. clear - Heq FPTR AGREE0 SIMDEF SIG SIG0.
                      unfold Genv.find_funct_ptr in *. des_ifs_safe.
                      cinv (AGREE0 PC); rewrite Heq in *; clarify. }
              -- eapply Mem.valid_block_inject_1; eauto.
              -- i. des. eauto.
            * unfold SimMemInj.valid_blocks, Mem.valid_block.
              erewrite <- Mem_nextblock_unfree; eauto. des.
              inv MLE0. ss. inv TGTUNCHANGED. eapply Plt_Ple_trans; eauto.
              inv MWF. eapply TGTEXT1 in PR. unfold SimMemInj.tgt_private in *. des. eauto.
          + inv MWFAFTR. ss.
            rewrite MEMSRC in *.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
          + inv MWFAFTR. ss.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
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

    eexists (SimMemInj.mk _ _ _ _ _ _ _). esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H UNDEF.
        inv WFINITSRC.
        eapply lessdef_commute; eauto.
      * des. esplits; eauto.

        {
          (* genv *)
          unfold Genv.find_funct, Genv.find_funct_ptr in *.
          des_ifs_safe.
          cinv (AGREEINIT PC); rewrite Heq in *; clarify.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq0. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq1.
          inv SIMSKENV. inv SIMSKE. ss.
          exploit SIMDEF; try apply FIND; eauto. i. des. clarify.

          exploit Genv_map_defs_def_inv; try apply DEFTGT.
          i. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq2; eauto.
          - exploit SIMSYMB2; eauto. i. des. clarify.
        }

      * unfold external_state in *.

        des_ifs_safe. exfalso.
        cinv (AGREE PC); try rewrite Heq in *; clarify; eauto.
        {
          (* genv *)
          des_ifs. clear RANOTFPTR.
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
            exploit DISJ; eauto.
        }
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
      * eapply Mem.free_unchanged_on; eauto.
        ii. eapply SRCEXT in H0. unfold SimMemInj.src_private in *. des.
        unfold loc_unmapped in *. congruence.
      * eapply Mem.free_unchanged_on; eauto.
        ii. eapply TGTEXT in H0. unfold SimMemInj.tgt_private in *. des.
        unfold loc_out_of_reach in *.
        exploit H0; eauto. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
        -- eapply Mem.free_range_perm; eauto.
           rewrite Ptrofs.add_zero_l in *.
           erewrite Ptrofs.unsigned_repr in *; split; try lia; eapply max_unsigned_zero.
        -- econs.
      * econs; ss; eauto. ii. des. clarify.
      * ii. eapply Mem.perm_free_3; eauto.
      * ii. eapply Mem.perm_free_3; eauto.
    + econs; ss; unfold SimMemInj.src_private, SimMemInj.tgt_private in *; ss; eauto; i.
      * ii. eapply SRCEXT in PR. des. splits; eauto.
        eapply Mem.valid_block_free_1; eauto.
      * ii. eapply TGTEXT in PR. des.
        unfold loc_out_of_reach in *.
        splits; eauto.
        -- ii. eapply PR; eauto.
           eapply Mem.perm_free_3; eauto.
        -- eapply Mem.valid_block_free_1; eauto.
      * etrans; eauto. erewrite <- Mem.nextblock_free; eauto. refl.
      * etrans; eauto. erewrite <- Mem.nextblock_free; eauto. refl.

  - left; i.
    esplits; ss; i.
    + admit "receptive".
    + exists O.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        inv MWF. destruct st0. ss. clarify.

        inv SIMSKENV. inv SIMSKE. ss.

        exploit asm_step_preserve_injection; eauto.

        {
          instantiate (1:=SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm).
          (* genv *)
          i. unfold SkEnv.revive in *. exists d_src.
          apply Genv_map_defs_def in FINDSRC. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq0.
          exploit SIMDEF; try apply FIND; eauto. i. des. clarify.
          esplits; eauto.
          exploit Genv_map_defs_def_inv; try apply DEFTGT.
          i. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq1; eauto.
          - exploit SIMSYMB1; eauto. i. des. eauto.
        }

        {
          i. unfold SkEnv.revive in *.
          rewrite Genv_map_defs_symb in FINDSRC.
          exploit SIMSYMB2; try apply FINDSRC; eauto.
        }

        { eapply symbols_inject_weak_imply.
          instantiate (1:=skenv_link_tgt). clear - SIMSKELINK.
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
            destruct (Genv.find_def skenv_link_src b1) eqn:DEQ.
            + exploit SIMDEF; eauto. i. des. clarify.
              rewrite DEFTGT. eauto.
            + des_ifs_safe. exfalso. exploit SIMDEFINV; eauto.
              i. des. clarify.
        }

        i. des.
        eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).
        eexists (SimMemInj.mk _ _ _ _ _ _ _).
        esplits.
        - left. econs; cycle 1.
          + apply star_refl.
          + symmetry. apply E0_right.
          + econs.
            * admit "determinate".
            * econs; ss; eauto.
        - instantiate (5 := j1).
          econs; ss.
          + eapply Mem.unchanged_on_implies. eauto.
            i. eapply SRCEXT; eauto.
          + eapply Mem.unchanged_on_implies; eauto.
            i. eapply TGTEXT; eauto.
          + econs. ii. des.
            exploit SEP; eauto. i. des.
            unfold Mem.valid_block in *. split.
            * eapply Ple_trans; eauto.
              apply Pos.le_nlt; eauto.
            * eapply Ple_trans; eauto.
              apply Pos.le_nlt; eauto.

          + ii. eapply asm_step_max_perm; eauto.
          + ii. eapply asm_step_max_perm; eauto.
        - econs; eauto.
          + eapply agree_incr; eauto.
          + { econs; ss.
              - etrans; eauto.
                unfold SimMemInj.src_private, loc_unmapped in *. ii. des; ss.
                split.
                + destruct (j1 x0) eqn:MAPPED; eauto. destruct p.
                  exfalso. exploit SEP; eauto.
                  i. des. eauto.
                + inv UNCHSRC. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                  xomega.
              - etrans; eauto.
                unfold SimMemInj.tgt_private, loc_out_of_reach in *. ii. des; ss.
                split; i.
                + destruct (SimMemInj.inj sm0 b0) eqn:MAP.
                  * destruct p.
                    dup MAP. apply INCR in MAP. clarify. ii.
                    exploit PR; eauto.
                    eapply asm_step_max_perm in STEP; eauto.
                    eapply Mem.valid_block_inject_1; eauto.
                  * exploit SEP; eauto. i. des. exfalso. eauto.
                + inv UNCHTGT. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                  xomega.
              - etrans; eauto.
                inv UNCHSRC. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                xomega.
              - etrans; eauto.
                inv UNCHTGT. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                xomega.
            }
          + i. exploit RSPDELTA; eauto. i. des. esplits; eauto.
      }

Qed.

Lemma asm_inj_drop
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  exploit asm_inj_drop_bot. i. des. eauto.
Qed.

Lemma SymSymbId_SymSymbDrop_bot sm_arg ss_link ge_src ge_tgt
      (SIMSKE: SimMemInjC.sim_skenv_inj sm_arg ss_link ge_src ge_tgt)
  :
    SimSymbDrop.sim_skenv sm_arg bot1 ge_src ge_tgt.
Proof.
  inv SIMSKE. ss. unfold SimSymbId.sim_skenv in *. clarify.
  inv INJECT. ss.
  econs; ss; i.
  + exploit DOMAIN; eauto.
    { instantiate (1:=blk_src).
      exploit Genv.genv_symb_range; eauto. }
    i. clarify. esplits; eauto.
  + esplits; eauto. exploit DOMAIN; eauto.
    exploit Genv.genv_symb_range; eauto.
  + esplits; eauto. exploit DOMAIN; eauto.
    exploit Genv.genv_symb_range; eauto.
  + exploit DOMAIN; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. rewrite SIMVAL in *. inv H. esplits; eauto.
  + exploit DOMAIN.
    { instantiate (1:=blk_src0).
      exploit Genv.genv_symb_range; eauto. } i.
    rewrite SIMVAL0 in *. inv H.
    exploit IMAGE; try apply SIMVAL1.
    { exploit Genv.genv_symb_range; eauto. }
    i. etrans; eauto.
  + exploit IMAGE; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. clarify.
    exploit DOMAIN; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. rewrite SIMVAL in *. inv H. esplits; eauto.
Qed.

Lemma asm_inj_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  set (asm_inj_drop_bot asm). des.
  destruct mp eqn: EQ. ss. clarify. inv SIM. ss.
  unfold ModPair.to_msp in *. ss.
  eexists (ModPair.mk _ _ _). esplits; ss. instantiate (1:=tt).
  econs; ss. unfold ModPair.to_msp. ss.
  i. destruct ss_link.
  exploit SIMMS; [apply INCLSRC|apply INCLTGT|..]; eauto.
  { inv SSLE. instantiate (1:=bot1). econs; ss. i. des. clarify. }
  { instantiate (1:=sm_init_link).
    exploit SymSymbId_SymSymbDrop_bot; eauto. }
  i. inv H. ss.
  econs; ss; eauto. i. exploit SIM; eauto.
  inv SIMSKENV. ss. econs; ss.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKE; eauto.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKELINK; eauto.
Qed.
