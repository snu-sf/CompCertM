Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import MutrecA MutrecAspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift AsmregsC MatchSimModSem.
Require SoundTop.
Require SimMemInjC SimMemInjInvC.
Require Import Clightdefs.
Require Import CtypesC.

Set Implicit Arguments.


Definition memoized_inv: SimMemInjInv.memblk_invariant :=
  SimMemInjInv.memblk_invarant_mk
    (fun mem =>
       forall
         chunk ofs ind
         (BOUND: 0 <= ind < 1000)
         (INT: chunk = Mint32)
         (INDEX: size_chunk Mint32 * ind = ofs),
       exists i,
         (<<VINT: mem chunk ofs = Some (Vint i)>>) /\
         (<<VAL: forall (NZERO: i.(Int.intval) <> 0),
             (<<MEMO: i = sum (Int.repr ind)>>)>>))
    (fun chunk ofs p =>
       exists ind,
         (<<CHUNK: chunk = Mint32>>) /\ (<<BOUND: 0 <= ind < 1000>>) /\
         (<<INDEX: ofs = size_chunk Mint32 * ind>>) /\ (<<WRITABLE: p = Writable>>)).

Local Instance SimMemMemoizedA: SimMem.class := SimMemInjInvC.SimMemInjInv
                                                 SimMemInjInv.top_inv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Lemma memoized_inv_store_le i ind blk ofs m_tgt
      (sm0 sm1: SimMemInjInv.t')
      (MWF: SimMem.wf sm0)
      (INVAR: sm0.(SimMemInjInv.mem_inv_tgt) blk)
      (SUM: i = sum (Int.repr ind))
      (OFS: ofs = size_chunk Mint32 * ind)
      (STR: Mem.store Mint32 sm0.(SimMemInjInv.minj).(SimMemInj.tgt) blk ofs (Vint i) = Some m_tgt)
      (MREL: sm1 = SimMemInjInv.mk
                     (SimMemInjC.update
                        (sm0.(SimMemInjInv.minj))
                        (sm0.(SimMemInjInv.minj).(SimMemInj.src))
                        m_tgt
                        (sm0.(SimMemInjInv.minj).(SimMemInj.inj)))
                     sm0.(SimMemInjInv.mem_inv_src)
                     sm0.(SimMemInjInv.mem_inv_tgt))
  :
    (<<MLE: SimMem.le sm0 sm1>>) /\
    (<<MWF: SimMem.wf sm1>>).
Proof.
  inv MWF. split.
  - econs; ss; eauto. econs; ss; eauto.
    + refl.
    + eapply Mem.store_unchanged_on; eauto.
      ii. inv WF. exploit INVRANGETGT; eauto. i. des.
      exfalso. eauto.
    + eapply SimMemInj.frozen_refl. + eapply SimMemInj.frozen_refl.
    + ii. eapply Mem.perm_store_2; eauto.
  - inv WF. econs; ss; eauto.
    + unfold SimMemInjC.update. econs; ss; eauto.
      * eapply MemoryC.private_unchanged_inject; eauto.
        { eapply Mem.store_unchanged_on; eauto.
          instantiate (1:=~2
                        loc_out_of_reach (SimMemInj.inj (SimMemInjInv.minj sm0))
                        (SimMemInj.src (SimMemInjInv.minj sm0))).
          ss. ii. eapply H0.
          exploit INVRANGETGT; eauto. i. des. eapply H1. }
        { ss. }
      * etrans; eauto.
        unfold SimMemInj.tgt_private, SimMemInj.valid_blocks in *. ss.
        ii. des. split; auto. eapply Mem.store_valid_block_1; eauto.
      * rpapply TGTLE. eapply Mem.nextblock_store; eauto.
    + ii. exploit SATTGT; eauto. i. inv H. econs; ss.
      * i. exploit PERMISSIONS; eauto. i.
        eapply Mem.store_valid_access_1; eauto.
      * i. exploit LOADVALS; eauto. i. des. destruct (peq blk blk0).
        { clarify. destruct (zeq ind ind0).
          - clarify. exists (sum (Int.repr ind0)).
            esplits; eauto. erewrite Mem.load_store_same; eauto. ss.
          - exists i. erewrite Mem.load_store_other; eauto.
            right. clear - n. ss. omega. }
        { exists i. erewrite Mem.load_store_other; eauto. }
Qed.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (MutrecAspec.module).
Let md_tgt: Mod.t := (ClightC.module2 prog).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimMemInjInvC.mk symbol_memoized md_src md_tgt) sm_link.

Inductive match_states_internal: nat -> MutrecAspec.state -> Clight.state -> Prop :=
| match_callstate_nonzero
    idx i m_src m_tgt
    fptr
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f))
    (IDX: (idx > 3)%nat)
  :
    match_states_internal idx (Callstate i m_src) (Clight.Callstate fptr (Tfunction
                                                                            (Tcons tint Tnil) tint cc_default)
                                                                    [Vint i] Kstop m_tgt)
| match_returnstate
    idx i m_src m_tgt
  :
    match_states_internal idx (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt)
.



Inductive match_states
          (idx: nat) (st_src0: MutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal idx st_src0 st_tgt0)
    (MCOMPATSRC: (get_mem st_src0) = sm0.(SimMem.src))
    (MCOMPATTGT: (ClightC.get_mem st_tgt0) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
.

Lemma g_blk_exists
  :
    exists g_blk,
      (<<FINDG: Genv.find_symbol
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_id = Some g_blk>>)
      /\
      (<<FINDG: Genv.find_funct_ptr
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_blk = None>>)
      /\
      (<<FINDG: exists skd, Genv.find_funct_ptr skenv_link g_blk = Some skd /\
                            Some (signature_of_type (Tcons tint Tnil) tint cc_default) = Sk.get_csig skd>>)
.
Proof.
  exploit (prog_defmap_norepet prog g_id); eauto.
  { unfold prog_defs_names. ss. repeat (econs; eauto).
    - ii; ss; des; ss.
    - ii; ss; des; ss. }
  { ss. eauto. }
  intro T; des.
  exploit SkEnv.project_impl_spec; eauto. intro PROJ.
  assert(PREC: SkEnv.genv_precise
                 (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                 prog).
  { eapply CSkEnv.project_revive_precise; ss; et. }
  inv PREC.
  exploit (P2GE g_id); eauto. i; des. des_ifs.
  rename b into g_blk.
  eexists. splits; et.
  { unfold Genv.find_funct_ptr. des_ifs. }
  { inv INCL.
    exploit (CSk.of_program_prog_defmap prog signature_of_function); et. rewrite T. intro S.

    remember ((prog_defmap (CSk.of_program signature_of_function prog)) ! g_id) as U in *.
    destruct U eqn:V; try (by ss). inv S. inv H1.

    exploit DEFS; eauto. i; des.
    assert(blk = g_blk).
    { inv PROJ. exploit SYMBKEEP; et.
      - instantiate (1:= g_id). unfold defs. des_sumbool. ss. et.
      - i. rewrite SYMB0 in *. clear - SYMB H. unfold SkEnv.revive in *. rewrite Genv_map_defs_symb in *. ss.
        rewrite SYMB in *. des. clarify.
    }
    clarify. inv MATCH.
    esplits; eauto.
    - unfold Genv.find_funct_ptr. rewrite DEF0. et.
    - ss. des_ifs. clear - H1. inv H1; ss.
  }
Qed.

Lemma match_states_lxsim
      idx st_src0 st_tgt0 sm0
      (SIMSK: SimSymb.sim_skenv
                sm0 (SimMemInjInvC.mk symbol_memoized md_src md_tgt)
                (SkEnv.project skenv_link (CSk.of_program signature_of_function prog))
                (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)))
      (MATCH: match_states idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsimL (md_src skenv_link) (md_tgt skenv_link)
                   (fun st => unit -> exists su m_init, SoundTop.sound_state su m_init st)
                   top3 (fun _ _ => SimMem.le)
                   (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until tge.
  pcofix CIH.
  i.
  pfold.
  generalize g_blk_exists; et. i; des.
  inv MATCH; subst. ss. inv MATCHST; ss; clarify.
  - (* call *)
    destruct (classic (i = Int.zero)).
    + (* zero *)
      clarify.
      econs 2. ii.
      econs 2.
      { split.
        - econs 2.
          + ss. econs 1.
          + econs 1.
          + ss.
        - eapply Ord.lift_idx_spec.
          instantiate (1:=3%nat). nia. }
      refl.

      left. pfold.
      econs 1. i; des.
      econs 2.

      * split; cycle 1.
        { apply Ord.lift_idx_spec.
          instantiate (1:=2%nat). nia. }

        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss; clarify.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
          - ss.
        }

        apply star_refl.
      * refl.
      * right. eapply CIH; eauto. econs; ss; eauto.
        replace (Int.repr 0) with (sum Int.zero).
        { econs; eauto. }
        { rewrite sum_recurse. des_ifs. }

    + (* nonzero *)

      destruct (Genv.find_symbol
                  (SkEnv.project skenv_link (CSk.of_program signature_of_function prog))
                  _memoized) eqn:BLK; cycle 1.
      { exfalso. clear - INCL BLK. inversion INCL; subst.
        exploit DEFS; eauto.
        - instantiate (2:=_memoized). ss.
        - i. des.
          exploit SkEnv.project_impl_spec. eapply INCL. i. inv H. ss.
          exploit SYMBKEEP. instantiate (1:=_memoized). ss. i.
          rr in H. rewrite H in *. clarify. }

      inv MWF. ss.

      assert (INVAR: SimMemInjInv.mem_inv_tgt sm0 b).
      { inv SIMSK. ss. inv INJECT.
        eapply INVCOMPAT; eauto. ss. }

      hexploit SATTGT; eauto. intros SAT0.
      exploit SAT0; eauto. i. inv H0. ss.
      hexploit LOADVALS; eauto. i. des.

      destruct (zeq (Int.intval i0) 0).
      {
        econs 2. ii.
        econs 2.
        { split.
          - econs 2; ss.
            + econs 2; eauto.
              clear - H.
              exploit Int.eq_false; eauto. i.
              unfold Int.eq in *. ss. des_ifs.
            + econs; eauto.
            + ss.
          - eapply Ord.lift_idx_spec. eauto. }
        refl.

        left. pfold.
        econs.
        i; des.
        econs 2; eauto.
        * esplits; cycle 1.
          { eapply Ord.lift_idx_spec. eauto. }

          eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
            econs; ss; eauto; try (by repeat (econs; ss; eauto)).
            unfold _x. unfold _t'1. rr. ii; ss. des; ss; clarify.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
            - repeat econs; et.
            - ss. rewrite Int.eq_false; ss.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto; swap 1 2.
            - econs.
              + ss. econs. econs; ss.
                * econs.
                  { eapply eval_Evar_global; ss.
                    instantiate (1:=b). eauto. }
                  { econs 2; ss. }
                * econs; ss.
                * ss.
              + econs 1; ss. psimpl.
                replace (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)))
                  with (4 * Int.intval i); cycle 1.
                { unfold Ptrofs.mul. ss.
                  destruct i. ss. unfold Ptrofs.of_ints. ss.
                  unfold Int.signed. ss. des_ifs; cycle 1;
                  unfold Int.half_modulus, Int.modulus, two_power_nat in *; ss;
                    unfold MAX in *; rewrite <- Zdiv2_div in *; ss.
                  { lia. }
                  repeat rewrite Ptrofs.unsigned_repr. auto.
                  all : unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_power;
                  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; des_ifs; ss; omega. } eauto. }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            ss. econs; eauto.
            - econs; ss.
              + econs; ss.
              + econs; ss.
              + ss.
            - ss. instantiate (1:=true).
              unfold Cop.bool_val. ss.
              unfold Int.eq. unfold Val.of_bool.
              destruct (zeq (Int.unsigned i0) (Int.unsigned (Int.repr 0))) eqn:EQ; ss. }
          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto; swap 1 2.
            - econs.
              + eapply eval_Evar_global; ss. et.
              + econs 2; et.
            - unfold Cop.classify_fun. ss.
            - repeat econs; ss; et.
          }

          eapply star_refl.

        * refl.

        * left. pfold. econs 3; et.
          { econs; eauto. }
          { econs. econs; eauto. }
          ii; des.
          inv ATSRC. ss; clarify.

          unfold Clight.fundef in *.
          assert(g_fptr = g_blk).
          { unfold SkEnv.revive in FINDG. rewrite Genv_map_defs_symb in *. clarify. }
          clarify.
          eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _).
          exists sm0.
          esplits; ss; eauto.
          { econs; ss; eauto.
            instantiate (1:=Vptr g_blk Ptrofs.zero).
            inv SIMSK. inv SIMSKENV. inv INJECT. ss.
            econs. eapply DOMAIN; eauto.
            exploit Genv.genv_symb_range. unfold Genv.find_symbol in *. eauto.
            i. ss. ii.
            exploit INVCOMPAT; eauto. i. rewrite <- H1 in H0. ss.
            rewrite Ptrofs.add_zero_l. ss. }
          { refl. }
          { econs; eauto. }
          i. inv AFTERSRC. inv SIMRETV; ss; clarify.

          hexploit Mem.valid_access_store.
          { instantiate (4:=sm_ret.(SimMemInjInv.minj).(SimMemInj.tgt)).
            inv MWF. inv WF. exploit SATTGT0; eauto.
            - inv MLE. erewrite <- MINVEQTGT. eauto.
            - i. inv H0. hexploit PERMISSIONS0; eauto. ss.
              esplits; eauto. }
          intros [m_tgt STR].

          exploit SimMemInjInvC.unlift_wf; try apply MLE; eauto.
          { econs; eauto. } intros MLE1.
          exploit memoized_inv_store_le; eauto.
          i. des.

          esplits.
          { econs; eauto. }
          { apply MLE0. }

          left. pfold. econs; eauto. i; des. econs 2; eauto.
          {
            esplits; eauto; cycle 1.
            { instantiate (1:= (Ord.lift_idx lt_wf 14%nat)). eapply Ord.lift_idx_spec; et. }

            eapply plus_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
            }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
            }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto. econs; eauto.
              - econs; eauto. ss.
              - econs; eauto. ss.
              - inv RETV. ss. unfold typify. des_ifs. }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
            }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
              - econs; eauto. econs; eauto.
                + econs; eauto.
                  * eapply eval_Evar_global; ss.
                    instantiate (1:=b). ss.
                  * ss. econs 2; eauto.
                + econs; eauto. ss.
                + econs; eauto.
              - econs; eauto. ss.
              - ss.
              - ss. psimpl. econs; ss; eauto.
                rpapply STR. f_equal.
                + unfold Ptrofs.mul. ss.
                  destruct i. ss. unfold Ptrofs.of_ints. ss.
                  unfold Int.signed. ss. des_ifs; cycle 1;
                  unfold Int.half_modulus, Int.modulus, two_power_nat in *; ss;
                    unfold MAX in *; rewrite <- Zdiv2_div in *; ss.
                  { lia. }
                  repeat rewrite Ptrofs.unsigned_repr. auto.
                  all : unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_power;
                    unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; des_ifs; ss; omega.
                + f_equal.
                  rewrite Int.repr_unsigned.
                  rewrite sum_recurse with (i := i). des_ifs.
                  rewrite Z.eqb_eq in Heq.
                  exploit Int.eq_spec. instantiate (1:=i). instantiate (1:=Int.zero).
                  unfold Int.eq. unfold Int.unsigned. rewrite Heq. des_ifs. i. subst i.
                  rewrite Int.sub_zero_r. rewrite sum_recurse. des_ifs. }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
            }

            eapply star_left with (t1 := E0) (t2 := E0); ss.
            { econs; eauto.
              { eapply modsem2_determinate; eauto. }
              econs; eauto.
              - econs; eauto. ss.
              - econs; eauto.
              - econs; eauto. }

            eapply star_refl.
          }
          { refl. }

          right. eapply CIH.
          { eapply SimMemInjInvC.sim_skenv_inj_lepriv; cycle 1; eauto.
            etrans; eauto.
            { exploit (SimMemLift.lift_priv sm0); eauto. ss. }
            etrans; eauto; cycle 1.
            { hexploit SimMem.pub_priv; try apply MLE0. eauto. }
            etrans; eauto.
            { hexploit SimMem.pub_priv; try apply MLE; eauto. }
            hexploit SimMemLift.unlift_priv; revgoals.
            { intro T. ss. eauto. }
            { eauto. }
            { eauto. }
            { exploit (SimMemLift.lift_priv sm0); eauto. ss. }
            { econs; eauto. } }
          { econs; ss.
            - replace (Int.add (sum (Int.sub i Int.one)) i) with (sum i); cycle 1.
              { rewrite sum_recurse with (i := i). des_ifs.
                rewrite Z.eqb_eq in Heq.
                exploit Int.eq_spec. instantiate (1:=i). instantiate (1:=Int.zero).
                unfold Int.eq. unfold Int.unsigned. rewrite Heq. des_ifs. i. subst i.
                rewrite Int.sub_zero_r. rewrite sum_recurse. des_ifs. }

              econs 2.
          }
      }

      { hexploit VAL; eauto. i. des. clarify.

        econs 2. ii.
        econs 2.
        { split.
          - econs 2; ss.
            + econs; eauto.
            + econs; eauto.
            + ss.
          - eapply Ord.lift_idx_spec. eauto. }
        refl.

        left. pfold.
        econs.
        i; des.
        econs 2; eauto.
        * esplits; cycle 1.
          { eapply Ord.lift_idx_spec. eauto. }

          eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
            econs; ss; eauto; try (by repeat (econs; ss; eauto)).
            unfold _x. unfold _t'1. rr. ii; ss. des; ss; clarify.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
            - repeat econs; et.
            - ss. rewrite Int.eq_false; ss.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto; swap 1 2.
            - econs.
              + ss. econs. econs; ss.
                * econs.
                  { eapply eval_Evar_global; ss.
                    instantiate (1:=b). ss. }
                  { econs 2; ss. }
                * econs; ss.
                * ss.
              + econs 1; ss. psimpl.
                replace (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)))
                  with (4 * Int.intval i); cycle 1.
                { unfold Ptrofs.mul. ss.
                  destruct i. ss. unfold Ptrofs.of_ints. ss.
                  unfold Int.signed. ss. des_ifs; cycle 1;
                  unfold Int.half_modulus, Int.modulus, two_power_nat in *; ss;
                    unfold MAX in *; rewrite <- Zdiv2_div in *; ss.
                  { lia. }
                  repeat rewrite Ptrofs.unsigned_repr. auto.
                  all : unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_power;
                  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; des_ifs; ss; omega. } eauto. }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            ss. econs; eauto.
            - econs; ss.
              + econs; ss.
              + econs; ss.
              + ss.
            - ss. instantiate (1:=false).
              unfold Cop.bool_val. ss.
              unfold Int.eq. unfold Val.of_bool.
              destruct (zeq (Int.unsigned (sum (Int.repr (Int.intval i))))
                            (Int.unsigned (Int.repr 0))) eqn:EQ; ss. }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
            - econs; ss.
            - econs.
            - ss. }

          apply star_refl.

        * refl.

        * right. eapply CIH; eauto.
          { econs; eauto.
            - ss. replace (Int.repr (Int.intval i)) with i.
              + econs; eauto.
              + symmetry. eapply Int.eqm_repr_eq.
                eapply Int.eqm_refl2. ss.
            - econs; eauto. }
      }

  - (* return *)
    econs 4; ss; eauto.
    + refl.
    + econs; ss; eauto.
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

  - i. des. inv SAFESRC.
    esplits; eauto.
    + refl.
    + econs; eauto.
    + instantiate (1:= (Ord.lift_idx lt_wf 15%nat)).
      inv INITTGT. inv TYP. ss.
      assert (FD: fd = func_f).
      { destruct args_src, args_tgt; ss. clarify.
        inv SIMARGS; ss. clarify. inv VALS. inv H1. inv H3. inv FPTR. ss.
        des_ifs.
        inv SIMSKENV. ss. inv SIMSKE. ss. inv INJECT. ss.
        exploit IMAGE; eauto.
        { exploit Genv.genv_symb_range.
          unfold Genv.find_symbol in SYMB. eauto. i. ss. eauto. }
        ii. des. subst. clarify.

        rewrite Genv.find_funct_ptr_iff in FINDF.
        unfold Genv.find_def in FINDF. ss.
        do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *.
        des_ifs.
        destruct (Genv.invert_symbol
                    (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) b2) eqn:SKENVSYMB; ss.
        unfold o_bind in FINDF. ss.
        exploit Genv.find_invert_symbol. eauto. i.
        rewrite H in *. clarify.
        destruct ((prog_defmap prog) ! f_id) eqn:DMAP; ss. clarify. } clarify.

      inv SIMARGS; ss. rewrite VS in *. inv VALS.
      inv H3. inv H1.
      unfold typify_list, zip, typify. ss. des_ifs; ss.

      eapply match_states_lxsim; ss.
      * inv SIMSKENV; eauto.
      * econs; eauto.
        { econs; eauto. omega. }

  - (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.

    esplits; eauto. econs; eauto.
    + instantiate (1:= func_f).
      ss.
      inv VALS; ss. inv H1. inv H0. inv FPTR0. ss.
      des_ifs.
      inv SIMSKENV. ss. inv SIMSKE. ss. inv INJECT. ss.
      exploit IMAGE; eauto.
      { exploit Genv.genv_symb_range.
        unfold Genv.find_symbol in SYMB. eauto. i. ss. eauto. }
      ii. des. subst. clarify.

      rewrite Genv.find_funct_ptr_iff in *.
      unfold Genv.find_def in *; ss.
      do 2 rewrite MapsC.PTree_filter_map_spec, o_bind_ignore in *.
      des_ifs.
      exploit Genv.find_invert_symbol. eauto. i.
      rewrite H0 in *. clarify.
    + econs; ss. erewrite <- inject_list_length; eauto.
      rewrite VS. auto.
Qed.


End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (MutrecAspec.module) (ClightC.module2 prog) (SimMemInjInvC.mk symbol_memoized (MutrecAspec.module) (ClightC.module2 prog)))
.
Proof.
  econs; ss.
  - econs; ss.
    + i. inv SS. esplits; ss; eauto.
      * econs; ss.
        ii. des. econs.
        { ii. ss. des. clarify. econs; ss.
          - ii. eapply PERM; eauto. unfold MAX in *. lia.
          - eapply Z.divide_factor_l. }
        { ss. i. clarify. erewrite INIT; ss; eauto.
          - esplits; eauto. i. rewrite sum_recurse. des_ifs.
          - lia.
          - unfold MAX. lia.
          - eapply Z.divide_factor_l. }
      * ii. des; clarify.
    + ii. destruct H. eapply in_prog_defmap in PROG.
      ss. unfold update_snd in PROG. ss.
      des; clarify; inv DROP; ss.
      des; clarify.
  - ii. ss.
    inv SIMSKENVLINK. inv SIMSKENV.
    eapply sim_modsem; eauto.
Qed.
