Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSem.
Require SoundTop.
Require SimMemExtSep.
Require Import Clightdefs.
Require Import CtypesC.
Require Import Any.
Require Import UnionFindSource UnionFindTarget.

Set Implicit Arguments.







Section SMO.

  Record t: Type :=
    mk {
      sm :> SimMem.t;
      oh_src: Any;
      oh_tgt: Any;
    }
  .

  Set Printing Universes.

  Inductive wf (smo: t): Prop :=
  | wf_intro
      (MWF: SimMem.wf smo)
      (map: UnionFindSource.owned_heap)
      (OHSRC: smo.(oh_src) = upcast map)
      (OHTGT: smo.(oh_tgt) = upcast tt)
      (SOME: forall
          k blk rk
          (SOME: map k = Some (blk, rk))
        ,
          (<<VLSRC: Mem.valid_block smo.(SimMem.src) k>>) /\
          (<<PM: (brange k (-8)%Z 12%Z) <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_src)>>) /\
          (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint64 k (-8)%Z Freeable>>) /\
          (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint32 k 0%Z Freeable>>) /\
          (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint64 k 4%Z Freeable>>) /\
          (<<LDTGT: Mem.load Mint64 smo.(SimMem.tgt) k (-8)%Z = Some (Vptrofs (Ptrofs.repr 12%Z))>>) /\
          (<<LDTGT: Mem.load Mint32 smo.(SimMem.tgt) k 0%Z = Some (Vint rk)>>) /\
          (<<LDTGT: Mem.load Mint32 smo.(SimMem.tgt) k 4%Z = Some (Vptr blk Ptrofs.zero)>>)
      )
  .

  Local Obligation Tactic := try (by ii; des; ss).

The term "t" has type "Type@{max(t.u0+1,t.u1+1,SimMem.class.u0)}" while it is expected to have type
 "Type@{SimMemOh.class.u0}" (universe inconsistency: Cannot enforce t.u0 < SimMemOh.class.u0 because
SimMemOh.class.u0 <= upcast.u2 = t.u0).

  Program Instance SimMemOh: (SimMemOh.class) :=
    {|
      SimMemOh.t := t;
      SimMemOh.sm := sm;
      SimMemOh.oh_src := oh_src;
      SimMemOh.oh_tgt := oh_tgt;
      SimMemOh.wf := wf;
      SimMemOh.le := SimMem.le;
      SimMemOh.lepriv := SimMem.lepriv;
      SimMemOh.midx := Some "OHAlloc";
      SimMemOh.set_sm := fun smo sm => mk sm smo.(oh_src) smo.(oh_tgt);
    |}
  .
  Next Obligation.
    ii. eapply PR.
  Qed.
  Next Obligation.
    ii. inv WF.
    econs; ss; et.
    ii. exploit SOME; et. i; des. esplits; ss; et.
    - eapply Mem_unchanged_noperm; eauto.
    - eapply Mem.valid_block_unchanged_on; et.
    - eapply Mem_valid_access_unchanged_on; et.
      eapply Mem.unchanged_on_implies; et; ss. ii.
      exploit PMTGT; et.
    - eapply Mem.load_unchanged_on; et. ii. ss. eapply PM; et.
    - ii.
      destruct is_raw; ss.
      exploit NEW; eauto. i; des. esplits; eauto.
      + eapply Mem_valid_access_unchanged_on; et.
        eapply Mem.unchanged_on_implies; et; ss. ii.
        exploit PMTGT; et.
      + eapply Mem.load_unchanged_on; et. ii. ss. eapply PMNEW; et.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.









Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (UnionFindSource.module).
Let md_tgt: Mod.t := (UnionFindTarget.module).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Inductive match_states
          (idx: nat) (st_src0: SIR.state owned_heap) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (* (MATCHST: match_states_internal idx st_src0 st_tgt0) *)
    (MCOMPATSRC: (SIR.m st_src0) = sm0.(SimMem.src))
    (MCOMPATTGT: (ClightC.get_mem st_tgt0) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
.

Lemma match_states_lxsim
      idx st_src0 st_tgt0 sm0
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
  inv MATCH; subst. ss.
  - (* call *)
    destruct (classic (i = Int.zero)).
    + (* zero *)
      clarify.
      econs 2. ii.
      econs 2; et.
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
      econs 2; et.

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
        econs 2; et.
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
          { rr. esplits; et. econs; eauto. }
          ii; des.
          inv ATSRC. ss; clarify.

          unfold Clight.fundef in *.
          assert(g_fptr = g_blk).
          { unfold SkEnv.revive in FINDG. rewrite Genv_map_defs_symb in *. clarify. }
          clarify.
          eexists tt, (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _).
          exists sm0.
          esplits; ss; eauto.
          { rr. esplits; ss; et. econs; ss; eauto.
            instantiate (1:=Vptr g_blk Ptrofs.zero).
            inv SIMSK. inv SIMSKENV. inv INJECT. ss.
            econs. eapply DOMAIN; eauto.
            exploit Genv.genv_symb_range. unfold Genv.find_symbol in *. eauto.
            i. ss. ii.
            exploit INVCOMPAT; eauto. i. rewrite <- H1 in H0. ss.
            rewrite Ptrofs.add_zero_l. ss. }
          { refl. }
          { econs; eauto. }
          i. inv AFTERSRC. rr in SIMRETV; des. inv SIMRETV0; ss; clarify.

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
          { et. }

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
        econs 2; et.
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
    + rr. esplits; ss; et. econs; ss; eauto.
Unshelve.
  all: ss.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply sim_mod_sem_implies.
  eapply ModSemPair.simL_intro with (has_footprint := top3) (mle_excl := fun _ _ => SimMem.le); try (by ss).
  { i. eapply SoundTop.sound_state_local_preservation. }
  { i. eapply Preservation.local_preservation_noguarantee_weak; eauto. eapply SoundTop.sound_state_local_preservation. }
  { ii; ss. r. etrans; eauto. }
  { ii. eauto. }
  { esplits; et. }
  i. ss. esplits; eauto.

  - i. des. inv SAFESRC.
    esplits; eauto.
    + refl.
    + eapply SimMemInjInvC.unch_true; et.
    + econs; eauto.
    + instantiate (1:= (Ord.lift_idx lt_wf 15%nat)).
      inv INITTGT. inv TYP. ss.
      assert (FD: fd = func_f).
      { destruct args_src, args_tgt; ss. clarify.
        rr in SIMARGS; des. inv SIMARGS0; ss. clarify. inv VALS. inv H1. inv H3. inv FPTR. ss.
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

      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. inv VALS.
      inv H3. inv H1.
      unfold typify_list, zip, typify. ss. des_ifs; ss.

      eapply match_states_lxsim; ss.
      * inv SIMSKENV; eauto.
      * econs; eauto.
        { econs; eauto. omega. }

  - (* init progress *)
    i.
    des. inv SAFESRC.
    rr in SIMARGS; des. inv SIMARGS0; ss. clarify.

    esplits; eauto. econs; eauto.
    + instantiate (1:= func_f).
      ss.
      inv VALS; ss. inv H1. inv H3. inv FPTR0. ss.
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
      rewrite H in *. clarify.
    + econs; ss. erewrite <- inject_list_length; eauto.
      auto.
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
    eexists. eapply sim_modsem; eauto.
Qed.
