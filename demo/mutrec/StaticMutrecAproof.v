Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import StaticMutrecA StaticMutrecAspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SoundTop.
Require SimMemInjInv.
Require Import Clightdefs.
Require Import CtypesC.

Set Implicit Arguments.

Print Instances SimMem.class.


Definition memoized_inv (chunk: memory_chunk) (ofs: Z) (v: option val): Prop :=
  forall
    ind
    (BOUND: 0 <= ind < 1000)
    (INT: chunk = Mint32)
    (INDEX: size_chunk Mint32 * ind = ofs),
  exists i,
    (<<VINT: v = Some (Vint i)>>) /\
    (<<VAL: forall (NZERO: i.(Int.intval) <> 0),
        (<<MEMO: i = sum (Int.repr ind)>>)>>).

Local Instance SimMemMemoized: SimMem.class := SimMemInjInv.SimMemInjInv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (StaticMutrecAspec.module).
Let md_tgt: Mod.t := (ClightC.module2 prog).
Hypothesis (INCL: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link md_src.(Mod.sk)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) symbol_memoized sm_link.


Inductive match_states_internal: StaticMutrecAspec.state -> Clight.state -> Prop :=
| match_callstate_nonzero
    i m_src m_tgt
    fptr
    (* targs tres cconv *)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f))
  :
    match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *)
                                                                        (Tcons tint Tnil) tint cc_default)
                                                                [Vint i] Kstop m_tgt)
| match_returnstate
    i m_src m_tgt
  :
    match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt)
.


(* Inductive match_states_internal: StaticMutrecAspec.state -> Clight.state -> Prop := *)
(* | match_callstate_nonzero_memoized *)
(*     i m_src m_tgt *)
(*     fptr blk memov *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*     (SYMB: Genv.find_symbol skenv_link _memoized = Some blk) *)
(*     (MEMOLD: Mem.loadv *)
(*                Mint64 m_tgt *)
(*                (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) = Some (Vint memov)) *)
(*     (MEMOIZED: memov = sum i) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_callstate_nonzero_nonmemoized *)
(*     i m_src m_tgt *)
(*     fptr blk memov *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*     (SYMB: Genv.find_symbol skenv_link _memoized = Some blk) *)
(*     (MEMOLD: Mem.loadv *)
(*                Mint64 m_tgt *)
(*                (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) = Some (Vint memov)) *)
(*     (NONMEMOIZED: memov.(Int.intval) < 0) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_returnstate *)
(*     i m_src m_tgt *)
(*   : *)
(*     match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt) *)
(* . *)

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: StaticMutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (IDX: (idx > 3)%nat)
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
                            signature_of_type (Tcons tint Tnil) tint cc_default = SkEnv.get_sig skd>>)
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
  (* exploit (@SkEnv.project_revive_precise _ _ skenv_link); eauto. *)
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
      sm_init idx st_src0 st_tgt0 sm0
      (SIMSK: SimSymb.sim_skenv
                sm0 symbol_memoized
                (SkEnv.project skenv_link (CSk.of_program signature_of_function prog))
                (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)))
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun (_: genv) st => exists su m_init, SoundTop.sound_state su m_init st)
                  sm_init (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until tge.
  pcofix CIH.
  i.
  pfold.
  generalize g_blk_exists; et. i; des.
  inv MATCH. ss. inv MATCHST; ss; clarify.
  - (* call *)
    destruct (classic (i = Int.zero)).
    + (* zero *)
      clarify.
      econs 2. i. esplits; cycle 3.
      { ii. esplits. econs; eauto. econs; ss; eauto.
        - econs.
        - econs; eauto. econs.
        - ii. ss. des; clarify.
        - econs. }
      { ii. inv H. inv H0. }
      { ii. inv H. inv H0. }
      econs 2.
      { split.
        - econs 2.
          + ss. econs 1.
          + econs 1.
          + ss.
        - admit "index". }
      left. pfold.
      econs 1. i; des.
      econs 2.

      (* econs 2; cycle 2. *)
      (* { admit "ez - spec is receptive". } *)
      (* { split; ii; rr in H; inv H; inv H0; ss. } *)
      (* i. ss. inv STEPSRC. *)
      (* esplits; eauto. *)

      * split; cycle 1.
        { admit "index". }

        (* left. *)
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
      (* * refl. *)
      * right. eapply CIH; eauto. econs; ss; eauto.
        replace (Int.repr 0) with (sum Int.zero).
        { econs; eauto. }
        { admit "". }

    + (* nonzero *)

      destruct (Genv.find_symbol
                  (SkEnv.project skenv_link (CSk.of_program signature_of_function prog))
                  _memoized) eqn:BLK; cycle 1.
      { exfalso. clear - INCL BLK. inv INCL.
        exploit DEFS; eauto.
        - instantiate (2:=_memoized). ss.
        - i. des. admit "genv". }

      inv MWF. ss.

      assert (INVAR: SimMemInjInv.mem_inv sm0 b).
      { inv SIMSK. ss. inv INJECT.
        eapply INVCOMPAT; eauto. ss. }

      hexploit SAT; eauto. intros [].
      exploit SAT0; eauto. i. des.
      destruct (zeq (Int.intval i0) 0).
      {

        econs 2. i. splits; cycle 3.
        { i. esplits. econs; ss; eauto.
          econs; ss; eauto.
          - econs.
          - econs; eauto. econs.
          - ii. ss. des; clarify.
          - econs. }
        { ii. inv H0. inv H1. }
        { ii. inv H0. inv H1. }
        econs 2.
        { split.
          - econs 2; ss.
            + econs 2; eauto.
              clear - H. admit "arithmetic".
            + econs; eauto.
            + ss.
          - admit "index". }

        left. pfold.
        econs.
        i; des.
        econs 2; eauto.
        * esplits; cycle 1.
          { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). admit "index". }

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
                { admit "arithmetic". } eauto. }

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
            - ss. instantiate (1:=true). admit "arithmetic". }

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
          (* eexists (SimMemInjInv.mk minj _ _ (SimMemInjInv.mem_inv sm_init)). *)
          esplits; ss; eauto.
          { econs; ss; eauto.
            instantiate (1:=Vptr g_blk Ptrofs.zero). admit "genv". }
          { eapply SimMemInjInv.SimMemInjInv_obligation_1. }
          { econs; eauto. }

          i. inv AFTERSRC. destruct retv_src, retv_tgt; ss. clarify. inv SIMRETV; ss; clarify.


          hexploit Mem.valid_access_store.
          { instantiate (1:=Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))).
            instantiate (1:=b).
            inv MWF. inv SAT1. eapply WRITABLE0.
            inv MLE0. ss. rewrite <- MINVEQ. auto. }
          instantiate (1:=Vint (Int.add (sum (Int.sub i Int.one)) i)).
          intros [m_tgt STR].

          exploit SimMemInjInv.SimMemInjInv_obligation_7.
          instantiate (1:=sm_ret). instantiate (1:=sm0). intros MLE1.

          eexists.
          exists (SimMemInjInv.update
                    (SimMemInjInv.unlift' sm0 sm_ret)
                    ((SimMemInjInv.unlift' sm0 sm_ret).(SimMemInjInv.minj).(SimMemInj.src))
                    m_tgt
                    ((SimMemInjInv.unlift' sm0 sm_ret).(SimMemInjInv.minj).(SimMemInj.inj))).

          esplits; eauto.
          { econs; eauto. }
          { eapply SimMemInjInv.SimMemInjInv_obligation_1; eauto.
            econs; ss; eauto. econs; ss; eauto.
            - refl.
            - eapply Mem.store_unchanged_on; eauto.
              ii. eapply TGTEXTGE in H1.
              inv SIMSK. ss. rewrite <- TGTGENB0 in *.
              eapply Genv.genv_symb_range in BLK. ss.
              clear - BLK H1. eapply Plt_strict. eapply Plt_Ple_trans; eauto.
            - eapply SimMemInj.frozen_refl.
            - ii. eapply Mem.perm_store_2; eauto. }

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
              - inv RETV. ss. unfold typify. des_ifs. ss. }

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
                    instantiate (1:=b). admit "genv".
                  * ss. econs 2; eauto.
                + econs; eauto. ss.
                + econs; eauto.
              - econs; eauto. ss.
              - ss.
              - ss. psimpl. econs; ss; eauto. }

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

          right. eapply CIH.
          { admit "sim_skenv_inj". }
          { econs; ss.
            - replace (Int.add (sum (Int.sub i Int.one)) i) with (sum i); cycle 1.
              { admit "arithmetic". }
              econs 2.
            - econs; ss.
              + admit "inject".
              + admit "invariant".
              + i. admit "".
              + admit "".
              + admit "".
              + admit "".
              + admit "".
            - admit "".
            - omega. }
      }

      { hexploit VAL; eauto. i. des. clarify.

        econs 2. i. splits; cycle 3.
        { i. esplits. econs; ss; eauto.
          econs; ss; eauto.
          - econs.
          - econs; eauto. econs.
          - ii. ss. des; clarify.
          - econs. }
        { ii. inv H0. inv H1. }
        { ii. inv H0. inv H1. }
        econs 2.
        { split.
          - econs 2; ss.
            + econs; eauto.
            + econs; eauto.
            + ss.
          - admit "index". }

        left. pfold.
        econs.
        i; des.
        econs 2; eauto.
        * esplits; cycle 1.
          { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). admit "index". }

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
                    instantiate (1:=b). admit "genv". }
                  { econs 2; ss. }
                * econs; ss.
                * ss.
              + econs 1; ss. psimpl.
                replace (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)))
                  with (4 * Int.intval i); cycle 1.
                { admit "arithmetic". } eauto. }

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
            - ss. instantiate (1:=false). admit "arithmetic". }

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

        * right. eapply CIH; eauto.
          { econs; eauto.
            - ss. replace (Int.repr (Int.intval i)) with i.
              + econs; eauto.
              + admit "arithmetic".
            - econs; eauto. }
      }

  - (* return *)
    econs 4; ss; eauto.
    econs; ss; eauto.
    Unshelve. all: admit "".
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { i. eapply SoundTop.sound_state_local_preservation. }
  i. ss. esplits; eauto.

  - i. des. inv SAFESRC.
    esplits; eauto.
    + eapply SimMemInjInv.SimMemInjInv_obligation_1.
    + econs; eauto.
    +
      instantiate (1:= (Ord.lift_idx lt_wf 15%nat)).
      inv INITTGT. inv TYP. ss.
      assert (FD: fd = func_f).
      { admit "genv". } clarify.

      inv SIMARGS. ss. rewrite VS in *. inv VALS.
      inv H2. inv H3. rewrite <- H1 in *.
      unfold typify_list, zip, typify. ss. des_ifs; ss.

      rewrite MEMSRC in *. rewrite MEMTGT in *.
      eapply match_states_lxsim; ss.
      * inv SIMSKENV; eauto.
      * econs; eauto.
        { econs; eauto. }
        { refl. }
        { omega. }

  - (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)

    (* exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. *)

    (* hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR. *)

    esplits; eauto. econs; eauto.
    + instantiate (1:= func_f).
      ss. admit "genv".
    + econs; ss. erewrite <- inject_list_length; eauto.
      rewrite VS. auto.
Qed.


End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (StaticMutrecAspec.module) (ClightC.module2 prog) symbol_memoized)
.
Proof.
  econs; ss.
  - econs; ss. i. inv SS. esplits; ss; eauto.
    + econs. admit "fill definition".
    + ii. des; clarify.
  - ii. ss.
    inv SIMSKENVLINK. inv SIMSKENV.
    eapply sim_modsem; eauto.
Qed.
