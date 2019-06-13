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
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SimMemId.
Require SoundTop.
Require Import Clightdefs.

Set Implicit Arguments.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (MutrecAspec.module prog).
Let md_tgt: Mod.t := (ClightC.module2 prog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog) prog.(prog_comp_env).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link.

Inductive match_states_internal: MutrecAspec.state -> Clight.state -> Prop :=
| match_callstate_nonzero
    i m_src m_tgt
    fptr
    (* targs tres cconv *)
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

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: MutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (IDX: (idx > 3)%nat)
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ => eq) eq tt) ge tge.
Proof.
  subst_locals. ss. ii.
  eapply SimSymbId.sim_skenv_revive; eauto.
  admit "ez - reflexivity".
Qed.

Lemma g_blk_exists
  :
    exists g_blk,
      <<FINDG: Genv.find_symbol
                 (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                 g_id = Some g_blk>>
.
Proof.
  admit "ez".
Qed.

Lemma match_states_lxsim
      sm_init idx st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun st => exists su m_init, SoundTop.sound_state su m_init st)
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
      econs 1. i; des.
      econs 1; cycle 2.
      { admit "ez - spec is receptive". }
      { split; ii; rr in H; inv H; inv H0; ss. }
      i. ss. inv STEPSRC.
      esplits; eauto.
      * left.
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
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
      * right. eapply CIH. econs; ss; eauto. econs; eauto.
    + (* nonzero *)
      econs.
      i; des.
      econs 2; eauto.
      * esplits; cycle 1.
        { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). lia. }

        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
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
            + eapply eval_Evar_global; ss. et.
            + econs 2; et.
          - unfold Cop.classify_fun. ss.
          - repeat econs; ss; et.
        }

        apply star_refl.
      * left. pfold. econs 3; et.
        { rr. esplits; eauto. ss. econs; et. ii. destruct i; ss. clarify. apply H. unfold Int.zero.
          Local Transparent Int.repr.
          unfold Int.repr.
          Local Opaque Int.repr.
          ss. apply eta; ss.
        }
        ii; des.
        inv ATSRC. ss; clarify.
        destruct sm0; ss. clarify.
        eexists (Args.mk _ _ _), (SimMemId.mk _ _).
        esplits; ss; eauto.
        { econs; ss; eauto.
  - (* return *)
    econs 4; ss; eauto.
Unshelve.
  all: ss.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { eapply SoundTop.sound_state_local_preservation. }
  i. ss. esplits; eauto; cycle 1.
  { (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.

    (* hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR. *)

    esplits; eauto. econs; eauto.
    + rewrite <- FPTR. eauto.
    + instantiate (1:= [Vint i]). rewrite VS in *. inv VALS. econs; ss.
      cbn. unfold typify. des_ifs; ss.
  }
  (* init bsim *)
  ii.
  destruct sm_arg; ss. clarify.
  clear MFUTURE.
  inv SIMARGS; ss. clarify.
  inv INITTGT.
  (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
  exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
  eexists. eexists (SimMemId.mk _ _).
  esplits; eauto.
  + eapply match_states_lxsim.
    econs; ss; eauto; cycle 1.
    { inv SAFESRC. ss. }

    inv SAFESRC. destruct args_src, args_tgt; ss. clarify.
    assert(tvs = [Vint i]).
    {
      unfold signature_of_function in TYP. ss.
      inv TYP. ss. cbn. unfold typify. des_ifs; ss.
    } clarify.
    econs; eauto.
Unshelve.
  all: try (ss; econs).
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := top4) (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct sm_arg; ss. clarify.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. eexists (SimMemInj.mk _ _ _ _ _ _ _).
    esplits; eauto.
    + econs; eauto with mem; ss.
      eapply SimMemInj.frozen_refl.
    + inv SAFESRC. destruct args_src, args_tgt; ss. clarify.
      econs; ss; eauto.
      inv VALS. inv H1. inv H3.
      assert(fd = func_f).
      {
        clear - FINDF.
        uge. des_ifs.
        unfold SkEnv.revive, SkEnv.project in Heq. ss.
        rewrite MapsC.PTree_filter_map_spec in *.
        unfold o_bind, o_join, o_map in Heq. des_ifs.
        clear - Heq2.
        unfold prog in *. unfold Clightdefs.mkprogram in *. ss.
        unfold prog_defmap in *. ss. unfold global_definitions in *.
        apply PTree_Properties.in_of_list in Heq2.
        ss. des; clarify.
      } clarify.
      assert(tvs = [Vint i]).
      {
        unfold signature_of_function in TYP. ss.
        inv TYP. ss. cbn. unfold typify. des_ifs; ss.
      } clarify.
      econs; eauto.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.

    (* exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder. *)
    hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR.

    (* exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder. *)
    (* inv TYP. *)
    esplits; eauto. econs; eauto.
    + rewrite <- FPTR. eauto.
    + instantiate (1:= [Vint i]). rewrite VS in *. inv VALS. inv H3. inv H2. econs; ss.
      cbn. unfold typify. des_ifs; ss.
  - (* call wf *)
    inv MATCH; ss.
  - (* call fsim *)
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    (* exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des. *)
    (* inv MATCH; ss. destruct sm0; ss. clarify. *)
    (* inv CALLSRC. inv MATCHST; ss. *)
    (* folder. *)
    (* (* inv MCOMPAT; ss. clear_tac. *) *)
    (* (* exploit (fsim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT. *) *)
    (* esplits; eauto. *)
    (* + econs; eauto. *)
    (*   * des. clarify. esplits; eauto. *)
    (*     (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *) *)

    (*     (* Arguments sim_internal_funct_inject [_]. *) *)
    (*     (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *) *)
    (*     (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *) *)
    (*     (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *) *)
    (*     (* { inv SIMSKENV. ss. } *) *)

    (*     (***************** TODO: Add as a lemma in GlobalenvsC. *******************) *)
    (*     inv SIMSKENV. *)
    (*     assert(fptr_arg = tv). *)
    (*     { eapply fsim_external_inject_eq; try apply SIG; et. Undo 1. *)
    (*       inv VAL; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *. *)
    (*       inv SIMSKE. ss. inv INJECT; ss. *)
    (*       exploit (DOMAIN b1); eauto. *)
    (*       { eapply Genv.genv_defs_range; et. } *)
    (*       i; clarify. *)
    (*     } *)
    (*     clarify. *)
    (* + ss. *)
    (* + reflexivity. *)
    admit "".

  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv AFTERSRC.
    inv SIMRET. ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    inv HISTORY. ss. clear_tac.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      inv MLE0; ss.
      (* inv MCOMPAT. clear_tac. *)
      inv RETV. unfold typify. des_ifs; ss.
      econs; eauto.
    + refl.

  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    (* inv MCONT_EXT. inv MCOMPAT; ss. *)
    clarify.
    eexists sm0. esplits; ss; eauto.
    + econs; eauto. ss.
    + refl.
  - left; i.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.

    esplits; eauto.
    { apply modsem1_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog skenv_link skenv_link); eauto; ss.
    i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem2_determinate; eauto.
    + econs; ss.
      * inv H0; ss; inv MCOMPAT; ss.
      * inv H0; ss; inv MCOMPAT; ss.

Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. esplits; eauto.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
