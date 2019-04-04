Require Import FSets.
Require Import CoqlibC Errors Ordered Maps IntegersC Floats.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Registers Op RTLC.
Require Import ValueDomain ValueAnalysisC NeedDomain NeedOp Inlining.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export Inliningproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.
Local Existing Instance Val.mi_normal.


(* Require Import FSets. *)
(* Require Import CoqlibC Maps Errors Integers Floats Lattice Kildall. *)
(* Require Import AST Linking. *)
(* Require Import ValuesC Memory Globalenvs Events Smallstep. *)
(* Require Import Registers Op RTLC. *)
(* Require Import ValueDomain ValueAnalysisC NeedDomain NeedOp Inlining. *)
(* Require Import sflib. *)
(* (** newly added **) *)
(* Require Export Inliningproof. *)
(* Require Import Simulation. *)
(* Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem. *)
(* Require SimMemInjC. *)
(* Require SoundTop. *)

Section SIMMODSEM.
  
Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Variables prog tprog: program.
Let md_src: Mod.t := (RTLC.module prog).
Let md_tgt: Mod.t := (RTLC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link_src md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link_tgt md_tgt.(Mod.sk)).
Hypothesis (WFSRC: SkEnv.wf skenv_link_src).
Hypothesis (WFTGT: SkEnv.wf skenv_link_tgt).
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt md_tgt.(Mod.sk)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src.(Mod.modsem) skenv_link_src) (md_tgt.(Mod.modsem) skenv_link_tgt) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Inliningproof.match_states prog skenv_link_src skenv_link_tgt ge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (MCOMPATIDX: idx = Inliningproof.measure st_src0)
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src md_src.(Mod.sk)) (SkEnv.project skenv_link_tgt md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - eapply Nat.lt_wf_0.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. exists sm_arg.
    esplits; eauto.
    { refl. }
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.
        exploit (Genv.find_funct_match_genv SIMGE); eauto. intro FINDFTGT; des. ss.
        assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link_src)).
        {
          inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss. 
          econs; eauto.
          + ii. ss. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
        }
        hexploit fsim_external_inject_eq; try apply FINDF0; et. i; clarify.
        rpapply match_call_states; ss; eauto.
        { i. inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss. 
          econs; eauto.
          - eapply SimMemInjC.sim_skenv_symbols_inject; eauto.
          - etrans; try apply MWF. ss.
        }
        { inv TYP. eapply inject_list_typify_list; try apply VALS; eauto. } 
        { apply MWF. }
        assert (fn_sig fd = fn_sig fd0).
        { unfold transf_function in *. unfold Errors.bind in *. des_ifs. }
        f_equal; eauto. f_equal; rewrite H; eauto.
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR.
    unfold Errors.bind in *. unfold transf_function in *. des_ifs. inv TYP.
    esplits; eauto. econs; eauto.
    + folder. ss. rewrite <- FPTR. eauto.
    + econs; eauto.
      erewrite <- inject_list_length; eauto.
    + erewrite <- inject_list_length; eauto.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss; cycle 1.
    { fold ge in EXTERNAL. clarify. }
    folder.
    inv MCOMPAT; ss. clear_tac.
    exploit (fsim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT.
    esplits; eauto.
    + econs; eauto.
      * des. clarify. esplits; eauto.
        (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *)

        (* Arguments sim_internal_funct_inject [_]. *)
        (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *)
        (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *)
        (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *)
        (* { inv SIMSKENV. ss. } *)

        (***************** TODO: Add as a lemma in GlobalenvsC. *******************)
        inv SIMSKENV. ss.
        assert(fptr_arg = tfptr).
        { eapply fsim_external_inject_eq; try apply SIG; et. Undo 1.
          inv FPTR; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
          inv SIMSKE. ss. inv INJECT; ss.
          exploit (DOMAIN b1); eauto.
          { eapply Genv.genv_defs_range; et. }
          i; clarify.
        }
        clarify.
        eapply SimSymb.simskenv_func_fsim; eauto; ss.
        (* { destruct tfptr; ss. des_ifs. econs; eauto; cycle 1. *)
        (*   { psimpl. instantiate (1:= 0). ss. } *)
        (*   inv H. inv INJECT. eapply DOMAIN; eauto. *)
        (*   { apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *. eapply Genv.genv_defs_range; et. } *)
        (* } *)
    + ss.
    + reflexivity.
  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv AFTERSRC.
    inv SIMRET. ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss; cycle 1.
    { inv HISTORY. inv CALLTGT. }
    inv HISTORY. ss. clear_tac.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      inv MLE0; ss.
      inv MCOMPAT. clear_tac.
      rpapply match_return_states; ss; eauto; ss.
      (* { clear - MWF. inv MWF. ii. apply TGTEXT in H. rr in H. des. ss. } *)
      { eapply match_stacks_le; eauto. eapply match_stacks_bound; cycle 1.
        { eapply Mem.unchanged_on_nextblock; eauto. }
        eapply match_stacks_extcall; try eapply MS; eauto.
        - eapply SkEnv.senv_genv_compat; eauto.
        - eapply SkEnv.senv_genv_compat; eauto.
        - ii. eapply MAXSRC; eauto.
        - ii. eapply MAXTGT; eauto.
        - eapply Mem.unchanged_on_implies; try eassumption. ii. rr. esplits; eauto.
        - eapply SimMemInj.inject_separated_frozen; et.
        - refl.
      }
      { eapply inject_typify; eauto. }
      { eapply MWFAFTR. }
    + refl.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss; cycle 1.
    { inv MS. clarify. }
    inv MS; cycle 1.
    { inv MS0; clarify. }
    inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto. refl.
  - (* step *)
    left; i.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    esplits; eauto.
    { apply modsem_receptive; et. }
    inv MATCH.
    ii. hexploit (@step_simulation prog _ skenv_link_src skenv_link_tgt ge tge); eauto.
    { eapply SkEnv.senv_genv_compat; eauto. }
    { eapply SkEnv.senv_genv_compat; eauto. }
    { assert (SkEnv.genv_precise ge prog).
      { eapply SkEnv.project_revive_precise; et. eapply SkEnv.project_impl_spec; et. }
      inv H. econs; ii.
      - exploit P2GE; eauto. i. inv H0. des. exists x. split; eauto. des_ifs. ii.
        ss. bsimpl. admit "ez - remove redundancy: AST.is_external_ef, ASTC.is_external_ef".
      - des. exploit GE2P; eauto. i; des. determ_tac Genv.genv_vars_inj.
    }
    i; des.
    + esplits; eauto.
      * left. eapply spread_dplus; eauto. eapply modsem_determinate; eauto.
      * econs; ss.
        { inv H0; ss; inv MCOMPAT; ss. }
        { inv H0; ss; inv MCOMPAT; ss. }
    + esplits; eauto.
      * right. subst tr. split. econs. eauto.
      * assert(MCOMPAT: get_mem st_src1 = SimMem.src sm1 /\ get_mem st_tgt0 = SimMem.tgt sm1).
        { inv H1; inv MCOMPAT; ss. }
        des. econs; eauto; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.




Section SIMMOD.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (RTLC.module prog) (RTLC.module tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy".
  - ii. eapply sim_modsem; eauto.
Qed.

End SIMMOD.

