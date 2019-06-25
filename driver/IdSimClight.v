Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Cop Ctypes ClightC.
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

Require Import MatchSimModSem.
Require Import ClightStepInj ClightStepExt.
Require Import IdSimExtra.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Lemma val_casted_inject val0 val1 j ty
      (VAL: Val.inject j val0 val1)
      (CAST: val_casted val0 ty)
  :
    val_casted val1 ty.
Proof.
  inv CAST; inv VAL; clarify; try econs; eauto.
Qed.

Require Import CtypingC.
Require Import CopC.

Lemma typecheck_inject vals0 vals1 j ty
      (VALS: Val.inject_list j vals0 vals1)
      (TYP: typecheck vals0 ty)
  :
    typecheck vals1 ty.
Proof.
  inv TYP. econs; eauto. clear - VALS TYP0.
  revert vals1 VALS TYP0. generalize (typelist_to_listtype ty).
  clear ty. induction vals0; ss.
  - i. inv VALS. inv TYP0. econs.
  - i. inv VALS. inv TYP0. econs.
    + eapply val_casted_inject; eauto.
    + eapply IHvals0; eauto.
Qed.

Lemma wt_retval_inject j v_src v_tgt ty
      (INJ: Val.inject j v_src v_tgt)
      (TYP: wt_retval v_tgt ty)
  :
    wt_retval v_src ty.
Proof.
  inv TYP; inv WTV; inv INJ; clarify; try by repeat (econs; eauto).
  exploit NVOID; eauto. clarify.
Qed.

Lemma typify_c_inject j retv_src retv_tgt tres tv_src
      (TYP: typify_c retv_src tres tv_src)
      (INJ: Val.inject j retv_src retv_tgt)
  :
    exists tv_tgt,
      (<<TYP: typify_c retv_tgt tres tv_tgt>>) /\
      (<<INJ: Val.inject j tv_src tv_tgt>>).
Proof.
  inv TYP.
  - destruct (classic (wt_retval retv_tgt tres)).
    + esplits; eauto. econs; eauto.
    + exists Vundef. esplits; eauto.
      * econs 2. eauto.
      * assert (tv_src = Vundef); clarify; eauto.
        inv INJ; inv WT; inv WTV; clarify;
          exfalso; eapply H; econs; clarify; try (econs; eauto).
        exploit NVOID; eauto. clarify.
  - exists Vundef. esplits; eauto.
    econs 2. ii. exploit wt_retval_inject; eauto.
Qed.

Lemma vals_casted_inject j vals_src vals_tgt tys
      (VALS: Val.inject_list j vals_src vals_tgt)
      (TYP: Forall2 val_casted vals_src tys)
  :
    Forall2 val_casted vals_tgt tys.
Proof.
  ginduction vals_src; i.
  - inv VALS. inv TYP. econs.
  - inv VALS. inv TYP. econs; eauto.
    eapply val_casted_inject; eauto.
Qed.

Definition cgenv skenv_link clight :=
  Build_genv
    (SkEnv.revive (SkEnv.project skenv_link (CtypesC.CSk.of_program signature_of_function clight)) clight)
    (prog_comp_env clight).

Lemma clight_id
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  rewrite SIMSKENVLINK in *.
  eapply match_states_sim; ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - instantiate (1:= fun sm_arg _ st_src st_tgt sm0 =>
                       (<<EQ: st_src = st_tgt>>) /\
                       (<<MWF: sm0.(SimMemId.src) = sm0.(SimMemId.tgt)>>) /\
                       (<<STMWF: st_src.(ClightC.get_mem) =
                                 sm0.(SimMemId.src)>>)).
    ss. i.
    destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
    clear SAFESRC. dup INITTGT. inv INITTGT. ss.
    eexists. eexists (SimMemId.mk tgt tgt). esplits; eauto; ss.
  - ii. destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
  - ii. ss. des. clarify.
  - i. ss. des. clarify. esplits; eauto.
    + inv CALLSRC. ss. clarify.
    + instantiate (1:=top4). ss.
  - i. clear HISTORY. ss. destruct sm_ret, retv_src, retv_tgt.
    inv SIMRET. des. ss. clarify. eexists (SimMemId.mk _ _). esplits; eauto.
    inv AFTERSRC. ss.
  - i. ss. des. destruct sm0. ss. clarify.
    eexists (SimMemId.mk (get_mem st_tgt0) (get_mem st_tgt0)).
    esplits; eauto.
    inv FINALSRC. ss.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1.
      eexists (SimMemId.mk (get_mem st_tgt1) (get_mem st_tgt1)).
      esplits; eauto.
      left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
Qed.

Lemma clight_ext_unreach
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  destruct SIMSKENVLINK.
  exploit clight_unreach_local_preservation. i. des.
  eapply match_states_sim with (match_states := match_states_ext_clight); ss.
  - apply unit_ord_wf.
  - eauto.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H.
    inv SIMARGS. ss.
    assert (FD: fd = fd0).
    { ss. inv FPTR.
      - rewrite H1 in *. clarify.
      - rewrite <- H0 in *. clarify. } clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; eauto.
      * rewrite MEMSRC. rewrite MEMTGT. eauto.
      * inv TYP. inv TYP0. eapply lessdef_list_typify_list; et.
      * econs; et.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS. ss. inv FPTR.
      * rewrite H1 in *. eauto.
      * rewrite <- H0 in *. clarify.
    + inv SIMARGS. ss. inv TYP. econs; eauto.
      erewrite <- lessdef_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss.
    esplits; eauto.
    + des. inv INJ; ss; clarify.
      econs; ss; eauto.
    + econs; ss.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists sm_ret.
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. rewrite MEMSRC. rewrite MEMTGT.
      econs; eauto.
      eapply lessdef_typify; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.

  - left. i. split.
    { eapply modsem2_receptive. }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto.
    left. apply plus_one. econs; ss; eauto.
    eapply modsem2_determinate.
Qed.


Lemma clight_ext_top
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  destruct SIMSKENVLINK.
  eapply match_states_sim with (match_states := match_states_ext_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - i. ss.
    inv INITTGT. inv SAFESRC. inv H.
    inv SIMARGS. ss.
    assert (FD: fd = fd0).
    { ss. inv FPTR.
      - rewrite H1 in *. clarify.
      - rewrite <- H0 in *. clarify. } clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; eauto.
      * rewrite MEMSRC. rewrite MEMTGT. eauto.
      * inv TYP. inv TYP0. eapply lessdef_list_typify_list; eauto.
      * econs; eauto.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS. ss. inv FPTR.
      * rewrite H1 in *. eauto.
      * rewrite <- H0 in *. clarify.
    + inv SIMARGS. ss. inv TYP. econs; eauto.
      erewrite <- lessdef_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss.
    esplits; eauto.
    + des. inv INJ; ss; clarify.
      econs; ss; eauto.
    + econs; ss.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists sm_ret.
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. rewrite MEMSRC. rewrite MEMTGT.
      econs; eauto. eapply lessdef_typify; eauto.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.

  - left. i. split.
    { eapply modsem2_receptive. }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto.
    left. apply plus_one. econs; ss; eauto.
    eapply modsem2_determinate.
Qed.

Lemma clight_inj_drop_bot
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
      /\ (<<SSBOT: mp.(ModPair.ss) = bot1>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { econs; ss; i; clarify.
    inv WF. auto. }
  eapply match_states_sim with (match_states := match_states_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss. exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    inv INITTGT. inv SAFESRC. inv SIMARGS. inv H. ss.
    exploit match_globals_find_funct; eauto.
    i. clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + econs; eauto.
      { inv TYP. inv TYP0. eapply inject_list_typify_list; eauto. }
      econs.

  - i. ss. exploit SimSymbDrop_match_globals.
    { inv SIMSKENV. ss. eauto. } intros GEMATCH.
    des. inv SAFESRC. inv SIMARGS. esplits. econs; ss.
    + eapply match_globals_find_funct; eauto.
    + inv TYP. econs; eauto.
      erewrite <- inject_list_length; eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. inv SIMSKENV. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * eapply SimSymbDrop_find_None; eauto.
        ii. clarify. ss. des. clarify.
      * des. clear EXTERNAL.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv INJ. inv SIMSKELINK.
        exploit SIMDEF; eauto. i. des. clarify. des_ifs. esplits; eauto.
    + econs; ss.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInj.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. econs; eauto.
      { eapply inject_typify; et. }
      ss. eapply match_cont_incr; try eassumption.
      inv MLE. inv MLE0. etrans; eauto.
    +  refl.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.
    + refl.

  - left. i. split.
    + eapply modsem2_receptive.
    + ii. exploit clight_step_preserve_injection; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry2_inject. ss. }
      { inv SIMSKENV. ss. eapply SimSymbDrop_symbols_inject; eauto. }
      { inv SIMSKENV. ss. eapply SimSymbDrop_match_globals; eauto. }
      i. des. esplits; eauto.
      left. apply plus_one. econs; ss; eauto.
      eapply modsem2_determinate.
Qed.

Lemma clight_inj_drop
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  exploit clight_inj_drop_bot; eauto. i. des. eauto.
Qed.

Lemma clight_inj_id
      (clight: Clight.program)
      (WF: Sk.wf clight.(module2))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  apply sim_inj_drop_bot_id. apply clight_inj_drop_bot; auto.
Qed.
