Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import CsemC ClightC.
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
Require Import ClightStep.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.



Lemma ccc_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
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
                       (<<STMWF: match st_src.(CsemC.get_mem) with
                                 | Some m => sm0.(SimMemId.src) = m
                                 | _ => True
                                 end>>)).
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
  - i. ss. des. destruct sm0. ss. clarify. eexists (SimMemId.mk tgt tgt).
    esplits; eauto.
    inv FINALSRC. ss.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1.
      exists (match st_tgt1.(CsemC.get_mem) with
              | Some m => SimMemId.mk m m
              | _ => SimMemId.mk tgt tgt
              end).
      esplits; eauto.
      * left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
      * des_ifs.
      * des_ifs.
Qed.

Lemma val_casted_injection val0 val1 j ty
      (VAL: Val.inject j val0 val1)
      (CAST: val_casted val0 ty)
  :
    val_casted val1 ty.
Proof.
  inv CAST; inv VAL; clarify; try econs; eauto.
Qed.

Require Import CtypingC.
Require Import CopC.

Lemma typecheck_injection vals0 vals1 j ty
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
    + eapply val_casted_injection; eauto.
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

Lemma typify_c_injection j retv_src retv_tgt tres tv_src
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

Definition cgenv skenv_link clight :=
  Build_genv
    (SkEnv.revive (SkEnv.project skenv_link (CtypesC.CSk.of_program signature_of_function clight)) clight)
    (prog_comp_env clight).

Lemma clight1_inj_id
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module1)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module1)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  eapply match_states_sim with (match_states := match_states_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. ss.
    assert (FD: fd = fd0).
    { admit "genv". } clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + inv SIMARGS. econs; eauto. econs.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + instantiate (1:=fd).
      admit "genv".
    + eapply typecheck_injection; eauto.
      inv SIMARGS. ss. eauto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * admit "genv".
      * admit "genv".
    + econs; ss.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInj.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH.
    exploit typify_c_injection; eauto.
    { inv SIMRET; ss; eauto. } i. des.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. econs; eauto.
      eapply match_cont_incr; cycle 1; eauto.
      inv MLE. inv MLE0. ss. etrans; eauto.
    + refl.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.
    + refl.

  - left. i. split.
    + admit "receptive".
    + ii. exploit clight_step_preserve_injection; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry1_inject. ss. }
      i. des. esplits; eauto.
      left. apply plus_one. econs; ss; eauto.
      admit "determinate".
Qed.

Lemma clight2_id
      (clight: Clight.program)
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

Lemma clight2_ext_unreach
      (clight: Clight.program)
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
      * inv TYP0. inv TYP.
        eapply lessdef_list_typify_list; eauto.
      * econs.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS. ss. inv FPTR.
      * rewrite H1 in *. eauto.
      * rewrite <- H0 in *. clarify.
    + inv SIMARGS. ss. inv TYP. econs; eauto.
      eapply lessdef_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); auto.

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
    { admit "receptive_at". }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto.
    left. apply plus_one. econs; ss; eauto.
    admit "determinate".
Qed.


Lemma clight2_ext_top
      (clight: Clight.program)
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
      * inv TYP0. inv TYP.
        eapply lessdef_list_typify_list; eauto.
      * econs.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + inv SIMARGS. ss. inv FPTR.
      * rewrite H1 in *. eauto.
      * rewrite <- H0 in *. clarify.
    + inv SIMARGS. ss. inv TYP. econs; eauto.
      eapply lessdef_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); auto.

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
    { admit "receptive_at". }
    ii. exploit clight_step_preserve_extension; eauto.
    { eapply function_entry2_extends. }
    i. des. esplits; eauto.
    left. apply plus_one. econs; ss; eauto.
    admit "determinate".
Qed.

Lemma clight2_inj_drop_bot
      (clight: Clight.program)
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
  { admit "add condition". }

  eapply match_states_sim with (match_states := match_states_clight); ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - i. ss.
    inv INITTGT. inv SAFESRC. inv H. ss.
    assert (FD: fd = fd0).
    { admit "genv". } clarify.
    esplits; eauto.
    + econs; eauto.
    + refl.
    + inv SIMARGS. econs; eauto.
      * inv TYP0. inv TYP.
        eapply inject_list_typify_list; eauto.
      * econs.

  - i. ss. des. inv SAFESRC. esplits. econs; ss.
    + instantiate (1:=fd).
      admit "genv".
    + inv SIMARGS. ss. inv TYP. econs; eauto.
      eapply inject_list_length in VALS.
      transitivity (Datatypes.length (Args.vs args_src)); auto.

  - i. ss. inv MATCH; eauto.

  - i. ss. clear SOUND. inv CALLSRC. inv MATCH. ss.
    esplits; eauto.
    + econs; ss; eauto.
      * admit "genv".
      * admit "genv".
    + econs; ss.
    + refl.
    + instantiate (1:=top4). ss.

  - i. ss. clear SOUND HISTORY.
    exists (SimMemInj.unlift' sm_arg sm_ret).
    inv AFTERSRC. inv MATCH.
    esplits; eauto.
    + econs; eauto.
    + inv SIMRET. econs; eauto.
      * eapply inject_typify; eauto.
      * ss. eapply match_cont_incr; try apply CONT; eauto.
        inv MLE. inv MLE0. etrans; eauto.
    +  refl.

  - i. ss. inv FINALSRC. inv MATCH. inv CONT.
    esplits; eauto.
    + econs.
    + econs; eauto.
    + refl.

  - left. i. split.
    + admit "receptive".
    + ii. exploit clight_step_preserve_injection; try eassumption.
      { instantiate (1:=cgenv skenv_link_tgt clight). ss. }
      { eapply function_entry2_inject. ss. }
      i. des. esplits; eauto.
      left. apply plus_one. econs; ss; eauto.
      admit "determinate".
Qed.

Lemma clight2_inj_drop
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  exploit clight2_inj_drop_bot; eauto. i. des. eauto.
Qed.

(* TODO: same as IdSimAsm. make IdSimExtra and move it to there *)
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

Lemma clight2_inj_id
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  set (clight2_inj_drop_bot clight). des.
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
