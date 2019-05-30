Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.


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

Lemma sim_inj_drop_bot_id
      src
      (DROP: exists mp,
          (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
          /\ (<<SRC: mp.(ModPair.src) = src>>)
          /\ (<<TGT: mp.(ModPair.tgt) = src>>)
          /\ (<<SSBOT: mp.(ModPair.ss) = bot1>>))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src>>).
Proof.
  des. clarify. destruct mp eqn: EQ. ss. clarify. inv SIM. ss.
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
