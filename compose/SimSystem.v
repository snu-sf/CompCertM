Require Import EventsC.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep Simulation.
Require Import CoqlibC.

Require Import Mod ModSem Skeleton System.
Require Import SimProg SimMod SimModSem.
Require Import SimMem Sound SimSymb Preservation Sem Syntax.

Set Implicit Arguments.


Section SIM.

  Context `{SM: SimMem.class}.
  Context `{SU: Sound.class}.
  Context {SS: SimSymb.class SM}.

  Variables pp: ProgPair.t.
  Hypothesis (SIMPROG: ProgPair.sim pp).
  Let p_src: program := (ProgPair.src pp).
  Let p_tgt: program := (ProgPair.tgt pp).
  Variable ss_link: SimSymb.t.
  Hypothesis (SIMSK: SimSymb.wf ss_link).
  Hypothesis (WFSRC: Sk.wf ss_link.(SimSymb.src)).
  Hypothesis (WFTGT: Sk.wf ss_link.(SimSymb.tgt)).
  (* Hypothesis (SSLE: Forall (fun mp => SimSymb.le (ModPair.ss mp) ss_link) pp). *)
  (* Hypothesis (SKSRC: link_sk p_src = Some (SimSymb.src ss_link)). *)
  (* Hypothesis (SKTGT: link_sk p_tgt = Some (SimSymb.tgt ss_link)). *)

  Theorem sim_system: exists mp,
      (<<SYSSRC: mp.(ModPair.src) = (System.module (Some ss_link.(SimSymb.src)))>>) /\
      (<<SYSTGT: mp.(ModPair.tgt) = (System.module (Some ss_link.(SimSymb.tgt)))>>) /\
      (<<SYSSIM: ModPair.sim mp>>)
  .
  Proof.
    exploit SimSymb.system_wf; eauto. i; des.
    eexists (ModPair.mk _ _ ss_sys). ss.
    esplits; eauto.
    econs; ss. ii. unfold ModPair.to_msp. ss.
    exploit system_local_preservation; eauto. intro SYSSU; des.
    econs; eauto; ss.
    { instantiate (2:= Empty_set). ii; ss. }
    ii. inv SIMSKENV. ss.
    split; cycle 1.
    { ii; des. inv SAFESRC. inv SIMARGS; ss. esplits; eauto. econs; eauto. }
    ii. sguard in SAFESRC. des. inv INITTGT.
    inv SIMARGS; ss. clarify.
    esplits; eauto.
    { refl. }
    { econs; eauto. }
    pfold.
    econs; eauto.
    i.
    econs; ss; cycle 2.
    { eapply System.modsem_receptive; et. }
    { u. esplits; ii; des; ss; eauto. inv H. }
    ii. inv STEPSRC.
    exploit SimSymb.system_axiom; eauto; swap 1 3; swap 2 4.
    { econs; eauto. }
    { ss. instantiate (1:= Retv.mk _ _). ss. eauto. }
    { ss. }
    { ss. }
    i; des.
    hexpl SimSymb.sim_skenv_func_bisim SIMGE0.
    inv SIMGE0. exploit FUNCFSIM; eauto. i; des. clarify.
    esplits; eauto.
    { left. apply plus_one. econs.
      - eapply System.modsem_determinate; et.
      - ss. econs; eauto. }
    left. pfold.
    econs 4.
    { refl. }
    { eauto. }
    { econs; eauto. }
    { econs; eauto. }
    { inv RETV; ss. unfold Retv.mk in *. clarify. econs; ss; eauto. }
  Unshelve.
    all: ss.
    all: try eapply Ord.idx_bot; eauto.
  Qed.

End SIM.
