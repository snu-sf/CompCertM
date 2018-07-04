Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC Renumber.
Require Import sflib.
(** newly added **)
Require Export Renumberproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymbId SimMemId SimMem AsmregsC MatchSimModSem.

Set Implicit Arguments.







Section RNMBREXTRA.

  Variables prog tprog: program.
  Hypothesis TRANSL: match_prog prog tprog.
  (* Let ge := Genv.globalenv prog. *)
  (* Let tge := Genv.globalenv tprog. *)
  Variable ge tge: genv.

  Lemma step_simulation (SIMGE: False):
  forall S1 t S2 (NOTEXT: ~ RTLC.is_external ge S1), Step (semantics_with_ge prog ge) S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', DStep (semantics_with_ge tprog tge) S1' t S2' /\ match_states S2 S2'.
  Proof.
    admit "".
  Qed.

End RNMBREXTRA.









Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).

Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem skenv_link_src prog) (RTLC.modsem skenv_link_tgt tprog) tt
.

Inductive match_states (rs_init_src rs_init_tgt: regset)
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt)
    (MATCHST: Renumberproof.match_states st_src0 st_tgt0)
    (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0)
.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states); eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - destruct sm_arg; ss. clarify.
    unfold SimMem.sim_regset in *. ss. apply Axioms.functional_extensionality in SIMRS. clarify.
    inv INITSRC.
    esplits; eauto.
    + econs; eauto.
      * inv SIMSKENV. ss.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        admit "simskenv".
    + instantiate (1:= SimMemId.mk _ _). econs; ss; eauto.
    + u. econs; ss; eauto. econs; ss; eauto. econs; ss; eauto.
  - inv CALLSRC. des. inv MATCH. ss. destruct sm0; ss.
    inv MATCHST; inv H; ss; clarify.
    inv MCOMPAT. ss. fold_all ge. u in *. clarify.
    esplits; eauto.
    econs; eauto.
    fold_all tge.
    admit "simskenv".
  - inv CALLTGT. inv MATCH; ss. u in *. destruct sm0; ss. inv MCOMPAT; ss. u in *. clarify.
    do 2 eexists. eexists (SimMemId.mk _ _).
    esplits; ss; eauto. inv MATCHST; ss.
    econs; eauto.
    admit "simskenv".
  - apply Axioms.functional_extensionality in SIMRSRET. clarify.
    apply Axioms.functional_extensionality in SIMRSARG. clarify.
    inv AFTERSRC. inv MATCH; ss. inv MCOMPAT. u in *. clarify.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    inv MATCHST; ss. des_ifs. clear_tac. destruct sm0; ss. clarify.
    destruct sm_ret; ss. clarify.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto.
      econs; eauto.
  - inv FINALSRC. inv MATCH; ss. inv MATCHST; ss. inv MCOMPAT0; ss. u in *. destruct sm0; ss. des_ifs.
    inv STACKS; ss. inv MCOMPAT; ss. u in *. des_ifs. clear_tac.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    esplits; eauto.
    + econs; eauto.
      admit "simskenv".
    + ii; ss.
  - esplits; eauto.
    { apply modsem_receptive. }
    inv MATCH.
    apply Axioms.functional_extensionality in SIMRSINIT. clarify.
    ii. hexploit (@step_simulation prog tprog ge tge); eauto.
    { admit "WE SHOULD ADDRESS THIS". }
    { apply not_external. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
    + econs; ss; eauto.
Unshelve.
  all: try (by econs).
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
  - econs; eauto. admit "easy".
  - ii. eapply sim_modsem; eauto.
Qed.

End SIMMOD.

