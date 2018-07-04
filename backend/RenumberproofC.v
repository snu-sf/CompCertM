Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC Renumber.
Require Import sflib.
(** newly added **)
Require Export Renumberproof.
Require Import Simulation.
Require Import ModSem SimModSem SimSymbId SimMemId SimMem AsmregsC MatchSimModSem.

Set Implicit Arguments.



Section RTLEXTRA.

  Variable prog: RTL.program.
  Let sem := RTL.semantics prog.

  Definition is_external (ge: genv) (st: RTL.state): Prop :=
    match st with
    | Callstate stack fptr sg args m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => True
      | _ => False
      end
    | _ => False
    end
  .

  Lemma semantics_receptive
        st
        (INTERNAL: ~is_external sem.(globalenv) st)
    :
      receptive_at sem st
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma semantics_determinate
        st
        (INTERNAL: ~is_external sem.(globalenv) st)
    :
      determinate_at sem st
  .
  Proof.
    admit "this should hold".
  Qed.

End RTLEXTRA.





Section RNMBREXTRA.

  Variables prog tprog: program.
  Hypothesis TRANSL: match_prog prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma step_simulation:
  forall S1 t S2 (NOTEXT: ~ is_external ge S1), RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', DStep (semantics tprog) S1' t S2' /\ match_states S2 S2'.
  Proof.
    admit "".
  Qed.

End RNMBREXTRA.





Section RTLCEXTRA.

  Variable prog: RTL.program.
  Let ge := Genv.globalenv prog.
  Let sem := RTL.semantics prog.

  Lemma not_external
        st0
        (* (STEP: ModSem.is_step (modsem prog) st0) *)
    :
      ~ is_external ge st0
  .
  Proof.
    ii. hnf in H. des_ifs.
    admit "this does not happen here!".
  Qed.

  Lemma is_external_at_external
        st0
        (ISEXT: is_external ge st0)
    :
      <<ATEXT: ModSem.is_call (modsem prog) st0>>
  .
  Proof.
    u in *. unfold is_external in *. des_ifs.
    esplits; eauto.
    econs; eauto.
  Abort.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at sem st)
    :
      receptive_at (modsem prog) st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss. exploit sr_receptive_at; eauto.
    admit "skenv admit".
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at (modsem prog) st
  .
  Proof.
    eapply lift_receptive_at; eauto. eapply semantics_receptive; eauto. eapply not_external; eauto.
    (* destruct (classic (is_external sem.(globalenv) st)); cycle 1. *)
    (* { eapply lift_receptive_at; eauto. eapply semantics_receptive; eauto. } *)
    (* u in H. hnf in H. des_ifs. *)
    (* exfalso. *)
    (* admit "this should not happen here!". *)
  Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at sem st0)
    :
      determinate_at (modsem prog) st0 
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    determ_tac sd_determ_at. esplits; eauto.
    admit "skenv admit".
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at (modsem prog) st
  .
  Proof.
    eapply lift_determinate_at; eauto. eapply semantics_determinate; eauto. eapply not_external; eauto.
    (* destruct (classic (is_external sem.(globalenv) st)); cycle 1. *)
    (* { eapply lift_determinate_at; eauto. eapply semantics_determinate; eauto. } *)
    (* u in H. hnf in H. des_ifs. *)
    (* exfalso. *)
    (* admit "this should not happen here!". *)
  Qed.

End RTLCEXTRA.





Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem prog) (RTLC.modsem tprog) tt.

Inductive match_states (rs_init_src rs_init_tgt: regset)
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt)
    (MATCHST: Renumberproof.match_states st_src0 st_tgt0)
    (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0)
.

Theorem sim
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
      * admit "simskenv".
    + instantiate (1:= SimMemId.mk _ _). econs; ss; eauto.
    + u. econs; ss; eauto. econs; ss; eauto. econs; ss; eauto.
  - inv CALLSRC. des. inv MATCH. ss. destruct sm0; ss.
    inv MATCHST; inv H; ss; clarify.
    inv MCOMPAT. ss. u in *. clarify.
    esplits; eauto.
    econs; eauto.
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
    ii. exploit (step_simulation prog tprog); eauto.
    { apply not_external. }
    i; des.
    esplits; eauto.
    + left. apply plus_one. ss. unfold DStep in *. des; ss. esplits; eauto. apply modsem_determinate.
    + instantiate (1:= SimMemId.mk _ _). econs; ss.
    + econs; ss; eauto.
Unshelve.
  all: try (by econs).
Qed.

End PRESERVATION.

