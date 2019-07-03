(** Libraries. *)
Require Import String.
Require Import CoqlibC Errors ErrorsC.
Require Import AST Linking Smallstep.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax CsemC Cstrategy Cexec.
Require Clight.
Require Csharpminor.
Require CminorC.
Require CminorSel.
Require RTLC.
Require LTL.
Require Linear.
Require Mach.
Require AsmC.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
(**
Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem MatchSimModSem.
Print Instances SimMem.class.
(** nothing **)
Require RenumberproofC.
Print Instances SimMem.class.
(** SimMemId **)
**)
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.
(** newly added **)
Require Import BehaviorsC.
Require Export Compiler.
Require Import Simulation.
Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import SemProps AdequacyLocal.

Require SimMemInj SoundTop SimSymbDrop.
Require IdSim.


Set Implicit Arguments.

Local Open Scope string_scope.
Local Open Scope list_scope.



Ltac lift :=
  eapply mixed_to_backward_simulation;
  rpapply adequacy_local;
  [|
   instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _); ss; f_equal; u; rewrite map_app; ss
   |
   u; rewrite map_app; ss
  ];
  r; rewrite Forall_forall in *; ii;
  rewrite in_app_iff in *; des; eauto;
  rewrite in_app_iff in *; des; eauto; ss; des; ss; clarify
.

Section Cstrategy.

  Require CstrategyC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Cstrategy_correct
        src tgt
        (TRANSF: src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [CsemC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [(CstrategyC.module tgt).(Mod.Atomic.trans)] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply CstrategyC.sim_mod; eauto.
  Qed.

End Cstrategy.



Section SimplExpr.

  Require SimplExprproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma SimplExpr_correct
        src tgt
        (TRANSF: SimplExpr.transl_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [(CstrategyC.module src).(Mod.Atomic.trans)] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [ClightC.module1 tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply SimplExprproofC.sim_mod; eauto.
    eapply SimplExprproof.transf_program_match; eauto.
  Qed.

End SimplExpr.



Section SimplLocals.

  Require SimplLocalsproofC.

  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimMemInjC.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma SimplLocals_correct
        src tgt
        (TRANSF: SimplLocals.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [ClightC.module1 src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [ClightC.module2 tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply SimplLocalsproofC.sim_mod; eauto.
    eapply SimplLocalsproof.match_transf_program; eauto.
  Qed.

End SimplLocals.



Section Cshmgen.

  Require CshmgenproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Cshmgen_correct
        src tgt
        (TRANSF: Cshmgen.transl_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [ClightC.module2 src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [CsharpminorC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply CshmgenproofC.sim_mod; eauto.
    eapply Cshmgenproof.transf_program_match; eauto.
  Qed.

End Cshmgen.



Section Cminorgen.

  Require CminorgenproofC.

  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimMemInjC.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Cminorgen_correct
        src tgt
        (TRANSF: Cminorgen.transl_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [CsharpminorC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [CminorC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply CminorgenproofC.sim_mod; eauto.
    eapply Cminorgenproof.transf_program_match; eauto.
  Qed.

End Cminorgen.



Section Selection.

  Require SelectionproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Selection_correct
        src tgt
        (TRANSF: Selection.sel_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [CminorC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [CminorSelC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply SelectionproofC.sim_mod; eauto.
    eapply Selectionproof.transf_program_match; eauto.
  Qed.

End Selection.



Section RTLgen.

  Require RTLgenproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma RTLgen_correct
        src tgt
        (TRANSF: RTLgen.transl_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [CminorSelC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply RTLgenproofC.sim_mod; eauto.
    eapply RTLgenproof.transf_program_match; eauto.
  Qed.

End RTLgen.



Section Renumber0.

  Require RenumberproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Renumber0_correct
        src tgt
        (TRANSF: Renumber.transf_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply RenumberproofC.sim_mod; eauto.
    eapply Renumberproof.transf_program_match; eauto.
  Qed.

End Renumber0.



Section Tailcall.

  Require Import TailcallproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma Tailcall_correct
        src tgt
        (TRANSF: total_if optim_tailcalls Tailcall.transf_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold total_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply TailcallproofC.sim_mod; eauto.
    eapply Tailcallproof.transf_program_match; eauto.
  Qed.

End Tailcall.



Section Inlining.

  Require Import InliningproofC.

  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimMemInjC.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Inlining_correct
        src tgt
        (TRANSF: Inlining.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply InliningproofC.sim_mod; eauto.
    eapply Inliningproof.transf_program_match; eauto.
  Qed.

End Inlining.



Section Constprop.

  Require Import ConstpropproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance UnreachC.Unreach | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma Constprop_correct
        src tgt
        (TRANSF: total_if optim_constprop Constprop.transf_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold total_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply ConstpropproofC.sim_mod; eauto.
    eapply Constpropproof.transf_program_match; eauto.
  Qed.

End Constprop.



Section Renumber1.

  Require RenumberproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma Renumber1_correct
        src tgt
        (TRANSF: total_if optim_constprop Renumber.transf_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold total_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply RenumberproofC.sim_mod; eauto.
    eapply Renumberproof.transf_program_match; eauto.
  Qed.

End Renumber1.



Section CSE.

  Require CSEproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance UnreachC.Unreach | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma CSE_correct
        src tgt
        (TRANSF: partial_if optim_CSE CSE.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold partial_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply CSEproofC.sim_mod; eauto.
    eapply CSEproof.transf_program_match; eauto.
  Qed.

End CSE.



Section Deadcode.

  Require Import DeadcodeproofC.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma Deadcode_correct
        src tgt
        (TRANSF: partial_if optim_redundancy Deadcode.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold partial_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply DeadcodeproofC.sim_mod; eauto.
    eapply Deadcodeproof.transf_program_match; eauto.
  Qed.

End Deadcode.



Section Unusedglob.

  Require Import UnusedglobproofC.

  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimSymbDrop.SimSymbDrop | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Unusedglob_correct
        src tgt
        (TRANSF: Unusedglob.transform_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module2 tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply UnusedglobproofC.sim_mod; eauto.
    eapply Unusedglobproof.transf_program_match; eauto.
  Qed.

End Unusedglob.








Section Allocation.

  Require Import AllocproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Allocation_correct
        src tgt
        (TRANSF: Allocation.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module2 src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [LTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply AllocproofC.sim_mod; eauto.
    eapply Allocproof.transf_program_match; eauto.
  Qed.

End Allocation.



Section Tunneling.

  Require Import TunnelingproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Tunneling_correct
        src tgt
        (TRANSF: Tunneling.tunnel_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [LTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply TunnelingproofC.sim_mod; eauto.
    eapply Tunnelingproof.transf_program_match; eauto.
  Qed.

End Tunneling.



Section Linearize.

  Require Import LinearizeproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Linearize_correct
        src tgt
        (TRANSF: Linearize.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [LinearC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply LinearizeproofC.sim_mod; eauto.
    eapply Linearizeproof.transf_program_match; eauto.
  Qed.

End Linearize.



Section CleanupLabels.

  Require Import CleanupLabelsproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma CleanupLabels_correct
        src tgt
        (TRANSF: CleanupLabels.transf_program src = tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LinearC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [LinearC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply CleanupLabelsproofC.sim_mod; eauto.
    eapply CleanupLabelsproof.transf_program_match; eauto.
  Qed.

End CleanupLabels.



Section Debugvar.

  Require Import DebugvarproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.
  Hypothesis CEQ: cps.(ProgPair.src) = cps.(ProgPair.tgt).
  Hypothesis AEQ: aps.(ProgPair.src) = aps.(ProgPair.tgt).

  Lemma Debugvar_correct
        src tgt
        (TRANSF: partial_if debug Debugvar.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LinearC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [LinearC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    unfold partial_if in *. des_ifs; cycle 1.
    { rpapply backward_simulation_refl. repeat f_equal; eauto. }
    lift.
    eapply DebugvarproofC.sim_mod; eauto.
    eapply Debugvarproof.transf_program_match; eauto.
  Qed.

End Debugvar.



Section Stacking.

  Require Import StackingproofC.

  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimMemInjC.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma return_address_offset_deterministic:
    forall f c ofs ofs',
      Asmgenproof0.return_address_offset f c ofs ->
      Asmgenproof0.return_address_offset f c ofs' ->
      ofs = ofs'.
  Proof.
    i. inv H; inv H0.
    rewrite TF in TF0. inv TF0. rewrite TC in TC0. inv TC0.
    eapply Asmgenproof0.code_tail_unique in TL; eauto.
    assert(Integers.Ptrofs.eq ofs ofs' = true).
    unfold Integers.Ptrofs.eq. rewrite TL. rewrite zeq_true. auto.
    exploit Integers.Ptrofs.eq_spec. rewrite H. auto.
  Qed.

  Lemma Stacking_correct
        src tgt
        (TRANSF: Stacking.transf_program src = OK tgt)
        (COMPILESUCCED: exists final_tgt, Asmgenproof.match_prog tgt final_tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LinearC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [MachC.module tgt Asmgenproof0.return_address_offset] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply StackingproofC.sim_mod; eauto.
    { eapply Asmgenproof.return_address_exists; eauto. }
    { ii. determ_tac return_address_offset_deterministic. }
    eapply Stackingproof.transf_program_match; eauto.
  Qed.

End Stacking.






Section Asmgen.

  Require Import AsmgenproofC.

  Local Existing Instance SimMemExt.SimMemExt | 0.
  Local Existing Instance SimMemExt.SimSymbExtends | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Asmgen_correct
        src tgt
        (TRANSF: Asmgen.transf_program src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [MachC.module src Asmgenproof0.return_address_offset] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [AsmC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    lift.
    eapply AsmgenproofC.sim_mod; eauto.
    eapply Asmgenproof.transf_program_match; eauto.
  Qed.

End Asmgen.





(* From stdpp Require list. *)

Ltac contains_term TERM :=
  match goal with
  | [ |- context[TERM] ] => idtac
  | _ => fail
  end
.

Ltac contains_term_in TERM H :=
  multimatch goal with
  | [ H': context[TERM] |- _ ] =>
    (* idtac H'; *)
    check_equal H H'
  | _ => fail
  end
.

Ltac find_sim LANG :=
  repeat
    multimatch goal with
    (* | [H0: ?L0 = ?R0, H1: ?L1 = ?R1 |- _ ] => *)
    (*   rewrite <- H0; rewrite <- H1; refl *)
    | [ T: @__GUARD__ _ (?SIM /\ ?SRC /\ ?TGT)  |- _ ] =>
      match SIM with
      | (@ProgPair.sim ?SIMMEM ?SIMSYMB ?SOUND _) =>
        contains_term SIMMEM;
        contains_term SIMSYMB;
        contains_term SOUND;
        contains_term_in LANG T;
        unfold __GUARD__ in T;
        let X := fresh "T" in
        let Y := fresh "T" in
        let Z := fresh "T" in
        destruct T as [X [Y Z]];
        (* let tx := type of X in *)
        (* let ty := type of Y in *)
        (* let tz := type of Z in *)
        (* idtac "-------------------------------------------"; *)
        (* idtac X; idtac Y; idtac Z; *)
        (* idtac tx; idtac ty; idtac tz; *)
        apply X
      | _ => idtac (* SIM *)
      end
    end
.

(** Copied from Compiler.v, but without "SimplLocals.transf_program" **)
(** SimplLocals translate Clight1 into Clight2 and our source program is Clight2. **)
(** We chose Clight2 because VST uses Clight2. **)

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
   @@ print print_Clight
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Lemma compiler_correct_single
      (src: Clight.program)
      (tgt: Asm.program)
      (cls: list Clight.program)
      (asms: list Asm.program)
      (TRANSF: transf_clight_program src = OK tgt)
  :
    improves (sem ((map ClightC.module2 cls) ++ [ClightC.module2 src] ++ (map AsmC.module asms)))
             (sem ((map ClightC.module2 cls) ++ [AsmC.module tgt] ++ (map AsmC.module asms)))
.
Proof.
  destruct (classic (forall x (IN: In x ((map ClightC.module2 cls) ++ [ClightC.module2 src] ++ (map AsmC.module asms))), Sk.wf x)) as [WF|NWF]; cycle 1.
  { eapply sk_nwf_improves; auto. }

  unfold transf_clight_program in *.
  unfold transf_cminor_program in *. unfold transf_rtl_program in *. unfold time in *.
  (* unfold total_if, partial_if in *. *)
  unfold print in *. cbn in *.
  unfold apply_total, apply_partial in *. des_ifs_safe.

  set (total_if optim_tailcalls Tailcall.transf_program p0) as ptail in *.
  set (Renumber.transf_program p9) as prenum0 in *.
  set (total_if optim_constprop Constprop.transf_program prenum0) as pconst in *.
  set (total_if optim_constprop Renumber.transf_program pconst) as prenum1 in *.
  set (Tunneling.tunnel_program p5) as ptunnel in *.
  set (CleanupLabels.transf_program p4) as pclean in *.

  assert (SRCSWF: forall x, In x cls -> Sk.wf (ClightC.module2 x)).
  { ii. eapply WF. eapply in_or_app. left. eapply in_map. auto. }
  assert (ASMSWF: forall x, In x asms -> Sk.wf (AsmC.module x)).
  { ii. eapply WF. eapply in_or_app. right. right. eapply in_map. auto. }

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_inj_drop cls); auto. intro SRCINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_inj_id cls); auto. intro SRCINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_ext_top cls); auto. intro SRCEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_ext_unreach cls); auto. intro SRCEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_id cls); auto. intro SRCID; des.

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_drop asms); auto. intro TGTINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_id asms); auto. intro TGTINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_top asms); auto. intro TGTEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_unreach asms); auto. intro TGTEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_id asms); auto. intro TGTID; des.


  Ltac next PASS_CORRECT :=
    etrans; [
      eapply bsim_improves; rp; [eapply PASS_CORRECT|..]; try refl; [find_sim Clight.program|find_sim Asm.program|..];
      try (by unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto)
     |];
    folder
  .

  (* next SimplLocals_correct. *)
  next Cshmgen_correct.
  next Cminorgen_correct.
  next Selection_correct.
  next RTLgen_correct.
  next Tailcall_correct.
  next Inlining_correct.
  next Renumber0_correct.
  next Constprop_correct.
  next Renumber1_correct.
  next CSE_correct.
  next Deadcode_correct.
  next Unusedglob_correct.
  next Allocation_correct.
  next Tunneling_correct.
  next Linearize_correct.
  next CleanupLabels_correct.
  next Debugvar_correct.
  next Stacking_correct.
  { eexists. eapply transf_program_match; eauto. }
  next Asmgen_correct.

  unfold __GUARD__ in *. des.
  repeat all ltac:(fun H => rewrite H).
  refl.

Qed.




(**
Note: we can't vertically compose in simulation level, because
1) it requires maximal memory relation (closure)
2) single_events of tgt (which is not true)

induction: src/tgt length is fixed (we don't do horizontal composition in behavior level)
**)

Theorem compiler_correct
        (srcs: list Clight.program)
        (tgts hands: list Asm.program)
        (TR: mmap transf_clight_program srcs = OK tgts)
  :
    improves (sem ((map ClightC.module2 srcs) ++ (map AsmC.module hands)))
             (sem ((map AsmC.module tgts) ++ (map AsmC.module hands)))
.
Proof.
  apply mmap_inversion in TR.
  apply forall2_eq in TR.
  generalize dependent hands.
  remember (length srcs) as len. rename Heqlen into T.
  generalize dependent srcs.
  generalize dependent tgts.
  induction len; i; ss.
  { destruct srcs; ss. inv TR. refl. }

  destruct (last_opt srcs) eqn:T2; cycle 1.
  {
    eapply last_none in T2. clarify.
  }
  apply last_some in T2. des. clarify.
  apply Forall2_app_inv_l in TR. des. clarify. inv TR0. inv H3.
  rename hds into srcs. rename l1' into tgts.
  rename p into hand_src. rename y into hand_tgt.
  rewrite ! map_app. ss.
  etrans.
  { rp; [eapply compiler_correct_single with (cls:= srcs) (asms:= hands)|..]; eauto.
    rewrite app_assoc. ss.
  }
  { rewrite <- ! app_assoc. ss.
    rewrite app_length in *. ss. rewrite Nat.add_1_r in *. clarify.
    specialize (IHlen tgts srcs). spc IHlen. specialize (IHlen (eq_refl _)).
    eapply (IHlen (hand_tgt :: hands)).
  }
Qed.

(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)

(** Additionally, we support C as a source language too. **)

Lemma clightgen_correct
        (srcs: list Csyntax.program)
        (cls tgts: list Clight.program)
        (hands: list Asm.program)
        (* (TR: mmap (fun src => OK src @@@ SimplExpr.transl_program @@@ SimplLocals.transf_program) srcs = OK tgts) *)
        irs
        (TR0: mmap (SimplExpr.transl_program) srcs = OK irs)
        (TR1: mmap (SimplLocals.transf_program) irs = OK tgts)
  :
    improves (sem ((map CsemC.module srcs) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands)))
             (sem ((map ClightC.module2 tgts) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands)))
.
Proof.
  (* apply mmap_inversion in TR. *)
  (* apply forall2_eq in TR. *)
  (* unfold apply_partial in *. *)
  (* assert(TR0: exists irs, mmap (SimplExpr.transl_program) srcs = OK irs /\ mmap (SimplLocals.transf_program) irs = OK tgts). *)
  (* { ginduction TR; ii; ss. *)
  (*   { esplits; eauto. } *)
  (*   des_ifs. exploit IHTR; eauto. i; des. *)
  (*   eexists (_ :: _). ss. unfold bind. des_ifs_safe. esplits; eauto. des_ifs. *)
  (* } *)
  (* clear TR. des. *)
  apply mmap_inversion in TR0.
  apply mmap_inversion in TR1.
  rewrite forall2_eq in *.

  destruct (classic (forall x (IN: In x ((map CsemC.module srcs) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands))), Sk.wf x)) as [WF|NWF]; cycle 1.
  { eapply sk_nwf_improves; auto. }

  assert (SRCSWF: forall x, In x cls -> Sk.wf (ClightC.module2 x)).
  { ii. eapply WF. eapply in_or_app. right. eapply in_app_iff. left. rewrite in_map_iff. eauto. }
  assert (ASMSWF: forall x, In x hands -> Sk.wf (AsmC.module x)).
  { ii. eapply WF. eapply in_or_app. right. eapply in_app_iff. right. rewrite in_map_iff. eauto. }

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_inj_drop cls); auto. intro SRCINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_inj_id cls); auto. intro SRCINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_ext_top cls); auto. intro SRCEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_ext_unreach cls); auto. intro SRCEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.clight_id cls); auto. intro SRCID; des.

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_drop hands); auto. intro TGTINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_id hands); auto. intro TGTINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_top hands); auto. intro TGTEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_unreach hands); auto. intro TGTEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_id hands); auto. intro TGTID; des.

  unfold __GUARD__ in *. des.

  etrans.
  { instantiate (1:= (sem ((map (Mod.Atomic.trans <*> CstrategyC.module) srcs) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands)))).
    eapply bsim_improves.
    eapply mixed_to_backward_simulation.
    move srcs at bottom.

    set (map (fun src => @ModPair.mk _ SimMemId.SimSymbId (CsemC.module src)
                                     (Mod.Atomic.trans (CstrategyC.module src)) tt) srcs) as X.
    exploit (@adequacy_local _ SimMemId.SimSymbId SoundTop.Top (X ++ pp3 ++ pp8)).
    { rr.
      eapply Forall_app; eauto.
      { subst X. rewrite Forall_forall. ii; ss. rewrite in_map_iff in *. des. clarify.
        eapply CstrategyC.sim_mod; eauto.
      }
      eapply Forall_app; eauto.
    }
    intro T. rpapply T; ss.
    { unfold ProgPair.src in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. rewrite map_map. ss.
    }
    { unfold ProgPair.tgt in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. rewrite map_map. ss.
    }
  }

  etrans.
  { instantiate (1:= (sem ((map ClightC.module1 irs) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands)))).
    eapply bsim_improves.
    eapply mixed_to_backward_simulation.
    move srcs at bottom.

    set (zip (fun src tgt => @ModPair.mk _ SimMemId.SimSymbId (Mod.Atomic.trans (CstrategyC.module src))
                                         (ClightC.module1 tgt) tt) srcs irs) as X.
    exploit (@adequacy_local _ SimMemId.SimSymbId SoundTop.Top (X ++ pp3 ++ pp8)).
    { rr.
      eapply Forall_app; eauto.
      { subst X. rewrite Forall_forall. ii; ss. apply in_zip_iff in H. des. clarify.
        eapply SimplExprproofC.sim_mod; eauto.
        clear - TR0 X Y.
        ginduction srcs; ii; ss.
        { destruct n; ss. }
        unfold bind in *. des_ifs. inv TR0.
        destruct n; ss; des_ifs.
        { eapply SimplExprproof.transf_program_match; et. }
        eapply IHsrcs; et.
      }
      eapply Forall_app; eauto.
    }
    intro T. rpapply T; ss.
    { unfold ProgPair.src in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. exploit Forall2_length; et. intro U.
      clear - U. ginduction srcs; ii; ss.
      des_ifs. ss. f_equal. erewrite IHsrcs; ss; eauto.
    }
    { unfold ProgPair.tgt in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. exploit Forall2_length; et. intro U.
      clear - U. ginduction srcs; ii; ss.
      { destruct irs; ss. }
      des_ifs. ss. f_equal. erewrite IHsrcs; ss; eauto.
    }
  }

  etrans.
  { instantiate (1:= (sem (map ClightC.module2 tgts ++ map ClightC.module2 cls ++ map AsmC.module hands))).
    eapply bsim_improves.
    eapply mixed_to_backward_simulation.
    move srcs at bottom.

    set (zip (fun ir tgt => @ModPair.mk _ SimMemInjC.SimSymbId (ClightC.module1 ir)
                                         (ClightC.module2 tgt) tt) irs tgts) as X.
    exploit (@adequacy_local _ SimMemInjC.SimSymbId SoundTop.Top (X ++ pp0 ++ pp5)).
    { rr.
      eapply Forall_app; eauto.
      { subst X. rewrite Forall_forall. ii; ss. apply in_zip_iff in H. des. clarify.
        eapply SimplLocalsproofC.sim_mod; eauto.
        clear - TR1 X Y.
        ginduction irs; ii; ss.
        { destruct n; ss. }
        unfold bind in *. des_ifs. inv TR1.
        destruct n; ss; des_ifs.
        { eapply SimplLocalsproof.match_transf_program; et. }
        eapply IHirs; et.
      }
      eapply Forall_app; eauto.
    }
    intro T. rpapply T; ss.
    { unfold ProgPair.src in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. clear TR0. exploit Forall2_length; et. intro U.
      clear - U. ginduction irs; ii; ss.
      des_ifs. ss. f_equal. erewrite IHirs; ss; eauto.
    }
    { unfold ProgPair.tgt in *.
      rewrite ! map_app. repeat f_equal; try congruence.
      subst X. clear TR0. exploit Forall2_length; et. intro U.
      clear - U. ginduction irs; ii; ss.
      { destruct tgts; ss. }
      des_ifs. ss. f_equal. erewrite IHirs; ss; eauto.
    }
  }

  refl.
Qed.

Theorem compiler_correct_full
        (srcs0: list Csyntax.program)
        (srcs1: list Clight.program)
        (tgts0 tgts1 hands: list Asm.program)
        (TR0: mmap transf_c_program srcs0 = OK tgts0)
        (TR1: mmap transf_clight_program srcs1 = OK tgts1)
  :
    improves (sem ((map CsemC.module srcs0) ++ (map ClightC.module2 srcs1) ++ (map AsmC.module hands)))
             (sem ((map AsmC.module tgts0) ++ (map AsmC.module tgts1) ++ (map AsmC.module hands)))
.
Proof.
  replace transf_c_program with
      (fun p => OK p @@@ SimplExpr.transl_program @@@ SimplLocals.transf_program @@@ transf_clight_program)
    in TR0; cycle 1.
  { unfold transf_c_program, transf_clight_program, Compiler.transf_clight_program.
    apply func_ext1. i. ss. unfold apply_partial, time, print.
    des_ifs_safe. des_ifs; ss. }
  eapply mmap_partial in TR0; eauto. des.
  eapply mmap_partial in MMAP0; eauto. des.
  hexploit clightgen_correct; eauto. intro T.
  etrans; eauto.
  rewrite app_assoc.
  rewrite app_assoc.
  rpapply (@compiler_correct (lb ++ srcs1) (tgts0 ++ tgts1) hands) ; eauto.
  { rewrite mmap_app. unfold bind. des_ifs. }
  { rewrite map_app. rewrite <- app_assoc. ss. }
  { rewrite map_app. rewrite <- app_assoc. ss. }
Qed.
