(** Libraries. *)
Require Import String.
Require Import CoqlibC Errors.
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
Require Import AdequacyLocal.

Require SimMemInj SoundTop SimSymbDrop.
Require IdSim.


Set Implicit Arguments.

Local Open Scope string_scope.
Local Open Scope list_scope.


(* TODO: Move to more proper place *)
Lemma backward_simulation_refl
      SEM
  :
    backward_simulation SEM SEM
.
Proof.
  eapply (@Backward_simulation _ _ unit bot2).
  econs; eauto.
  { apply unit_ord_wf. }
  ii. ss.
  exists tt.
  esplits; eauto.
  clear st_init_src_ INITSRC INITTGT.
  rename st_init_tgt into st. revert st.
  pcofix CIH. i. pfold.
  econs; eauto.
  { ii. esplits; eauto. econs; eauto. }
  ii. econs; eauto.
  { ii. esplits; eauto. left. apply plus_one. ss. }
  i. r in SAFESRC. specialize (SAFESRC st (star_refl _ _ _ _)). ss.
Qed.





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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
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

  Lemma Stacking_correct
        src tgt
        (TRANSF: Stacking.transf_program src = OK tgt)
        (COMPILESUCCED: exists final_tgt, Asmgenproof.match_prog tgt final_tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [LinearC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [MachC.module tgt Asmgenproof0.return_address_offset] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
    eapply StackingproofC.sim_mod; eauto.
    { eapply Asmgenproof.return_address_exists; eauto. }
    { admit "ez - ask @yonghyunkim. int2ptr repository has the proof (10 LOC?)". }
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
    eapply mixed_to_backward_simulation.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
    eapply AsmgenproofC.sim_mod; eauto.
    eapply Asmgenproof.transf_program_match; eauto.
  Qed.

End Asmgen.





(* From stdpp Require list. *)

Lemma compiler_correct_single
        (src: Csyntax.program)
        (tgt: Asm.program)
        (cs: list Csyntax.program)
        (asms: list Asm.program)
        (TRANSF: transf_c_program src = OK tgt)
  :
    Smallstep.backward_simulation (sem ((map CsemC.module cs) ++ [CsemC.module src] ++ (map AsmC.module asms)))
                                  (sem ((map CsemC.module cs) ++ [AsmC.module tgt] ++ (map AsmC.module asms)))
.
Proof.
  eapply compose_backward_simulation; eauto.
  idtac "SINGLE EVENTS!!!!".
Abort.





Lemma compiler_correct_single
        (src: Csyntax.program)
        (tgt: Asm.program)
        (cs: list Csyntax.program)
        (asms: list Asm.program)
        (TRANSF: transf_c_program src = OK tgt)
  :
    improves (sem ((map CsemC.module cs) ++ [CsemC.module src] ++ (map AsmC.module asms)))
             (sem ((map CsemC.module cs) ++ [AsmC.module tgt] ++ (map AsmC.module asms)))
.
Proof.
  unfold transf_c_program in *. unfold transf_clight_program in *.
  unfold transf_cminor_program in *. unfold transf_rtl_program in *. unfold time in *.
  (* unfold total_if, partial_if in *. *)
  unfold print in *. cbn in *.
  unfold apply_total, apply_partial in *. des_ifs_safe.

  set (total_if optim_tailcalls Tailcall.transf_program p1) as ptail in *.
  set (Renumber.transf_program p10) as prenum0 in *.
  set (total_if optim_constprop Constprop.transf_program prenum0) as pconst in *.
  set (total_if optim_constprop Renumber.transf_program pconst) as prenum1 in *.
  set (Tunneling.tunnel_program p6) as ptunnel in *.
  set (CleanupLabels.transf_program p5) as pclean in *.

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.ccc_inj_drop cs). intro SRCINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.ccc_inj_id cs). intro SRCINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.ccc_ext_top cs). intro SRCEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.ccc_ext_unreach cs). intro SRCEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.ccc_id cs). intro SRCID; des.

  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_drop asms). intro TGTINJDROP; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_inj_id asms). intro TGTINJID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_top asms). intro TGTEXTID; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_ext_unreach asms). intro TGTEXTUNREACH; des.
  hexploit (@IdSim.lift _ _ _ _ _ IdSim.asm_id asms). intro TGTID; des.


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



  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Cstrategy_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). reflexivity.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply SimplExpr_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply SimplLocals_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Cshmgen_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Cminorgen_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Selection_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply RTLgen_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  
  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Tailcall_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Inlining_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Renumber0_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Constprop_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Renumber1_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply CSE_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Deadcode_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Unusedglob_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Allocation_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Tunneling_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Linearize_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply CleanupLabels_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }
  folder.

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Debugvar_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    { unfold __GUARD__ in *; des; all ltac:(fun H => rewrite H); eauto. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Stacking_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    { eexists. eapply transf_program_match; eauto. }
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Asmgen_correct|..]; try refl.
    { find_sim Csyntax.program. }
    { find_sim Asm.program. }
    eauto.
    unfold __GUARD__ in *. des.
    all ltac:(fun H => rewrite H). eauto.
  }

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
        (srcs: list Csyntax.program)
        (tgts hands: list Asm.program)
        (TR: mmap transf_c_program srcs = OK tgts)
  :
    improves (sem ((map CsemC.module srcs) ++ (map AsmC.module hands)))
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
  { rp; [eapply compiler_correct_single with (cs:= srcs) (asms:= hands)|..]; eauto.
    rewrite app_assoc. ss.
  }
  { rewrite <- ! app_assoc. ss.
    rewrite app_length in *. ss. rewrite Nat.add_1_r in *. clarify.
    specialize (IHlen tgts srcs). spc IHlen. specialize (IHlen (eq_refl _)).
    eapply (IHlen (hand_tgt :: hands)).
  }
Qed.





