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
Require Unreadglob.
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
(** nothing **)
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

Require SimMemInj SoundTop SimSymbDrop SimSymbDropInv.
Require IdSim.

Require Import RUSC.

Definition CompCert_relations_list: list program_relation.t :=
  [ (mkPR SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top) ;
    (mkPR SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top) ;
    (mkPR SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach) ;
    (mkPR SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top) ;
    (mkPR SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top) ;
    (mkPR SimSymbDropInv.SimMemInvTop SimSymbDropInv.SimSymbDropInv SoundTop.Top)
  ].

Definition CompCert_relations := (fun r => In r CompCert_relations_list).

Lemma asm_self_related (asm: Asm.program):
    self_related CompCert_relations [asm.(AsmC.module)].
Proof.
  intros r RELIN. unfold CompCert_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  - exploit IdSim.asm_id; ss; eauto.
  - exploit IdSim.asm_ext_top; ss; eauto.
  - exploit IdSim.asm_ext_unreach; ss; eauto.
  - exploit IdSim.asm_inj_drop; ss; eauto.
  - exploit IdSim.asm_inj_id; ss; eauto.
  - exploit IdSim.asm_inj_inv_drop; ss; eauto.
Qed.

Lemma asms_self_related (asms: list Asm.program):
    self_related CompCert_relations (map AsmC.module asms).
Proof.
  induction asms; ss; ii.
  exploit IHasms; ss; eauto. i.
  eapply (@program_relation.horizontal _ [a.(AsmC.module)] _ [a.(AsmC.module)]); eauto.
  eapply asm_self_related; eauto.
Qed.

Lemma clight_self_related (cl: Clight.program):
    self_related CompCert_relations [cl.(ClightC.module2)].
Proof.
  intros r RELIN. unfold CompCert_relations in *. ss.
  des; clarify; eapply relate_single_program; intros WF.
  - exploit IdSim.clight_id; ss; eauto.
  - exploit IdSim.clight_ext_top; ss; eauto.
  - exploit IdSim.clight_ext_unreach; ss; eauto.
  - exploit IdSim.clight_inj_drop; ss; eauto.
  - exploit IdSim.clight_inj_id; ss; eauto.
  - exploit IdSim.clight_inj_inv_drop; ss; eauto.
Qed.

Lemma clights_self_related (cls: list Clight.program):
    self_related CompCert_relations (map ClightC.module2 cls).
Proof.
  induction cls; ss; ii.
  exploit IHcls; ss; eauto. i.
  eapply (@program_relation.horizontal _ [a.(ClightC.module2)] _ [a.(ClightC.module2)]); eauto.
  eapply clight_self_related; eauto.
Qed.


Section Cstrategy.

  Require CstrategyproofC.
  Lemma Cstrategy_correct
        src tgt
        (TRANSF: src = tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (CsemC.module src) (CstrategyC.module tgt).(Mod.Atomic.trans).
  Proof.
    unfold relate_single. clarify. exploit CstrategyproofC.sim_mod; eauto. esplits; eauto; ss.
  Qed.

End Cstrategy.


Section SimplExpr.

  Require SimplExprproofC.
  Lemma SimplExpr_correct
        src tgt
        (TRANSF: SimplExpr.transl_program src = OK tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (CstrategyC.module src).(Mod.Atomic.trans) (ClightC.module1 tgt).
  Proof.
    unfold relate_single. exploit SimplExprproofC.sim_mod; i; esplits; eauto; ss.
    eapply SimplExprproof.transf_program_match; eauto.
  Qed.

End SimplExpr.


Section SimplLocals.

  Require SimplLocalsproofC.
  Lemma SimplLocals_correct
        src tgt
        (TRANSF: SimplLocals.transf_program src = OK tgt):
      relate_single
        SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top
        (ClightC.module1 src) (ClightC.module2 tgt).
  Proof.
    unfold relate_single. exploit SimplLocalsproofC.sim_mod; i; esplits; eauto; ss.
    eapply SimplLocalsproof.match_transf_program; eauto.
  Qed.

End SimplLocals.


Section Cshmgen.

  Require CshmgenproofC.
  Lemma Cshmgen_correct
        src tgt
        (TRANSF: Cshmgen.transl_program src = OK tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (ClightC.module2 src) (CsharpminorC.module tgt).
  Proof.
    unfold relate_single. exploit CshmgenproofC.sim_mod; i; esplits; eauto; ss.
    eapply Cshmgenproof.transf_program_match; eauto.
  Qed.

End Cshmgen.


Section Cminorgen.

  Require CminorgenproofC.
  Lemma Cminorgen_correct
        src tgt
        (TRANSF: Cminorgen.transl_program src = OK tgt):
      relate_single
        SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top
        (CsharpminorC.module src) (CminorC.module tgt).
  Proof.
    unfold relate_single. exploit CminorgenproofC.sim_mod; i; esplits; eauto; ss.
    eapply Cminorgenproof.transf_program_match; eauto.
  Qed.

End Cminorgen.


Section Selection.

  Require SelectionproofC.
  Lemma Selection_correct
        src tgt
        (TRANSF: Selection.sel_program src = OK tgt):
      relate_single
        SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top
        (CminorC.module src) (CminorSelC.module tgt).
  Proof.
    unfold relate_single. exploit SelectionproofC.sim_mod; i; esplits; eauto; ss.
    eapply Selectionproof.transf_program_match; eauto.
  Qed.

End Selection.


Section RTLgen.

  Require RTLgenproofC.
  Lemma RTLgen_correct
        src tgt
        (TRANSF: RTLgen.transl_program src = OK tgt):

      relate_single
        SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top
        (CminorSelC.module src) (RTLC.module tgt).
  Proof.
    unfold relate_single. exploit RTLgenproofC.sim_mod; i; esplits; eauto; ss.
    eapply RTLgenproof.transf_program_match; eauto.
  Qed.

End RTLgen.



Section Renumber0.

  Require RenumberproofC.
  Lemma Renumber0_correct
        src tgt
        (TRANSF: Renumber.transf_program src = tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold relate_single. exploit RenumberproofC.sim_mod; eauto.
    { eapply Renumberproof.transf_program_match; eauto. }
    i. rewrite TRANSF in *. esplits; eauto; ss.
  Qed.

End Renumber0.


Section Tailcall.

  Require Import TailcallproofC.
  Lemma Tailcall_correct
        src tgt
        (TRANSF: total_if optim_tailcalls Tailcall.transf_program src = tgt):
      rtc (relate_single
             SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top)
          (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold total_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit TailcallproofC.sim_mod; i; esplits; eauto; ss.
      eapply Tailcallproof.transf_program_match; eauto.
  Qed.

End Tailcall.


Section Inlining.

  Require Import InliningproofC.
  Lemma Inlining_correct
        src tgt
        (TRANSF: Inlining.transf_program src = OK tgt):
      relate_single
        SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top
        (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold relate_single. exploit InliningproofC.sim_mod; i; esplits; eauto; ss.
    eapply Inliningproof.transf_program_match; eauto.
  Qed.

End Inlining.


Section Constprop.

  Require Import ConstpropproofC.
  Lemma Constprop_correct
        src tgt
        (TRANSF: total_if optim_constprop Constprop.transf_program src = tgt):
      rtc (relate_single
             SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach)
          (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold total_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit ConstpropproofC.sim_mod; i; esplits; eauto; ss.
      eapply Constpropproof.transf_program_match; eauto.
  Qed.

End Constprop.



Section Renumber1.

  Require RenumberproofC.
  Lemma Renumber1_correct
        src tgt
        (TRANSF: total_if optim_constprop Renumber.transf_program src = tgt):
      rtc (relate_single
             SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top)
          (RTLC.module src) (RTLC.module tgt)
  .
  Proof.
    unfold total_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit RenumberproofC.sim_mod; i; esplits; eauto; ss.
      eapply Renumberproof.transf_program_match; eauto.
  Qed.

End Renumber1.


Section CSE.

  Require CSEproofC.
  Lemma CSE_correct
        src tgt
        (TRANSF: partial_if optim_CSE CSE.transf_program src = OK tgt):
      rtc (relate_single
             SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach)
          (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold partial_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit CSEproofC.sim_mod; i; esplits; eauto; ss.
      eapply CSEproof.transf_program_match; eauto.
  Qed.

End CSE.


Section Deadcode.

  Require Import DeadcodeproofC.
  Lemma Deadcode_correct
        src tgt
        (TRANSF: partial_if optim_redundancy Deadcode.transf_program src = OK tgt):
      rtc (relate_single
             SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach)
          (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold partial_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit DeadcodeproofC.sim_mod; i; esplits; eauto; ss.
      eapply Deadcodeproof.transf_program_match; eauto.
  Qed.

End Deadcode.



Section Unreadglob.

  Require Import UnreadglobproofC.
  Lemma Unreadglob_correct
        src tgt
        (TRANSF: Unreadglob.transform_program src = OK tgt):
      relate_single
        SimSymbDropInv.SimMemInvTop SimSymbDropInv.SimSymbDropInv SoundTop.Top
        (RTLC.module src) (RTLC.module tgt).
  Proof.
    unfold relate_single. exploit UnreadglobproofC.sim_mod; i; esplits; eauto; ss.
    eapply Unreadglobproof.transf_program_match; eauto.
  Qed.

End Unreadglob.



Section Unusedglob.

  Require Import UnusedglobproofC.
  Lemma Unusedglob_correct
        src tgt
        (TRANSF: Unusedglob.transform_program src = OK tgt):
      relate_single
        SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top
        (RTLC.module src) (RTLC.module2 tgt).
  Proof.
    unfold relate_single. exploit UnusedglobproofC.sim_mod; i; esplits; eauto; ss.
    eapply Unusedglobproof.transf_program_match; eauto.
  Qed.

End Unusedglob.



Section Allocation.

  Require Import AllocproofC.
  Lemma Allocation_correct
        src tgt
        (TRANSF: Allocation.transf_program src = OK tgt):
      relate_single
        SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top
        (RTLC.module2 src) (LTLC.module tgt).
  Proof.
    unfold relate_single. exploit AllocproofC.sim_mod; i; esplits; eauto; ss.
    eapply Allocproof.transf_program_match; eauto.
  Qed.

End Allocation.



Section Tunneling.

  Require Import TunnelingproofC.
  Lemma Tunneling_correct
        src tgt
        (TRANSF: Tunneling.tunnel_program src = tgt):
      relate_single
        SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top
        (LTLC.module src) (LTLC.module tgt).
  Proof.
    unfold relate_single. exploit TunnelingproofC.sim_mod; eauto.
    { eapply Tunnelingproof.transf_program_match; eauto. }
    i. rewrite TRANSF in *. esplits; eauto; ss.
  Qed.

End Tunneling.



Section Linearize.

  Require Import LinearizeproofC.
  Lemma Linearize_correct
        src tgt
        (TRANSF: Linearize.transf_program src = OK tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (LTLC.module src) (LinearC.module tgt).
  Proof.
    unfold relate_single. exploit LinearizeproofC.sim_mod; i; esplits; eauto; ss.
    eapply Linearizeproof.transf_program_match; eauto.
  Qed.

End Linearize.



Section CleanupLabels.

  Require Import CleanupLabelsproofC.
  Lemma CleanupLabels_correct
        src tgt
        (TRANSF: CleanupLabels.transf_program src = tgt):
      relate_single
        SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top
        (LinearC.module src) (LinearC.module tgt).
  Proof.
    unfold relate_single. exploit CleanupLabelsproofC.sim_mod; eauto.
    { eapply CleanupLabelsproof.transf_program_match; eauto. }
    i. rewrite TRANSF in *. esplits; eauto; ss.
  Qed.

End CleanupLabels.



Section Debugvar.

  Require Import DebugvarproofC.
  Lemma Debugvar_correct
        src tgt
        (TRANSF: partial_if debug Debugvar.transf_program src = OK tgt):
      rtc (relate_single
             SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top)
        (LinearC.module src) (LinearC.module tgt).
  Proof.
    unfold partial_if in *. des_ifs; try refl.
    - apply rtc_once. unfold relate_single. exploit DebugvarproofC.sim_mod; i; esplits; eauto; ss.
      eapply Debugvarproof.transf_program_match; eauto.
  Qed.

End Debugvar.



Section Stacking.

  Require Import StackingproofC.

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
        (COMPILESUCCED: exists final_tgt, Asmgenproof.match_prog tgt final_tgt):
      relate_single
        SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top
        (LinearC.module src) (MachC.module tgt Asmgenproof0.return_address_offset).
  Proof.
    unfold relate_single. des. exploit StackingproofC.sim_mod; eauto.
    { eapply Asmgenproof.return_address_exists; eauto. }
    { ii. determ_tac return_address_offset_deterministic. }
    { eapply Stackingproof.transf_program_match; eauto. }
    i. esplits; eauto; ss.
  Qed.

End Stacking.




Section Asmgen.

  Require Import AsmgenproofC.
  Lemma Asmgen_correct
        src tgt
        (TRANSF: Asmgen.transf_program src = OK tgt):
      relate_single
        SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top
        (MachC.module src Asmgenproof0.return_address_offset) (AsmC.module tgt).
  Proof.
    unfold relate_single. exploit AsmgenproofC.sim_mod; i; esplits; eauto; ss.
    eapply Asmgenproof.transf_program_match; eauto.
  Qed.

End Asmgen.



(** Copied from Compiler.v, but without "SimplLocals.transf_program" **)
(** SimplLocals translate Clight1 into Clight2 and our source program is Clight2. **)
(** We chose Clight2 because VST uses Clight2. **)

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
   @@ print print_Clight
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.


Lemma compiler_single_rusc
      (src: Clight.program)
      (tgt: Asm.program)
      (TRANSF: transf_clight_program src = OK tgt):
    rusc CompCert_relations [src.(ClightC.module2)] [tgt.(AsmC.module)].
Proof.
  unfold transf_clight_program in *. unfold transf_cminor_program in *. unfold transf_rtl_program in *.
  unfold time in *. unfold print in *. cbn in *. unfold apply_total, apply_partial in *. des_ifs_safe.

  set (total_if optim_tailcalls Tailcall.transf_program p0) as ptail in *.
  set (Renumber.transf_program p10) as prenum0 in *.
  set (total_if optim_constprop Constprop.transf_program prenum0) as pconst in *.
  set (total_if optim_constprop Renumber.transf_program pconst) as prenum1 in *.
  set (Tunneling.tunnel_program p5) as ptunnel in *.
  set (CleanupLabels.transf_program p4) as pclean in *.

  Ltac next PASS_CORRECT :=
    etrans; [try (hexploit PASS_CORRECT; eauto;
                  [..|intros REL;
                   eapply (@relate_single_rtc_rusc) in REL; eauto;
                   unfold CompCert_relations; ss; eauto 10; fail]);
             (hexploit PASS_CORRECT; eauto;
              [..|intros REL;
               eapply (@relate_single_rusc) in REL; eauto;
               unfold CompCert_relations; ss; eauto 10])|].

  next Cshmgen_correct. next Cminorgen_correct. next Selection_correct. next RTLgen_correct.
  next Tailcall_correct. next Inlining_correct. next Renumber0_correct. next Constprop_correct.
  next Renumber1_correct. next CSE_correct. next Deadcode_correct. next Unreadglob_correct.
  next Unusedglob_correct. next Allocation_correct. next Tunneling_correct. next Linearize_correct.
  next CleanupLabels_correct. next Debugvar_correct. next Stacking_correct.
  { eexists. eapply transf_program_match; eauto. }
  next Asmgen_correct. refl.
Qed.

Lemma compiler_rusc
      (srcs: list Clight.program)
      (tgts: list Asm.program)
      (TR: mmap transf_clight_program srcs = OK tgts):
    rusc CompCert_relations (map ClightC.module2 srcs) (map AsmC.module tgts).
Proof.
  apply mmap_inversion in TR. revert tgts TR. induction srcs; ss; i; inv TR; try refl; ss.
  - replace (ClightC.module2 a :: map ClightC.module2 srcs) with
        ([ClightC.module2 a] ++ map ClightC.module2 srcs); auto.
    replace (AsmC.module b1 :: map AsmC.module bl) with
        ([AsmC.module b1] ++ map AsmC.module bl); auto.
    eapply rusc_horizontal; eauto.
    + eapply compiler_single_rusc; auto.
    + eapply clight_self_related.
    + eapply clights_self_related.
    + eapply asm_self_related.
    + eapply asms_self_related.
Qed.

Theorem compiler_correct
        (srcs: list Clight.program)
        (tgts hands: list Asm.program)
        (TR: mmap transf_clight_program srcs = OK tgts)
        ctx
        (SELF: self_related CompCert_relations ctx)
  :
    improves (sem ((map ClightC.module2 srcs) ++ (map AsmC.module hands) ++ ctx))
             (sem ((map AsmC.module tgts) ++ (map AsmC.module hands) ++ ctx)).
Proof.
  eapply rusc_adequacy_right_ctx.
  - eapply compiler_rusc; eauto.
  - eapply self_related_horizontal; eauto.
    eapply asms_self_related.
Qed.


(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)

(** Additionally, we support C as a source language too. **)


Lemma clightgen_rusc
      (srcs: list Csyntax.program)
      (tgts: list Clight.program)
      irs
      (TR0: mmap (SimplExpr.transl_program) srcs = OK irs)
      (TR1: mmap (SimplLocals.transf_program) irs = OK tgts)
  :
    rusc
      CompCert_relations
      (map CsemC.module srcs)
      (map ClightC.module2 tgts).
Proof.
  apply mmap_inversion in TR0. apply mmap_inversion in TR1. rewrite forall2_eq in *.

  transitivity (map (Mod.Atomic.trans <*> CstrategyC.module) srcs).
  { eapply rusc_incl.
    - eapply (relate_each_program SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
      eapply Forall2_apply_Forall2 with (P:=eq); eauto.
      + clear. induction srcs; eauto.
      + i. eapply Cstrategy_correct; eauto.
    - unfold CompCert_relations. ss. auto. }

  transitivity (map ClightC.module1 irs).
  { eapply rusc_incl.
    - eapply (relate_each_program SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
      eapply Forall2_apply_Forall2; eauto. i. eapply SimplExpr_correct; eauto.
    - unfold CompCert_relations. ss. auto. }

  { eapply rusc_incl.
    - eapply (relate_each_program SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top).
      eapply Forall2_apply_Forall2; eauto. i. eapply SimplLocals_correct; eauto.
    - unfold CompCert_relations. ss. auto 10. }
Qed.

Lemma clightgen_correct
      (srcs: list Csyntax.program)
      (cls tgts: list Clight.program)
      (hands: list Asm.program)
      irs
      (TR0: mmap (SimplExpr.transl_program) srcs = OK irs)
      (TR1: mmap (SimplLocals.transf_program) irs = OK tgts)
      ctx
      (SELF: self_related CompCert_relations ctx)
  :
    improves (sem ((map CsemC.module srcs) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands) ++ ctx))
             (sem ((map ClightC.module2 tgts) ++ (map ClightC.module2 cls) ++ (map AsmC.module hands) ++ ctx)).
Proof.
  eapply rusc_adequacy_right_ctx.
  - eapply clightgen_rusc; eauto.
  - eapply self_related_horizontal.
    + eapply clights_self_related.
    + eapply self_related_horizontal; eauto.
      eapply asms_self_related.
Qed.

Theorem compiler_correct_full
        (srcs0: list Csyntax.program)
        (srcs1: list Clight.program)
        (tgts0 tgts1 hands: list Asm.program)
        (TR0: mmap transf_c_program srcs0 = OK tgts0)
        (TR1: mmap transf_clight_program srcs1 = OK tgts1)
        ctx
        (SELF: self_related CompCert_relations ctx)
  :
    improves (sem ((map CsemC.module srcs0) ++ (map ClightC.module2 srcs1) ++ (map AsmC.module hands) ++ ctx))
             (sem ((map AsmC.module tgts0) ++ (map AsmC.module tgts1) ++ (map AsmC.module hands) ++ ctx)).
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
