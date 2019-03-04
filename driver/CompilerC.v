(** Libraries. *)
Require Import String.
Require Import CoqlibC Errors.
Require Import AST Linking Smallstep.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax CsemC Cstrategy Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
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



Local Existing Instance Values.Val.mi_normal.

Parameter C2R: Csyntax.program -> res RTL.program.
(* Parameter C2R_SM: SimMem.class. *)
(* Parameter C2R_SU: Sound.class. *)
(* Parameter C2R_SS: SimSymb.class C2R_SM. *)
Parameter C2R_sim_mod: forall
    src tgt
    (TRANSF: C2R src = OK tgt)
  ,
    exists ss,
      <<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top (ModPair.mk (CsemC.module src) (RTLC.module tgt) ss)>>
.

Section C2R.

  (* Local Existing Instance C2R_SM. *)
  (* Local Existing Instance C2R_SU. *)
  (* Local Existing Instance C2R_SS. *)
  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimMemInjC.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma C2R_correct
        src tgt
        (TRANSF: C2R src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [CsemC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [RTLC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    eapply mixed_to_backward_simulation.
    exploit (C2R_sim_mod); eauto. i; des.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
    eauto.
  Qed.

End C2R.


Section Renumber.

  Require RenumberproofC.

  Local Existing Instance SimMemId.SimMemId | 0.
  Local Existing Instance SimMemId.SimSymbId | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Renumber_correct
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

End Renumber.



Section Deadcode.

  Require Import DeadcodeproofC.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma Deadcode_correct
        src tgt
        (TRANSF: Deadcode.transf_program src = OK tgt)
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
    eapply DeadcodeproofC.sim_mod; eauto.
    eapply Deadcodeproof.transf_program_match; eauto.
  Qed.

End Deadcode.



Parameter R2A: RTL.program -> res Asm.program.
Parameter R2A_sim_mod: forall
    src tgt
    (TRANSF: R2A src = OK tgt)
  ,
    exists ss,
      <<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top (ModPair.mk (RTLC.module src) (AsmC.module tgt) ss)>>
.

Section R2A.

  (* Local Existing Instance R2A_SM. *)
  (* Local Existing Instance R2A_SU. *)
  (* Local Existing Instance R2A_SS. *)
  Local Existing Instance SimMemInjC.SimMemInj | 0.
  Local Existing Instance SimSymbDrop.SimSymbDrop | 0.
  Local Existing Instance SoundTop.Top | 0.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma R2A_correct
        src tgt
        (TRANSF: R2A src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [RTLC.module src] ++ aps.(ProgPair.src)))
                          (sem (cps.(ProgPair.tgt) ++ [AsmC.module tgt] ++ aps.(ProgPair.tgt)))
  .
  Proof.
    eapply mixed_to_backward_simulation.
    exploit (R2A_sim_mod); eauto. i; des.
    rpapply adequacy_local; cycle 1.
    { instantiate (1:= _ ++ [ModPair.mk _ _ _] ++ _). ss. f_equal.
      u. rewrite map_app. ss.
    }
    { u. rewrite map_app. ss. }
    r. rewrite Forall_forall in *. ii.
    rewrite in_app_iff in *. des; eauto.
    rewrite in_app_iff in *. des; eauto.
    ss. des; ss. clarify.
    eauto.
  Qed.

End R2A.





























Let transf_c_program: Csyntax.program -> res Asm.program :=
  fun src => src.(C2R) @@ Renumber.transf_program @@@ Deadcode.transf_program @@@ R2A
.

(* TODO: this is not used, remove it *)
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





Module PLAYGROUND.

  Variable A B: Type.
  Variable EQ: A = B.
  Variable a0: A.
  Definition tmp: B.
    rewrite <- EQ. apply a0.
  Defined.
  Check a0.
  Check (eq_rect A (fun T : Type => T) a0 B EQ).
  Check (eq_rect A id a0 B EQ).
  Check (eq_rect _ id a0 B EQ).
  Check (eq_rect _ id a0 _ EQ).

  Variable a1: A.
  Variable M: A -> Type.
  Check M a0.
  Check M a1.

End PLAYGROUND.

(* Inductive world_cases (SM: SimMem.class): SimSymb.class SM -> Sound.class -> Prop := *)
(* | world_cases_id *)
(*     (EQ: SM = SimMemId.SimMemId) *)
(*   : *)
(*     world_cases (eq_rect _ id SimMemId.SimSymbId) SoundTop.Top *)
(* . *)

(* Inductive sm_cases: SimMem.class -> Prop := *)
(* | sm_cases_id: sm_cases SimMemId.SimMemId *)
(* | sm_cases_ext: sm_cases SimMemExt.SimMemExtends *)
(* . *)

(* Inductive ss_cases: SimSymb.class -> Prop := *)
(* | ss_cases_id: ss_cases SimMemId.SimSymbId *)
(* . *)





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
  unfold transf_c_program in *. unfold apply_total, apply_partial in *. des_ifs.

  (* assert(exists cps, <<SIM: ProgPair.sim cps>> /\ <<SRC: ProgPair.src cps = map C_module cs>>). *)
  (* { eapply IdSim.lift. *)
  (*   i. *)
  (*   eapply Morphisms_Prop.ex_impl_morphism_obligation_1; cycle 1. *)
  (*   { apply IdSim.src_inj_id. } *)
  (*   ii. des; eauto. *)
  (* } *)
  (* des. *)

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

  Ltac find_replacer := 
    repeat
      match goal with
      | [H0: ?L0 = ?R0, H1: ?L1 = ?R1 |- _ ] =>
        rewrite <- H0; rewrite <- H1; refl
      end
  .
  (* unfold C_module in *. *)

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply C2R_correct|..]; try refl; revgoals.
    { find_replacer. }
    all: eauto.
  }
  repeat all ltac:(fun H => rewrite H).

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Renumber_correct|..]; try refl; revgoals.
    { find_replacer. }
    all: eauto.
  }
  repeat all ltac:(fun H => rewrite H).
  
  etrans.
  {
    eapply bsim_improves.
    rp; [eapply Deadcode_correct|..]; try refl; revgoals.
    { find_replacer. }
    all: eauto.
  }
  repeat all ltac:(fun H => rewrite H).

  etrans.
  {
    eapply bsim_improves.
    rp; [eapply R2A_correct|..]; try refl; revgoals.
    { find_replacer. }
    all: eauto.
  }
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





