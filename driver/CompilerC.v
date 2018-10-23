(** Libraries. *)
Require Import String.
Require Import CoqlibC Errors.
Require Import AST Linking Smallstep.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy Cexec.
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
Require Import Behaviors.
Require Export Compiler.
Require Import Simulation.
Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.



Set Implicit Arguments.

Local Open Scope string_scope.
Local Open Scope list_scope.



Parameter C2R: Csyntax.program -> res RTL.program.
Parameter C2R_SM: SimMem.class.
Parameter C2R_SU: Sound.class.
Parameter C2R_SS: SimSymb.class C2R_SM.
Parameter C_module: Csyntax.program -> Mod.t.
Parameter C2R_sim_mod: forall
    src tgt
    (TRANSF: C2R src = OK tgt)
  ,
    exists ss,
      <<SIM: @ModPair.sim C2R_SM C2R_SS C2R_SU (ModPair.mk (C_module src) (RTLC.module tgt) ss)>>
.

Section C2R.

  Local Existing Instance C2R_SM.
  Local Existing Instance C2R_SU.
  Local Existing Instance C2R_SS.

  Variable cps: list ModPair.t.
  Variable aps: list ModPair.t.
  Hypothesis CSIM: Forall ModPair.sim cps.
  Hypothesis ASIM: Forall ModPair.sim aps.

  Lemma C2R_correct
        src tgt
        (TRANSF: C2R src = OK tgt)
    :
      backward_simulation (sem (cps.(ProgPair.src) ++ [C_module src] ++ aps.(ProgPair.src)))
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
Parameter R2A_SM: SimMem.class.
Parameter R2A_SU: Sound.class.
Parameter R2A_SS: SimSymb.class R2A_SM.
Parameter R2A_sim_mod: forall
    src tgt
    (TRANSF: R2A src = OK tgt)
  ,
    exists ss,
      <<SIM: @ModPair.sim R2A_SM R2A_SS R2A_SU (ModPair.mk (RTLC.module src) (AsmC.module tgt) ss)>>
.

Section R2A.

  Local Existing Instance R2A_SM.
  Local Existing Instance R2A_SU.
  Local Existing Instance R2A_SS.

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

Lemma backward_simulation_refl
      SEM
  :
    backward_simulation SEM SEM
.
Proof.
  eapply (@Backward_simulation _ _ unit bot2).
  econs; eauto.
  { admit "ez". }
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
  i. r in SAFESRC. specialize (SAFESRC st (star_refl _ _ _)). ss.
Qed.

From stdpp Require list.

Lemma rev_nil
      X (xs: list X)
      (NIL: rev xs = [])
  :
    xs = []
.
Proof.
  generalize (f_equal (@length _) NIL). i. ss.
  destruct xs; ss.
  rewrite app_length in *. ss. xomega.
Qed.

Lemma compiler_correct_single
        (src: Csyntax.program)
        (tgt: Asm.program)
        (cs: list Csyntax.program)
        (asms: list Asm.program)
        (TRANSF: transf_c_program src = OK tgt)
  :
    Smallstep.backward_simulation (sem ((map C_module cs) ++ [C_module src] ++ (map AsmC.module asms)))
                                  (sem ((map C_module cs) ++ [AsmC.module tgt] ++ (map AsmC.module asms)))
.
Proof.
  eapply compose_backward_simulation; eauto.
  idtac "SINGLE EVENTS!!!!".
Abort.

Definition improves (L1 L2: semantics): Prop := forall
    beh2
    (BEH: program_behaves L2 beh2)
  ,
    exists beh1, <<BEH: program_behaves L1 beh1>> /\ <<IMPRV: behavior_improves beh1 beh2>>
.

Global Program Instance improves_PreOrder: PreOrder improves.
Next Obligation.
  ii. esplits; eauto. eapply behavior_improves_refl.
Qed.
Next Obligation.
  ii. r in H. r in H0. repeat spc H0. des. specialize (H _ BEH0). des.
  esplits; eauto. eapply behavior_improves_trans; eauto.
Qed.

Lemma bsim_improves
      L1 L2
      (BSIM: backward_simulation L1 L2)
  :
    <<IMRPV: improves L1 L2>>
.
Proof.
  ii.
  eapply backward_simulation_behavior_improves; eauto.
  eapply backward_to_compcert_backward_simulation; eauto.
Qed.




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

Module IdSim.

  Lemma tgt_id_id_top
        (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma tgt_ext_id_top
        (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExtends SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma tgt_ext_id_unreach
        (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExtends SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = tgt.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = tgt.(AsmC.module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma src_id_id_top
        (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma src_ext_id_top
        (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExtends SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma src_ext_id_unreach
        (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExtends SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
  .
  Proof.
    admit "this should hold".
  Qed.

End IdSim.



Lemma compiler_correct_single
        (src: Csyntax.program)
        (tgt: Asm.program)
        (cs: list Csyntax.program)
        (asms: list Asm.program)
        (TRANSF: transf_c_program src = OK tgt)
  :
    improves (sem ((map C_module cs) ++ [C_module src] ++ (map AsmC.module asms)))
             (sem ((map C_module cs) ++ [AsmC.module tgt] ++ (map AsmC.module asms)))
.
Proof.
  unfold transf_c_program in *. unfold apply_total, apply_partial in *. des_ifs.

  assert(C2R_SM = SimMemId.SimMemId).
  { admit "somehow". }

  assert(exists cps, <<SRC: ProgPair.src cps = map C_module cs>> /\ <<SIM: ProgPair.sim cps>>).
  { admit "somehow". }
  des.
  assert(exists aps, <<SRC: ProgPair.src aps = map AsmC.module asms>> /\ <<SIM: ProgPair.sim aps>>).
  { admit "somehow". }
  des.

  etrans.
  {
    rewrite <- SRC. rewrite <- SRC0.
    eapply bsim_improves.
    rp; [eapply C2R_correct|..]; try eassumption; try reflexivity; revgoals.
    { Set Printing All. reflexivity.
    { rewrite SRC.
    Fail eapply C2R_correct. admit "pairing".
  }
  etrans.
  { eapply bsim_improves. admit "renumber". }
  admit "R2A".
Unshelve.
  all: admit "somehow".
Qed.


(**
Note: we can't vertically compose in simulation level, because
1) it requires maximal memory relation (closure)
2) single_events of tgt (which is not true)

induction: src/tgt length is fixed (we don't do horizontal composition in behavior level)
**)

(* Fixpoint last X (xs: list X): option X := *)
(*   match xs with *)
(*   | [] => None *)
(*   | [hd] => Some hd *)
(*   | hd :: tl => last tl *)
(*   end *)
(* . *)

Lemma last_none
      X (xs: list X)
      (NONE: list.last xs = None)
  :
    xs = []
.
Proof.
  ginduction xs; ii; ss.
  des_ifs. spc IHxs. ss.
Qed.

Lemma last_some
      X (xs: list X) x
      (SOME: list.last xs = Some x)
  :
    exists hds, xs = hds ++ [x]
.
Proof.
  ginduction xs; ii; ss.
  des_ifs.
  { exists nil. ss. }
  exploit IHxs; eauto. i; des.
  rewrite H. exists (a :: hds). ss.
Qed.

Lemma forall2_eq
      X Y (P: X -> Y -> Prop) xs ys
  :
    list_forall2 P xs ys <-> Forall2 P xs ys
.
Proof.
  split; i.
  - ginduction xs; ii; ss; inv H; ss; econs; eauto.
  - ginduction xs; ii; ss; inv H; ss; econs; eauto.
Qed.

Theorem compiler_correct
        (srcs: list Csyntax.program)
        (tgts hands: list Asm.program)
        (TR: mmap transf_c_program srcs = OK tgts)
  :
    improves (sem ((map C_module srcs) ++ (map AsmC.module hands)))
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

  destruct (list.last srcs) eqn:T2; cycle 1.
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





