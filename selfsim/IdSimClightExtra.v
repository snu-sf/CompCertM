Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
From compcertr Require Import Cop Ctypes.
Require Import ClightC.
Require Import AsmC.
Require SimMemInjInvC.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
From compcertr Require Import Events Integers Conventions.
Require Import Preservation.
Require Import LocationsC.
Require Import Conventions1C.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import StoreArguments.
Require Import AsmStepInj IntegersC.
Require Import Coq.Logic.PropExtensionality.
Require Import AsmExtra IdSimExtra IdSimAsmExtra IdSimInvExtra.

Require Import MatchSimModSem.
Require Import Conventions1C.

Require Import ClightStepInj.
Require Import IdSimExtra IdSimInvExtra.
Require Import mktac.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Lemma val_casted_inject val0 val1 j ty
      (VAL: Val.inject j val0 val1)
      (CAST: val_casted val0 ty):
    val_casted val1 ty.
Proof.
  inv CAST; inv VAL; clarify; try econs; eauto.
Qed.

Require Import CtypingC.
Require Import CopC.

Lemma typecheck_inject vals0 vals1 j ty
      (VALS: Val.inject_list j vals0 vals1)
      (TYP: typecheck vals0 ty):
    typecheck vals1 ty.
Proof.
  inv TYP. econs; eauto. clear - VALS TYP0.
  revert vals1 VALS TYP0. generalize (typelist_to_listtype ty).
  clear ty. induction vals0; ss; i; inv VALS; inv TYP0; econs.
  - eapply val_casted_inject; eauto.
  - eapply IHvals0; eauto.
Qed.

Lemma wt_retval_inject j v_src v_tgt ty
      (INJ: Val.inject j v_src v_tgt)
      (TYP: wt_retval v_tgt ty):
    wt_retval v_src ty.
Proof.
  inv TYP; inv WTV; inv INJ; clarify; try by repeat (econs; eauto).
Qed.

Lemma vals_casted_inject j vals_src vals_tgt tys
      (VALS: Val.inject_list j vals_src vals_tgt)
      (TYP: Forall2 val_casted vals_src tys):
    Forall2 val_casted vals_tgt tys.
Proof.
  ginduction vals_src; i.
  - inv VALS. inv TYP. econs.
  - inv VALS. inv TYP. econs; eauto. eapply val_casted_inject; eauto.
Qed.

Definition cgenv skenv_link clight :=
  Build_genv
    (SkEnv.revive (SkEnv.project skenv_link (CtypesC.CSk.of_program signature_of_function clight)) clight)
    (prog_comp_env clight).
