Require Import String.
Require Import CoqlibC Maps Integers Floats Errors.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import CtypesC Cop Csyntax Csem.
Require Import sflib.
(** newly added **)
Require Export Ctyping.
Require Import Skeleton.
(* Require Import AxiomsC. *)

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Inductive typify_c (v: val) (ty: type): val -> Prop :=
| typify_c_ok
    (WT: wt_retval v ty)
  :
    typify_c v ty v
| typify_c_no
    (NWT: ~ wt_retval v ty)
  :
    typify_c v ty Vundef
.

Lemma typify_c_dtm
      v ty tv0 tv1
      (TY0: typify_c v ty tv0)
      (TY1: typify_c v ty tv1)
  :
    tv0 = tv1
.
Proof.
  inv TY0; inv TY1; des; ss.
Qed.

Lemma typify_c_ex
      v ty
  :
    exists tv, <<TYP: typify_c v ty tv>>
.
Proof.
  destruct (classic (wt_retval v ty)).
  - esplits; econs 1; eauto.
  - esplits; econs 2; eauto.
Qed.

Lemma typify_c_spec
      v ty tv
      (TY: typify_c v ty tv)
  :
    <<WT: wt_retval tv ty>>
.
Proof.
  inv TY; des; ss.
  split.
  - econs.
  - reflexivity.
Qed.

Lemma wt_initial_frame
      (cp: Csyntax.program) fptr vs_arg m
      targs tres cconv
      (ge: genv)
      (INT: exists fd, Genv.find_funct ge fptr = Some (Internal fd))
      (* (WTARGS: list_forall2 Val.has_type vs_arg (typlist_of_typelist targs)) *)
      (WTARGS: Forall2 val_casted vs_arg (typelist_to_listtype targs))
      (NVOID: Forall (fun ty : type => ty <> Tvoid) (typelist_to_listtype targs))
  :
    wt_state ge (Csem.Callstate fptr (Tfunction targs tres cconv) vs_arg Kstop m)
.
Proof.
  des.
  econs; et; ss.
  - econs; et.
  - ii. exfalso. eapply EXT; et.
Qed.

Lemma wt_val_has_type
      v ty
      (WT: wt_val v ty)
      (NVOID: ty <> Tvoid)
  :
    <<TY: Val.has_type v ty.(typ_of_type)>>
.
Proof.
  inv WT; ss.
Qed.

Lemma wt_retval_has_type
      v ty
      (WT: wt_retval v ty)
  :
    <<TY: Val.has_type v ty.(typ_of_type)>>
.
Proof.
  inv WT; ss. inv WTV; ss. erewrite NVOID; ss.
Qed.
