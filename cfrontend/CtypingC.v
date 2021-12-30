Require Import String.
Require Import CoqlibC.
From compcertr Require Import
     Maps Integers Floats Errors
     AST Linking
     Values Memory Globalenvs Events
     Cop Csyntax Csem
     sflib.
Require Import CtypesC ValuesC.
(** newly added **)
From compcertr Require Export Ctyping.
(* Require Import AxiomsC. *)

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Lemma wt_initial_frame
      (cp: Csyntax.program) fptr vs_arg m
      targs tres cconv
      (ge: genv)
      (INT: exists fd, Genv.find_funct ge fptr = Some (Internal fd))
      (WTLOCALS:
         forall fd, Genv.find_funct ge fptr = Some (Internal fd) ->
         Forall (fun t : type => wt_type ge t) (map snd (fn_params fd ++ fn_vars fd)))
      (* (WTARGS: list_forall2 Val.has_type vs_arg (typlist_of_typelist targs)) *)
      (WTARGS: Forall2 val_casted vs_arg (typelist_to_listtype targs))
      (NVOID: Forall (fun ty : type => ty <> Tvoid) (typelist_to_listtype targs)):
    wt_state cp ge (Csem.Callstate fptr (Tfunction targs tres cconv) vs_arg Kstop m).
Proof.
  des. econs; et; ss.
  - econs; et.
  - ii. exfalso. eapply EXT; et.
Qed.

Lemma wt_val_has_type
      v ty
      (WT: wt_val v ty)
      (NVOID: ty <> Tvoid):
    <<TY: Val.has_type v (typ_of_type ty)>>.
Proof. inv WT; ss. Qed.

Lemma wt_retval_has_type
      v ty
      (WT: wt_retval v ty):
    <<TY: Val.has_type v (typ_of_type ty)>>.
Proof. inv WT; ss. inv WTV; ss. erewrite NVOID; ss. Qed.

Lemma wt_retval_has_rettype:
  forall v ty,
  wt_retval v ty -> Val.has_rettype v (rettype_of_type ty).
Proof.
  i. inv H. destruct ty; subst; ss.
  - inv WTV; ss; destruct i; destruct s; ss.
  - inv WTV; ss; destruct i; destruct s; ss.
  - inv WTV; ss; destruct f; ss.
  - inv WTV; ss.
Qed.

Lemma has_rettype_wt_retval:
  forall v ty,
    Val.has_rettype v (rettype_of_type ty) -> wt_retval v ty.
Proof.
  econs.
  - eapply has_rettype_wt_val; et.
  - destruct ty; ss; destruct v; ss.
Qed.

Lemma rettypify_wt_ret_val
      v ty:
  wt_retval (rettypify v (rettype_of_type ty)) ty.
Proof.
  unfold rettypify. des_ifs.
  - econs.
    + eapply has_rettype_wt_val; et.
    + destruct ty; ss; destruct v; ss.
  - econs; ss.
    + econs.
    + destruct ty; ss.
Qed.
