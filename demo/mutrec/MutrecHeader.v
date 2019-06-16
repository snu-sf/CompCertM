Require Import IntegersC.
Require Import CoqlibC.
Require Import Zwf.
Require Coq.Program.Wf.
Require Import Recdef.
Require Import Intv.
Require Import AxiomsC.

Definition main_id := (77%positive).
Definition f_id := (154%positive).
Definition g_id := (176%positive).
(* Definition MAX: Z := 100%Z. *)

Definition sum (i: int): int :=
  let sumz: Z := fold_rec Z Z.add 0%Z 0%Z (i.(Int.intval) + 1)%Z in
  Int.repr sumz
.

Lemma eta
      i iproof j jproof
      (EQ: i = j)
  :
    Int.mkint i iproof = Int.mkint j jproof
.
Proof.
  clarify.
  assert(iproof = jproof).
  { eapply proof_irr. }
  clarify.
Qed.

(* Local Transparent Int.repr. *)
Lemma sum_recurse
      i
  :
    (sum i) = if Z.eqb i.(Int.intval) 0%Z then Int.zero else Int.add (sum (Int.sub i Int.one)) i 
.
Proof.
  des_ifs.
  - apply Z.eqb_eq in Heq. destruct i; ss. clarify. unfold sum. ss.
    rewrite fold_rec_equation. des_ifs. zsimpl. rewrite fold_rec_equation. des_ifs.
  - destruct i; ss. apply Z.eqb_neq in Heq.
    assert(intval >= 1) by xomega.
    unfold Int.sub. ss.
    unfold sum at 1.
    rewrite fold_rec_equation. ss. des_ifs; try xomega.
    assert(exists j, j.(Int.intval) = intval - 1).
    { unshelve eexists (Int.mkint _ _); simpl; try reflexivity.
      xomega.
    }
    des.
    rewrite Int.unsigned_one.
    unfold sum.
    assert(MOD0: Int.Z_mod_modulus intval = intval).
    { rewrite Int.Z_mod_modulus_eq.
      symmetry. eapply Z.mod_unique_pos with (q := 0%Z); try xomega.
    }
    assert(MOD1: Int.Z_mod_modulus (intval - 1) = intval - 1).
    { rewrite Int.Z_mod_modulus_eq.
      symmetry. eapply Z.mod_unique_pos with (q := 0%Z); try xomega.
    }
    replace {| Int.intval := intval; Int.intrange := conj intrange intrange0 |} with
        (Int.repr intval); cycle 1.
    { Local Transparent Int.repr.
      eapply eta.
      Local Opaque Int.repr.
      ss.
    }
    rewrite Int.Ptrofs_add_repr.
    f_equal.
    zsimpl.
    rewrite Z.add_comm. f_equal. f_equal.
    Local Transparent Int.repr.
    ss.
    Local Opaque Int.repr.
    rewrite MOD1. lia.
Qed.

(* Function elements_rec (lo hi: Z) {wf (Zwf lo) hi} : list Z := *)
(*   if zlt lo hi then (hi - 1)%Z :: elements_rec lo (hi - 1) else nil. *)
(* Proof. *)
(*   intros. red. omega. *)
(*   apply Zwf_well_founded. *)
(* Qed. *)

(* Function sum (i: int): int := *)
(*   m *)
(* Fixpoint sum (i: int): int := *)
(*   i.(intval) *)
(* . *)
