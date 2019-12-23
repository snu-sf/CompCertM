Require Import CoqlibC Maps.
Require Import ValuesC.
Require Import LocationsC Stacklayout Conventions.
Require Import MemoryC Integers AST.
(** newly added **)
Require Import Asm.
Require Import Locations.
Require Mach.

Set Implicit Arguments.

Lemma to_mreg_injective
      pr0 pr1
      (SOME: is_some ((to_mreg pr0)))
      (EQ: (to_mreg pr0) = (to_mreg pr1)):
    <<EQ: pr0 = pr1>>.
Proof. destruct pr0; ss; destruct pr1; ss; des_ifs. Qed.

Lemma preg_of_injective
      mr0 mr1
      (EQ: preg_of mr0 = preg_of mr1):
    <<EQ: mr0 = mr1>>.
Proof. destruct mr0, mr1; ss. Qed.

Lemma to_mreg_to_preg: forall pr0,
    o_map ((to_mreg pr0)) (to_preg) = Some pr0 \/ (to_mreg pr0) = None.
Proof. destruct pr0; ss; des_ifs; eauto. Qed.

Corollary to_mreg_some_to_preg
      pr0 mr0
      (SOME: (to_mreg pr0) = Some mr0):
    <<EQ: (to_preg mr0) = pr0>>.
Proof.
  eapply to_mreg_injective with (pr0 := (to_preg mr0)) (pr1 := pr0).
  { rewrite to_preg_to_mreg; ss. }
  rewrite to_preg_to_mreg; ss.
Qed.

Definition to_pregset (mrs: Mach.regset): regset :=
  fun pr =>
    match (to_mreg pr) with
    | Some mr => mrs mr
    | None => Vundef
    end.

Definition to_mregset (prs: regset): Mach.regset :=
  fun mr => prs (to_preg mr).

Lemma to_mreg_preg_of
      pr mr
      (MR: Asm.to_mreg pr = Some mr):
    <<PR: preg_of mr = pr>>.
Proof. destruct mr, pr; ss; des_ifs. Qed.
