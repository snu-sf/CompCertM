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
      (SOME: is_some (pr0.(to_mreg)))
      (EQ: pr0.(to_mreg) = pr1.(to_mreg))
  :
    <<EQ: pr0 = pr1>>
.
Proof.
  destruct pr0; ss; destruct pr1; ss; des_ifs.
Qed.

Lemma preg_of_injective
      mr0 mr1
      (EQ: preg_of mr0 = preg_of mr1)
  :
    <<EQ: mr0 = mr1>>
.
Proof. destruct mr0, mr1; ss. Qed.

Lemma to_mreg_to_preg
      pr0
  :
    o_map (pr0.(to_mreg)) (to_preg) = Some pr0 \/ pr0.(to_mreg) = None
.
Proof.
  destruct pr0; ss; des_ifs; eauto.
Qed.

Corollary to_mreg_some_to_preg
      pr0 mr0
      (SOME: pr0.(to_mreg) = Some mr0)
  :
    <<EQ: mr0.(to_preg) = pr0>>
.
Proof.
  eapply to_mreg_injective with (pr0 := mr0.(to_preg)) (pr1 := pr0).
  { rewrite to_preg_to_mreg; ss. }
  rewrite to_preg_to_mreg; ss.
Qed.

Definition to_pregset (mrs: Mach.regset): regset :=
  fun pr =>
    match pr.(to_mreg) with
    | Some mr => mrs mr
    | None => Vundef
    end
.

Definition to_mregset (prs: regset): Mach.regset :=
  fun mr => prs (to_preg mr)
.
