Require Import CoqlibC.
Require Import ASTC.
Require Import LocationsC.
Require Export Conventions1.
(* newly added *)
Require Export Conventions.

Local Opaque Z.add Z.mul Z.divide list_nth_z.
Lemma tailcall_size_aux
      tys ir fr
      (TAIL: forall l,
          In l (regs_of_rpairs (loc_arguments_64 tys ir fr 0)) ->
          match l with
          | R _ => True
          | S _ _ _ => False
          end)
      (IRBOUND: (ir - 1) < list_length_z int_param_regs)
      (FRBOUND: (fr - 1) < list_length_z float_param_regs)
  :
    <<SZ: size_arguments_64 tys ir fr 0 = 0>>
.
Proof.
  ginduction tys; ii; ss.
  destruct a; des_ifs; ss;
    try (by exploit TAIL; eauto; ss);
    (eapply IHtys; eauto;
     [ii; des_ifs; []; exploit TAIL; eauto
     |rewrite Z.add_simpl_r; apply list_nth_z_range in Heq; xomega]).
Qed.

Lemma tailcall_size
      sg
      (TAIL: tailcall_possible sg)
  :
    size_arguments sg = 0
.
Proof.
  eapply tailcall_size_aux; eauto; cbn; xomega.
Qed.

Definition agree_callee_save_regs (ls1 ls2: Locmap.t) : Prop :=
  forall r, is_callee_save r -> ls1 (R r) = ls2 (R r).

