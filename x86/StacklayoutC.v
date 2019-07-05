Require Import CoqlibC.
Require Import AST Memory Separation.
Require Import Bounds.

Local Open Scope sep_scope.
(** newly added **)
Require Export Stacklayout.
Require Import Lia.


Local Opaque Z.add Z.mul.

Lemma bound_outgoing_stack_data: forall b,
   (4 * bound_outgoing b <= fe_stack_data (make_env b)).
Proof.
  Local Transparent make_env.
  ss.
  Local Opaque make_env.
  des_ifs. etrans; cycle 1.
  { eapply align_le; eauto. lia. }
  etrans; cycle 1.
  { generalize (bound_local_pos b); i.
    instantiate (1:= align (size_callee_save_area b (align (4 * bound_outgoing b) 8 + 8)) 8).
    lia.
  }
  etrans; cycle 1.
  { eapply align_le; eauto. lia. }
  etrans; cycle 1.
  { eapply size_callee_save_area_incr. }
  etrans; cycle 1.
  { instantiate (1:= align (4 * bound_outgoing b) 8). lia. }
  eapply align_le; eauto. lia.
Qed.

