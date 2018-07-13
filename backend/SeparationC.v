Require Import Setoid Program.Basics.
Require Import CoqlibC Decidableplus.
Require Import AST Integers Values Memory Events Globalenvs.
(** newly added **)
Require Export Separation.

Local Open Scope sep_scope.




Section INJ.

Context `{Val.meminj_ctx}.

Lemma separation_private
      m_src m_tgt F P
      (MATCH: m_tgt |= P ** minjection F m_src)
  :
     P.(m_footprint) <2= loc_out_of_reach F m_src
.
Proof.
  inv MATCH. des; ss.
  ii. unfold disjoint_footprint in *. ss.
  eapply H2; eauto.
Qed.

End INJ.

