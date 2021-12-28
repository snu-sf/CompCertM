From compcertr Require Import
     Coqlib
     AST
     Integers
     Floats
     Values
     Memdata.
From compcert Require Archi.

Require Import CoqlibC.


Ltac my_tac :=
  match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] =>
    let name := fresh "A" in destruct x eqn:name; ss; subst;
                             try rewrite andb_true_iff in *; des; des_sumbool; subst
  end.

Lemma proj_bytes_only_bytes
      mvs bts
      (PROJ: proj_bytes mvs = Some bts):
    forall mv (IN: In mv mvs), exists bt, mv = Byte bt.
Proof.
  ginduction mvs; ii; ss. des_ifs. des; clarify; ss; eauto.
Qed.

Lemma decode_fragment_all chunk vl v mv q n
      (DECODE: decode_val chunk vl = v)
      (IN: In (Fragment mv q n) vl)
      (VALUE: v <> Vundef):
    mv = v.
Proof.
  unfold decode_val in *.
  destruct (proj_bytes vl) eqn:T.
  { hexploit proj_bytes_only_bytes; eauto. i; des. clarify. }
  clear T. sguard in IN. destruct chunk; ss; des_ifs; clear_tac; destruct vl; ss; repeat my_tac; unsguard IN; des; clarify.
Qed.

Lemma decode_normal_all_normal chunk vl v mv
      (DECODE: decode_val chunk vl = v)
      (VALUE: v <> Vundef /\ forall blk ofs, v <> Vptr blk ofs)
      (IN: In mv vl):
    forall blk ofs q n, mv <> Fragment (Vptr blk ofs) q n.
Proof.
  ii. des. rewrite H in *.
  destruct v; ss; exploit decode_fragment_all; eauto; i; clarify.
  - exfalso. eapply VALUE0. eauto.
Qed.

Lemma decode_pointer_all_pointer chunk vl mv blk ofs
      (DECODE: decode_val chunk vl = Vptr blk ofs)
      (IN: In mv vl):
    exists q n, mv = Fragment (Vptr blk ofs) q n.
Proof.
  unfold decode_val, Val.load_result in *. des_ifs; unfold proj_value in *; des_ifs;
      repeat (repeat (apply_all_once andb_prop; des); des_sumbool; clarify; des_ifs_safe; ss; des; ss; clarify); eauto; des_ifs.
Qed.

Program Instance memval_inject_Reflexive: RelationClasses.Reflexive (@memval_inject inject_id).
Next Obligation.
  destruct x; ss; econs; eauto. apply val_inject_id. ss.
Qed.
