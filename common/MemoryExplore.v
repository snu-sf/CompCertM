Require Import Zwf.
Require Import Axioms.
Require Import CoqlibC.
Require Intv.
Require Import MapsC.
Require Archi.
Require Import ASTC.
Require Import Integers.
Require Import Floats.
Require Import ValuesC.
Require Export Memdata.
Require Export Memtype.
Require Import sflib.
Require Import Lia.
Require Import MemoryC.

Require Import Events.
Import Mem.
Local Notation "a # b" := (PMap.get b a) (at level 1).

Local Existing Instance Val.mi_normal.

Inductive mvs_lessdef (chunk: memory_chunk): list memval -> list memval -> Prop :=
| mvs_lessdef_eq
    mvs
  :
    mvs_lessdef chunk mvs mvs
| mvs_lessdef_broken
    mvs
  :
    mvs_lessdef chunk (list_repeat (size_chunk_nat chunk) Undef) mvs
| mvs_lessdef_undef
    mvs
  :
    mvs_lessdef chunk (inj_value chunk.(quantity_chunk) Vundef) mvs
  (* mvs_lessdef Many32 *)
  (* [Fragment Vundef Q32 3; Fragment Vundef Q32 2; Fragment Vundef Q32 1; Fragment Vundef Q32 0] *)
  (* [Byte i; Byte i0; Byte i1; Byte i2] *)
.

Lemma encode_decode_val
      chunk mvs
      (LENGTH: length mvs = (size_chunk_nat chunk))
  :
    mvs_lessdef chunk (encode_val chunk (decode_val chunk mvs)) mvs
.
Proof.
  pose chunk.
  unfold size_chunk_nat, nat_of_Z, size_chunk in *.
  destruct (proj_bytes mvs) eqn:T; cycle 1.
  { admit "one case does not hold - Fragment - Byte ". }
(* { unfold encode_val, decode_val. *)
(*     Ltac des_nat := match goal with *)
(*                     | [n: nat |- _] => destruct n; ss *)
(*                     end. *)
(*     Ltac des_outest_if := *)
(*       match goal with *)
(*       | [ H: context[match ?X with _ => _ end] |- _ ] => let name := fresh "NAME" in destruct X eqn:NAME *)
(*       end. *)
(*     Ltac simpl_true := *)
(*       match goal with *)
(*       | [ H: ?b0 && ?b1 = true |- _ ] => apply andb_true_iff in H; des *)
(*       end. *)
(*     des_ifs; ss; des_ifs; ss; try (econsby ss); *)
(*       unfold proj_value in *; des_ifs; ss. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). *)
(* (* mvs_lessdef Mint64 (inj_bytes (encode_int 8 (Int64.unsigned i))) *) *)
(* (*   [Fragment (Vlong i) Q64 7; Fragment (Vlong i) Q64 6; Fragment (Vlong i) Q64 5; Fragment (Vlong i) Q64 4; *) *)
(* (*   Fragment (Vlong i) Q64 3; Fragment (Vlong i) Q64 2; Fragment (Vlong i) Q64 1; Fragment (Vlong i) Q64 0] *) *)
(*       admit "raw admit!!!!!!!!!!!!!!!!!!!!!!". *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*     - repeat (des_outest_if; repeat (simpl_true); des_sumbool; clarify). econs; eauto. *)
(*   } *)
  
  exploit inj_proj_bytes; eauto. i; clarify.
  exploit length_proj_bytes; eauto. i; clarify.

  unfold encode_val, decode_val.
  Ltac des_list := match goal with
                   | [l: list byte |- _] => destruct l; ss
                   end.
  unfold inj_bytes in *.
  des_ifs; ss; try (econsby ss).
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
  - repeat (des_list; des_ifs; ss; []).
    admit "maybe true".
Qed.

Local Transparent Mem.store Mem.load.
Lemma Mem_load_store_extends
      m0 m1 chunk blk ofs v
      (LOAD: Mem.load chunk m0 blk ofs = Some v)
      (STORE: Mem.store chunk m0 blk ofs v = Some m1)
  :
    Mem.extends m1 m0
.
Proof.
  hexploit Mem_store_perm_iff; eauto. intro PERM.
  (* unfold load, store in *; ss. des_ifs; ss. *)

  assert(TY: Val.has_type v (type_of_chunk chunk)).
  { eapply Mem.load_type; eauto. }
  econs; eauto with mem.
  unfold inject_id.
  econs; ii; ss; clarify; eauto.
  - rewrite Z.add_0_r. eapply PERM; eauto.
  - apply Z.divide_0_r.
  - rewrite Z.add_0_r. apply PERM in H0. clear PERM.
    unfold load in *. des_ifs.
    unfold store in *. des_ifs; ss.
    rewrite PMap.gsspec. des_ifs; cycle 1.
    { destruct (ZMap.get ofs0 (mem_contents m0) # b2) eqn:T; econs; ss; eauto.
      apply val_inject_id. econs; eauto. }
    destruct (classic (ofs <= ofs0 < ofs +
Z.of_nat (length (encode_val chunk (decode_val chunk (getN (size_chunk_nat chunk) ofs (mem_contents m0) # blk)))))); cycle 1.
    { erewrite setN_outside; try xomega.
      destruct (ZMap.get ofs0 (mem_contents m0) # blk) eqn:T; econs; ss; eauto.
      apply val_inject_id. econs; eauto.
    }
    hexploit setN_in; eauto. instantiate (1:= (mem_contents m0) # blk).
    rewrite ! encode_val_length in *; rewrite <- ! size_chunk_conv in *.
    intro IN.
    set (encode_val chunk (decode_val chunk (getN (size_chunk_nat chunk) ofs (mem_contents m0) # blk)))
      as newv in *.
    set ((mem_contents m0) # blk) as contents in *.
    (* We should change memval_inject!!!!
  mvs_lessdef Many32
  [Fragment Vundef Q32 3; Fragment Vundef Q32 2; Fragment Vundef Q32 1; Fragment Vundef Q32 0]
  [Byte i; Byte i0; Byte i1; Byte i2]

mvs_lessdef Mint64 (inj_bytes (encode_int 8 (Int64.unsigned i)))
  [Fragment (Vlong i) Q64 7; Fragment (Vlong i) Q64 6; Fragment (Vlong i) Q64 5; Fragment (Vlong i) Q64 4;
  Fragment (Vlong i) Q64 3; Fragment (Vlong i) Q64 2; Fragment (Vlong i) Q64 1; Fragment (Vlong i) Q64 0]
*)
Abort.
Local Opaque Mem.store Mem.load.

(* m0 -store v-> m1 // m0 -load v-> m1' ===> m1' is better state than m1. (load is harder than store) *)
(* this should hold *)
Lemma Mem_store_left_inject
      j0 m_src0 m_src1 m_tgt
      (INJ: Mem.inject j0 m_src0 m_tgt)
      v_src v_tgt
      (INJV: Val.inject j0 v_src v_tgt) 
      ty rsp_src rsp_tgt rspdelta ofs
      (SRC: Mem.storev (chunk_of_type ty) m_src0 (Vptr rsp_src ofs true) v_src = Some m_src1)
      (TGT: Mem.loadv (chunk_of_type ty) m_tgt (Vptr rsp_tgt (Ptrofs.add ofs rspdelta) true) = Some v_tgt)
      (INJRSP: j0 rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned)))
  :
    <<INJ: Mem.inject j0 m_src1 m_tgt>>
.
Proof.
  unfold storev in *. des_ifs. ss.
  hexploit Mem_store_perm_eq; eauto. intro PERM.

  exploit store_mapped_inject; eauto. intro STORETGT; des.
  eapply inject_extends_compose; eauto.
  eapply Mem_load_store_extends; eauto.
  rpapply STORETGT. f_equal.
  rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; ss.
  admit "sz".
  Ptrofs.repr_unsigned:
  ss.
  { unfold loadv.
  eapply extends_inject_compose; eauto.
  assert(n2 = m_tgt).
  { clear - STORETGT TGT. admit "". }
  clarify.

  econs; try apply INJ; eauto.
  - econs; ii; try eapply INJ; ii; eauto with mem congruence.
    Local Transparent Mem.store. unfold Mem.store in *. des_ifs; ss.
    rewrite PMap.gsspec. des_ifs.
    + Local Transparent Mem.load. unfold Mem.load in *. des_ifs; ss.
      destruct (classic
                  (Ptrofs.unsigned ofs <= ofs0 <
                   Ptrofs.unsigned ofs + Z.of_nat (length (encode_val (chunk_of_type ty) v_src)))); cycle 1.
      { rewrite setN_outside; try omega. eapply INJ; eauto. }
      clear - INJV H H1. abstr (chunk_of_type ty) chnk.
      admit "this should hold".
Admitted.


End ARGPASSING.
