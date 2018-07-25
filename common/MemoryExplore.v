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
Local Notation "a # b" := (PMap.get b a) (at level 1).














Section STORED.

Inductive Mem_stored (chunk: memory_chunk) (m0: mem) (b: block) (ofs: Z) (v: val): Prop :=
| stored_intro
    (STORED: (Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b m0.(Mem.mem_contents)))
             = (encode_val chunk v))
    (WRITABLE: Mem.valid_access m0 chunk b ofs Writable)
.

Definition Mem_storedv chunk m addr v: Prop :=
  match addr with
  | Vptr b ofs true => Mem_stored chunk m b (Ptrofs.unsigned ofs) v
  | _ => False
  end
.

Theorem Mem_store_stored
        chunk m0 b ofs v m1
        (STORE: Mem.store chunk m0 b ofs v = Some m1)
  :
    <<STORED: Mem_stored chunk m1 b ofs v>>
.
Proof.
  econs; eauto with mem.
  erewrite Mem.store_mem_contents; eauto.
  rewrite Maps.PMap.gsspec. des_ifs.
  erewrite <- encode_val_length; eauto.
  rewrite Mem.getN_setN_same. ss.
Qed.

(* Local Transparent Mem.load. *)
(* Lemma Mem_stored_load *)
(*       chunk m0 b ofs v *)
(*       (STORE: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     <<LOAD: Mem.load chunk m0 b ofs = Some v>> *)
(* . *)
(* Proof. *)
(*   inv STORE. *)
(*   unfold Mem.load. des_ifs; cycle 1. *)
(*   { exfalso. eapply n. eauto with mem. } *)
(*   red. f_equal. *)
(*   destruct chunk; ss; des_ifs. *)
(*   - unfold encode_val in *. *)
(*   destruct chunk; ss. *)
(*   - unfold Maps.PMap.get. des_ifs. econs; eauto. *)
(* Qed. *)
(* Local Opaque Mem.load. *)

(* Local Transparent Mem.store. *)

(* Definition ZMap_equal {X} (eqX: X -> X -> Prop) (EQUIV: RelationClasses.Equivalence eqX) *)
(*            (zm0 zm1: Maps.ZMap.t X): Prop := *)
(*   zm0.(fst) = zm1.(fst) /\ Maps.PTree_Properties.Equal EQUIV zm0.(snd) zm1.(snd) *)
(* . *)

(* Inductive Mem_equal (m0 m1: mem): Prop := *)
(* | equal_intro *)
(*       (EQ0: m0.(Mem.mem_contents).(fst) = m1.(Mem.mem_contents).(fst)) *)
(*       (EQ1: @Maps.PTree_Properties.Equal _ (ZMap_equal eq (@Eqsth _)) *)
(*                                          (admit "") *)
(*                                          m0.(Mem.mem_contents).(snd) m1.(Mem.mem_contents).(snd)) *)
(*       (EQ2: m0.(Mem.mem_access) = m1.(Mem.mem_access)) *)
(*       (EQ3: m0.(Mem.nextblock) = m1.(Mem.nextblock)) *)
(* . *)

(* Theorem Mem_stored_store *)
(*         chunk m0 b ofs v *)
(*         (STORED: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     exists m1, <<STORE: Mem.store chunk m0 b ofs v = Some m1>> /\ *)
(*                         <<EQUIV: Mem_equal m0 m1>> *)
(* . *)
(* Proof. *)
(*   inv STORED. *)
(*   unfold Mem.store. des_ifs. destruct m0; ss. *)
(*   esplits; eauto. *)
(*   econs; eauto. cbn. *)
(*   destruct mem_contents; ss. *)
(*   hnf. ii; ss. *)
(*   destruct (Maps.PTree.get x t0) eqn:T. *)
(*   - rewrite Maps.PTree.gsspec. rewrite T. *)
(*     unfold Maps.PMap.get in *. ss. des_ifs; try reflexivity. *)
(*     econs; ss. *)
(*     { rewrite Mem.setN_default. ss. } *)
(*     hnf. ii. *)
(*     destruct (Maps.PTree.get x (snd t1)) eqn:U. *)
(*     + *)
(*     des_ifs. *)
(*     rewrite <- STORED0. erewrite <- encode_val_length with (v:=v); eauto. *)
(*     rewrite Mem.getN_setN_same. ss. *)
(*     econs; eauto. *)
(*   unfold Maps.PMap.set. ss. f_equal. *)
(*   Maps.PTree_Properties.Equal *)
(*   assert(forall i, Maps.PTree.set b (Mem.setN (encode_val chunk v) ofs (Maps.PMap.get b (t, t0))) t0 *)
(*   rewrite Maps.PTree.gsspec. *)
(*   eapply Axioms.functional_extensionality. *)
(*   cbn. *)
(*   Set Printing All. *)
(*   rewrite Maps.PMap.gsspec. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(*   econs; eauto. *)
(*   econs; eauto with mem. *)
(*   erewrite Mem.store_mem_contents; eauto. *)
(*   rewrite Maps.PMap.gsspec. des_ifs. *)
(*   erewrite <- encode_val_length; eauto. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(* Qed. *)


(* Lemma Mem_equal_proof_irr *)
(*       m0 m1 *)
(*       (EQ0: m0.(Mem.mem_contents) = m1.(Mem.mem_contents)) *)
(*       (EQ1: m0.(Mem.mem_access) = m1.(Mem.mem_access)) *)
(*       (EQ2: m0.(Mem.nextblock) = m1.(Mem.nextblock)) *)
(*   : *)
(*     m0 = m1 *)
(* . *)
(* Proof. *)
(*   destruct m0, m1; ss. clarify. *)
(*   f_equal; eapply Axioms.proof_irr. *)
(* Qed. *)

(* Theorem Mem_stored_store *)
(*         chunk m0 b ofs v *)
(*         (STORED: Mem_stored chunk m0 b ofs v) *)
(*   : *)
(*     exists m1, <<STORE: Mem.store chunk m0 b ofs v = Some m1>> /\ *)
(*                         <<EQUIV: m0 = m1>> *)
(* . *)
(* Proof. *)
(*   inv STORED. *)
(*   unfold Mem.store. des_ifs. destruct m0; ss. *)
(*   esplits; eauto. cbn. *)
(*   f_equal. eapply Mem_equal_proof_irr; eauto. *)
(*   ss. *)
(*   destruct mem_contents; ss. *)
(*   unfold Maps.PMap.set. ss. f_equal. *)
(*   Maps.PTree_Properties.Equal *)
(*   assert(forall i, Maps.PTree.set b (Mem.setN (encode_val chunk v) ofs (Maps.PMap.get b (t, t0))) t0 *)
(*   rewrite Maps.PTree.gsspec. *)
(*   eapply Axioms.functional_extensionality. *)
(*   cbn. *)
(*   Set Printing All. *)
(*   rewrite Maps.PMap.gsspec. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(*   econs; eauto. *)
(*   econs; eauto with mem. *)
(*   erewrite Mem.store_mem_contents; eauto. *)
(*   rewrite Maps.PMap.gsspec. des_ifs. *)
(*   erewrite <- encode_val_length; eauto. *)
(*   rewrite Mem.getN_setN_same. ss. *)
(* Qed. *)


Context `{CTX: Val.meminj_ctx}.

Lemma memval_inject_refl
      mv
  :
    @memval_inject Val.mi_normal (fun b0 : block => Some (b0, 0)) mv mv
.
Proof.
  destruct mv; ss; econs; eauto.
  apply val_inject_id. ss.
Qed.

Lemma store_stored_extends
      m0 m1
      chunk rsp pos v
      (STORED: Mem_stored chunk m0 rsp pos v)
      (STORE: Mem.store chunk m0 rsp pos v = Some m1)
  :
    <<EXTENDS: Mem.extends m1 m0>>
.
Proof.
Local Transparent Mem.store.
  hexploit Mem_store_perm_eq; eauto. intro PERM. des.
  unfold Mem.store in *. inv STORE. des_ifs.
  econs; eauto.
  unfold inject_id.
  econs; ss; eauto.
  - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss.
  - ii; clarify. unfold Mem.range_perm, Mem.perm in *. ss. rewrite Z.divide_0_r. reflexivity.
  - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss.
    rewrite Maps.PMap.gsspec. des_ifs; cycle 1.
    { apply memval_inject_refl. }
    inv STORED.
    rewrite <- STORED0.
    destruct chunk; ss; rewrite ! Maps.ZMap.gsspec; des_ifs; try apply memval_inject_refl.
Local Opaque Mem.store.
Qed.

Lemma store_stored_inject
      j0 m_src0 m_src1 m_tgt
      (INJ: Mem.inject j0 m_src0 m_tgt)
      v_src v_tgt
      (INJV: Val.inject j0 v_src v_tgt) 
      ty rsp_src rsp_tgt rspdelta ofs
      (SRC: Mem.storev (chunk_of_type ty) m_src0 (Vptr rsp_src ofs true) v_src = Some m_src1)
      (TGT: Mem_stored (chunk_of_type ty) m_tgt rsp_tgt (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) v_tgt)
      (INJRSP: j0 rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned)))
      (BOUND: Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta <= Ptrofs.max_unsigned)
  :
    <<INJ: Mem.inject j0 m_src1 m_tgt>>
.
Proof.
  ss. red.
  exploit Mem.store_mapped_inject; eauto. i; des.
  eapply Mem.inject_extends_compose; eauto.
  eapply store_stored_extends; try apply SRC; eauto.
  rpapply H. f_equal.
  rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; ss. split; try xomega.
  hexploit (Ptrofs.unsigned_range ofs); eauto. i.
  hexploit (Ptrofs.unsigned_range rspdelta); eauto. i.
  xomega.
Qed.

Lemma Mem_stored_unchanged_on
      P m0 m1
      (UNCH: Mem.unchanged_on P m0 m1)
      b ofs v chunk
      (INSIDE: forall i : Z, ofs <= i < ofs + size_chunk chunk -> P b i)
      (STORED: Mem_stored chunk m0 b ofs v)
  :
    <<STORED: Mem_stored chunk m1 b ofs v>>
.
Proof.
  inv UNCH.
  inv STORED. econs; eauto.
  - erewrite <- STORED0.
    unfold Mem.valid_access in *. ss. des; ss.
    apply Mem.range_perm_implies with (p2:= Readable) in WRITABLE; eauto with mem.
    destruct chunk; ss; rewrite ! unchanged_on_contents; eauto with lia.
  - hnf in WRITABLE. des.
    hnf. splits; eauto. ii. eapply unchanged_on_perm; eauto.
    eauto with mem.
Qed.



Goal forall ty, type_of_chunk (chunk_of_type ty) = ty.
Proof. i; destruct ty; ss. Qed.

Goal forall chunk, (chunk_of_type (type_of_chunk chunk)) = chunk.
Proof. i. destruct chunk; ss. Abort.

Lemma float32_eq
      f0 f1
      (EQ: Float32.to_bits f0 = Float32.to_bits f1)
  :
    f0 = f1
.
Proof.
  rewrite <- Float32.of_to_bits. symmetry. rewrite <- Float32.of_to_bits.
  rewrite EQ. ss.
Qed.

Lemma float_eq
      f0 f1
      (EQ: Float.to_bits f0 = Float.to_bits f1)
  :
    f0 = f1
.
Proof.
  rewrite <- Float.of_to_bits. symmetry. rewrite <- Float.of_to_bits.
  rewrite EQ. ss.
Qed.

Lemma mod_eq
      x y
      A
      (EQ0: x mod A = y mod A)
      (EQ1: x / A = y / A)
      (BOUND: 0 < A)
  :
    x = y
.
Proof.
  des. try lia. try xomega.
  rewrite Z_div_mod_eq with (b:=A); try lia.
  symmetry.
  rewrite Z_div_mod_eq with (b:=A); try lia.
  congruence.
Qed.

Lemma Mem_stored_dtm
      ty m b ofs v0 v1
      (* (TY0: Val.has_type v0 ty) *)
      (* (TY1: Val.has_type v1 ty) *)
      (WELLDEF0: ~ In Undef (encode_val (chunk_of_type ty) v0))
      (WELLDEF1: ~ In Undef (encode_val (chunk_of_type ty) v0))
      (STORED0: Mem_stored (chunk_of_type ty) m b ofs v0)
      (STORED1: Mem_stored (chunk_of_type ty) m b ofs v1)
  :
    v0 = v1
.
Proof.
Local Transparent Byte.repr.
  inv STORED0. inv STORED1.
  clear WRITABLE WRITABLE0.
  clear_tac.
  rewrite STORED in *. clear STORED. clear_tac.
  unfold encode_val in *; ss.
  pose v0 as X. pose v1 as Y. pose ty as TY.
  unfold inj_bytes, encode_int, rev_if_be in *.
  destruct Archi.big_endian eqn:T; ss.
  assert(BYTE: Byte.modulus = 256).
  { unfold Byte.modulus in *. unfold Byte.wordsize. ss. }
  destruct ty; ss.
  - des_ifs; ss; try (by exfalso; eauto).
    unfold Byte.repr in *. ss. clarify.
    f_equal.
    destruct i, i0; ss.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    eapply Int.mkint_eq.
    { unfold Int.modulus in *. unfold two_power_nat in *. ss.
      do 4 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    apply float_eq.
    abstr (Float.to_bits f) F0.
    abstr (Float.to_bits f0) F1.
    destruct F0, F1; ss.
    eapply Int64.mkint_eq.
    { unfold Int64.modulus in *. unfold two_power_nat in *. ss.
      do 8 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    destruct i, i0; ss.
    eapply Int64.mkint_eq.
    { unfold Int64.modulus in *. unfold two_power_nat in *. ss.
      do 8 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs; ss; try (by exfalso; eauto).
    f_equal.
    rewrite ! Byte.Z_mod_modulus_eq in *.
    rewrite BYTE in *.
    apply float32_eq.
    abstr (Float32.to_bits f) F0.
    abstr (Float32.to_bits f0) F1.
    destruct F0, F1; ss.
    eapply Int.mkint_eq.
    { unfold Int.modulus in *. unfold two_power_nat in *. ss.
      do 4 (eapply mod_eq with (A:=256); try xomega).
      rewrite ! Zdiv.Zdiv_Zdiv; try xomega. ss.
      rewrite ! Z.div_small; xomega.
    }
  - des_ifs.
  - des_ifs.
Qed.

End STORED.














Program Definition Mem_drop_perm_none (m: mem) (b: block) (lo hi: Z): mem :=
  (Mem.mkmem m.(Mem.mem_contents)
                 (PMap.set b
                           (fun ofs k =>
                              if zle lo ofs && zlt ofs hi
                              then None
                              else m.(Mem.mem_access)#b ofs k)
                           m.(Mem.mem_access))
                 m.(Mem.nextblock) _ _ _)
.
Next Obligation.
  repeat rewrite PMap.gsspec.
  destruct (peq b0 b); cycle 1.
  { apply Mem.access_max. }
  subst.
  des_ifs.
  - apply Mem.access_max.
Qed.
Next Obligation.
  hexploit Mem.nextblock_noaccess; eauto; []; i; des.
  rewrite PMap.gsspec.
  des_ifs; eauto.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.

Lemma Mem_drop_perm_none_spec
      m0 blk0 lo hi m1
      (DROP: Mem_drop_perm_none m0 blk0 lo hi = m1)
  :
    (<<NB: Mem.nextblock m0 = Mem.nextblock m1>>)
    /\
    (<<UNCH: Mem.unchanged_on (fun blk1 ofs => blk0 <> blk1 \/ ofs < lo \/ hi <= ofs) m0 m1>>)
    /\
    (<<INSIDE: forall
        ofs
        (INSIDE: lo <= ofs < hi)
    ,
      all2 ~2 Mem.perm m1 blk0 ofs>>)
.
Proof.
  ii.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
  splits; ii; ss.
  - econs; ss; eauto.
    { reflexivity. }
    ii.
    unfold Mem.perm. cbn. rewrite ! PMap.gsspec in *. des_ifs. simpl_bool.
    des; ss; des_sumbool; try lia.
  - des_ifs. simpl_bool. des; des_sumbool; lia.
Qed.

Lemma Mem_set_perm_none_impl
      m0 blk lo hi m1
      (DROP: Mem_drop_perm_none m0 blk lo hi = m1)
  :
    <<PERM: Mem.perm m1 <4= Mem.perm m0>>
.
Proof.
  ii.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
Qed.

Lemma Mem_set_perm_none_left_inject
      `{Val.meminj_ctx}
      j m_src0 m_tgt0
      (INJ: Mem.inject j m_src0 m_tgt0)
      blk lo hi m_src1
      (DROP: Mem_drop_perm_none m_src0 blk lo hi = m_src1)
  :
    <<INJ: Mem.inject j m_src1 m_tgt0>>
.
Proof.
  hexploit Mem_set_perm_none_impl; eauto. intro IMPL; des.
  inv INJ.
  unfold Mem_drop_perm_none in *. des_ifs.
  unfold Mem.perm in IMPL. ss.
  econs; ss; eauto.
  - inv mi_inj.
    econs; i; ss; eauto.
    + exploit mi_perm; eauto.
      eapply IMPL; eauto.
    + eapply mi_align; eauto.
      ii.
      eapply IMPL; eauto. eapply H1; eauto.
    + exploit mi_memval; eauto.
      eapply IMPL; eauto.
  - ii. unfold Mem.perm in *. ss. eapply mi_no_overlap; eauto; eapply IMPL; eauto.
  - unfold Mem.perm. ss.
    ii. eapply mi_representable; eauto.
    des.
    + left. eapply IMPL; eauto.
    + right. eapply IMPL; eauto.
  - ii. hexploit mi_perm_inv; eauto.
    unfold Mem.perm. ss. unfold Mem.perm in H1.
    i; des.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
Qed.

Global Opaque Mem_drop_perm_none.








Module DEPRECATED.

Program Definition Mem_set_perm (m: mem) (b: block) (lo hi: Z) (op: option permission): option mem :=
  match op with
    | Some p =>
      if (Mem.range_perm_dec m b lo hi Max p) then
        if (plt b m.(Mem.nextblock)) then
          Some (Mem.mkmem m.(Mem.mem_contents)
                          (PMap.set b
                                    (fun ofs k =>
                                       match k with
                                         | Cur =>
                                           if zle lo ofs && zlt ofs hi
                                           then Some p
                                           else m.(Mem.mem_access)#b ofs k
                                         | Max => m.(Mem.mem_access)#b ofs k
                                       end
                                    )
                                    m.(Mem.mem_access))
                          m.(Mem.nextblock) _ _ _)
        else None
      else None
    | None =>
      Some (Mem.mkmem m.(Mem.mem_contents)
                      (PMap.set b
                                (fun ofs k =>
                                   if zle lo ofs && zlt ofs hi
                                   then None
                                   else m.(Mem.mem_access)#b ofs k)
                                m.(Mem.mem_access))
                      m.(Mem.nextblock) _ _ _)
  end.
Next Obligation.
  repeat rewrite PMap.gsspec.
  destruct (peq b0 b); cycle 1.
  { apply Mem.access_max. }
  subst.
  des_ifs.
  - simpl_bool; des; des_sumbool.
    exploit H; eauto.
  - apply Mem.access_max.
Qed.
Next Obligation.
  specialize (Mem.nextblock_noaccess m b0 ofs k H1). intros.
  rewrite PMap.gsspec.
  des_ifs.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply Mem.access_max.
  apply Mem.access_max.
Qed.
Next Obligation.
  hexploit Mem.nextblock_noaccess; eauto; []; i; des.
  rewrite PMap.gsspec.
  des_ifs; eauto.
Qed.
Next Obligation.
  apply Mem.contents_default.
Qed.

Lemma Mem_set_perm_none_spec
      m0 blk0 lo hi m1
      (DROP: Mem_set_perm m0 blk0 lo hi None = Some m1)
  :
    (<<OUTSIDE: forall
      blk1 ofs
      (DISJOINT: blk0 <> blk1 \/ ofs < lo \/ hi <= ofs)
    ,
      all2 (Mem.perm m0 blk1 ofs <2> Mem.perm m1 blk1 ofs)>>)
    /\
    (<<INSIDE: forall
        ofs
        (INSIDE: lo <= ofs < hi)
    ,
      all2 ~2 Mem.perm m1 blk0 ofs>>)
.
Proof.
  ii.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
  split; ii; ss.
  - rewrite PMap.gsspec.
    des_ifs. simpl_bool. des_safe. des_sumbool. admit "IDK WHY BUT IT MAKES xomega SLOW IN STACKINGPROOFC1.v!!!!!! des; try xomega".
  - des_ifs. simpl_bool. des_safe. admit "des; des_sumbool; try xomega".
Qed.

Lemma Mem_set_perm_none_impl
      m0 blk lo hi m1
      (DROP: Mem_set_perm m0 blk lo hi None = Some m1)
  :
    <<PERM: Mem.perm m1 <4= Mem.perm m0>>
.
Proof.
  ii.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in *. ss. rewrite PMap.gsspec in *. des_ifs.
Qed.

Lemma Mem_set_perm_none_left_inject
      `{Val.meminj_ctx}
      j m_src0 m_tgt0
      (INJ: Mem.inject j m_src0 m_tgt0)
      blk lo hi m_src1
      (DROP: Mem_set_perm m_src0 blk lo hi None = Some m_src1)
  :
    <<INJ: Mem.inject j m_src1 m_tgt0>>
.
Proof.
  hexploit Mem_set_perm_none_impl; eauto. intro IMPL; des.
  inv INJ.
  unfold Mem_set_perm in *. des_ifs.
  unfold Mem.perm in IMPL. ss.
  econs; ss; eauto.
  - inv mi_inj.
    econs; i; ss; eauto.
    + exploit mi_perm; eauto.
      eapply IMPL; eauto.
    + eapply mi_align; eauto.
      ii.
      eapply IMPL; eauto. eapply H1; eauto.
    + exploit mi_memval; eauto.
      eapply IMPL; eauto.
  - ii. unfold Mem.perm in *. ss. eapply mi_no_overlap; eauto; eapply IMPL; eauto.
  - unfold Mem.perm. ss.
    ii. eapply mi_representable; eauto.
    des.
    + left. eapply IMPL; eauto.
    + right. eapply IMPL; eauto.
  - ii. hexploit mi_perm_inv; eauto.
    unfold Mem.perm. ss. unfold Mem.perm in H1.
    i; des.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
    + rewrite PMap.gsspec in *. des_ifs; ss; eauto.
Qed.

Global Opaque Mem_set_perm.

(* heap(malloc) has permission on (b, -1) *)
(* TODO: Name is not precise... malloc && drop_perm will satsify this condition. *)
Definition is_stack_block (m: mem) (blk: block): Prop := forall
    ofs kind perm
    (PERM: Mem.perm m blk ofs kind perm)
  ,
    <<POS: 0 <= ofs>>
.
Hint Unfold is_stack_block.

End DEPRECATED.

Definition dead_block (m: mem) (b: block): Prop := forall ofs, ~Mem.perm m b ofs Cur Nonempty.

Inductive mem_equiv (m0 m1: mem): Prop :=
| mem_equiv_intro
    (UNCH: Mem.unchanged_on top2 m0 m1)
    (DEAD: forall b (BETWEEN: (m0.(Mem.nextblock) <= b < m1.(Mem.nextblock))%positive), dead_block m1 b)
.

Lemma Mem_unchanged_on_trans_strong
      P m0 m1 m2
      (UNCH0: Mem.unchanged_on P m0 m1)
      (UNCH1: Mem.unchanged_on (P /2\ (fun b _ => Mem.valid_block m0 b)) m1 m2)
  :
    <<UNCH2: Mem.unchanged_on P m0 m2>>
.
Proof.
  inv UNCH0. inv UNCH1.
  econs; i.
  - xomega.
  - etransitivity.
    { eapply unchanged_on_perm; eauto. }
    eapply unchanged_on_perm0; eauto.
    { unfold Mem.valid_block in *. xomega. }
  - erewrite <- unchanged_on_contents; eauto.
    dup H0. apply Mem.perm_valid_block in H1. unfold Mem.valid_block in *.
    erewrite <- unchanged_on_contents0; eauto.
    eapply unchanged_on_perm; eauto.
Qed.

Lemma drop_perm_none_dead_block
      m0 blk lo hi
      (INSIDE: forall ofs k p (PERM: Mem.perm m0 blk ofs k p), lo <= ofs < hi)
  :
    dead_block (Mem_drop_perm_none m0 blk lo hi) blk
.
Proof.
  ii.
  exploit (Mem_drop_perm_none_spec m0 blk lo hi); eauto. i; des.
  destruct (classic (lo <= ofs < hi)).
  - eapply INSIDE0; eauto.
  - inv UNCH.
    erewrite <- unchanged_on_perm in *; ss.
    + eapply INSIDE in H. xomega.
    + right. xomega.
    + unfold Mem.valid_block. rewrite NB.
      eapply Mem.perm_valid_block; eauto.
Qed.

Lemma Mem_alloc_range_perm
      m0 lo hi m1 blk
      (ALLOC: Mem.alloc m0 lo hi = (m1, blk))
  :
    <<PERM: Mem.range_perm m1 blk lo hi Cur Freeable>>
.
Proof.
  ii. eapply Mem.perm_alloc_2; eauto.
Qed.

Hint Resolve Mem_alloc_range_perm : mem.



Inductive future_imm (m0 m1: mem): Prop :=
| future_imm_alloc
    blk lo hi
    (FREE: Mem.alloc m0 lo hi = (m1, blk))
| future_imm_store
    chunk blk ofs v
    (STORE: Mem.store chunk m0 blk ofs v = Some m1)
| future_imm_storebytes
    ofs blk mvs
    (STOREB: Mem.storebytes m0 blk ofs mvs = Some m1)
| future_imm_free
    blk lo hi
    (FREE: Mem.free m0 blk lo hi = Some m1)
| future_imm_drop_perm_none
    blk lo hi
    (DROPN: Mem_drop_perm_none m0 blk lo hi = m1)
(* TODO: drop_perm? *)
.
Hint Constructors future_imm.

Definition future: mem -> mem -> Prop := rtc future_imm.
Hint Unfold future.























Import Mem.

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
