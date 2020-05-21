Require Import MemoryC.
Require Import ASTC.
Require Import ValuesC.
Require Import MapsC.
Require Import CoqlibC.

Set Implicit Arguments.


(*** TODO: delete this file later ***)








Lemma Mem_setN_getN_same_aux
      n p c0 c1
      ofs
      (SAME: ZMap.get ofs c0 = ZMap.get ofs c1)
  :
    <<SAME: ZMap.get ofs (Mem.setN (Mem.getN n p c0) p c1) = ZMap.get ofs c0>>
.
Proof.
  ginduction n; ii; ss. des.
  erewrite IHn; ss.
  ii. rewrite ZMap.gsspec. des_ifs.
Qed.

Lemma Mem_setN_getN_same2
      n p c0 c1
      ofs
      (RANGE: p <= ofs < p + Z.of_nat n)
  :
    <<SAME: ZMap.get ofs (Mem.setN (Mem.getN n p c0) p c1) = ZMap.get ofs c0>>
.
Proof.
  ginduction n; ii; ss.
  { xomega. }
  des.
  destruct (classic (ofs = p)).
  - clarify. r. rewrite Mem.setN_outside; ss.
    { rewrite ZMap.gsspec. des_ifs. }
    left. xomega.
  - erewrite IHn; ss.
    xomega.
Qed.

Lemma Mem_setN_getN_same
      n p c
  :
    <<SAME: forall ofs, ZMap.get ofs (Mem.setN (Mem.getN n p c) p c) = ZMap.get ofs c>>
.
Proof.
  ii.
  eapply Mem_setN_getN_same_aux; eauto.
Qed.

Inductive Mem_stored (chunk: memory_chunk) (m0: mem) (b: block) (ofs: Z) (v: val) (m1: mem): Prop :=
| Mem_stored_intro
    (NB: Mem.nextblock m0 = Mem.nextblock m1)
    (UNCH: Mem.unchanged_on (~2 brange b ofs (ofs + (size_chunk chunk))) m0 m1)
    (STORED: Mem.load chunk m1 b ofs = Some v)
    (* (PERM: forall mid (OFS: ofs <= mid < ofs + (size_chunk chunk)) k p, *)
    (*     Mem.perm m0 b mid k p <-> Mem.perm m1 b mid k p) *)
    (PERM: forall b0 ofs0 k p,
        Mem.perm m0 b0 ofs0 k p <-> Mem.perm m1 b0 ofs0 k p)
.



Local Transparent Mem.load Mem.loadbytes Mem.storebytes.
Lemma extends_load_right_stored_left
      m_src0 m_tgt0
      chunk v b ofs
      (EXT: Mem.extends m_src0 m_tgt0)
      (LDTGT: Mem.load chunk m_tgt0 b ofs = Some v)
      (VALID: Mem.valid_access m_src0 chunk b ofs Writable)
      (* (PERM: Mem.range_perm m_src0 b ofs (ofs + (size_chunk chunk)) Cur Writable) *)
  :
    exists m_src1, (<<STRSRC: Mem_stored chunk m_src0 b ofs v m_src1>>)
                   /\ (<<EXT: Mem.extends m_src1 m_tgt0>>)
.
Proof.
  rr in VALID. des.
  hexploit (Mem.range_perm_loadbytes m_tgt0 b ofs).
  { ii. eapply Mem.perm_extends; eauto. eapply Mem.perm_implies with Writable; eauto with mem. }
  intro LDBYTES. des.
  exploit Mem.loadbytes_length; et. intro LEN.
  generalize (size_chunk_pos chunk); intro SZC.
  hexploit (Mem.range_perm_storebytes m_src0 b ofs bytes); eauto.
  { ii. eapply VALID. rewrite LEN in *. rewrite Z2Nat.id in *; try xomega. }
  intro STRBYTES. destruct STRBYTES as [m_src1 STRBYTES].
  exists m_src1.
  (* inv EXT. *)
  (* dup LDTGT. unfold Mem.load in LDTGT. des_ifs. *)
  (* edestruct (Mem.range_perm_storebytes . *)
  (* esplits. *)
  (* { econs. et. *)
  (* } *)
  dsplits.
  - econs; eauto with mem.
    + exploit Mem.nextblock_storebytes; et.
    + eapply Mem.storebytes_unchanged_on; et. i. intro U. apply U; clear U.
      rr. esplits; ss; try xomega. rewrite LEN in *. rewrite Z2Nat.id in *; try xomega.
    + exploit Mem.loadbytes_storebytes_same; eauto. intro LDB.
      rewrite LEN in *. rewrite Z2Nat.id in *; try xomega.
      exploit Mem.loadbytes_load; try apply LDB; et. intro LDSRC.
      exploit Mem.loadbytes_load; try apply LDBYTES; et. intro LDTGT0.
      clarify.
  - inv EXT. inv SPLITHINT.
    econs; et.
    + congruence.
    + unfold inject_id in *.
      inv mext_inj.
      econs; et.
      * ii. clarify. eapply mi_perm; eauto. eapply PERM; eauto.
      * ii. clarify. eapply mi_align; eauto. ii. exploit H0; eauto. intro T. eapply PERM; eauto.
      * ii; clarify.
        exploit mi_memval; eauto.
        { eapply PERM; eauto. }
        intro INJ.
        destruct (classic (b2 = b /\ ofs <= ofs0 < ofs + size_chunk chunk)).
        { (* stored regoion *)
          rename H into RANGE.
          des. clarify.
          unfold Mem.storebytes in STRBYTES. des_ifs. ss.
          rewrite PMap.gsspec. des_ifs.
          clear - SZC RANGE0 RANGE1 INJ LDBYTES. unfold Mem.loadbytes in LDBYTES. des_ifs.
          zsimpl.
          erewrite Mem_setN_getN_same2; eauto.
          { refl. }
          rewrite Z2Nat.id in *; try xomega.
        }
        { (* not stored regoion *)
          inv UNCH.
          assert(INJ0: memval_inject inject_id (ZMap.get ofs0 (Mem.mem_contents m_src1) !! b2)
                                     (ZMap.get ofs0 (Mem.mem_contents m_src0) !! b2)).
          {
            erewrite unchanged_on_contents; eauto.
            { refl. }
            eapply PERM; eauto.
          }
          exploit memval_inject_compose; eauto.
        }
    + ii. exploit mext_perm_inv; eauto.
      i; des; eauto.
      * left. eapply PERM; eauto.
      * right. ii. eapply H0. eapply PERM; eauto.
Qed.
Local Opaque Mem.load Mem.loadbytes Mem.storebytes.

