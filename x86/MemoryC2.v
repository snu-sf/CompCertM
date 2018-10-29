Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import Lia.

Set Implicit Arguments.

Local Opaque Z.mul.

Existing Instance Val.mi_final.

Lemma separated_out_of_reach j0 j1 m_src0 m_src1 m_tgt0 blk delta
      (INJ: Mem.inject j0 m_src0 m_tgt0)
      (INCR: inject_incr j0 j1)
      (SEPARATED: inject_separated j0 j1 m_src0 m_tgt0)
      (BOUND: Plt blk m_tgt0.(Mem.nextblock))
      (OUTOFREACH: loc_out_of_reach j0 m_src0 blk delta)
      (MAXPERM: forall b ofs p
                       (VALED: Mem.valid_block m_src0 b)
                       (PERM: Mem.perm m_src1 b ofs Max p),
          Mem.perm m_src0 b ofs Max p)
  :
    loc_out_of_reach j1 m_src1 blk delta.
Proof.
  ii.
  unfold inject_separated in *.
  destruct (j0 b0) eqn:EQ.
  - destruct p. specialize (INCR _ _ _ EQ). clarify.
    eapply OUTOFREACH; eauto. eapply MAXPERM; eauto.
    destruct (Registers.Regset.MSet.Raw.MX.lt_dec b0 m_src0.(Mem.nextblock)); eauto.
    eapply Mem.mi_freeblocks in n; eauto. clarify.
  - specialize (SEPARATED _ _ _ EQ H). des.
    apply SEPARATED0. eauto.
Qed.

Program Definition memcpy (m: mem) (blk_old blk_new : Values.block) : mem :=
  Mem.mkmem
    (PMap.set blk_new (PMap.get blk_old m.(Mem.mem_contents))
              m.(Mem.mem_contents))
    m.(Mem.mem_access) m.(Mem.nextblock)
                           m.(Mem.access_max) m.(Mem.nextblock_noaccess) _.
Next Obligation.
  rewrite PMap.gsspec. des_ifs; apply Mem.contents_default.
Qed.

Lemma unfree_nextblock m_src0 m_src1 blk_src lo hi
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
  :
    m_src0.(Mem.nextblock) = m_src1.(Mem.nextblock).
Proof.
  unfold Mem_unfree in *. des_ifs.
Qed.

Lemma private_unfree_inj j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (lo+delta) (hi+delta) Cur Freeable) 
      (PRVT: forall delta' (BOUND: delta + lo <= delta' <delta + hi),
          loc_out_of_reach j m_src0 blk_tgt delta')
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (INJ: Mem.inject j m_src0 m_tgt)
  :
    Mem.inject j m_src1 m_tgt.
Proof. 
(*   econs; i. *)
(*   assert (UNCHANGED: Mem.unchanged_on (~2 brange blk_src lo hi) m_src0 m_src1). *)
(*   { eapply Mem_unfree_unchanged_on; eauto. } *)
(*   - econs; i. *)
(*     destruct (classic (brange blk_src lo hi b1 ofs)); unfold brange in *; ss; *)
(*       des; clarify. *)
(*     + eapply Mem.perm_implies. eapply Mem.perm_cur. eapply PERM. *)
(*       omega. econs. *)
(*     + eapply Mem.mi_perm;[eapply INJ|..]; eauto. *)
(*       exploit Mem.unchanged_on_perm; eauto. *)
(*       instantiate (1 := ofs). instantiate (1 := b1). *)
(*       unfold brange. ss. *)
(*       unfold Mem.valid_block. erewrite unfree_nextblock; eauto. *)
(*       eapply Mem.perm_valid_block; eauto. *)
(*       i. des. eauto. *)
(*     + *)
(*  eapply Mem.mi_align;[eapply INJ|..]; eauto.  *)
(*     destruct (classic (brange blk_src lo hi b1 (ofs+size_chunk chunk))); unfold brange in *; ss; *)
(*       des; clarify. *)
(*     * eapply Mem.perm_implies. eapply Mem.perm_cur. eapply PERM. *)
(*       omega. econs. *)
(*     * eapply Mem.mi_perm;[eapply INJ|..]; eauto. *)
(*       exploit Mem.unchanged_on_perm; eauto. *)
(*       instantiate (1 := ofs). instantiate (1 := b1). *)
(*       unfold brange. ss. *)
(*       unfold Mem.valid_block. erewrite unfree_nextblock; eauto. *)
(*       eapply Mem.perm_valid_block; eauto. *)
(*       i. des. eauto. *)
(* admit "". *)
(*     + admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(* destruct (eq_block b1 blk_src). *)
(*     + clarify. destruct (classic (lo <= ofs < hi)). *)
(*       * eapply Mem.perm_implies. eapply Mem.perm_cur. eapply PERM. *)
(*         omega. econs. *)
(*       * eapply Mem.mi_perm;[eapply INJ|..]; eauto. *)
(*         exploit Mem.unchanged_on_perm; eauto. *)
(*         instantiate (1 := ofs). instantiate (1 := blk_src). *)
(*         unfold brange. ss. tauto. *)
(*         unfold Mem.valid_block. erewrite unfree_nextblock; eauto. *)
(*         eapply Mem.perm_valid_block; eauto. *)
(*         i. des. eauto. *)
(*     + eapply Mem.mi_perm;[eapply INJ|..]; eauto. *)
(*       exploit Mem.unchanged_on_perm; eauto. *)
(*       instantiate (1 := ofs). instantiate (1 := b1). *)
(*       unfold brange. ss. tauto. *)
(*       unfold Mem.valid_block. erewrite unfree_nextblock; eauto. *)
(*       eapply Mem.perm_valid_block; eauto. *)
(*       i. des. eauto. *)
(*     + eapply Mem.mi_align;[eapply INJ|..]; eauto. admit "". *)
(*     + admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*   - admit "". *)
(*     admit "". *)
Admitted.

Record freed_from m0 m1 blk lo hi : Prop :=
  mk_freed_from
    {
      freed_from_unchanged: Mem.unchanged_on
                              (fun blk' ofs =>
                                 if eq_block blk' blk
                                 then ~ (lo <= ofs < hi)
                                 else True)
                              m0 m1;
      freed_from_nextblock: m1.(Mem.nextblock) = m0.(Mem.nextblock);
      freed_from_perm: Mem.range_perm m0 blk lo hi Cur Freeable;
      freed_from_noperm: Mem_range_noperm m1 blk lo hi;
      freed_from_contents: forall ofs (IN: lo <= ofs < hi),
          ZMap.get ofs (Mem.mem_contents m0) !! blk =
          ZMap.get ofs (Mem.mem_contents m1) !! blk;
    }.

Lemma freed_from_perm_le m_src0 m_src1 blk lo hi blk' ofs k p
      (FREED: freed_from m_src0 m_src1 blk lo hi)
      (PERM: Mem.perm m_src1 blk' ofs k p)
  :
    Mem.perm m_src0 blk' ofs k p.
Proof.
  destruct (eq_block blk' blk).
  - clarify. destruct (classic (lo <= ofs < hi)).
    + exfalso. eapply freed_from_noperm; eauto.
      eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
    + eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
      des_ifs; eauto.
      eapply Mem.perm_valid_block in PERM.
      unfold Mem.valid_block in *. erewrite <- freed_from_nextblock; eauto.
  - eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
    des_ifs; eauto.
    eapply Mem.perm_valid_block in PERM.
    unfold Mem.valid_block in *. erewrite <- freed_from_nextblock; eauto.
Qed.

Lemma freed_from_inject j m_src0 m_src1 m_tgt blk lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (FREED: freed_from m_src0 m_src1 blk lo hi)
  :
    Mem.inject j m_src1 m_tgt.
Proof.
  eapply Mem.extends_inject_compose; eauto.
  econs.
  - eapply freed_from_nextblock; eauto.
  - econs; i; unfold inject_id in *; clarify; try rewrite Z.add_0_r.
    + eapply freed_from_perm_le; eauto.
    + eapply Z.divide_0_r.
    + destruct (eq_block b2 blk).
      * clarify. destruct (classic (lo <= ofs < hi)).
        -- erewrite <- freed_from_contents; eauto. refl.
        -- erewrite (Mem.unchanged_on_contents _ _ _ (freed_from_unchanged FREED)); auto.
           refl.
           des_ifs; eauto.
           eapply freed_from_perm_le; eauto.
      * erewrite (Mem.unchanged_on_contents _ _ _ (freed_from_unchanged FREED)); auto.
        refl.
        des_ifs; eauto.
        eapply freed_from_perm_le; eauto.
  - i. destruct (eq_block b blk).
    + clarify. destruct (classic (lo <= ofs < hi)).
      * right. eapply freed_from_noperm; eauto.
      * left.
        eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
        des_ifs; eauto. eapply Mem.perm_valid_block; eauto.
    + left.
      eapply (Mem.unchanged_on_perm _ _ _ (freed_from_unchanged FREED)); auto.
      des_ifs; eauto. eapply Mem.perm_valid_block; eauto.
Qed.

Lemma freed_from_out_of_reach j m_src0 m_src1 m_tgt blk lo hi blk' delta ofs
      (INJECT: Mem.inject j m_src0 m_tgt)
      (FREED: freed_from m_src0 m_src1 blk lo hi)
      (DELTA: j blk = Some (blk', delta))
      (IN: lo + delta <= ofs < hi + delta)
  :
    loc_out_of_reach j m_src1 blk' ofs.
Proof.
  ii. destruct (eq_block b0 blk).
  - clarify. eapply freed_from_noperm; eauto. omega.
  - exploit Mem.inject_no_overlap; eauto. 
    + eapply freed_from_perm_le; eauto.
    + eapply Mem.perm_cur.
      eapply Mem.perm_implies.
      eapply freed_from_perm; eauto. 
      instantiate (1 := ofs - delta). omega. econs.
    + i. des; eauto. omega.
Qed.

Definition callee_injection (j: meminj) old_blk new_blk: meminj :=
  fun blk => if (eq_block blk new_blk)
             then j old_blk
             else (j blk).

Local Ltac simp := repeat (bsimpl; des; des_sumbool; ss; clarify).

Local Transparent Mem.alloc.
Lemma memcpy_inject
      j m_src0 m_src1 m_src2 m_tgt blk_old blk_new lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (NEQ: blk_old <> blk_new)
      (FREE: freed_from m_src0 m_src1 blk_old lo hi)
      (ALLOC: Mem.alloc m_src1 lo hi = (m_src2, blk_new))
      blk_tgt delta
      (INJBLK: j blk_old = Some (blk_tgt, delta))
  :
    Mem.inject (callee_injection j blk_old blk_new)
               (memcpy m_src2 blk_old blk_new) m_tgt
.
Proof.
  assert(JEMPTY: j blk_new = None).
  { eapply Mem.mi_freeblocks; eauto. unfold Mem.valid_block. erewrite <- freed_from_nextblock; eauto.
    ii.
    exploit Mem.alloc_result; eauto. i. clarify. xomega.
  }
  assert(INCR: inject_incr j (callee_injection j blk_old blk_new)).
  { ii; ss. unfold callee_injection. des_ifs. }
  assert(PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable).
  { clear - INJBLK INJ FREE. ii.
    assert(exists ofs', ofs = ofs' + delta).
    { exists (ofs - delta). xomega. } des. clarify.
    eapply Mem.mi_perm; try apply INJ; try apply INJBLK; eauto.
    eapply freed_from_perm; eauto. xomega.
  }
  unfold callee_injection, memcpy in *.
  dup INJ.
  inv INJ.
  econs; eauto.
  - clear_until mi_inj.
    inv mi_inj.
    econs.
    + ii; ss.
      unfold Mem.perm in *. ss.
      des_ifs.
      { eapply Mem.perm_cur.
        eapply Mem.perm_implies with Freeable; try eauto with mem.
        eapply PERM.
        exploit Mem.perm_alloc_3; eauto. i.
        xomega.
      }
      destruct (peq b1 blk_old); clarify.
      { assert(~lo <= ofs < hi).
        { ii.
          exploit freed_from_noperm; eauto.
          eauto with mem.
        }
        assert(PERM0: Mem.perm_order' ((Mem.mem_access m_src1) !! blk_old ofs k) p).
        { eapply Mem.perm_alloc_4; eauto. }
        eapply mi_perm; eauto.
        inv FREE.
        eapply Mem.unchanged_on_perm; eauto.
        - ii; ss. des_ifs.
        - apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify.
      }
      eapply mi_perm; eauto.
      assert(PERM0: Mem.perm_order' ((Mem.mem_access m_src1) !! b1 ofs k) p).
      { eapply Mem.perm_alloc_4; eauto. }
      inv FREE.
      eapply Mem.unchanged_on_perm; eauto.
      * ii; ss. des_ifs.
      * apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify.
    + ii; ss.
      admit "this does not hold".
    + ii; ss. rewrite PMap.gsspec. des_ifs.
      { specialize (mi_memval _ ofs _ _ H).
        unfold Mem.perm in *. ss.
        exploit Mem.perm_alloc_3; eauto. i.
        hexploit1 mi_memval.
        { eapply Mem.perm_implies with Freeable; eauto with mem.
          eapply freed_from_perm; eauto.
        }
        eapply memval_lessdef_inject_compose; eauto; cycle 1.
        { eapply memval_inject_incr; eauto. }
        unfold Mem.alloc in *.
        clarify.
        ss.
        rewrite PMap.gsspec. des_ifs.
        erewrite <- freed_from_contents; eauto. refl.
      }
      clear_tac.
      eapply memval_inject_incr; eauto.
      unfold Mem.alloc in *. clarify. ss. unfold Mem.perm in *. ss.
      rewrite PMap.gsspec in *. des_ifs.
      erewrite Mem.unchanged_on_contents; try apply FREE; eauto.
      { eapply mi_memval; eauto.
        eapply freed_from_perm_le; eauto.
      }
      { ii; ss. des_ifs. ii.
        exploit freed_from_noperm; eauto. eauto with mem.
      }
      { des_ifs. ii.
        exploit freed_from_noperm; eauto. eauto with mem.
      }
      { apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify. }
  - ii; ss. unfold Mem.valid_block in *. ss.
    exploit Mem.alloc_result; eauto. i; subst.
    exploit Mem.nextblock_alloc; eauto. i.
    des_ifs.
    + exfalso. eapply H. rewrite H0. xomega.
    + eapply mi_freeblocks; eauto. ii. eapply H.
      rewrite H0. erewrite freed_from_nextblock; eauto. xomega.
  - ii. des_ifs; eauto.
  - ii. unfold Mem.perm in *. ss.
    destruct (eq_block b1 blk_new); clarify.
    { specialize (mi_no_overlap blk_old blk_tgt delta b2 b2' delta2).
      des_ifs.
      destruct (peq b2 blk_old).
      { clarify. right. ii.
        exploit Mem.perm_alloc_3; eauto. i.
        hexploit freed_from_noperm; eauto. i. specialize (H5 ofs1 H4).
        exploit Mem.perm_alloc_4; eauto. i.
        assert(ofs1 = ofs2) by xomega. clarify.
      }
      eapply mi_no_overlap; eauto.
      - exploit Mem.perm_alloc_3; eauto. i.
        eapply Mem.perm_cur_max. eapply Mem.perm_implies with Freeable; (eauto with mem).
        eapply freed_from_perm; eauto.
      - assert(Mem.perm_order' ((Mem.mem_access m_src1) !! b2 ofs2 Max) Nonempty).
        { eapply Mem.perm_alloc_4; eauto. }
        inv FREE.
        eapply Mem.unchanged_on_perm; eauto.
        { ss. des_ifs. }
        { apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify. }
    }
    destruct (eq_block b2 blk_new); clarify.
    {
      specialize (mi_no_overlap b1 b1' delta1 blk_old blk_tgt delta).
      destruct (peq b1 blk_old).
      { clarify. right. ii.
        exploit Mem.perm_alloc_3; eauto. i.
        hexploit freed_from_noperm; eauto. i. specialize (H5 ofs2 H4).
        exploit Mem.perm_alloc_4; try apply H2; eauto. i.
        assert(ofs1 = ofs2) by xomega. clarify.
      }
      eapply mi_no_overlap; eauto.
      - assert(Mem.perm_order' ((Mem.mem_access m_src1) !! b1 ofs1 Max) Nonempty).
        { eapply Mem.perm_alloc_4; eauto. }
        inv FREE.
        eapply Mem.unchanged_on_perm; eauto.
        { ss. des_ifs. }
        { apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify. }
      - exploit Mem.perm_alloc_3; eauto. i.
        eapply Mem.perm_cur_max. eapply Mem.perm_implies with Freeable; (eauto with mem).
        eapply freed_from_perm; eauto.
    }
    specialize (mi_no_overlap b1 b1' delta1 b2 b2' delta2).
    eapply mi_no_overlap; eauto.
    + assert(Mem.perm m_src1 b1 ofs1 Max Nonempty).
      { eapply Mem.perm_alloc_4; eauto. }
      eapply freed_from_perm_le; eauto.
    + assert(Mem.perm m_src1 b2 ofs2 Max Nonempty).
      { eapply Mem.perm_alloc_4; eauto. }
      eapply freed_from_perm_le; eauto.
  - unfold Mem.perm. ss.
    admit "this does not hold".
  - unfold Mem.perm. ss.
    ii. des_ifs.
    + destruct (classic (lo <= ofs < hi)).
      { left. eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem. }
      { right. ii. exploit Mem.perm_alloc_3; eauto. }
    + exploit mi_perm_inv; eauto. i.
      unfold Mem.alloc in *. clarify. ss. rewrite PMap.gsspec. des_ifs.
      destruct (classic (b1 = blk_old /\ lo <= ofs < hi)).
      { des_safe; clarify. right. eapply freed_from_noperm; eauto. }
      { apply not_and_or in H2.
        destruct H2.
        - des; ss.
          + left. inv FREE.
            eapply Mem.unchanged_on_perm with (m_after := m_src1) (m_before := m_src0); eauto.
            { ii; ss. des_ifs. }
            { apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify. }
          + right. ii. eapply H1. eapply freed_from_perm_le; eauto.
        - des; ss.
          + left. inv FREE.
            eapply Mem.unchanged_on_perm with (m_after := m_src1) (m_before := m_src0); eauto.
            { ii; ss. des_ifs. }
            { apply NNPP. ii. exploit Mem.mi_freeblocks; eauto. i; clarify. }
          + right. ii. eapply H1. eapply freed_from_perm_le; eauto.
      }
Qed.
Local Opaque Mem.alloc.

Lemma free_freed_from m0 m1 blk lo hi
      (FREE: Mem.free m0 blk lo hi = Some m1)
  :
    freed_from m0 m1 blk lo hi.
Proof.
  econs.
  - eapply Mem.free_unchanged_on; eauto.
    i. des_ifs.
  - eapply Mem.nextblock_free; eauto.
  - eapply Mem.free_range_perm; eauto.
  - eapply Mem_free_noperm; eauto.
  - i. Local Transparent Mem.free. unfold Mem.free in *.
    des_ifs.
Qed.

Lemma init_mem_freed_from m_init
  :
    freed_from m_init m_init 1%positive 0 0.
Proof.
  econs; ii; auto; try omega.
  econs; eauto. refl.
Qed.

Inductive inj_same (j: meminj) v_caller v_callee : Prop :=
| inj_same_intro
    blk_caller blk_callee blk delta ofs
    (OFSZERO: ofs = Ptrofs.zero)
    (CALLERRSP: v_caller = Vptr blk_caller ofs true)
    (CALLEERSP: v_callee = Vptr blk_callee ofs true)
    (CALLER: j blk_caller = Some (blk, delta))
    (CALLEE: j blk_callee = Some (blk, delta)).

Lemma inj_same_inj j v_caller v_callee v_tgt
      (SAME: inj_same j v_caller v_callee)
      (INJ: Val.inject j v_caller v_tgt)
  :
    Val.inject j v_callee v_tgt.
Proof.
  inv SAME. inv INJ. clarify. econs; eauto. 
Qed.

Lemma inj_same_inj2 j v_caller v_callee v_tgt
      (SAME: inj_same j v_caller v_callee)
      (INJ: Val.inject j v_callee v_tgt)
  :
    Val.inject j v_caller v_tgt.
Proof.
  inv SAME. inv INJ. clarify. econs; eauto. 
Qed.

Definition to_fake (v: val) : val :=
  match v with
  | Vptr blk ofs true => Vptr blk ofs false
  | _ => v
  end.

Lemma to_fake_inj j v_src v_tgt
      (INJ: Val.inject j v_src v_tgt)
  :
    Val.inject j (to_fake v_src) v_tgt.
Proof. unfold to_fake. inv INJ; econs; eauto. Qed.

Lemma to_fake_inj2 j v_src v_tgt
      (INJ: Val.inject j (to_fake v_src) v_tgt)
  :
    Val.inject j v_src v_tgt.
Proof. unfold to_fake in *. des_ifs; inv INJ; clarify. econs; eauto. Qed.

Lemma unfree_free_inj j (m_src0 m_src1 m_src2 m_tgt: mem) blk0 blk1 delta1 delta2 ofs1 ofs2 size
      (DELTA1: delta1 = Ptrofs.unsigned ofs1)
      (DELTA2: delta2 = Ptrofs.unsigned ofs2)
      (FREE: Mem.free m_src0 blk0 delta1 (delta1 + size) = Some m_src1)
      (UNFREE: Mem_unfree m_src1 blk1 delta2 (delta2 + size) = Some m_src2)
      (SAME: inj_same j (Vptr blk1 ofs2 true) (Vptr blk0 ofs1 true))
      (INJ: Mem.inject j m_src0 m_tgt)
  :
    Mem.inject j m_src2 m_tgt.
Proof.
  inv SAME. clarify. des_ifs.
  eapply private_unfree_inj; cycle 3; eauto.
  - eapply Mem.free_left_inject; eauto.
  - eapply Mem.range_perm_inj; try apply INJ; eauto.
    eapply Mem.free_range_perm. rewrite Ptrofs.unsigned_zero in *. eauto.
  - i. intros blk' ofs' INJECT. destruct (eq_block blk' blk_callee); clarify.
    + eapply Mem.perm_free_2; eauto. lia.
    + intros PERM. eapply Mem.perm_free_3 in PERM; eauto.
      eapply Mem.free_range_perm in FREE.
      exploit Mem.inject_no_overlap; eauto.
      eapply Mem.perm_max; eauto.
      eapply Mem.perm_implies; eauto.
      eapply FREE; eauto.
      * assert (Ptrofs.unsigned Ptrofs.zero <= delta' - delta < Ptrofs.unsigned Ptrofs.zero + size).
        rewrite Ptrofs.unsigned_zero in *. lia. eauto.
      * econs.
      * splits. des; eauto. lia.
Qed.

Lemma memcpy_load
      m_src0 m_src1 m_src2 chunk blk_old blk_new lo hi ofs v
      (NEQ: blk_old <> blk_new)
      (FREE: freed_from m_src0 m_src1 blk_old lo hi)
      (ALLOC: Mem.alloc m_src1 lo hi = (m_src2, blk_new))
      (BOUND0: lo <= ofs)
      (BOUND1: ofs + size_chunk chunk <= hi) 
      (LOAD: Mem.load chunk m_src0 blk_old ofs = Some v)
  :
    Mem.load chunk (memcpy m_src2 blk_old blk_new)
             blk_new ofs = Some v.
Proof.
  Local Transparent Mem.load. unfold Mem.load in *. des_ifs.
  - f_equal. f_equal. ss. rewrite PMap.gss.
    rewrite size_chunk_conv in *.
    generalize (size_chunk_nat chunk) ofs BOUND0 BOUND1.
    induction n; ss.
    i. f_equal.
    + symmetry. erewrite freed_from_contents; [|apply FREE|lia].
      f_equal. rewrite (Mem.alloc_result _ _ _ _ _ ALLOC) in NEQ.
      Local Transparent Mem.alloc. unfold Mem.alloc in *.
      clarify. ss. symmetry. apply PMap.gso; auto.
    + eapply IHn; lia.
  - exfalso. eapply n. unfold Mem.valid_access in *. des. split; auto.
    ii. eapply Mem.perm_implies; [|econs 2].
    exploit Mem.perm_alloc_2; eauto. lia.
Qed.

Lemma nextblock_unvalid j m1 m2
      (INJ: Mem.inject j m1 m2)
  :
    j (Mem.nextblock m1) = None.
Proof.
  inv INJ. eapply mi_freeblocks.
  unfold Mem.valid_block. apply Plt_strict.
Qed.

Inductive almost_eq : val -> val -> Prop :=
| almost_eq_refl v : almost_eq v v
| almost_eq_ptr blk ofs b1 b2 : almost_eq (Vptr blk ofs b1) (Vptr blk ofs b2)
.

Lemma to_fake_almost_eq v
  :
    almost_eq v (to_fake v).
Proof.
  destruct v; try econs. destruct b0; econs.
Qed.

Lemma almost_eq_commute j v_src0 v_src1 v_tgt
      (INJ: Val.inject j v_src1 v_tgt)
      (EQ: almost_eq v_src0 v_src1)
  :
    Val.inject j v_src0 v_tgt.
Proof.
  inv EQ; eauto.
  destruct b1, b2; inv INJ; try econs; eauto. clarify.
Qed.

Lemma lessdef_commute j v_src0 v_src1 v_tgt
      (INJ: Val.inject j v_src1 v_tgt)
      (LESS: Val.lessdef v_src0 v_src1)
  :
    Val.inject j v_src0 v_tgt.
Proof.
  inv LESS; inv INJ; eauto.
Qed.

Lemma to_fake_fake_ptr v : ~ is_real_ptr (to_fake v).
Proof.
  intros i. inv i. destruct v; ss. destruct b0; ss.
Qed.

Lemma callee_injection_incr j old_blk new_blk
      (INJ_NONE: j new_blk = None)
  :
    inject_incr j (callee_injection j old_blk new_blk).
Proof.
  unfold callee_injection. ii. des_ifs.
Qed.
