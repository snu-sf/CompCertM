Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC Lia LinkingC2 Conventions1C.

Set Implicit Arguments.

Local Opaque Z.mul.

Local Notation "a # b" := (PMap.get b a) (at level 1).
Local Ltac simp := repeat (bsimpl; des; des_sumbool; ss; clarify).

Existing Instance Val.mi_final.

Inductive inj_range_block_wf (j: meminj) (m: mem) blk_src
          (P: Z -> Prop) : Prop :=
| inj_range_wf_empty
    (REACH: j blk_src = None)
    (BOT: P <1= bot1)
| inj_range_wf_intro
    blk_tgt delta
    (DELTA: j blk_src = Some (blk_tgt, delta))
    (ALIGN: forall chunk ofs k p, (range ofs (ofs + size_chunk chunk) <1= ((fun ofs => Mem.perm m blk_src ofs k p) \1/ P)) -> (align_chunk chunk | delta))
    (RANGE: forall ofs,
        (P (Ptrofs.unsigned ofs) \/
         P (Ptrofs.unsigned ofs - 1) ->
         delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned))
.

Definition inj_range_wf (j: meminj) (m: mem) (P: Values.block -> Z -> Prop) :=
  forall blk, inj_range_block_wf j m blk (P blk).

Lemma inj_range_wf_le j m P0 P1
      (INJWF: inj_range_wf j m P0)
      (PLE: P1 <2= P0)
  :
    inj_range_wf j m P1.
Proof.
  ii. destruct (INJWF blk).
  - econs 1; eauto.
  - econs 2; eauto; ii.
    + eapply ALIGN. ii. eapply H in PR. des; eauto.
    + eapply RANGE. des; eauto.
Qed.

Lemma private_unfree_inj_wf
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (* --------------------------------------------------------- *)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src)
  :
    <<WFINJ: inj_range_wf j m_src1 P>>
.
Proof.
  ii. destruct (WFINJ blk).
  - econs 1; eauto.
  - econs 2; eauto. ii.
    eapply ALIGN. ii. eapply H in PR. des; eauto.
    eapply Mem_unfree_unchanged_on in UNFREE; eauto.
    inv UNFREE. specialize (unchanged_on_perm blk x0 k p).
    destruct (classic (brange blk_src lo hi blk x0)).
    + right. inv H0. eauto.
    + left. eapply unchanged_on_perm; eauto.
      eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma private_unfree_inj
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (* --------------------------------------------------------- *)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src)
  :
    <<INJ: Mem.inject j m_src1 m_tgt>>
.
Proof.
  unfold Mem.inject in *.
  unfold Mem_unfree in *. des_ifs.
  inv INJ.
  econs; eauto.
  -
    (* clear_until mi_inj. *)

    inv mi_inj. econs; ii; ss; eauto.
    + unfold Mem.perm, Mem.perm_order' in H0. ss. des_ifs_safe.
      rewrite PMap.gsspec in *.
      destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify; cycle 1.
      * eapply mi_perm; eauto. unfold Mem.perm. bsimpl.
        assert(((Mem.mem_access m_src0) # b1) ofs k = Some p1).
        { des_ifs; simp. }
        rewrite H1; ss.
      * des_ifs; simp.
        eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem.
        eapply PERM; eauto with xomega.
    + destruct (WFINJ b1); clarify.
      destruct (eq_block b1 blk_src); clarify.
      { eapply ALIGN.
        instantiate (1:=p0). instantiate (1:=Max). instantiate (1:=ofs). ii.
        unfold Mem.range_perm, Mem.perm in *. ss.
        rewrite PMap.gss in H0; eauto.
        specialize (H0 _ PR). unfold proj_sumbool in *. des_ifs; ss; eauto. }
      * assert (Mem.range_perm m_src0 b1 ofs (ofs + size_chunk chunk) Max p0).
        { unfold Mem.range_perm, Mem.perm in *. ss.
          i. specialize (H0 ofs0 H).
          rewrite PMap.gso in H0; eauto. } clear H0.
        eapply mi_align; eauto.
    + unfold Mem.range_perm, Mem.perm in H0; ss.
      destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify; cycle 1.
      * assert(Mem.perm m_src0 b1 ofs Cur Readable).
        { rewrite PMap.gsspec in H0. des_ifs; simp. }
        clear H0.
        rewrite PMap.gsspec.
        des_ifs; ss; cycle 1.
        { eapply mi_memval; eauto. }
        destruct (classic (0 <= hi - lo)); cycle 1.
        { assert(NEG: exists n, hi - lo = Z.neg n).
          { assert(Z.sgn (hi - lo) = - 1).
            { eapply Z.sgn_neg. xomega. }
            unfold Z.sgn in *. des_ifs. eauto.
          }
          des. rewrite NEG. rewrite Z2Nat.inj_neg. ss.
          eapply mi_memval; eauto.
        }
        rewrite Mem.setN_other; ss.
        { eapply mi_memval; eauto. }
        ii. rewrite length_list_repeat in *.
        simp.
        { rewrite Z2Nat.id in *; ss. xomega. }
      * simp. rewrite PMap.gsspec. des_ifs.
        destruct (classic (0 <= hi - lo)); cycle 1.
        { rewrite PMap.gsspec in *. des_ifs; simp. xomega. }
        rewrite Mem_setN_in_repeat; ss.
        { econs; eauto. }
        rewrite Z2Nat.id; ss.
        xomega.
  - clear_until mi_no_overlap.
    rr. unfold Mem.perm; ss. ii.
    destruct (peq b1 blk_src && zle lo ofs1 && zlt ofs1 hi) eqn:T1; clarify.
    { simp. clear mi_no_overlap.
      rewrite PMap.gss in *. des_ifs; simp. clear H2.
      rewrite PMap.gso in *; cycle 1.
      { ii; clarify. }
      eapply not_and_or. ii. des. clarify.
      eapply PRVT; try apply H1; eauto; cycle 1.
      { instantiate (1:= ofs2 + delta2). zsimpl. eauto. }
      { rr. xomega. }
    }
    destruct (peq b2 blk_src && zle lo ofs2 && zlt ofs2 hi) eqn:T2; clarify.
    { sguard in T1. simp. clear mi_no_overlap.
      rewrite PMap.gss in *. des_ifs; simp. clear H3.
      rewrite PMap.gso in *; cycle 1.
      { ii; clarify. }
      eapply not_and_or. ii. des. clarify.
      eapply PRVT; try apply H0; eauto; cycle 1.
      { instantiate (1:= ofs1 + delta1). zsimpl. eauto. }
      { rr. xomega. }
    }
    specialize (mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2).
    do 3 (hexploit1 mi_no_overlap; ss).
    eapply mi_no_overlap.
    + rewrite PMap.gsspec in H2. des_ifs; simp.
    + rewrite PMap.gsspec in H3. des_ifs; simp.
  - i. ss. destruct (WFINJ b); clarify.
   destruct (eq_block b blk_src). subst.
    + des; unfold Mem.perm in *; ss; rewrite PMap.gss in H0.
      * unfold proj_sumbool in *; des_ifs; eauto 6.
      * unfold proj_sumbool in *; des_ifs; eauto 6.
    + assert (Mem.perm m_src0 b (Ptrofs.unsigned ofs) Max Nonempty \/
              Mem.perm m_src0 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
      { unfold Mem.range_perm, Mem.perm in *. ss.
        rewrite PMap.gso in H0; eauto. } clear H0.
      eapply mi_representable; eauto.
  - unfold Mem.perm. ss.
    ii.
    exploit mi_perm_inv; eauto. i.
    destruct (peq b1 blk_src && zle lo ofs && zlt ofs hi) eqn:T; clarify.
    + bsimpl. des_safe. des_sumbool. rewrite PMap.gsspec. des_ifs_safe. ss. left. eauto with mem.
    + rewrite PMap.gsspec. des_ifs_safe. left. ss. eauto with mem.
Qed.

Lemma private_unfree_inj_inj_wf
      P j m_src0 m_src1 m_tgt blk_src blk_tgt delta lo hi
      (INJ: Mem.inject j m_src0 m_tgt)
      (DELTA: j blk_src = Some (blk_tgt, delta))
      (PERM: Mem.range_perm m_tgt blk_tgt (delta + lo) (delta + hi) Cur Freeable)
      (PRVT: range (delta + lo) (delta + hi) <1= loc_out_of_reach j m_src0 blk_tgt)
      (UNFREE: Mem_unfree m_src0 blk_src lo hi = Some m_src1)
      (* --------------------------------------------------------- *)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range lo hi <1= P blk_src)
  :
    <<INJ: Mem.inject j m_src1 m_tgt>> /\ <<WFINJ: inj_range_wf j m_src1 P>>
.
Proof.
  split.
  - eapply private_unfree_inj; eauto.
  - eapply private_unfree_inj_wf; eauto.
Qed.

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
    apply NNPP. intro N.
    eapply Mem.mi_freeblocks in N; eauto. clarify.
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

Lemma freed_from_perm_greater m0 m1 blk lo hi
      (FREE: freed_from m0 m1 blk lo hi)
  :
    Mem.perm m1 <4= Mem.perm m0.
Proof.
  ii. inv FREE. inv freed_from_unchanged0.
  specialize (unchanged_on_perm x0 x1 x2 x3).
  des_ifs; [destruct (zle lo x1); destruct (zlt x1 hi)|];
    [exploit freed_from_perm0; eauto;
     i; eapply Mem.perm_cur;
     eapply Mem.perm_implies; eauto; econs | ..];
    eapply unchanged_on_perm; eauto with lia;
      eapply Mem.perm_valid_block in PR; ii;
        unfold Mem.valid_block; rewrite <- freed_from_nextblock0; auto.
Qed.

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
      dup FREE. inv FREE. inv freed_from_unchanged0.
      des_ifs.
      * eapply mi_align. eauto. instantiate (2 := ofs). ii.
        assert (Mem.range_perm m_src2 blk_new ofs (ofs+size_chunk chunk) Max p); eauto.
        assert (range ofs (ofs + size_chunk chunk) <1= range lo hi).
        { ii. ii. eapply H2 in PR.
          eapply Mem.perm_alloc_3 in PR; eauto. }
        apply H3 in H1. eapply freed_from_perm0 in H1.
        eapply Mem.perm_cur_max. eauto.
      * eapply mi_align. eauto. instantiate (2 := ofs).
        eassert (Mem.range_perm m_src2 b1 ofs (ofs+size_chunk chunk) Max p); eauto.
        eassert (Mem.range_perm m_src1 b1 ofs (ofs+size_chunk chunk) Max p); eauto.
        { ii. eapply Mem.perm_alloc_4; eauto. }
        ii. eapply freed_from_perm_greater; eauto.
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
  - ii. ss. dup FREE. inv FREE. inv freed_from_unchanged0.
    assert (Mem.perm m_src2 b (Ptrofs.unsigned ofs) Max Nonempty \/
            Mem.perm m_src2 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
    { eauto. } clear H0. des_ifs.
    + eapply mi_representable; eauto.
      des.
      * left. exploit freed_from_perm0.
        { eapply Mem.perm_alloc_3; eauto. }
        i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. econs.
      * right. exploit freed_from_perm0.
        { eapply Mem.perm_alloc_3; eauto. }
        i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. econs.
    + eapply mi_representable; eauto.
      assert (Mem.perm m_src1 b (Ptrofs.unsigned ofs) Max Nonempty \/
              Mem.perm m_src1 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
      { des; eapply Mem.perm_alloc_4 in H1; eauto. } clear H1.
      des; [left|right]; eapply freed_from_perm_greater; eauto.
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

Lemma unfree_free_inj_inj_wf P j (m_src0 m_src1 m_src2 m_tgt: mem)
      blk0 blk1 delta1 delta2 ofs1 ofs2 size
      (DELTA1: delta1 = Ptrofs.unsigned ofs1)
      (DELTA2: delta2 = Ptrofs.unsigned ofs2)
      (FREE: Mem.free m_src0 blk0 delta1 (delta1 + size) = Some m_src1)
      (UNFREE: Mem_unfree m_src1 blk1 delta2 (delta2 + size) = Some m_src2)
      (SAME: inj_same j (Vptr blk1 ofs2 true) (Vptr blk0 ofs1 true))
      (INJ: Mem.inject j m_src0 m_tgt)
      (WFINJ: inj_range_wf j m_src0 P)
      (RANGE: range delta2 (delta2 + size) <1= P blk1)
  :
    <<INJ: Mem.inject j m_src2 m_tgt>> /\ <<WFINJ: inj_range_wf j m_src2 P>>.
Proof.
  inv SAME. clarify. des_ifs. eapply private_unfree_inj_inj_wf; cycle 4; eauto.
  - ii. destruct (WFINJ blk0).
    + econs 1; eauto.
    + econs 2; eauto.
      i. eapply ALIGN. ii. eapply H in PR. des; eauto.
      left. eapply Mem.perm_free_3; eauto.
  - eapply Mem.free_left_inject; eauto.
  - rewrite Z.add_comm.
    replace (delta + (Ptrofs.unsigned Ptrofs.zero + size)) with ((Ptrofs.unsigned Ptrofs.zero + size)+delta) by lia.
    eapply Mem.range_perm_inj; try apply INJ; eauto.
    eapply Mem.free_range_perm; eauto.
  - intros delta' RANGE0 blk' ofs' INJECT. unfold range in *.
    destruct (eq_block blk' blk_callee); clarify.
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

Lemma nextblock_unvalid CTX j m1 m2
      (INJ: @Mem.inject CTX j m1 m2)
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

Definition extcall_args_reg (mr: mreg) (sg: signature):
  {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
  {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
Proof.
  generalize (regs_of_rpairs (loc_arguments sg)). induction l.
  - ss. tauto.
  - ss. inv IHl; [tauto|].
    destruct a.
    + destruct (mreg_eq r mr); [clarify; eauto|].
      right. intros []; clarify.
    + right. intros []; clarify.
Qed.

Definition src_init_rs sg (rs_src: regset) (rsp: val) : regset :=
  fun (pr : PregEq.t) =>
    match Asm.to_mreg pr with
    | Some mr =>
      if (extcall_args_reg mr sg)
      then (rs_src pr)
      else (to_fake (rs_src pr))
    | None =>
      match pr with
      | IR RSP => rsp
      | PC => rs_src PC
      | RA => to_fake (rs_src RA)
      | _ => to_fake (rs_src pr)
      end
    end.

Program Definition arg_copy_mem (m: mem) (blk_old blk_new: Values.block)
        (sg: signature) (args: list val) : mem :=
  Mem.mkmem
    (admit "")
    m.(Mem.mem_access) m.(Mem.nextblock)
                           m.(Mem.access_max) m.(Mem.nextblock_noaccess)
                                                  _.
Next Obligation.
Admitted.

Definition arg_copy_reg (sg: signature) (args: list val)
           (rs: regset) : regset.
Admitted.

Lemma arg_copy_reg_spec sg args rs pr
      (DIFF: (arg_copy_reg sg args rs) pr <> rs pr)
  :
    (<<UNDEF: (arg_copy_reg sg args rs) pr = Vundef>>) /\
    (<<ARGS: exists mr (MR: to_mreg pr = Some mr),
        In (R mr) (regs_of_rpairs (loc_arguments sg))>>).
Admitted.

Lemma arg_copy_reg_RA sg args rs
  :
    (arg_copy_reg sg args rs) RA = rs RA.
Proof.
  destruct (classic (arg_copy_reg sg args rs RA = rs RA)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_PC sg args rs
  :
    (arg_copy_reg sg args rs) PC = rs PC.
Proof.
  destruct (classic (arg_copy_reg sg args rs PC = rs PC)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_RSP sg args rs
  :
    (arg_copy_reg sg args rs) RSP = rs RSP.
Proof.
  destruct (classic (arg_copy_reg sg args rs RSP = rs RSP)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_more_undef sg args rs pr
  :
    (arg_copy_reg sg args rs) pr = rs pr \/
    (arg_copy_reg sg args rs) pr = Vundef.
Proof.
  destruct (classic (arg_copy_reg sg args rs pr = rs pr)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  eauto.
Qed.

Lemma arg_copy_reg_callee_save sg args rs mr
      (SAVE: is_callee_save mr)
  :
    (arg_copy_reg sg args rs) (to_preg mr) = rs (to_preg mr).
Proof.
  destruct (classic (arg_copy_reg sg args rs (to_preg mr) = rs (to_preg mr))); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  rewrite to_preg_to_mreg in MR. clarify.
  exploit loc_args_callee_save_disjoint; eauto.
  intros [].
Qed.

Lemma memcpy_store_arguments
      rs m_src0 m_src1 m_src2 sg args blk_old blk_new ofs
      (ARGS: Asm.extcall_arguments rs m_src0 sg args)
      (RSRSP: rs RSP = Vptr blk_old ofs true)
      (OFSZERO: ofs = Ptrofs.zero)
      (NEQ: blk_old <> blk_new)
      (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (FREE: freed_from m_src0 m_src1
                        blk_old ofs.(Ptrofs.unsigned)
                                      (ofs.(Ptrofs.unsigned)+4*size_arguments sg))
      (ALLOC: Mem.alloc m_src1 ofs.(Ptrofs.unsigned)
                                     (ofs.(Ptrofs.unsigned)+4*size_arguments sg)
              = (m_src2, blk_new))
  :
    store_arguments
      m_src1
      (arg_copy_reg sg args (src_init_rs sg rs (Vptr blk_new ofs true)))
      (typify_list args (sig_args sg))
      sg (arg_copy_mem m_src2 blk_old blk_new sg args).
Proof.
Admitted.

Lemma arg_copy_mem_extends m blk_old blk_new sg args
  :
    Mem.extends (arg_copy_mem m blk_old blk_new sg args) (memcpy m blk_old blk_new).
Proof.
Admitted.


(* Lemma memcpy_store_arguments *)
(*       rs m_src0 m_src1 m_src2 sg args blk_old blk_new ofs *)
(*       (ARGS: Asm.extcall_arguments rs m_src0 sg args) *)
(*       (RSRSP: rs # RSP = Vptr blk_old ofs true) *)
(*       (OFSZERO: ofs = Ptrofs.zero) *)
(*       (NEQ: blk_old <> blk_new) *)
(*       (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
(*       (FREE: freed_from m_src0 m_src1 *)
(*                         blk_old ofs.(Ptrofs.unsigned) *)
(*                                       (ofs.(Ptrofs.unsigned)+4*size_arguments sg)) *)
(*       (ALLOC: Mem.alloc m_src1 ofs.(Ptrofs.unsigned) *)
(*                                      (ofs.(Ptrofs.unsigned)+4*size_arguments sg) *)
(*               = (m_src2, blk_new)) *)
(*   : *)
(*     store_arguments *)
(*       m_src1 *)
(*       (src_init_rs sg rs (Vptr blk_new ofs true)) *)
(*       args sg (memcpy m_src2 blk_old blk_new). *)
(* Proof. *)
(*   admit "it doesn't hold.". *)
(* Qed. *)

(*   clarify; econs; eauto. *)
(*   - unfold extcall_arguments in *. *)
(*     revert args ARGS. generalize (is_tail_refl (loc_arguments sg)). *)
(*     assert (forall *)
(*                l args *)
(*                (TAIL: is_tail l (loc_arguments sg)) *)
(*                (ARGS: list_forall2 (extcall_arg_pair rs m_src0) l args) *)
(*              , *)
(*                list_forall2 *)
(*                  (extcall_arg_pair (src_init_rs sg rs (Vptr blk_new Ptrofs.zero true)) *)
(*                                    (memcpy m_src2 blk_old blk_new)) l args); auto. *)
(*     induction l; i; inv ARGS; econs; eauto. *)
(*     + inv H1; econs. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := One l0) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. auto. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. tauto. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. tauto. *)
(*     + eapply IHl; auto. *)
(*       eapply is_tail_trans; eauto. econs 2. econs 1. *)
(*   - econs; ss; eauto. *)
(*     + refl. *)
(*     + intros b ofs0 IN PERM. des_ifs. *)
(*       * exfalso. apply IN. eapply Mem.perm_alloc_3; eauto. *)
(*       * f_equal. eapply PMap.gso; auto. *)
(*   - ss. ii. unfold Mem.perm. ss. *)
(*     eapply Mem.perm_alloc_2; eauto. *)
(* Qed. *)
