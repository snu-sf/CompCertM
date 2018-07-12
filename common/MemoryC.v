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

Local Notation "a # b" := (PMap.get b a) (at level 1).
(** Above is exactly copied from Memory.v **)

(* newly added *)
Require Export Memory.

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

