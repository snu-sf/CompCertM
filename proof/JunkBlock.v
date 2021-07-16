Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.

Set Implicit Arguments.



Fixpoint assign_junk_blocks (m0: mem) (n: nat): mem :=
  match n with
  | O => m0
  | S n' => let (m1, _) := Mem.alloc m0 0%Z 0%Z in assign_junk_blocks m1 n'
  end.

Definition is_junk_value (m0 m1: mem) (v: val): Prop :=
  match v with
  | Vptr blk _ => ~ Mem.valid_block m0 blk /\ Mem.valid_block m1 blk
  | _ => True
  end.



Section PROPS.

  Lemma assign_junk_blocks_perm: forall m0 n,
    <<EQ: Mem.perm (assign_junk_blocks m0 n) = Mem.perm m0>>.
  Proof.
    i. repeat (apply func_ext1; i). apply AxiomsC.prop_ext.
    ginduction n; ii; ss. des_ifs. split; i; cycle 1.
    - erewrite IHn. eauto with mem.
    - erewrite IHn in H. destruct (peq x0 b).
      { clarify. exploit Mem.perm_alloc_3; eauto. extlia. }
      eapply Mem.perm_alloc_4; eauto.
  Qed.

  Lemma assign_junk_blocks_nextblock: forall m0 n,
    <<NB: (Mem.nextblock (assign_junk_blocks m0 n) = if Zerob.zerob n then Mem.nextblock m0 else Mem.nextblock m0 + Pos.of_nat n)%positive>>.
  Proof.
    i. unfold NW. ginduction n; ii; ss. des_ifs_safe.
    erewrite IHn; eauto. erewrite Mem.nextblock_alloc; eauto. rewrite ! Pplus_one_succ_r; ss.
    des_ifs; try extlia. rewrite <- Pos.add_assoc. rewrite Pos.add_comm with (p := 1%positive). ss.
  Qed.

  Lemma assign_junk_blocks_nextblock'
        m0 n
        (NZR: n <> O):
    <<NB: (Mem.nextblock (assign_junk_blocks m0 n) = Mem.nextblock m0 + Pos.of_nat n)%positive>>.
  Proof. rewrite assign_junk_blocks_nextblock. destruct n; ss. Qed.

  Lemma assign_junk_blocks_unchanged_on: forall m0 n,
      <<UNCH: Mem.unchanged_on top2 m0 (assign_junk_blocks m0 n)>>.
  Proof.
    i. ginduction n; ii; ss.
    { eapply Mem.unchanged_on_refl; eauto. }
    des_ifs. r. etrans; cycle 1.
    { eapply IHn; eauto. }
    eapply Mem.alloc_unchanged_on; eauto.
  Qed.

  Lemma assign_junk_blocks_load
        m0 chunk n blk ofs
        (VALID: Mem.valid_block m0 blk):
      Mem.load chunk (assign_junk_blocks m0 n) blk ofs = Mem.load chunk m0 blk ofs.
  Proof.
    ginduction n; ii; ss. des_ifs. erewrite IHn; eauto with mem. repeat (apply func_ext1; i).
    eapply Mem.load_alloc_unchanged; eauto.
  Qed.

  Lemma assign_junk_block_extends
        m_src m_tgt
        (EXT: Mem.extends m_src m_tgt):
      forall n, <<EXT: Mem.extends (assign_junk_blocks m_src n) (assign_junk_blocks m_tgt n)>>.
  Proof.
    i. ginduction n; ii; ss. des_ifs. eapply IHn.
    exploit (Mem.alloc_extends m_src m_tgt 0 0 b m 0 0); eauto; try lia. i; des. rewrite H in *. clarify.
  Qed.

End PROPS.

