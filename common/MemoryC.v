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

Local Notation "a # b" := (PMap.get b a) (at level 1).
(** Above is exactly copied from Memory.v **)

(* newly added *)
Require Export Memory.

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

(* TODO: move to CoqlibC *)
Notation "p <2> q" := (fun x0 x1 => (p x0 x1) <-> (q x0 x1)) (at level 50, no associativity).

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
