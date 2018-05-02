Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import SimMem.

Set Implicit Arguments.

(* Copied from CRELLVM *)
Inductive frozen (f_old f_new: meminj) (bound_src bound_tgt: block): Prop :=
| frozen_intro
    (NEW_IMPLIES_OUTSIDE:
       forall b_src b_tgt delta
              (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
         <<OUTSIDE_SRC: (bound_src <= b_src)%positive>> /\ <<OUTSIDE_TGT: (bound_tgt <= b_tgt)%positive>>)
.

Remark inject_separated_frozen
       f_old f_new m_src m_tgt
  :
    Events.inject_separated f_old f_new m_src m_tgt <->
    frozen f_old f_new m_src.(Mem.nextblock) m_tgt.(Mem.nextblock)
.
Proof.
  unfold Events.inject_separated in *.
  unfold Mem.valid_block in *.
  split; i.
  - econs; eauto.
    i. des.
    hexploit H; eauto. i; des.
    splits; xomega.
  - inv H.
    exploit NEW_IMPLIES_OUTSIDE; eauto.
    i; des.
    split; xomega.
Qed.

Lemma frozen_preserves_src
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_src
      (INSIDE: (b_src < bound_src)%positive)
  :
    <<PRESERVED: f_old b_src = f_new b_src>>
.
Proof.
  inv FROZEN.
  destruct (f_old b_src) eqn:T0; ss;
    destruct (f_new b_src) eqn:T1; ss.
  - destruct p, p0; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    exfalso.
    xomega.
Qed.

Lemma frozen_preserves_tgt
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_tgt
      (INSIDE: (b_tgt < bound_tgt)%positive)
  :
    <<PRESERVED: forall b_src delta (NOW: f_new b_src = Some (b_tgt, delta)),
      <<OLD: f_old b_src = Some (b_tgt, delta)>> >>
.
Proof.
  inv FROZEN.
  ii.
  destruct (f_old b_src) eqn:T; ss.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - exfalso.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    xomega.
Qed.

Lemma frozen_shortened
      f_old f_new
      bd_src0 bd_tgt0
      (FROZEN: frozen f_old f_new bd_src0 bd_tgt0)
      bd_src1 bd_tgt1
      (SHORT_SRC: (bd_src1 <= bd_src0)%positive)
      (SHORT_TGT: (bd_tgt1 <= bd_tgt0)%positive)
  :
    <<FROZEN: frozen f_old f_new bd_src1 bd_tgt1>>
.
Proof.
  inv FROZEN.
  econs; eauto.
  ii. des.
  hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
  split; ss.
  - red. etransitivity; eauto.
  - red. etransitivity; eauto.
Qed.

Lemma frozen_refl
      f
      bound_src bound_tgt
  :
    <<FROZEN: frozen f f bound_src bound_tgt>>
.
Proof.
  econs; eauto. i; des. clarify.
Qed.



Section MEMINJ.

Local Existing Instance Val.mi_normal.
(* Variable gbound_src gbound_tgt: block. *)

Record t' := mkrelation {
  inj: meminj; (* public memory injection *)
  src_private: forall (b: block) (ofs: Z), Prop; (* source private memory *)
  tgt_private: forall (b: block) (ofs: Z), Prop; (* target private memory *)
  src_external: forall (b: block) (ofs: Z), Prop; (* source external memory *)
  tgt_external: forall (b: block) (ofs: Z), Prop; (* target external memory *)
  src_mem: mem; (* source memory *)
  tgt_mem: mem; (* target memory *)
  src_mem_parent: mem;
  tgt_mem_parent: mem;
}.

Inductive wf' (rel: t'): Prop :=
| wf_intro
    (PUBLIC: Mem.inject rel.(inj) rel.(src_mem) rel.(tgt_mem))
    (SRCDISJ: rel.(src_private) \2/ rel.(src_external) <2= loc_unmapped rel.(inj))
    (TGTDISJ: rel.(tgt_private) \2/ rel.(tgt_external) <2= loc_out_of_reach rel.(inj) rel.(src_mem))
    (SRCPRIVEXT: forall b ofs, ~ (rel.(src_private) b ofs /\ rel.(src_external) b ofs))
    (TGTPRIVEXT: forall b ofs, ~ (rel.(tgt_private) b ofs /\ rel.(tgt_external) b ofs))
    (SRCSUBSET: forall b ofs, rel.(src_private) b ofs \/
                         rel.(src_external) b ofs ->
                         Plt b rel.(src_mem).(Mem.nextblock))
    (TGTSUBSET: forall b ofs, rel.(tgt_private) b ofs \/
                         rel.(tgt_external) b ofs ->
                         Plt b rel.(tgt_mem).(Mem.nextblock))
    (SRCPBOUND: (rel.(src_mem_parent).(Mem.nextblock) <= rel.(src_mem).(Mem.nextblock))%positive)
    (TGTPBOUND: (rel.(tgt_mem_parent).(Mem.nextblock) <= rel.(tgt_mem).(Mem.nextblock))%positive)
    (* It should be mem_parent, in order to exploit "FROZEN" *)
    (* (SRCGBOUND: (gbound_src <= rel.(src_mem_parent).(Mem.nextblock))%positive) *)
    (* (TGTGBOUND: (gbound_tgt <= rel.(tgt_mem_parent).(Mem.nextblock))%positive) *)
.

Inductive le' (mrel0 mrel1: t'): Prop :=
| le_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (SRCEXT: mrel0.(src_external) <2= mrel1.(src_external))
    (TGTEXT: mrel0.(tgt_external) <2= mrel1.(tgt_external))
    (SRCUNCHANGED: Mem.unchanged_on mrel0.(src_external) mrel0.(src_mem) mrel1.(src_mem))
    (TGTUNCHANGED: Mem.unchanged_on mrel0.(tgt_external) mrel0.(tgt_mem) mrel1.(tgt_mem))
    (SRCPARENTEQ: mrel0.(src_mem_parent) = mrel1.(src_mem_parent))
    (TGTPARENTEQ: mrel0.(tgt_mem_parent) = mrel1.(tgt_mem_parent))
    (FROZEN: frozen mrel0.(inj) mrel1.(inj) (mrel0.(src_mem_parent).(Mem.nextblock))
                                            (mrel0.(tgt_mem_parent).(Mem.nextblock)))
    (SRCBOUND: (mrel0.(src_mem).(Mem.nextblock) <= mrel1.(src_mem).(Mem.nextblock))%positive)
    (TGTBOUND: (mrel0.(tgt_mem).(Mem.nextblock) <= mrel1.(tgt_mem).(Mem.nextblock))%positive)
.

Definition lift' (mrel0: t'): t' :=
  (mkrelation mrel0.(inj) (fun _ _ => False) (fun _ _ => False)
                          (mrel0.(src_private) \2/ mrel0.(src_external))
                          (mrel0.(tgt_private) \2/ mrel0.(tgt_external))
                          mrel0.(src_mem) mrel0.(tgt_mem) mrel0.(src_mem) mrel0.(tgt_mem))
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mkrelation mrel1.(inj)
                      (mrel0.(src_private)) (mrel0.(tgt_private))
                      (mrel0.(src_external)) (mrel0.(tgt_external))
                      mrel1.(src_mem) mrel1.(tgt_mem) mrel0.(src_mem_parent) mrel0.(tgt_mem_parent))
.

(* TODO: Let's have this as policy. (giving explicit name) *)
(* TODO: apply this policy for identity/extension *)

(* "Global" is needed as it is inside section *)
Global Program Instance SimMemInj : SimMem.class :=
{
  t := t';
  src_mem := src_mem;
  tgt_mem := tgt_mem;
  wf := wf';
  le := le';
  lift := lift';
  unlift := unlift';
  sim_val := fun (mrel: t') => Val.inject mrel.(inj);
}.
Next Obligation.
  econs.
  - i. econs; eauto; try reflexivity; try apply Mem.unchanged_on_refl; eauto.
    { eapply frozen_refl; eauto. }
  - ii. inv H; inv H0.
    econs; eauto.
    + eapply inject_incr_trans; eauto.
    + eapply Mem.unchanged_on_implies in SRCUNCHANGED0.
      eapply Mem.unchanged_on_trans; eauto.
      i. eapply SRCEXT; eauto.
    + eapply Mem.unchanged_on_implies in TGTUNCHANGED0.
      eapply Mem.unchanged_on_trans; eauto.
      i. eapply TGTEXT; eauto.
    + rewrite SRCPARENTEQ. ss.
    + rewrite TGTPARENTEQ. ss.
    + econs; eauto.
      ii; des.
      destruct (inj y b_src) eqn:T.
      * destruct p.
        exploit INCR0; eauto. i; clarify.
        inv FROZEN.
        hexploit NEW_IMPLIES_OUTSIDE; eauto.
      * inv FROZEN0.
        hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
        split; ss.
        rewrite SRCPARENTEQ. ss.
        rewrite TGTPARENTEQ. ss.
    + etransitivity; eauto.
    + etransitivity; eauto.
Qed.
Next Obligation.
  rename H into VALID.
  inv VALID. econs; ss; eauto; ii; des; ss; eauto.
  - eapply TGTDISJ; eauto.
  - eapply TGTDISJ; eauto.
  - eapply Pos.compare_gt_iff in H. xomega.
  - eapply Pos.compare_gt_iff in H. xomega.
  (* - eapply Pos.compare_gt_iff in H. xomega. *)
  (* - eapply Pos.compare_gt_iff in H. xomega. *)
Qed.
Next Obligation.
  inv H; ss.
  econs; ss; eauto; ii; des; ss.
  - eapply Mem.unchanged_on_implies; eauto.
    i. right. ss.
  - eapply Mem.unchanged_on_implies; eauto.
    i. right. ss.
  - inv H0. ss.
    eapply frozen_shortened; eauto.
Qed.
Next Obligation.
  inv H. inv H0. inv H1.
  econs; ss; eauto. (* eauto did well here *)
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Lemma loc_unmapped_frozen
      F F'
      fbound_src fbound_tgt
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_src)
      (UNMAPPED: loc_unmapped F b ofs)
  :
    loc_unmapped F' b ofs
.
Proof.
  unfold loc_unmapped in *.
  destruct (F' b) eqn:T; ss.
  destruct p; ss.
  inv FROZEN.
  exploit NEW_IMPLIES_OUTSIDE; eauto.
  i; des. xomega.
Qed.

Lemma loc_out_of_reach_frozen
      F F'
      fbound_src fbound_tgt
      (INCR: inject_incr F F')
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_tgt)
      m0 m1
      (UNMAPPED: loc_out_of_reach F m0 b ofs)
      (UNCHANGED: forall k p b0 delta (MAPPED: F b0 = Some (b, delta)),
          Mem.perm m0 b0 (ofs - delta) k p <-> Mem.perm m1 b0 (ofs - delta) k p)
  :
    loc_out_of_reach F' m1 b ofs
.
Proof.
  unfold loc_out_of_reach in *.
  i.
  exploit frozen_preserves_tgt; eauto.
  i. des.
  hexploit UNMAPPED; eauto. i.
  ii.
  contradict H1.
  eapply UNCHANGED; eauto.
Qed.

End MEMINJ.
