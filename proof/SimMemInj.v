Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimDef SimSymb Skeleton Mod ModSem.
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

Record t' := mk {
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
  (mk mrel0.(inj) (fun _ _ => False) (fun _ _ => False)
                          (mrel0.(src_private) \2/ mrel0.(src_external))
                          (mrel0.(tgt_private) \2/ mrel0.(tgt_external))
                          mrel0.(src_mem) mrel0.(tgt_mem) mrel0.(src_mem) mrel0.(tgt_mem))
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mk mrel1.(inj)
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
Next Obligation.
  ii. inv MLE. eapply val_inject_incr; eauto.
Qed.

End MEMINJ.













Inductive sim_skenv (skenv0 skenv1: SkEnv.t): Prop :=
| sim_skenv_intro
    (NEXT: skenv0.(Genv.genv_next) = skenv1.(Genv.genv_next))
    (SYMB: all1 (skenv0.(Genv.find_symbol) =1= skenv1.(Genv.find_symbol)))
    (DEFS: all1 (skenv0.(Genv.find_def) =1= skenv1.(Genv.find_def)))
    (PUBS: skenv0.(Genv.genv_public) = skenv1.(Genv.genv_public))
.

Inductive skenv_inject (skenv: SkEnv.t) (j: meminj): Prop :=
| sken_inject_intro
    (DOMAIN: forall b, Plt b skenv.(Genv.genv_next) -> j b = Some(b, 0))
    (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 skenv.(Genv.genv_next) -> b1 = b2)
.

Inductive sim_skenv_inj (sm: SimMem.t) (__noname__: unit) (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INJECT: skenv_inject skenv_src sm.(inj))
    (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_mem_parent).(Mem.nextblock))
    (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_mem_parent).(Mem.nextblock))
    (SIMSKENV: sim_skenv skenv_src skenv_tgt)
.

Inductive sim_sk (u: unit) (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (SIM: match_program (fun _ => sim_fun) eq sk_src sk_tgt)
.

Global Program Instance SimSymbId: SimSymb.class SimMemInj := {
  t := unit;
  le := top4;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv_inj;
}
.
Next Obligation.
  inv SIMSK. inv SIMSK0.
  SearchAbout TransfLink.
  admit "this should hold".
Qed.
Next Obligation.
  u in *. inv SIMSK.
  Print Genv.init_mem_transf.
  Print Genv.init_mem_transf_partial.
  About Genv.init_mem_match.
  exploit (Genv.init_mem_match SIM); eauto. i. clarify.
  esplits; eauto.
  - instantiate (1:= mk (Mem.flat_inj m_src.(Mem.nextblock))
                                  bot2 bot2 bot2 bot2 m_src m_src m_src m_src).
    econs; ss; eauto.
    + econs; eauto; ii; ss.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
      * unfold Mem.flat_inj in *. erewrite ! Genv.init_mem_genv_next in *; eauto. des_ifs.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto. reflexivity.
    + ss. erewrite ! Genv.init_mem_genv_next; eauto. reflexivity.
    + econs; eauto.
      * erewrite ! Genv.init_mem_genv_next; eauto.
      * i. symmetry. apply (Genv.find_symbol_match SIM).
      * ii. hexploit (Genv.find_def_match_2 SIM x0); eauto. intro REL.
        inv REL; ss. inv H2; ss.
        { admit "remove sig then this will hold // or just now this will hold if we don't drop sig on opt". }
        inv H3; ss.
      * inv SIM; des; ss. rewrite ! Genv.globalenv_public. ss.
  - ss.
  - ss.
  - econs; ss; try xomega; ii; des; ss; eauto.
    eapply Genv.initmem_inject; eauto.
Unshelve.
Qed.
Next Obligation.
  assert(BOUNDSRC: Ple (Genv.genv_next skenv_src) (Mem.nextblock (src_mem_parent sm1))).
  { inv MLE. rewrite <- SRCPARENTEQ. eapply SIMSKENV. }
  assert(BOUNDTGT: Ple (Genv.genv_next skenv_src) (Mem.nextblock (tgt_mem_parent sm1))).
  { inv MLE. rewrite <- TGTPARENTEQ. eapply SIMSKENV. }
  inv SIMSKENV. inv INJECT.
  econs; eauto.
  econs; eauto.
  - ii. exploit DOMAIN; eauto. i. eapply MLE; eauto.
  - ii. inv MLE.
    eapply IMAGE; eauto.
    erewrite frozen_preserves_tgt; eauto.
    eapply Plt_Ple_trans; eauto.
Qed.
Next Obligation.
  inv MWF. inv SIMSKENV.
  econs; eauto.
  - etransitivity; try apply SRCPBOUND. ss.
  - etransitivity; try apply TGTPBOUND. ss.
Qed.
Next Obligation.
  inv LESRC.
  inv LETGT.
  inv SIMSKENV. inv SIMSKENV0.
  inv SIMSK. unfold match_program in *.
  assert(DEFSEQ: sk_src.(defs) = sk_tgt.(defs)).
  { apply Axioms.functional_extensionality. intro id.
    hexploit (@match_program_defmap _ _ _ _ _ _ _ _ _ _ _ SIM).
    instantiate (1:= id).
    i.
    inv H; ss.
    - unfold defs.
      admit "this is weak. add list_norept or prove my own theorem with induction.".
    - admit "this will hold".
  }
  econs; eauto.
  { inv INJECT.
    econs; ii; eauto.
    - eapply DOMAIN; eauto. rewrite NEXT. ss.
    - eapply IMAGE; eauto. rewrite NEXT. ss.
  }
  { rewrite <- NEXT. ss. }
  { rewrite <- NEXT. ss. }
  econs; eauto.
  - eq_closure_tac.
  - intro id.
    destruct (Classical_Prop.classic (sk_src.(defs) id)); cycle 1.
    + exploit SYMBDROP; eauto. i; des.
      exploit SYMBDROP0; eauto. { rewrite <- DEFSEQ. eauto. } i; des.
      rewrite H0. rewrite H1. ss.
    + exploit SYMBKEEP; eauto. i; des.
      exploit SYMBKEEP0; eauto. { rewrite <- DEFSEQ. eauto. } i; des.
      rewrite H0. rewrite H1. ss.
  - intro blk.
    destruct (Genv.invert_symbol skenv_link_src blk) eqn:T0; cycle 1.
    + rewrite DEFORPHAN; ss.
      destruct (Genv.invert_symbol skenv_link_tgt blk) eqn:T1; cycle 1.
      * rewrite DEFORPHAN0; ss.
      * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
        rewrite <- SYMB in *.
        repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
        clarify.
    + destruct (Genv.invert_symbol skenv_link_tgt blk) eqn:T1; cycle 1.
      * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
        rewrite SYMB in *.
        repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
        clarify.
      * repeat all_once_fast ltac:(fun H => try apply Genv.invert_find_symbol in H; des).
        assert(i = i0).
        { eapply Genv.genv_vars_inj; eauto. unfold Genv.find_symbol in *. rewrite SYMB. ss. }
        clarify.
        repeat all_once_fast ltac:(fun H => try apply Genv.find_invert_symbol in H; des).
        destruct (classic (defs sk_src i0)).
        { erewrite DEFKEEP; eauto. erewrite DEFKEEP0; eauto. rewrite <- DEFSEQ; ss. }
        { erewrite DEFDROP; eauto. erewrite DEFDROP0; eauto. rewrite <- DEFSEQ; ss. }
  - rewrite PUBLIC. rewrite PUBLIC0. ss.
Qed.
Next Obligation.
  inv SIMSKENV. inv SIMSKENV0. inv INJECT.
  econs; eauto.
  - ii. ss.
    assert(fptr_src = fptr_tgt).
    { inv SIMFPTR; ss. des_ifs. rewrite Ptrofs.add_zero_l.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      exploit DOMAIN; eauto. { eapply Genv.genv_defs_range; eauto. } i; clarify. }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    erewrite <- DEFS; eauto. des_ifs. esplits; eauto.
    admit "just use eq".
  - ii.
    assert(fptr_src = fptr_tgt).
    { inv SIMFPTR; ss. des_ifs.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
      exploit IMAGE; eauto. { rewrite NEXT. eapply Genv.genv_defs_range; eauto. } i; clarify.
      exploit DOMAIN; eauto. { rewrite <- DEFS in *. eapply Genv.genv_defs_range; eauto. } i; clarify.
      rewrite e. rewrite Ptrofs.add_zero in *. clarify.
    }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    erewrite DEFS; eauto. des_ifs. esplits; eauto.
    admit "just use eq".
Qed.

