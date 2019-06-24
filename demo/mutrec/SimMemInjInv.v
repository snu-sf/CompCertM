Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMem.
Require SimSymbId.
Require Import Conventions1.
Require MachC.
Require Export SimMemInj.
Require Import SimMemInjC.

Set Implicit Arguments.



Section MEMINJINV.

  Variable P : memory_chunk -> Z -> option val -> Prop.

  Record t' := mk
    { minj:> SimMemInj.t';
      src_genv_nb : block;
      tgt_genv_nb : block;
      mem_inv: block -> Prop;
      (* mem_inv: block -> (memory_chunk -> Z -> option val -> Prop); *)
    }.

  (* Record t' := *)
  (*   mk *)
  (*     { src : mem; *)
  (*       tgt : mem; *)
  (*       inj : meminj; *)
  (*       mem_inv: block -> option (memory_chunk -> Z -> val -> Prop); *)
  (*     }. *)

  Definition tgt_private_nge (sm: t') :=
    (loc_out_of_reach sm.(inj) sm.(src))
      /2\ (valid_blocks sm.(tgt)) /2\ (fun blk _ => Ple blk sm.(tgt_genv_nb)).

  Definition src_private_nge (sm: t') :=
    (loc_unmapped sm.(inj))
      /2\ (valid_blocks sm.(src)) /2\ (fun blk _ => Ple blk sm.(src_genv_nb)).

  Inductive invariant_satisfied (invar : block -> Prop) (m: mem): Prop :=
  | invariant_satisfied_intro
      (SAT: forall
          blk chunk ofs v
          (INV: invar blk)
          (LOAD: Mem.load chunk m blk ofs = v),
          P chunk ofs v)
      (WRITABLE: forall
          blk chunk ofs
          (INV: invar blk),
          Mem.valid_access m chunk blk ofs Writable).

  Inductive wf' (sm0: t'): Prop :=
  | wf_intro
      (WF: SimMemInj.wf' sm0)
      (SAT: invariant_satisfied sm0.(mem_inv) sm0.(SimMemInj.tgt))
      (INVRANGE: forall blk ofs (INV: sm0.(mem_inv) blk),
          tgt_private sm0 blk ofs /\ Plt blk sm0.(tgt_genv_nb))
      (SRCGENB: Ple sm0.(src_genv_nb) sm0.(src_parent_nb))
      (TGTGENB: Ple sm0.(tgt_genv_nb) sm0.(tgt_parent_nb))
      (SRCEXTGE: forall blk ofs (EXTERN: src_external sm0 blk ofs),
          Ple sm0.(src_genv_nb) blk)
      (TGTEXTGE: forall blk ofs (EXTERN: tgt_external sm0 blk ofs),
          Ple sm0.(tgt_genv_nb) blk)
  .

  Lemma unchanged_on_invariant invar m0 m1
        (INVAR: invariant_satisfied invar m0)
        (INVRANGE: invar <1= Mem.valid_block m0)
        (UNCH: Mem.unchanged_on (fun blk _ => invar blk) m0 m1)
    :
      invariant_satisfied invar m1.
  Proof.
    inv INVAR. econs.
    - i. eapply SAT; eauto.
      erewrite <- Mem.load_unchanged_on_1; eauto.
    - i. unfold Mem.valid_access in *.
      exploit WRITABLE; eauto. i. des.
      split; eauto. ii.
      eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Definition lift' (mrel0: t'): t' :=
    mk (SimMemInj.mk mrel0.(src) mrel0.(tgt) mrel0.(inj) mrel0.(src_private_nge) mrel0.(tgt_private_nge) mrel0.(src_parent_nb) mrel0.(tgt_parent_nb))
       (mrel0.(src_parent_nb))
       (mrel0.(tgt_parent_nb))
       (mrel0.(mem_inv)).

  Definition unlift' (mrel0 mrel1: t'): t' :=
    mk (SimMemInj.mk mrel1.(src) mrel1.(tgt) mrel1.(inj) mrel0.(src_external) mrel0.(tgt_external) mrel0.(src_parent_nb) mrel0.(tgt_parent_nb))
       (mrel0.(src_parent_nb))
       (mrel0.(tgt_parent_nb))
       (mrel0.(mem_inv)).

  Inductive le' (mrel0 mrel1: t'): Prop :=
  | le_intro
      (MLE: SimMemInj.le' mrel0 mrel1)
      (SRCGENBEQ: mrel0.(src_genv_nb) = mrel1.(src_genv_nb))
      (TGTGENBEQ: mrel0.(tgt_genv_nb) = mrel1.(tgt_genv_nb))
      (MINVEQ: mrel0.(mem_inv) = mrel1.(mem_inv))
  .

  (* "Global" is needed as it is inside section *)
  Global Program Instance SimMemInjInv : SimMem.class :=
    {
      t := t';
      src := src;
      tgt := tgt;
      wf := wf';
      le := le';
      lift := lift';
      unlift := unlift';
      sim_val := fun (mrel: t') => Val.inject mrel.(inj);
      sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
    }.
  Next Obligation.
    econs.
    - econs; ss. refl.
    - ii. inv H. inv H0. econs; etrans; eauto.
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.

  Lemma mem_inv_le sm0 sm1
        (MLE: le' sm0 sm1)
    :
      sm0.(mem_inv) <1= sm1.(mem_inv).
  Proof.
    inv MLE. rewrite MINVEQ. auto.
  Qed.

  Definition update (sm0: t') (src tgt: mem) (inj: meminj) :=
    mk (SimMemInjC.update sm0 src tgt inj) (sm0.(src_genv_nb)) (sm0.(tgt_genv_nb)) (sm0.(mem_inv)).

End MEMINJINV.


Section SIMSYMBINV.

Variable P : memory_chunk -> Z -> option val -> Prop.

Inductive le (ss0: ident -> Prop) (sk_src sk_tgt: Sk.t) (ss1: ident -> Prop): Prop :=
| symb_le_intro
    (LE: ss0 <1= ss1)
    (OUTSIDE: forall
        id
        (IN: (ss1 -1 ss0) id)
      ,
        <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
.

Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj)
          (invar: block -> Prop) : Prop :=
| sken_inject_intro
    (DOMAIN: forall b, Plt b ge.(Genv.genv_next) ->
                       forall (NINV: ~ invar b), j b = Some(b, 0))
    (NDOMAIN: forall b, Plt b ge.(Genv.genv_next) ->
                       forall (NINV: invar b), j b = None)
    (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 ge.(Genv.genv_next) -> b1 = b2)
.

Inductive invariant_globvar F V: globdef F V -> Prop :=
| invariant_globvar_intro
    v
    (INITD: admit "about init data" v.(gvar_init))
  :
    invariant_globvar (Gvar v)
.

Inductive sim_skenv_inj (sm: t') (ss: ident -> Prop) (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_inj_intro
    (INVCOMPAT: forall id blk (FIND: skenv_tgt.(Genv.find_symbol) id = Some blk),
        ss id <-> sm.(mem_inv) blk)
    (PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
    (INJECT: skenv_inject skenv_src sm.(inj) sm.(mem_inv))
    (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src_parent_nb))
    (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt_parent_nb))
    (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
    (SRCGENB: Genv.genv_next skenv_src = sm.(src_genv_nb))
    (TGTGENB: Genv.genv_next skenv_tgt = sm.(tgt_genv_nb))
.

Inductive sim_sk (ss: ident -> Prop) (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (SKSAME: sk_src = sk_tgt)
    (CLOSED: forall id (SS: ss id),
        exists g,
          (<<DEF: sk_tgt.(prog_defmap) ! id = Some g>>) /\
          (<<INV: invariant_globvar g>>) /\
          (<<PRVT: ~ In id (prog_public sk_tgt)>>)).

Global Program Instance SimSymbIdInv: SimSymb.class (SimMemInjInv P) := {
  t := ident -> Prop;
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv_inj;
}
.
Next Obligation.
  econs; eauto. i. des. clarify.
Qed.
Next Obligation.
  admit "ez - copy SimSymbDrop".
Qed.
Next Obligation.
  inv SIMSK. eauto.
Qed.
Next Obligation.
  inv SIMSK. inv SIMSK0. exists (ss0 \1/ ss1).
  admit "copy SimSymbDrop".
Qed.
Next Obligation.
  inv SIMSKE. inv SIMSKENV. eauto.
Qed.
Next Obligation.
  inv SIMSK. eexists.
  assert (SS: forall id, {ss id} + {~ ss id}).
  { admit "choice + classic". }
  set (j := fun blk => if (plt blk (Mem.nextblock m_src))
                       then match Genv.invert_symbol (Sk.load_skenv sk_tgt) blk with
                            | Some id =>
                              if (SS id) then None else Some (blk, 0)
                            | None => None
                            end
                       else None).
  eexists (mk (SimMemInj.mk _ _ j bot2 bot2 _ _) _ _ _). ss.
  instantiate (1:=fun blk => exists id,
                      (<<FIND: (Sk.load_skenv sk_tgt).(Genv.find_symbol) id = Some blk>>) /\
                      (<<SINV: ss id>>)).
  esplits; eauto.
  - econs; ss; eauto.
    + i. split; i; eauto. des.
      apply Genv.find_invert_symbol in FIND.
      apply Genv.find_invert_symbol in H. clarify.
    + ii. exploit CLOSED; eauto. i. des.
      apply PRVT. rewrite <- Genv.globalenv_public. auto.
    + admit "".
    + refl.
    + refl.
  - econs; ss; eauto.
    + econs; ss; eauto.
      * admit "".
      * unfold Sk.load_mem in *.
        apply Genv.init_mem_genv_next in LOADMEMSRC.
        rewrite <- LOADMEMSRC. refl.
      * unfold Sk.load_mem in *.
        apply Genv.init_mem_genv_next in LOADMEMSRC.
        rewrite <- LOADMEMSRC. refl.
    + admit "fill invariant_globvar".
    + i. unfold tgt_private. ss. des. splits; auto.
      * ii. unfold j in *. des_ifs.
        apply Genv.find_invert_symbol in INV. clarify.
      * unfold Sk.load_mem, Sk.load_skenv in *.
        eapply Genv.find_symbol_not_fresh; eauto.
      * eapply Genv.genv_symb_range; eauto.
    + refl.
    + refl.
Qed.
Next Obligation.
  destruct sm0, sm1. inv MLE. inv MLE0. ss. clarify.
  inv SIMSKENV. econs; ss; eauto.
  - inv INJECT. econs; eauto.
    + i. destruct (inj minj1 b) eqn:BLK; auto. destruct p. exfalso.
      inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto.
      i. des. eapply Plt_strict. eapply Plt_Ple_trans.
      * apply H.
      * transitivity (src_parent_nb minj0); eauto.
    + i. destruct (inj minj0 b1) eqn:BLK.
      * destruct p. dup BLK. apply INCR in BLK. clarify.
        eapply IMAGE; eauto.
      * inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto.
        i. des. exfalso. eapply Plt_strict. eapply Plt_Ple_trans.
        { apply H0. }
        { etrans; eauto. }
  - rewrite <- SRCPARENTEQNB. auto.
  - rewrite <- TGTPARENTEQNB. auto.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  inv SIMSKENV. inv SIMSKENV0.
  inv ARGS. ss.
  exploit ec_mem_inject; eauto.
  - eapply external_call_spec.
  - instantiate (1:=skenv_sys_tgt).
    admit "ez".
  - instantiate (1:=tgt sm0). rewrite MEMSRC.
    inv MWF. inv WF. eauto.
  - i. des.
    eexists (mk (SimMemInj.mk (Retv.m retv_src) m2' f' _ _ _ _) _ _ _). ss.
    exists (Retv.mk vres' m2'). ss.
    esplits; ss; eauto.
    + rewrite MEMTGT. eauto.
    + admit "".
    + admit "".
      Unshelve. all:admit"".
Qed.

End SIMSYMBINV.
