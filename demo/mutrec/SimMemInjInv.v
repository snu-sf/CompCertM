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

  Variable P : memory_chunk -> Z -> val -> Prop.

  (* Record t' := mk *)
  (*   { minj:> SimMemInj.t'; *)
  (*     mem_inv: block -> option (memory_chunk -> Z -> val -> Prop); }. *)

  Record t' := mk
    { minj:> SimMemInj.t';
      mem_inv: block -> Prop; }.

  Definition update (sm0: t') (j: SimMemInj.t') :=
    mk j sm0.(mem_inv).

  Inductive wf' (sm0: t'): Prop :=
  | wf_intro
      (WF: SimMemInj.wf' sm0)
      (SAT: forall blk chunk ofs v
                   (INV: sm0.(mem_inv) blk)
                   (LOAD: Mem.load chunk sm0.(SimMemInj.tgt) blk ofs = Some v),
          P chunk ofs v)
      (INVRANGE: forall blk ofs (INV: sm0.(mem_inv) blk),
          tgt_private sm0 blk ofs)
  .

  (* "Global" is needed as it is inside section *)
  Global Program Instance SimMemInjInv : SimMem.class :=
    {
      t := t';
      src := src;
      tgt := tgt;
      wf := wf';
      le := fun sm0 sm1 => (<<MLE: le' sm0 sm1>>) /\  (<<INVSAME: mem_inv sm0 = mem_inv sm1>>);
      lift := fun sm0 => update sm0 (lift' sm0);
      unlift := fun sm0 sm1 => update sm1 (unlift' sm0 sm1);
      sim_val := fun (mrel: t') => Val.inject mrel.(inj);
      sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
    }.
  Next Obligation.
    econs.
    - econs; ss. red. refl.
    - econs; ss.
      + des. red. etrans; eauto.
      + des. red. etrans; eauto.
  Qed.
  Next Obligation.
    inv H. econs; eauto. ss.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    split; auto. inv H0. destruct mrel0, mrel1. ss.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    inv H. inv H0. inv H1. econs; eauto.
    destruct mrel0, mrel1. ss.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    inv H.
    admit "ez - find this lemma".
  Qed.
  Next Obligation.
    admit "ez - find this lemma".
  Qed.

End MEMINJINV.


Section SIMSYMBINV.

Variable P : memory_chunk -> Z -> val -> Prop.

Inductive le (ss0: ident -> Prop) (sk_src sk_tgt: Sk.t) (ss1: ident -> Prop): Prop :=
| le_intro
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
  { admit "". }
  set (j := fun blk => if (plt blk (Mem.nextblock m_src))
                       then match Genv.invert_symbol (Sk.load_skenv sk_tgt) blk with
                            | Some id =>
                              if (SS id) then None else Some (blk, 0)
                            | None => None
                            end
                       else None).
  eexists (mk (SimMemInj.mk _ _ j bot2 bot2 _ _) _). ss.
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
Admitted.
Next Obligation.
Admitted.

End SIMSYMBINV.
