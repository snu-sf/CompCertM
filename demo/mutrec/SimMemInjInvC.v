Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMem SimMemLift.
Require SimSymbId.
Require Export SimMemInjInv.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ChoiceFacts.

Set Implicit Arguments.


Section MEMINJINV.

  Variable P_src : memblk_invariant.
  Variable P_tgt : memblk_invariant.

  Inductive lepriv (sm0 sm1: t'): Prop :=
  | lepriv_intro
      (INCR: inject_incr sm0.(SimMemInj.inj) sm1.(SimMemInj.inj))
      (SRCGENB: sm0.(SimMemInj.src_ge_nb) = sm1.(SimMemInj.src_ge_nb))
      (TGTGENB: sm0.(SimMemInj.tgt_ge_nb) = sm1.(SimMemInj.tgt_ge_nb))
      (FROZEN: SimMemInj.frozen sm0.(SimMemInj.inj) sm1.(SimMemInj.inj) (sm0.(SimMemInj.src_ge_nb)) (sm0.(SimMemInj.tgt_ge_nb)))
      (INVSRC: sm0.(mem_inv_src) = sm1.(mem_inv_src))
      (INVTGT: sm0.(mem_inv_tgt) = sm1.(mem_inv_tgt))
  .

  Global Program Instance SimMemInjInv : SimMem.class :=
    {
      t := t';
      src := SimMemInj.src;
      tgt := SimMemInj.tgt;
      wf := wf' P_src P_tgt;
      le := le';
      lepriv := lepriv;
      (* lift := lift'; *)
      (* unlift := unlift'; *)
      sim_val := fun (mrel: t') => Val.inject mrel.(SimMemInj.inj);
      sim_val_list := fun (mrel: t') => Val.inject_list mrel.(SimMemInj.inj);
    }.
  Next Obligation.
    inv H. inv MLE. econs; eauto.
  Qed.
  Next Obligation.
    inv MLE. inv MLE0. eauto.
  Qed.
  Next Obligation.
    extensionality l0. extensionality l1. eapply prop_ext2.
    induction x0; ss; i; split; intros H; inv H; econs; eauto.
    - eapply IHx0; eauto.
    - eapply IHx0; eauto.
  Qed.
  Next Obligation.
    inv H. ss.
  Qed.

  Lemma unchanged_on_mle (sm0: t') m_src1 m_tgt1 j1
        (WF: SimMemInjInv.wf' P_src P_tgt sm0)
        (INJECT: Mem.inject j1 m_src1 m_tgt1)
        (INCR: inject_incr sm0.(SimMemInj.inj) j1)
        (SEP: inject_separated sm0.(SimMemInj.inj) j1 sm0.(SimMemInj.src) sm0.(SimMemInj.tgt))
        (UNCHSRC: Mem.unchanged_on
                    (loc_unmapped sm0.(SimMemInj.inj))
                    sm0.(SimMemInj.src) m_src1)
        (UNCHTGT: Mem.unchanged_on
                    (loc_out_of_reach sm0.(SimMemInj.inj) sm0.(SimMemInj.src))
                    sm0.(SimMemInj.tgt) m_tgt1)
        (MAXSRC: forall
            b ofs
            (VALID: Mem.valid_block sm0.(SimMemInj.src) b)
          ,
            <<MAX: Mem.perm m_src1 b ofs Max <1= Mem.perm sm0.(SimMemInj.src) b ofs Max>>)
        (MAXTGT: forall
            b ofs
            (VALID: Mem.valid_block sm0.(SimMemInj.tgt) b)
          ,
            <<MAX: Mem.perm m_tgt1 b ofs Max <1= Mem.perm sm0.(SimMemInj.tgt) b ofs Max>>)
    :
      (<<MLE: SimMemInjInv.le' sm0 (mk (SimMemInj.mk
                                       m_src1 m_tgt1 j1
                                       (SimMemInj.src_external sm0)
                                       (SimMemInj.tgt_external sm0)
                                       (SimMemInj.src_parent_nb sm0)
                                       (SimMemInj.tgt_parent_nb sm0)
                                       (SimMemInj.src_ge_nb sm0)
                                       (SimMemInj.tgt_ge_nb sm0)) sm0.(mem_inv_src) sm0.(mem_inv_tgt))>>) /\
      (<<MWF: SimMemInjInv.wf' P_src P_tgt
                               (mk (SimMemInj.mk
                                   m_src1 m_tgt1 j1
                                   (SimMemInj.src_external sm0)
                                   (SimMemInj.tgt_external sm0)
                                   (SimMemInj.src_parent_nb sm0)
                                   (SimMemInj.tgt_parent_nb sm0)
                                   (SimMemInj.src_ge_nb sm0)
                                   (SimMemInj.tgt_ge_nb sm0)) sm0.(mem_inv_src) sm0.(mem_inv_tgt))>>).
  Proof.
    split.
    - assert(FROZEN: SimMemInj.frozen (SimMemInj.inj sm0) j1 (SimMemInj.src_parent_nb sm0) (SimMemInj.tgt_parent_nb sm0)).
      { + econs. ii. des. exploit SEP; eauto. i. des. inv WF. inv WF0. split.
          * clear - H SRCLE. unfold Mem.valid_block in *. red. xomega.
          * clear - H0 TGTLE. unfold Mem.valid_block in *. red. xomega.
      }
      econs; ss; eauto. econs; ss; eauto.
      + eapply Mem.unchanged_on_implies; eauto. inv WF. inv WF0.
        ii. eapply SRCEXT; eauto.
      + eapply Mem.unchanged_on_implies; eauto. inv WF. inv WF0.
        ii. eapply TGTEXT; eauto.
      + inv WF. inv WF0. eapply SimMemInj.frozen_shortened; eauto; try xomega.
    - inv WF. inv WF0. econs; ss; eauto.
      + econs; ss; eauto.
        * etransitivity; eauto.
          ii. destruct PR. split; ss.
          { unfold loc_unmapped. destruct (j1 x0) eqn:BLK; eauto.
            destruct p. exploit SEP; eauto. i. des. clarify. }
          { eapply Plt_Ple_trans; eauto.
            eapply Mem.unchanged_on_nextblock; eauto. }
        * etransitivity; eauto.
          ii. destruct PR. split; ss.
          { ii. destruct (SimMemInj.inj sm0 b0) eqn:BLK.
            - destruct p. dup BLK. eapply INCR in BLK. clarify.
              exploit H; eauto. eapply MAXSRC; eauto.
              eapply Mem.valid_block_inject_1; eauto.
            - exploit SEP; eauto. i. des. clarify. }
          { eapply Plt_Ple_trans; eauto.
            eapply Mem.unchanged_on_nextblock; eauto. }
        * etransitivity; eauto. eapply Mem.unchanged_on_nextblock; eauto.
        * etransitivity; eauto. eapply Mem.unchanged_on_nextblock; eauto.
      + eapply private_unchanged_on_invariant; eauto.
        * ii. eapply Plt_Ple_trans; eauto.
          eapply INVRANGESRC; eauto. apply 0.
        * eapply Mem.unchanged_on_implies; eauto.
          i. eapply INVRANGESRC; eauto.
      + eapply private_unchanged_on_invariant; eauto.
        * ii. eapply Plt_Ple_trans; eauto.
          eapply INVRANGETGT; eauto. apply 0.
        * eapply Mem.unchanged_on_implies; eauto.
          i. eapply INVRANGETGT; eauto.
      + i. eapply INVRANGESRC in INV. des. split; eauto.
        destruct (j1 blk) eqn:BLK; auto.
        destruct p. exploit SEP; eauto. i. des.
        exfalso. eapply H. eapply Plt_Ple_trans; eauto.
      + i. eapply INVRANGETGT in INV. des. split; eauto.
        ii. destruct (SimMemInj.inj sm0 b0) eqn:BLK.
        * destruct p. dup BLK. eapply INCR in BLK. clarify.
          exploit INV; eauto. eapply MAXSRC; eauto.
          eapply Mem.valid_block_inject_1; eauto.
        * exploit SEP; eauto. i. des.
          eapply H2; eauto. eapply Plt_Ple_trans; eauto.
  Qed.

  Definition lift' (mrel0: t'): t' :=
    mk (SimMemInj.mk
          (SimMemInj.src mrel0)
          (SimMemInj.tgt mrel0)
          (SimMemInj.inj mrel0)
          (SimMemInj.src_private mrel0 /2\ fun blk _ => ~ mrel0.(mem_inv_src) blk)
          (SimMemInj.tgt_private mrel0 /2\ fun blk _ => ~ mrel0.(mem_inv_tgt) blk)
          ((SimMemInj.src mrel0).(Mem.nextblock))
          ((SimMemInj.tgt mrel0).(Mem.nextblock))
          ((SimMemInj.src_ge_nb mrel0))
          ((SimMemInj.tgt_ge_nb mrel0)))
       (mem_inv_src mrel0)
       (mem_inv_tgt mrel0)
  .

  Definition unlift' (mrel0 mrel1: t'): t' :=
    mk (SimMemInj.mk
          (SimMemInj.src mrel1)
          (SimMemInj.tgt mrel1)
          (SimMemInj.inj mrel1)
          (SimMemInj.src_external mrel0)
          (SimMemInj.tgt_external mrel0)
          (SimMemInj.src_parent_nb mrel0)
          (SimMemInj.tgt_parent_nb mrel0)
          (SimMemInj.src_ge_nb mrel0)
          (SimMemInj.tgt_ge_nb mrel0)) (mem_inv_src mrel0) (mem_inv_tgt mrel0).

  Lemma unlift_spec : forall mrel0 mrel1 : t',
      le' (lift' mrel0) mrel1 -> wf' P_src P_tgt mrel0 -> le' mrel0 (unlift' mrel0 mrel1).
  Proof.
    i.
    inv H; ss. inv MLE. econs; eauto. inv H0. inv WF. ss.
    econs; ss; eauto; ii; des; ss.
    - eapply Mem.unchanged_on_implies; eauto.
      ii. ss. split; eauto. ii.
      exploit INVRANGESRC; eauto. i. des. eauto.
    - eapply Mem.unchanged_on_implies; eauto.
      ii. ss. split; eauto.
      ii. eapply INVRANGETGT in H1. des. apply H2. eauto.
    - ss. eapply SimMemInj.frozen_shortened; eauto.
  Qed.

  Lemma lift_wf : forall mrel0 : t',
      wf' P_src P_tgt mrel0 ->
      wf' P_src P_tgt (lift' mrel0).
  Proof.
    i. inv H. inv WF. econs; ss; eauto.
    - econs; ss; eauto.
      + ii. des. destruct PR. split; ss.
      + ii. des. destruct PR. split; ss.
      + reflexivity.
      + reflexivity.
      + xomega.
      + xomega.
    - ii. exploit INVRANGESRC; eauto. i. des. splits; eauto.
      + ii. des. clarify.
      + eapply Plt_Ple_trans; eauto.
    - ii. exploit INVRANGETGT; eauto. i. des. splits; eauto.
      + ii. des. clarify.
      + eapply Plt_Ple_trans; eauto.
  Qed.

  Lemma unlift_wf : forall mrel0 mrel1 : t',
      wf' P_src P_tgt mrel0 ->
      wf' P_src P_tgt mrel1 -> le' (lift' mrel0) mrel1 -> wf' P_src P_tgt (unlift' mrel0 mrel1).
  Proof.
    i.
    inv H. inv H0. inv H1. inv WF. inv WF0. inv MLE.
    econs; ss; eauto.
    - econs; ss; try etransitivity; eauto.
      + ii. destruct (classic (mem_inv_src mrel0 x0)).
        * rewrite MINVEQSRC in *. exploit INVRANGESRC0; eauto.
          i. des. split; eauto. ss. destruct PR.
          eapply Mem.valid_block_unchanged_on; eauto.
        * eapply SRCEXT0. rewrite <- SRCPARENTEQ. auto.
      + ii. destruct (classic (mem_inv_tgt mrel0 x0)).
        * rewrite MINVEQTGT in *. exploit INVRANGETGT0; eauto.
          i. des. split; eauto. ss. destruct PR.
          eapply Mem.valid_block_unchanged_on; eauto.
        * eapply TGTEXT0. rewrite <- TGTPARENTEQ. auto.
      + inv SRCUNCHANGED; ss.
      + inv TGTUNCHANGED; ss.
    - rewrite MINVEQSRC. eauto.
    - rewrite MINVEQTGT. eauto.
    - ii. split.
      + eapply INVRANGESRC0. rewrite <- MINVEQSRC. auto.
      + eapply INVRANGESRC; eauto.
    - ii. split.
      + eapply INVRANGETGT0. rewrite <- MINVEQTGT. auto.
      + eapply INVRANGETGT; eauto.
  Qed.

  Global Program Instance lepriv_PreOrder: RelationClasses.PreOrder lepriv.
  Next Obligation.
    ii. econs; eauto. apply SimMemInj.frozen_refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0.
    des; clarify.
    econs; eauto with mem congruence.
    + eapply inject_incr_trans; eauto.
    + econs; eauto.
      ii; des.
      destruct (SimMemInj.inj y b_src) eqn:T.
      * destruct p.
        exploit INCR0; eauto. i; clarify.
        inv FROZEN.
        hexploit NEW_IMPLIES_OUTSIDE; eauto.
      * inv FROZEN0.
        hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
        esplits; congruence.
  Qed.

  Global Program Instance SimMemInjInvLift : SimMemLift.class SimMemInjInv :=
    {
      lift := lift';
      unlift := unlift';
    }.
  Next Obligation.
    eapply lift_wf; eauto.
  Qed.
  Next Obligation.
    eapply unlift_spec; eauto.
  Qed.
  Next Obligation.
    eapply unlift_wf; eauto.
  Qed.
  Next Obligation.
    econs; eauto. ss. eapply SimMemInj.frozen_refl.
  Qed.
  Next Obligation.
    inv MWF. inv MLE. inv MLE0. inv MLIFT.
    econs; ss; et; try congruence.
    - eapply SimMemInj.frozen_refl.
  Qed.

End MEMINJINV.




(* Copied from Unusedglob.v *)
Definition ref_init (il : list init_data) (id : ident): Prop :=
  exists ofs, In (Init_addrof id ofs) il
.

Section SIMSYMBINV.

  Variable P : memblk_invariant.

  Inductive le (ss0: ident -> Prop) (sk_src sk_tgt: Sk.t) (ss1: ident -> Prop): Prop :=
  | symb_le_intro
      (LE: ss0 <1= ss1)
      (OUTSIDE: forall
          id
          (IN: (ss1 -1 ss0) id)
        ,
          <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
  .

  Inductive invariant_globvar F V: globdef F V -> Prop :=
  | invariant_globvar_intro
      v
      (NVOL: v.(gvar_volatile) = false)
      (WRITABLE: v.(gvar_readonly) = false)
      (* (INITD: admit "about init data" v.(gvar_init)) *)
      (INITD: forall
          (ge: Genv.t F V) m b
          (INIT: Genv.load_store_init_data ge m b 0 (gvar_init v))
          (PERM: Mem.range_perm
                   m b 0 (init_data_list_size (gvar_init v)) Cur
                   (Genv.perm_globvar v))
        ,
          inv_sat_blk P b m)
    :
      invariant_globvar (Gvar v)
  .

  Inductive sim_sk (ss: ident -> Prop) (sk_src sk_tgt: Sk.t): Prop :=
  | sim_sk_intro
      (SKSAME: sk_src = sk_tgt)
      (CLOSED: forall id (SS: ss id),
          exists g,
            (<<DEF: sk_tgt.(prog_defmap) ! id = Some g>>) /\
            (<<INV: invariant_globvar g>>) /\
            (<<PRVT: ~ In id (prog_public sk_tgt)>>))
      (NOMAIN: ~ ss sk_src.(prog_main))
      (NOREF: forall
          id gv
          (PROG: sk_tgt.(prog_defmap) ! id  = Some (Gvar gv))
        ,
          <<NOREF: forall id_drop (DROP: ss id_drop), ~ ref_init gv.(gvar_init) id_drop>>)
  .

  Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj)
            (invar: block -> Prop) : Prop :=
  | sken_inject_intro
      (DOMAIN: forall b i (SYMB: Genv.find_symbol ge i = Some b),
          Plt b ge.(Genv.genv_next) ->
          forall (NINV: ~ invar b), j b = Some(b, 0))
      (NDOMAIN: forall b i (SYMB: Genv.find_symbol ge i = Some b),
          Plt b ge.(Genv.genv_next) ->
          forall (NINV: invar b), j b = None)
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) ->
                                  (Plt b1 ge.(Genv.genv_next) \/ Plt b2 ge.(Genv.genv_next)) ->
                                  (<<BLK: b1 = b2>> /\ <<DELTA: delta = 0>>))
  .

  Inductive sim_skenv_inj (sm: t') (ss: ident -> Prop) (skenv_src skenv_tgt: SkEnv.t): Prop :=
  | sim_skenv_inj_intro
      (INVCOMPAT: forall id blk (FIND: skenv_tgt.(Genv.find_symbol) id = Some blk),
          ss id <-> sm.(mem_inv_tgt) blk)
      (PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
      (INJECT: skenv_inject skenv_src sm.(SimMemInj.inj) sm.(mem_inv_tgt))
      (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
      (NBSRC: skenv_src.(Genv.genv_next) = sm.(SimMemInj.src_ge_nb))
      (NBTGT: skenv_tgt.(Genv.genv_next) = sm.(SimMemInj.tgt_ge_nb))
  .

  Lemma skenv_inject_symbols_inject sm ss skenv_src skenv_tgt
        (SKENVINJ: sim_skenv_inj sm ss skenv_src skenv_tgt)
    :
      symbols_inject sm.(SimMemInj.inj) skenv_src skenv_tgt.
  Proof.
    inv SKENVINJ. inv SIMSKENV. inv INJECT. econs; ss. splits.
    - i. exploit IMAGE; eauto.
      + left. eapply Genv.genv_symb_range; eauto.
      + i. des. clarify.
    - i. esplits; eauto.
      exploit DOMAIN; eauto.
      + eapply Genv.genv_symb_range; eauto.
      + ii. eapply PUBKEPT; eauto.
        * unfold Genv.public_symbol, proj_sumbool in *.
          des_ifs. eauto.
        * eapply INVCOMPAT; eauto.
    - i. destruct (Genv.block_is_volatile skenv_tgt b1) eqn:VOL1.
      + dup VOL1. eapply Genv.block_is_volatile_below in VOL1.
        exploit IMAGE; eauto. i. des. clarify.
      + destruct (Genv.block_is_volatile skenv_tgt b2) eqn:VOL2; auto.
        dup VOL2. eapply Genv.block_is_volatile_below in VOL2.
        exploit IMAGE; eauto. i. des. clarify .
  Qed.

  Lemma SimSymbIdInv_skenv_func_bisim sm ss skenv_src skenv_tgt
        (SIMSKENV: sim_skenv_inj sm ss skenv_src skenv_tgt)
    :
      SimSymb.skenv_func_bisim (Val.inject (SimMemInj.inj sm)) skenv_src skenv_tgt.
  Proof.
    inv SIMSKENV. inv SIMSKENV0. econs; ss; eauto.
    - i. assert (fptr_tgt = fptr_src).
      { unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs_safe.
        inv SIMFPTR. inv INJECT.
        exploit IMAGE; eauto.
        - left. eapply Genv.genv_defs_range; eauto.
        - i. des. clarify. }
      clarify. eauto.
    - i. assert (fptr_tgt = fptr_src).
      { unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs_safe.
        inv SIMFPTR; clarify. inv INJECT.
        exploit IMAGE; eauto.
        - right. eapply Genv.genv_defs_range; eauto.
        - i. des. clarify. psimpl. clarify. }
      clarify. eauto.
  Qed.

  (* TODO: from SimSymbDrop *)
  Lemma Mem_getN_forall2:
    forall (P: memval -> memval -> Prop) c1 c2 i n p,
      list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
      p <= i -> i < p + Z.of_nat n ->
      P (ZMap.get i c1) (ZMap.get i c2).
  Proof.
    induction n; simpl Mem.getN; intros.
    - simpl in H1. omegaContradiction.
    - inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p).
      + congruence.
      + apply IHn with (p + 1); auto. omega. omega.
  Qed.

  Lemma init_mem_inject ss sk sk_tgt j m
        (SIMSK: sim_sk ss sk sk_tgt)
        (LOADMEM: Genv.init_mem sk = Some m)
        (SS: forall id, {ss id} + {~ ss id})
        (J: j = fun blk : positive =>
                  if plt blk (Mem.nextblock m)
                  then
                    match Genv.invert_symbol (Genv.globalenv sk) blk with
                    | Some id => if SS id then None else Some (blk, 0)
                    | None => None
                    end
                  else None)
    :
      Mem.inject j m m.
  Proof.
    inv SIMSK.
    hexploit Genv.init_mem_characterization_gen; eauto. intros INIT.
    hexploit Genv.initmem_inject; eauto. unfold Mem.flat_inj. intros INJECT.
    inv INJECT. econs.
    - inv mi_inj. econs.
      + i. eapply mi_perm; eauto. des_ifs.
      + i. eapply mi_align; eauto. des_ifs.
      + i. des_ifs. exploit mi_memval; eauto.
        { des_ifs. }
        intros VAL.
        apply Genv.invert_find_symbol in Heq.
        dup Heq. eapply Genv.find_symbol_inversion in Heq.
        eapply prog_defmap_dom in Heq. des.
        dup Heq. eapply Genv.find_def_symbol in Heq. des. clarify.
        exploit INIT; eauto. i.
        destruct g as [f|v].
        * exfalso. des. exploit H1; try apply H0; eauto. i. des. clarify.
        * destruct (gvar_volatile v) eqn:NVOL.
          { exfalso. des. exploit H1; eauto. i. des.
            unfold Genv.perm_globvar in *. des_ifs. inv H5. }
          des. clear H2.
          generalize (H3 eq_refl). intros LOADDATA. clear H3.
          hexploit NOREF; eauto. clear NOREF. intros NOREF. zsimpl.
          eapply Mem_getN_forall2 with
              (P:=fun m0 : memval =>
                    (fun m1 : memval =>
                       memval_inject
                         (fun blk : positive =>
                            if plt blk (Mem.nextblock m)
                            then
                              match Genv.invert_symbol (Genv.globalenv sk_tgt) blk with
                              | Some id => if SS id then None else Some (blk, 0)
                              | None => None
                              end
                            else None) m0 m1)).
          { Local Transparent Mem.loadbytes. unfold Mem.loadbytes in *.
            des_ifs. repeat rewrite H3.
            clear - NOREF LOADMEM.
            revert NOREF. induction (gvar_init v); ss; i.
            - econs.
            - eapply list_forall2_app.
              + unfold Genv.bytes_of_init_data. des_ifs.
                * eapply inj_bytes_inject.
                * eapply inj_bytes_inject.
                * eapply inj_bytes_inject.
                * eapply inj_bytes_inject.
                * eapply inj_bytes_inject.
                * eapply inj_bytes_inject.
                * induction (Z.to_nat z); ss; econs; eauto. econs.
                * dup Heq. eapply Genv.genv_symb_range in Heq1.
                  erewrite Genv.init_mem_genv_next in *; eauto.
                  eapply Genv.find_invert_symbol in Heq.
                  eapply inj_value_inject. econs.
                  { instantiate (1:=0). des_ifs.
                    exploit NOREF; eauto; clarify.
                    unfold ref_init. ss. eauto. }
                  { psimpl. auto. }
                * eapply list_forall2_imply; [eapply repeat_Undef_inject_self|eauto].
              + eapply IHl; eauto. ii. exploit NOREF; eauto.
                unfold ref_init in *. des. esplits; ss; eauto.
          }
          { eapply H1; eauto. }
          { zsimpl. rewrite nat_of_Z_eq.
            - eapply H1; eauto.
            - eapply init_data_list_size_pos. }
    - i. des_ifs.
    - i. des_ifs.
    - ii. des_ifs. eapply mi_no_overlap; eauto; des_ifs.
    - ii. eapply mi_representable; eauto. des_ifs.
    - i. eapply mi_perm_inv; eauto. des_ifs.
  Qed.

  Lemma sim_skenv_inj_lepriv ss sm0 sm1 skenv_src skenv_tgt
        (MLE: lepriv sm0 sm1)
        (SIMSKENV : sim_skenv_inj sm0 ss skenv_src skenv_tgt)
    :
      sim_skenv_inj sm1 ss skenv_src skenv_tgt.
  Proof.
    inv MLE. inv SIMSKENV.
    destruct sm0, sm1. destruct minj. destruct minj0. ss. clarify.
    rename inj0 into inj1. rename inj into inj0.
    econs; ss; eauto.
    - inv INJECT. econs; ss; eauto.
      + i. destruct (inj1 b) as [[b0 delta]|]eqn:BLK; auto.
        exfalso. inv FROZEN. hexploit NEW_IMPLIES_OUTSIDE; eauto.
        i. des. eapply (Plt_strict b).
        eapply Plt_Ple_trans; eauto.
      + i. destruct (inj0 b1) as [[b0 delta0]|]eqn:BLK; auto.
        * dup BLK. eapply INCR in BLK. clarify.
          eapply IMAGE; eauto.
        * inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des.
          { exfalso. eapply (Plt_strict b1).
            eapply Plt_Ple_trans; eauto. }
          { inv SIMSKENV0. exfalso. eapply (Plt_strict b2).
            eapply Plt_Ple_trans; eauto. }
  Qed.

  Global Program Instance SimSymbIdInv: SimSymb.class (SimMemInjInv top_inv P) :=
    {
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
    inv LE0. inv LE1. econs; eauto.
    i. des.
    destruct (classic (ss1 id)).
    - exploit OUTSIDE; eauto.
    - exploit OUTSIDE0; eauto. i. des.
      inv LINKORD0. inv LINKORD1. des.
      split; eauto.
      + ii. eapply OUTSIDESRC.
        eapply defs_prog_defmap in H6. des.
        eapply defs_prog_defmap. exploit H5; eauto. i. des. eauto.
      + ii. eapply OUTSIDETGT.
        eapply defs_prog_defmap in H6. des.
        eapply defs_prog_defmap. exploit H4; eauto. i. des. eauto.
  Qed.
  Next Obligation.
    inv SIMSK. eauto.
  Qed.
  Next Obligation.
    inv SIMSK. inv SIMSK0. exists (ss0 \1/ ss1).
    hexploit (link_prog_inv sk_tgt0 sk_tgt1); eauto. i. des. clarify.
    esplits; eauto.
    - econs; eauto. i. des; clarify.
      exploit CLOSED0; eauto. i. des.
      assert (~ defs sk_tgt0 id); eauto.
      unfold defs, proj_sumbool. des_ifs.
      eapply prog_defmap_dom in i. des.
      exploit H0; eauto. i. des. clarify.
    - econs; eauto. i. des; clarify.
      exploit CLOSED; eauto. i. des.
      assert (~ defs sk_tgt1 id); eauto.
      unfold defs, proj_sumbool. des_ifs.
      eapply prog_defmap_dom in i. des.
      exploit H0; eauto. i. des. clarify.
    - econs; ss; eauto.
      + i. des.
        * exploit CLOSED; eauto. i. des.
          destruct ((prog_defmap sk_tgt1) ! id) eqn:NONE.
          { exploit H0; eauto. i. des. clarify. }
          esplits; ss; eauto.
          { erewrite prog_defmap_elements.
            erewrite PTree.gcombine; ss.
            rewrite DEF. rewrite NONE. auto. }
          { ii. eapply in_app in H1. des; clarify.
            inv WFSRC1. eapply PUBINCL in H1.
            eapply prog_defmap_spec in H1. des. clarify. }
        * exploit CLOSED0; eauto. i. des.
          destruct ((prog_defmap sk_tgt0) ! id) eqn:NONE.
          { exploit H0; eauto. i. des. clarify. }
          esplits; ss; eauto.
          { erewrite prog_defmap_elements.
            erewrite PTree.gcombine; ss.
            rewrite DEF. rewrite NONE. auto. }
          { ii. eapply in_app in H1. des; clarify.
            inv WFSRC0. eapply PUBINCL in H1.
            eapply prog_defmap_spec in H1. des. clarify. }
      + ii. rewrite H in *. des; clarify.

      + ii.
        assert(T: (In (id, Gvar gv) (prog_defs sk_tgt0))
                  \/ (In (id, Gvar gv) (prog_defs sk_tgt1))).
        { unfold prog_defmap in PROG. ss.
          rewrite PTree_Properties.of_list_elements in *.
          rewrite PTree.gcombine in *; ss.
          unfold link_prog_merge in PROG. clear - PROG. des_ifs.
          - apply PTree_Properties.in_of_list in Heq.
            apply PTree_Properties.in_of_list in Heq0.
            exploit (link_unit_same g g0); et. i; des; clarify; et.
          - apply PTree_Properties.in_of_list in Heq. eauto.
          - apply PTree_Properties.in_of_list in PROG. eauto.
        }
        inv WFSRC0. inv WFSRC1.
        eapply NoDup_norepet in NODUP. eapply NoDup_norepet in NODUP0. des.
        * exploit NOREF; eauto. eapply prog_defmap_norepet; eauto.
        * destruct H1. exploit WFPTR; eauto.
          i. exploit CLOSED0; eauto. i. des.
          eapply prog_defmap_dom in H2. des.
          exploit H0; eauto. i. des.
          exploit CLOSED0; eauto.
        * destruct H1. exploit WFPTR0; eauto.
          i. exploit CLOSED; eauto. i. des.
          eapply prog_defmap_dom in H2. des.
          exploit H0; eauto. i. des.
          exploit CLOSED; eauto.
        * exploit NOREF0; eauto. eapply prog_defmap_norepet; eauto.
  Qed.
  Next Obligation.
    inv SIMSKE. inv SIMSKENV. eauto.
  Qed.
  Next Obligation.
    dup SIMSK. inv SIMSK. eexists.
    assert (inhabited (forall id, {ss id} + {~ ss id})).
    { hexploit (non_dep_dep_functional_choice choice).
      instantiate (1:=fun id => {ss id} + {~ ss id}).
      i. hexploit (H top2).
      - i. destruct (classic (ss x)); eauto.
      - i. des. esplits; eauto. } destruct H as [SS].
    set (j := fun blk => if (plt blk (Mem.nextblock m_src))
                         then match Genv.invert_symbol (Sk.load_skenv sk_tgt) blk with
                              | Some id =>
                                if (SS id) then None else Some (blk, 0)
                              | None => None
                              end
                         else None).
    eexists (mk (SimMemInj.mk _ _ j bot2 bot2 (Mem.nextblock m_src) (Mem.nextblock m_src) _ _) _ _). ss.
    instantiate (1:=fun blk => exists id,
                        (<<FIND: (Sk.load_skenv sk_tgt).(Genv.find_symbol) id = Some blk>>) /\
                        (<<SINV: ss id>>)).
    unfold Sk.load_mem, Sk.load_skenv in *. dup LOADMEMSRC.
    apply Genv.init_mem_genv_next in LOADMEMSRC.
    esplits; eauto.
    - econs; ss; eauto.
      + i. split; i; eauto. des.
        apply Genv.find_invert_symbol in FIND.
        apply Genv.find_invert_symbol in H. clarify.
      + ii. exploit CLOSED; eauto. i. des.
        apply PRVT. rewrite <- Genv.globalenv_public. auto.
      + econs; eauto.
        * i. unfold j. des_ifs.
          { exfalso. eapply NINV.
            eapply Genv.invert_find_symbol in Heq. eauto. }
          { exfalso. eapply Genv.find_invert_symbol in SYMB. clarify. }
          { exfalso. eapply n. rewrite <- LOADMEMSRC. auto. }
        * i. unfold j. des. apply Genv.find_invert_symbol in NINV.
          des_ifs.
        * i. unfold j in *. des_ifs.

    - econs; ss; eauto.
      + econs; ss.
        * eapply init_mem_inject; ss; eauto.
        * refl.
        * refl.
        * rewrite LOADMEMSRC. refl.
        * rewrite LOADMEMSRC. refl.
      + ii. des. exploit CLOSED; eauto. i. des.
        inv INV. erewrite Genv.find_def_symbol in DEF. des. clarify.
        hexploit Genv.init_mem_characterization_gen; eauto.
        i. exploit H; eauto. ss. intros [A [B [C D]]].
        exploit INITD; eauto.
      + instantiate (1:=bot1). clarify.
      + i. des. unfold j. splits; ss.
        * ii. eapply Genv.find_invert_symbol in INV. des_ifs.
        * eapply Genv.genv_symb_range in INV.
          rewrite LOADMEMSRC in *. auto.
    - unfold Genv.symbol_address. des_ifs.
      subst j.
      econs; eauto; cycle 1.
      { psimpl. ss. }
      exploit Genv.genv_symb_range; eauto. intro T.
      erewrite Genv.init_mem_genv_next in T; eauto. des_ifs_safe.
      eapply Genv.find_invert_symbol in Heq. des_ifs.
  Qed.
  Next Obligation.
    eapply sim_skenv_inj_lepriv; eauto.
  Qed.
  (* Next Obligation. *)
  (*   inv SIMSKENV. inv MWF. inv WF. *)
  (*   destruct sm0; ss. destruct minj; ss. econs; ss; eauto. *)
  (*   - ss. etrans; eauto. *)
  (*   - ss. etrans; eauto. *)
  (* Qed. *)
  Next Obligation.
    inv LE. inv SIMSKENV. econs; ss; eauto.
    - i. assert (Genv.find_symbol skenv_link_tgt id = Some blk).
      { exploit SkEnv.project_impl_spec.
        { eapply INCLTGT. } i. inv H. ss.
        erewrite <- SYMBKEEP; eauto.
        apply NNPP. ii. exploit SYMBDROP; eauto. i. red in H0. clarify. }
      exploit INVCOMPAT; eauto. i. des.
      split; eauto; i.
      apply NNPP. intros n. exploit OUTSIDE; eauto.
      i. des. apply OUTSIDETGT.
      unfold SkEnv.project in FIND.
      erewrite Genv_map_defs_symb in FIND. ss.
      unfold Genv.find_symbol in FIND. ss.
      rewrite MapsC.PTree_filter_key_spec in FIND. des_ifs.
    - ii. eapply PUBKEPT; eauto.
      inv INCLSRC. eauto.
    - inv INJECT.
      clear INCLTGT. exploit SkEnv.project_impl_spec; eauto.
      i. inv H.
      econs; ss; eauto.
      + i. eapply DOMAIN; eauto. instantiate (1:=i).
        destruct (classic (defs sk_src i)).
        * rewrite <- SYMBKEEP; eauto.
        * rewrite SYMBDROP in SYMB; eauto. clarify.
      + i. eapply NDOMAIN; eauto. instantiate (1:=i).
        destruct (classic (defs sk_src i)).
        * rewrite <- SYMBKEEP; eauto.
        * rewrite SYMBDROP in SYMB; eauto. clarify.
    - inv SIMSKENV0. inv SIMSK. ss.
  Qed.
  Next Obligation.
    eapply SimSymbIdInv_skenv_func_bisim; eauto.
  Qed.
  Next Obligation.
    inv SIMSKENV. econs; eauto.
    - inv INJECT. econs; eauto.
    - inv SIMSKENV0. ss.
  Qed.
  Next Obligation.
    dup SIMSKENV. inv SIMSKENV. inv SIMSKENV1.
    inv ARGS; ss. dup MWF. inv MWF. inv WF.
    exploit ec_mem_inject; eauto.
    - eapply external_call_spec.
    - eapply skenv_inject_symbols_inject; eauto.
    - i. des.
      exploit unchanged_on_mle; eauto.
      + ii. eapply ec_max_perm; eauto. eapply external_call_spec.
      + ii. eapply ec_max_perm; eauto. eapply external_call_spec.
      + i. des. esplits; eauto.
        * instantiate (1:=Retv.mk vres' m2'). ss.
        * destruct retv_src; ss. econs; ss.
  Qed.

End SIMSYMBINV.
