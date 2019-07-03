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
Require Export SimMemInjInv.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ChoiceFacts.

Set Implicit Arguments.



Section MEMINJINV.

  Variable P_src : memblk_invariant.
  Variable P_tgt : memblk_invariant.

  Global Program Instance SimMemInjInv : SimMem.class :=
    {
      t := t';
      src := SimMemInj.src;
      tgt := SimMemInj.tgt;
      wf := wf' P_src P_tgt;
      le := le';
      lift := lift';
      unlift := unlift';
      sim_val := fun (mrel: t') => Val.inject mrel.(SimMemInj.inj);
      sim_val_list := fun (mrel: t') => Val.inject_list mrel.(SimMemInj.inj);
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
      (INITD: admit "about init data" v.(gvar_init))
      (* (INITD: forall m b (INIT: Genv.load_store_init_data ge m b 0 (gvar_init v)), *)
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
      (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(SimMemInj.src_parent_nb))
      (BOUNDTGT: Ple skenv_tgt.(Genv.genv_next) sm.(SimMemInj.tgt_parent_nb))
      (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
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

  Global Program Instance SimSymbIdInv: SimSymb.class (SimMemInjInv top1 P) :=
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
    eexists (mk (SimMemInj.mk _ _ j bot2 bot2 (Mem.nextblock m_src) (Mem.nextblock m_src)) _ _). ss.
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
      + rewrite <- LOADMEMSRC. refl.
      + rewrite <- LOADMEMSRC. refl.

    - econs; ss; eauto.
      + econs; ss.
        * eapply init_mem_inject; ss; eauto.
        * refl.
        * refl.
      + ii. unfold inv_sat_blk. des. exploit CLOSED; eauto. i. des.
        inv INV.
        admit "fill invariant_globvar".

      + instantiate (1:=bot1). i. des. split; ss.
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
    inv MLE. inv MLE0. inv SIMSKENV.
    destruct sm0, sm1. destruct minj. destruct minj0. ss. clarify.
    rename inj0 into inj1. rename inj into inj0.
    econs; ss; eauto.
    - inv INJECT. econs; ss; eauto.
      + i. destruct (inj1 b) as [[b0 delta]|]eqn:BLK; auto.
        exfalso. inv FROZEN. hexploit NEW_IMPLIES_OUTSIDE; eauto.
        i. des. eapply (Plt_strict b).
        eapply Plt_Ple_trans; eauto. etrans; eauto.
      + i. destruct (inj0 b1) as [[b0 delta0]|]eqn:BLK; auto.
        * dup BLK. eapply INCR in BLK. clarify.
          eapply IMAGE; eauto.
        * inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des.
          { exfalso. eapply (Plt_strict b1).
            eapply Plt_Ple_trans; eauto. etrans; eauto. }
          { inv SIMSKENV0. exfalso. eapply (Plt_strict b2). clear BOUNDSRC.
            eapply Plt_Ple_trans; eauto. etrans; eauto. }
  Qed.
  Next Obligation.
    inv SIMSKENV. inv MWF. inv WF.
    destruct sm0; ss. destruct minj; ss. econs; ss; eauto.
    - ss. etrans; eauto.
    - ss. etrans; eauto.
  Qed.
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
  Next Obligation.
    inv SIMSKENV. econs; eauto.
    - inv INJECT. econs; eauto.
    - inv SIMSKENV0. ss.
  Qed.
  Next Obligation.
    dup SIMSKENV. inv SIMSKENV. inv SIMSKENV1.
    inv ARGS. dup MWF. inv MWF. inv WF.
    ss. rewrite MEMSRC in *. rewrite MEMTGT in *.
    exploit ec_mem_inject; eauto.
    - eapply external_call_spec.
    - eapply skenv_inject_symbols_inject; eauto.
    - i. des.
      exploit lift_wf; eauto. i.
      exploit unchanged_on_mle; eauto.
      + ii. eapply ec_max_perm; eauto. eapply external_call_spec.
      + ii. eapply ec_max_perm; eauto. eapply external_call_spec.
      + i. des. esplits; eauto.
        * instantiate (1:=Retv.mk vres' m2'). ss.
        * ss.
  Qed.

End SIMSYMBINV.
