Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require SimMemId SimMemExt.
From compcertr Require SimMemInj.
Require SoundTop SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ASTC ValuesC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
From compcertr Require Import Events.
Require Import Preservation.

Set Implicit Arguments.

Section MEMORYLEMMAS.
  Lemma mem_store_readonly
        chunk m0 m1 b ofs v
        (STORE: Mem.store chunk m0 b ofs v = Some m1):
    Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    eapply Mem.unchanged_on_implies; try eapply Mem.store_unchanged_on; eauto.
    ii. apply Mem.store_valid_access_3 in STORE. apply H0.
    apply Mem.perm_cur_max. eapply STORE; eauto.
  Qed.

  Lemma mem_free_readonly
        m0 m1 b lo hi
        (STORE: Mem.free m0 b lo hi = Some m1):
      Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    eapply Mem.unchanged_on_implies; try eapply Mem.free_unchanged_on; eauto. ii. apply H0.
    apply Mem.perm_cur_max. eapply Mem.perm_implies; try eapply perm_F_any. eapply Mem.free_range_perm; eauto.
  Qed.

  Lemma mem_readonly_trans
        m0 m1 m2
        (UNCH0: Mem.unchanged_on (loc_not_writable m0) m0 m1)
        (UNCH1: Mem.unchanged_on (loc_not_writable m1) m1 m2):
      Mem.unchanged_on (loc_not_writable m0) m0 m2.
  Proof.
    inv UNCH0. inv UNCH1. econs.
    - etrans; eauto.
    - ii. exploit unchanged_on_perm; eauto. i. etrans; eauto. eapply unchanged_on_perm0; eauto.
      + ii. eapply unchanged_on_perm in H2; eauto.
      + unfold Mem.valid_block in *. eapply Plt_Ple_trans; eauto.
    - ii. exploit unchanged_on_contents; eauto. i. etrans; try apply H1.
      eapply unchanged_on_contents0; eauto.
      + ii. eapply unchanged_on_perm in H2; eauto. eapply Mem.perm_valid_block; eauto.
      + eapply unchanged_on_perm; eauto. eapply Mem.perm_valid_block; eauto.
  Qed.

  Lemma mem_free_list_readonly
        m0 m1 ls
        (STORE: Mem.free_list m0 ls = Some m1):
      Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    revert m0 m1 STORE. induction ls; ss; i; clarify; try refl.
    des_ifs. eapply mem_readonly_trans; eauto. eapply mem_free_readonly; eauto.
  Qed.

  Lemma mem_alloc_readonly
        m0 m1 b lo hi
        (STORE: Mem.alloc m0 lo hi = (m1, b)):
      Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    eapply Mem.unchanged_on_implies; try eapply Mem.alloc_unchanged_on; eauto.
  Qed.

End MEMORYLEMMAS.


Lemma SymSymbId_SymSymbDrop_bot sm_arg ss_link ge_src ge_tgt sk_src sk_tgt
      (SIMSKE: SimMemInjC.sim_skenv_inj sm_arg ss_link ge_src ge_tgt)
  :
    SimSymbDrop.sim_skenv sm_arg (SimSymbDrop.mk bot1 sk_src sk_tgt) ge_src ge_tgt.
Proof.
  inv SIMSKE. ss. unfold SimSymbId.sim_skenv in *. clarify.
  inv INJECT. ss.
  econs; ss; i.
  + exploit DOMAIN; eauto.
    { instantiate (1:=blk_src). exploit Genv.genv_symb_range; eauto. }
    i. clarify. esplits; eauto.
  + esplits; eauto. exploit DOMAIN; eauto. exploit Genv.genv_symb_range; eauto.
  + esplits; eauto. exploit DOMAIN; eauto. exploit Genv.genv_symb_range; eauto.
  + exploit DOMAIN; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. rewrite SIMVAL in *. inv H. esplits; eauto.
  + exploit DOMAIN.
    { instantiate (1:=blk_src0). exploit Genv.genv_symb_range; eauto. } i.
    rewrite SIMVAL0 in *. inv H.
    exploit IMAGE; try apply SIMVAL1.
    { exploit Genv.genv_symb_range; eauto. }
    i. etrans; eauto.
  + exploit IMAGE; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. clarify.
    exploit DOMAIN; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. rewrite SIMVAL in *. inv H. esplits; eauto.
Qed.

Lemma sim_inj_drop_bot_id
      sk_src sk_tgt src
      (DROP: exists mp,
          (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
          /\ (<<SRC: mp.(ModPair.src) = src>>)
          /\ (<<TGT: mp.(ModPair.tgt) = src>>)
          /\ (<<SSBOT: mp.(ModPair.ss) = (SimSymbDrop.mk bot1 sk_src sk_tgt)>>)):
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src>>).
Proof.
  des. clarify. destruct mp eqn: EQ. ss. clarify. inv SIM. ss.
  unfold ModPair.to_msp in *. ss.
  eexists (ModPair.mk _ _ _). esplits; ss. instantiate (1:=(SimSymbId.mk sk_src sk_tgt)).
  econs; ss.
  { inv SIMSK. ss. }
  unfold ModPair.to_msp. ss.
  i. destruct ss_link.
  exploit SIMMS; [apply INCLSRC|apply INCLTGT|..]; eauto.
  { inv SSLE. instantiate (1:=SimSymbDrop.mk bot1 src src).
    econs; ss; try apply Linking.linkorder_refl. i. des. clarify. }
  { instantiate (1:=sm_init_link). exploit SymSymbId_SymSymbDrop_bot; eauto. }
  i. inv H. ss. econs; try eassumption; eauto; ss. i.
  exploit SIM; eauto. inv SIMSKENV. ss. econs; ss.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKE; eauto.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKELINK; eauto.
Unshelve.
  all: ss.
Qed.

Inductive def_match A V: globdef A V -> globdef A V -> Prop :=
| def_match_gfun f: def_match (Gfun f) (Gfun f)
| def_match_gvar inf init0 init1 ro vol:
    def_match
      (Gvar (mkglobvar inf init0 ro vol))
      (Gvar (mkglobvar inf init1 ro vol)).

Program Instance def_match_reflexive A V : Reflexive (@def_match A V).
Next Obligation.
Proof. i. destruct x; try econs. destruct v; try econs. Qed.

Lemma def_match_refl A V (g: globdef A V):
    def_match g g.
Proof. refl. Qed.
Hint Resolve def_match_refl.

Inductive meminj_match_globals F V (R: globdef F V -> globdef F V -> Prop)
          (ge_src ge_tgt: Genv.t F V) (j: meminj) : Prop :=
| meminj_match_globals_intro
    (DEFLE: forall
        b_src b_tgt delta d_src
        (FINDSRC: Genv.find_def ge_src b_src = Some d_src)
        (INJ: j b_src = Some (b_tgt, delta)),
        exists d_tgt,
          (<<FINDTGT: Genv.find_def ge_tgt b_tgt = Some d_tgt>>) /\
          (<<DELTA: delta = 0>>) /\
          (<<DEFMATCH: R d_src d_tgt>>))
    (SYMBLE: forall
        i b_src
        (FINDSRC: Genv.find_symbol ge_src i = Some b_src),
        exists b_tgt,
          (<<FINDTGT: Genv.find_symbol ge_tgt i = Some b_tgt>>) /\
          (<<INJ: j b_src = Some (b_tgt, 0)>>)).

Lemma SimSymbDrop_match_globals F `{HasExternal F} V sm0 sk_src sk_tgt skenv_src skenv_tgt (p: program F V)
      (SIMSKE: SimSymbDrop.sim_skenv sm0 (SimSymbDrop.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt):
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0).
Proof.
  inv SIMSKE. econs.
  - i. unfold SkEnv.revive in *. exists d_src.
    apply Genv_map_defs_def in FINDSRC. des.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP. des_ifs_safe.
    apply Genv.invert_find_symbol in Heq0.
    exploit SIMDEF; try apply FIND; eauto. i. des. clarify. esplits; eauto.
    exploit Genv_map_defs_def_inv; try apply DEFTGT. i. rewrite H0.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst. erewrite Genv.find_invert_symbol.
    + rewrite Heq1; eauto.
    + exploit SIMSYMB1; eauto. i. des. eauto.
  - i. unfold SkEnv.revive in *. rewrite Genv_map_defs_symb in FINDSRC.
    exploit SIMSYMB2; try apply FINDSRC; eauto.
Qed.

Lemma SimSymbDrop_symbols_inject sm0 ss_link skenv_src skenv_tgt
      (SIMSKELINK: SimSymbDrop.sim_skenv sm0 ss_link skenv_src skenv_tgt):
    symbols_inject (SimMemInj.inj sm0) skenv_src skenv_tgt.
Proof.
  inv SIMSKELINK. econs; esplits; ss; i.
  - unfold Genv.public_symbol, proj_sumbool. rewrite PUB in *. des_ifs; ss.
    + exploit SIMSYMB3; eauto. i. des. clarify.
    + exploit SIMSYMB2; eauto. i. des. clarify.
  - exploit SIMSYMB1; eauto. i. des. eauto.
  - exploit SIMSYMB2; eauto.
    { unfold Genv.public_symbol, proj_sumbool in *. des_ifs. eauto. }
    i. des. eauto.
  - unfold Genv.block_is_volatile, Genv.find_var_info.
    destruct (Genv.find_def skenv_src b1) eqn:DEQ.
    + exploit SIMDEF; eauto. i. des. clarify. rewrite DEFTGT. eauto.
    + des_ifs_safe. exfalso. exploit SIMDEFINV; eauto. i. des. clarify.
Qed.

Lemma match_globals_find_funct F V (ge_src ge_tgt: Genv.t F V) j fptr_src fptr_tgt d
      (FINDSRC: Genv.find_funct ge_src fptr_src = Some d)
      (GENV: meminj_match_globals eq ge_src ge_tgt j)
      (FPTR: Val.inject j fptr_src fptr_tgt):
    Genv.find_funct ge_tgt fptr_tgt = Some d.
Proof.
  inv GENV. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
  inv FPTR. exploit DEFLE; eauto. i. des. clarify. des_ifs.
Qed.

Lemma SimSymbDrop_find_None F `{HasExternal F} V (p: program F V)
      sm0 sk_src sk_tgt skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimSymbDrop.sim_skenv sm0 (SimSymbDrop.mk bot1 sk_src sk_tgt) skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef):
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  unfold Genv.find_funct, Genv.find_funct_ptr, SkEnv.revive, o_bind, o_bind2, o_join, o_map, curry2, fst in *.
  des_ifs_safe. exfalso. ss. apply Genv_map_defs_def in Heq. des. des_ifs_safe.
  apply Genv.invert_find_symbol in Heq0. inv SIMSKE. ss. inv FPTR; clarify.
  exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
  erewrite Integers.Ptrofs.add_zero in H4. clarify.
  exploit Genv_map_defs_def_inv; try apply DEFSRC.
  i. revert FINDSRC. rewrite H0.
  erewrite Genv.find_invert_symbol.
  - rewrite Heq1; eauto. i. des_ifs.
  - exploit SIMSYMB3; eauto. i. des.
    replace b1 with blk_src; clarify. eapply DISJ; eauto.
Qed.

Require MatchSimModSem.

Lemma any_id
      (md: Mod.t)
      (WF: Sk.wf md):
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = md>>)
      /\ (<<TGT: mp.(ModPair.tgt) = md>>).
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=(SimSymbId.mk md md)). econs; ss; i.
  rewrite SIMSKENVLINK in *. inv SIMSKENVLINK. inv SSLE.
  eapply MatchSimModSem.match_states_sim; ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - instantiate (1:= fun _ st_src st_tgt sm0 =>
                       (<<EQ: st_src = st_tgt>>) /\
                       (<<MWF: sm0.(SimMemId.src) = sm0.(SimMemId.tgt)>>)).
    ss. i. inv SIMARGS; ss; esplits; eauto; try congruence; ss.
    assert(rs_tgt = rs_src) by (eapply functional_extensionality; r in RS; ss). congruence.
  - ii. destruct args_src, args_tgt, sm_arg; inv SIMARGS; ss; clarify.
    assert(rs_tgt = rs_src) by (eapply functional_extensionality; r in RS; ss). subst. eauto.
  - ii. ss. des. clarify.
  - i. ss. des. clarify. destruct args_src, sm0; ss; clarify.
    + eexists _, (SimMemId.mk _ _). ss. esplits; eauto.
      * econs; ss; eauto.
      * instantiate (1:=top4). ss.
    + eexists _, (SimMemId.mk _ _). ss. esplits; eauto.
      * econs 2; ss; eauto.
  - i. clear HISTORY. ss.
    destruct sm_ret, retv_src, retv_tgt; inv SIMRET; des; ss; clarify; eexists (SimMemId.mk _ _); esplits; eauto.
    assert(rs_tgt = rs_src) by (eapply functional_extensionality; r in RS; ss). congruence.
  - i. ss. des. destruct sm0. ss. clarify. destruct retv_src; ss; eexists (SimMemId.mk m m); esplits; eauto.
    + econs; ss; eauto.
    + econs 2; ss; eauto.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1. eexists (SimMemId.mk _ _). ss.
      esplits; eauto.
      left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
Unshelve.
  all: ss.
Qed.
