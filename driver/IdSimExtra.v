Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.

Set Implicit Arguments.

Lemma SymSymbId_SymSymbDrop_bot sm_arg ss_link ge_src ge_tgt
      (SIMSKE: SimMemInjC.sim_skenv_inj sm_arg ss_link ge_src ge_tgt)
  :
    SimSymbDrop.sim_skenv sm_arg bot1 ge_src ge_tgt.
Proof.
  inv SIMSKE. ss. unfold SimSymbId.sim_skenv in *. clarify.
  inv INJECT. ss.
  econs; ss; i.
  + exploit DOMAIN; eauto.
    { instantiate (1:=blk_src).
      exploit Genv.genv_symb_range; eauto. }
    i. clarify. esplits; eauto.
  + esplits; eauto. exploit DOMAIN; eauto.
    exploit Genv.genv_symb_range; eauto.
  + esplits; eauto. exploit DOMAIN; eauto.
    exploit Genv.genv_symb_range; eauto.
  + exploit DOMAIN; eauto.
    { exploit Genv.genv_defs_range; eauto. }
    i. rewrite SIMVAL in *. inv H. esplits; eauto.
  + exploit DOMAIN.
    { instantiate (1:=blk_src0).
      exploit Genv.genv_symb_range; eauto. } i.
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
      src
      (DROP: exists mp,
          (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
          /\ (<<SRC: mp.(ModPair.src) = src>>)
          /\ (<<TGT: mp.(ModPair.tgt) = src>>)
          /\ (<<SSBOT: mp.(ModPair.ss) = bot1>>))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src>>).
Proof.
  des. clarify. destruct mp eqn: EQ. ss. clarify. inv SIM. ss.
  unfold ModPair.to_msp in *. ss.
  eexists (ModPair.mk _ _ _). esplits; ss. instantiate (1:=tt).
  econs; ss. unfold ModPair.to_msp. ss.
  i. destruct ss_link.
  exploit SIMMS; [apply INCLSRC|apply INCLTGT|..]; eauto.
  { inv SSLE. instantiate (1:=bot1). econs; ss. i. des. clarify. }
  { instantiate (1:=sm_init_link).
    exploit SymSymbId_SymSymbDrop_bot; eauto. }
  i. inv H. ss.
  econs; ss; eauto. i. exploit SIM; eauto.
  inv SIMSKENV. ss. econs; ss.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKE; eauto.
  - exploit SymSymbId_SymSymbDrop_bot; try apply SIMSKELINK; eauto.
Qed.

Inductive def_match A V: globdef A V -> globdef A V -> Prop :=
| def_match_gfun f: def_match (Gfun f) (Gfun f)
| def_match_gvar inf init0 init1 ro vol
  :
    def_match
      (Gvar (mkglobvar inf init0 ro vol))
      (Gvar (mkglobvar inf init1 ro vol))
.

Program Instance def_match_reflexive A V : Reflexive (@def_match A V).
Next Obligation.
Proof.
  i. destruct x; try econs. destruct v; try econs.
Qed.

Lemma def_match_refl A V (g: globdef A V)
  :
    def_match g g
.
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

Lemma SimSymbDrop_match_globals F `{HasExternal F} V sm0 skenv_src skenv_tgt (p: program F V)
      (SIMSKE: SimSymbDrop.sim_skenv sm0 bot1 skenv_src skenv_tgt)
  :
    meminj_match_globals
      eq
      (SkEnv.revive skenv_src p)
      (SkEnv.revive skenv_tgt p)
      (SimMemInj.inj sm0).
Proof.
  inv SIMSKE. econs.
  - i. unfold SkEnv.revive in *. exists d_src.
    apply Genv_map_defs_def in FINDSRC. des.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
    des_ifs_safe.
    apply Genv.invert_find_symbol in Heq0.
    exploit SIMDEF; try apply FIND; eauto. i. des. clarify.
    esplits; eauto.
    exploit Genv_map_defs_def_inv; try apply DEFTGT.
    i. rewrite H0.
    unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
    erewrite Genv.find_invert_symbol.
    + rewrite Heq1; eauto.
    + exploit SIMSYMB1; eauto. i. des. eauto.
  - i. unfold SkEnv.revive in *.
    rewrite Genv_map_defs_symb in FINDSRC.
    exploit SIMSYMB2; try apply FINDSRC; eauto.
Qed.

Lemma SimSymbDrop_symbols_inject sm0 ss_link skenv_src skenv_tgt
      (SIMSKELINK: SimSymbDrop.sim_skenv sm0 ss_link skenv_src skenv_tgt)
  :
    symbols_inject (SimMemInj.inj sm0) skenv_src skenv_tgt.
Proof.
  inv SIMSKELINK. econs; esplits; ss; i.
  - unfold Genv.public_symbol, proj_sumbool.
    rewrite PUB in *. des_ifs; ss.
    + exploit SIMSYMB3; eauto. i. des. clarify.
    + exploit SIMSYMB2; eauto. i. des. clarify.
  - exploit SIMSYMB1; eauto. i. des. eauto.
  - exploit SIMSYMB2; eauto.
    { unfold Genv.public_symbol, proj_sumbool in *. des_ifs. eauto. }
    i. des. eauto.
  - unfold Genv.block_is_volatile, Genv.find_var_info.
    destruct (Genv.find_def skenv_src b1) eqn:DEQ.
    + exploit SIMDEF; eauto. i. des. clarify.
      rewrite DEFTGT. eauto.
    + des_ifs_safe. exfalso. exploit SIMDEFINV; eauto.
      i. des. clarify.
Qed.

Lemma match_globals_find_funct F V (ge_src ge_tgt: Genv.t F V) j fptr_src fptr_tgt d
      (FINDSRC: Genv.find_funct ge_src fptr_src = Some d)
      (GENV: meminj_match_globals eq ge_src ge_tgt j)
      (FPTR: Val.inject j fptr_src fptr_tgt)
  :
    Genv.find_funct ge_tgt fptr_tgt = Some d.
Proof.
  inv GENV. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
  inv FPTR. exploit DEFLE; eauto. i. des. clarify. des_ifs.
Qed.

Lemma SimSymbDrop_find_None F `{HasExternal F} V (p: program F V)
      sm0 skenv_src skenv_tgt fptr_src fptr_tgt
      (FINDSRC: Genv.find_funct (SkEnv.revive skenv_src p) fptr_src = None)
      (SIMSKE: SimSymbDrop.sim_skenv sm0 bot1 skenv_src skenv_tgt)
      (FPTR: Val.inject (SimMemInj.inj sm0) fptr_src fptr_tgt)
      (FPTRDEF: fptr_src <> Vundef)
  :
    Genv.find_funct (SkEnv.revive skenv_tgt p) fptr_tgt = None.
Proof.
  unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. exfalso.
  unfold SkEnv.revive in *. ss.
  apply Genv_map_defs_def in Heq. des.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
  des_ifs_safe.
  apply Genv.invert_find_symbol in Heq0.
  inv SIMSKE. ss. inv FPTR; clarify.
  exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
  erewrite Integers.Ptrofs.add_zero in H4. clarify.
    exploit Genv_map_defs_def_inv; try apply DEFSRC.
  i. revert FINDSRC. rewrite H0.
  unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
  erewrite Genv.find_invert_symbol.
  - rewrite Heq1; eauto. i. des_ifs.
  - exploit SIMSYMB3; eauto. i. des.
    assert (blk_src = b1).
    { exploit DISJ; eauto. }
    clarify.
Qed.
