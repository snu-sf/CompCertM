Require Import Events.
Require Import Values.
Require Import AST.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import IntegersC.
Require Import ASTC.
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimSymb.
Require Import SimMem.
Require Import SimMemInjC.
Require Import ModSem.

Local Existing Instance Val.mi_normal.


(* Copied from Unusedglob.v *)
Definition ref_init (il : list init_data) (id : ident): Prop := 
  exists ofs, In (Init_addrof id ofs) il
.

Section MEMINJ.

(* Definition t': Type := ident -> bool. *)
Definition t': Type := ident -> Prop.

Inductive sim_sk (ss: t') (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (KEPT: forall
        id
        (KEPT: ~ ss id)
      ,
       sk_tgt.(prog_defmap) ! id = sk_src.(prog_defmap) ! id)
    (DROP: forall
        id
        (DROP: ss id)
      ,
        sk_tgt.(prog_defmap) ! id = None)
    (* (SIMSK: forall *)
    (*     id *)
    (*   , *)
    (*    sk_tgt.(prog_defmap) ! id = if ss id then None else sk_src.(prog_defmap) ! id) *)
    (CLOSED: ss <1= sk_src.(privs))
    (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
    (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
    (NOREF: forall
        id gv
        (PROG: sk_tgt.(prog_defmap) ! id  = Some (Gvar gv))
      ,
        <<NOREF: forall id_drop (DROP: ss id_drop), ~ ref_init gv.(gvar_init) id_drop>>)
    (NODUP: NoDup (prog_defs_names sk_tgt))
.

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        (<<DELTA: delta = 0>>) /\
        (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
        (<<KEPT: ~ ss id>>)
    )
    (SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>))
    (SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          (<<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>)
    (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    )
    (SIMDEF: forall
        blk_src blk_tgt delta def_src
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, (<<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>))
    (DISJ: forall
        id blk_src0 blk_src1 blk_tgt
        (SYMBSRC: Genv.find_symbol skenv_src id = Some blk_src0)
        (SIMVAL0: sm0.(SimMemInj.inj) blk_src0 = Some (blk_tgt, 0))
        (SIMVAL1: sm0.(SimMemInj.inj) blk_src1 = Some (blk_tgt, 0))
      ,
        blk_src0 = blk_src1)
    (SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, (<<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>))
    (PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
    (PUB: skenv_src.(Genv.genv_public) = skenv_tgt.(Genv.genv_public))
.

Theorem sim_skenv_symbols_inject
        sm0 ss0 skenv_src skenv_tgt
        (SIMSKENV: sim_skenv sm0 ss0 skenv_src skenv_tgt)
  :
    <<SINJ: symbols_inject sm0.(SimMemInj.inj) skenv_src skenv_tgt>>
.
Proof.
  { clear - SIMSKENV.
    inv SIMSKENV; ss.
    rr. esplits; ii; ss.
    - unfold Genv.public_symbol.
      rewrite <- PUB.
      destruct (Genv.find_symbol skenv_tgt id) eqn:T.
      + exploit SIMSYMB3; et. i; des. rewrite BLKSRC. ss.
      + des_ifs. des_sumbool. ii.
        exploit PUBKEPT; et.
        apply NNPP. ii.
        exploit SIMSYMB2; et. i; des. clarify.
    - exploit SIMSYMB1; eauto. i; des. esplits; et.
    - exploit SIMSYMB2; eauto.
      { ii. eapply PUBKEPT; eauto. unfold Genv.public_symbol in H. des_ifs. des_sumbool. ss. }
      i; des.
      esplits; eauto.
    - unfold Genv.block_is_volatile, Genv.find_var_info.
      destruct (Genv.find_def skenv_src b1) eqn:T0.
      { exploit SIMDEF; try eassumption.
        i; des.
        des_ifs.
      }
      destruct (Genv.find_def skenv_tgt b2) eqn:T1.
      { exploit SIMDEFINV; try eassumption.
        i; des.
        des_ifs.
      }
      ss.
  }
Qed.

Definition sim_skenv_splittable (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
    (<<SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        (<<DELTA: delta = 0>>) /\
        (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
        (<<KEPT: ~ ss id>>)
    >>)
    /\
    (<<SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>)>>)
    /\
    (<<SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          (<<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>)
    (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    >>)
    /\
    (<<SIMDEF: forall
        blk_src blk_tgt delta def_src
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, (<<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>)>>)
    /\
    (<<DISJ: forall
        id blk_src0 blk_src1 blk_tgt
        (SYMBSRC: Genv.find_symbol skenv_src id = Some blk_src0)
        (SIMVAL0: sm0.(SimMemInj.inj) blk_src0 = Some (blk_tgt, 0))
        (SIMVAL1: sm0.(SimMemInj.inj) blk_src1 = Some (blk_tgt, 0))
      ,
        blk_src0 = blk_src1>>)
    /\
    (<<SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, (<<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>)>>)
    /\
    (<<PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss>>)
    /\
    (<<PUB: skenv_src.(Genv.genv_public) = skenv_tgt.(Genv.genv_public)>>)
.

Theorem sim_skenv_splittable_spec
  :
    (sim_skenv_splittable <4= sim_skenv) /\ (sim_skenv <4= sim_skenv_splittable)
.
Proof.
  split; ii; inv PR; ss; des; econs; eauto.
  splits; ss.
Qed.

Inductive le (ss0: t') (sk_src sk_tgt: Sk.t) (ss1: t'): Prop :=
| le_intro
    (LE: ss0 <1= ss1)
    (OUTSIDE: forall
        id
        (IN: (ss1 -1 ss0) id)
      ,
        <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
.

Global Program Definition link_ss (ss0 ss1: t'): option t' :=
  (* Some (fun id => orb (ss0 id) (ss1 id)) *)
  Some (ss0 \1/ ss1)
.

Global Program Instance Linker_t: Linker t' := {|
  link := link_ss;
  linkorder (ss0 ss1: t') := ss0 <1= ss1;
|}.


Lemma linkorder_defs
      F V
      `{Linker F} `{Linker V}
      (p0 p1: AST.program F V)
      (LINKORD: linkorder p0 p1)
  :
    <<DEFS: p0.(defs) <1= p1.(defs)>>
.
Proof.
  inv LINKORD.
  ii. u in *. des.
  simpl_bool. des_sumbool. apply prog_defmap_spec in PR. des.
  exploit H3; try eassumption. i; des.
  apply prog_defmap_spec. esplits; eauto.
Qed.

Lemma Genv_invert_symbol_none_spec
      F V
      (ge: Genv.t F V)
      b
  :
    <<INV: Genv.invert_symbol ge b = None>> <-> <<FIND: forall id, Genv.find_symbol ge id <> Some b>>
.
Proof.
  unfold Genv.find_symbol, Genv.invert_symbol in *.
  abstr (Genv.genv_symb ge) tree.
  split; i; des; red.
  - generalize dependent H.
    eapply PTree_Properties.fold_rec; ii; ss; clarify.
    + eapply H0; eauto. erewrite H; eauto.
    + erewrite PTree.gempty in H0. ss.
    + des_ifs.
      rewrite PTree.gsspec in *. des_ifs.
      eapply H1; eauto.
  -
    eapply PTree_Properties.fold_rec; ii; ss; clarify.
    des_ifs.
    contradict H. ii. eapply H; eauto.
Qed.


Global Program Instance SimSymbDrop: SimSymb.class SimMemInj := {
  t := t';
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}
.
(* Next Obligation. *)
(*   inv SIMSK. *)
(*   econs; eauto. *)
(*   ii. *)
(*   destruct (classic (ss id)). *)
(*   - erewrite DROP in *; eauto. ss. *)
(*   - erewrite <- KEPT; ss. *)
(*     esplits; eauto. *)
(*     reflexivity. *)
(* Qed. *)
Next Obligation.
  econs; eauto. ii. des; ss.
Qed.
Next Obligation.
  inv LE0. inv LE1.
  econs; eauto.
  ii; des.
  specialize (OUTSIDE id).
  specialize (OUTSIDE0 id).
  destruct (classic (ss1 id)).
  - exploit OUTSIDE; eauto.
  - exploit OUTSIDE0; eauto. i; des.
    hexploit (linkorder_defs LINKORD0); eauto. i; des.
    hexploit (linkorder_defs LINKORD1); eauto. i; des.
    esplits; eauto.
Qed.
Next Obligation.
  inv SIMSK. inv WFSRC.
  econs; et.
  i. apply prog_defmap_norepet in IN; cycle 1.
  { apply NoDup_norepet; ss. }
  destruct (classic (ss0 id_to)).
  - exploit NOREF; et; ss.
    rr. esplits; et.
  - assert(KEPT0: ~ ss0 id_fr).
    { ii. exploit DROP; et. i; clarify. }
    dup IN.
    rewrite KEPT in IN; ss.
    exploit WFPTR; et.
    { eapply in_prog_defmap; et. }
    i; des.
    eapply prog_defmap_spec in H0. des.
    eapply prog_defmap_image; et.
    erewrite KEPT; et.
Qed.
Next Obligation.
  admit "See 'link_match_program' in Unusedglobproof.v.
Note that we have one more goal (exists ss) but it is OK, as the 'link_match_program' proof already proves it.".
Qed.
Next Obligation.
  inv SIMSKE. unfold Genv.public_symbol. apply func_ext1. intro i0.
  destruct (Genv.find_symbol skenv_tgt i0) eqn:T.
  - exploit SIMSYMB3; et. i; des. des_ifs. rewrite PUB. ss.
  -  des_ifs. des_sumbool. ii. eapply PUBKEPT in H. exploit SIMSYMB2; et. i; des. clarify.
Qed.
Next Obligation.
  admit "See 'init_meminj_preserves_globals' in Unusedglobproof.v".
Qed.
Next Obligation.
  admit "The proof must exist in Unusedglobproof.v. See match_stacks_preserves_globals, match_stacks_incr".
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
Qed.
Next Obligation.
  set (SkEnv.project skenv_link_src sk_src) as skenv_src.
  generalize (SkEnv.project_impl_spec INCLSRC); intro LESRC.
  set (SkEnv.project skenv_link_tgt sk_tgt) as skenv_tgt.
  generalize (SkEnv.project_impl_spec INCLTGT); intro LETGT.
  exploit SkEnv.project_spec_preserves_wf; try apply LESRC; eauto. intro WFSMALLSRC.
  exploit SkEnv.project_spec_preserves_wf; try apply LETGT; eauto. intro WFSMALLTGT.
(* THIS IS TOP *)
  inv SIMSKENV. ss.
  apply sim_skenv_splittable_spec.
  folder.
  dsplits; eauto; ii; ss.
  - (* SIMSYMB1 *)
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    exploit SIMSYMB1; eauto. { rewrite <- KEEP. ss. } i; des.

    inv LETGT.
    destruct (classic (defs sk_tgt id)); cycle 1.
    { erewrite SYMBDROP0; ss.
      exfalso.
      clear - LE KEPT H H0 SIMSK.
      apply H0. clear H0.
      inv SIMSK.
      u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss. esplits; eauto.
      - exfalso. apply KEPT. inv LE. eauto.
    }
    erewrite SYMBKEEP0; ss.
    esplits; eauto.
    {
      clear - LE H0 KEPT.
      inv LE.
      ii. apply KEPT.
      apply NNPP. ii.
      exploit OUTSIDE; eauto. { split; eauto. }
    }


  - (* SIMSYMB2 *)
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    rewrite KEEP in *.
    exploit (SIMSYMB2 id); eauto.
    { inv LE. ii. eapply KEPT. specialize (OUTSIDE id).
      exploit OUTSIDE; eauto. i; des. ss.
    }
    i; des.
    esplits; eauto.

    inv LETGT.
    erewrite SYMBKEEP0; ss.
    destruct (classic (defs sk_tgt id)); ss.
    { exfalso.
      clear - LE KEPT H H0 SIMSK.
      apply H0. clear H0.
      inv SIMSK.
      u in *.
      simpl_bool. des_sumbool. rewrite prog_defmap_spec in *.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss.
      - exfalso. apply KEPT. ss.
    }

  - (* SIMSYMB3 *)
    inv LETGT.
    destruct (classic (defs sk_tgt id)); cycle 1. 
    { exploit SYMBDROP; eauto. i; des. clarify. }

    erewrite SYMBKEEP in *; ss.
    exploit SIMSYMB3; eauto. i; des.
    esplits; eauto.

    inv LESRC.
    erewrite SYMBKEEP0; ss.

    { clear - H SIMSK.
      inv SIMSK.
      u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); ss.
      { erewrite DROP in *; ss. }
      exploit KEPT; eauto. i; des. rewrite <- H1. esplits; eauto.
    }

  - (* SIMDEF *)

    inv LESRC.
    inv WFSMALLSRC. exploit DEFSYMB; eauto. intro SYMBSMALL; des. rename SYMB into SYMBSMALL.
    destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des. rewrite SYMBSMALL in *. symmetry in SYMBBIG.
    inv WFSRC.
    exploit SYMBDEF; eauto. i; des.
    exploit SIMDEF; eauto. i; des. clarify.

    exploit SPLITHINT; eauto. i; des.
    move DEFSRC at bottom. move H0 at bottom.

    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    rename H1 into KEEP.
    clarify.

    (* assert(def_src = def_tgt). *)
    (* { exploit DEFKEEP; eauto. eapply Genv.find_invert_symbol; eauto. i. *)
    (*   rewrite DEFSRC in *. rewrite H0 in *. des. clarify. } clarify. *)
    esplits; eauto.

    inv LETGT.
    exploit SIMSYMB1; eauto. i; des.


    destruct (Genv.find_def skenv_tgt blk_tgt) eqn:T.
    { exploit DEFKEPT0; eauto.
      { eapply Genv.find_invert_symbol; eauto. }
      i; des.
      clarify.
      inv SIMSK.
      specialize (KEPT1 id).
      destruct (classic (ss id)).
      { exploit DROP; et. i; clarify. }
      exploit KEPT1; et. i; clarify. congruence.
    }
    exploit DEFKEEP0; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    { inv SIMSK. exploit KEPT1; eauto. i.
      unfold internals in *. des_ifs.
    }
    i; des. clarify.

  - inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; et. i; des. clarify. }
    eapply DISJ; et.
    erewrite <- SYMBKEEP; et.

  - (* SIMDEFINV *)

    assert(exists gd_big, <<DEFBIG: Genv.find_def skenv_link_tgt blk_tgt = Some gd_big>>
                                    /\ <<LO: linkorder def_tgt gd_big>>).
    {
      inv LETGT.
      destruct (Genv.invert_symbol skenv_link_tgt blk_tgt) eqn:T.
      - exploit DEFKEPT; eauto. i; des. ss. esplits; et.
      - exploit DEFORPHAN; eauto. i; des. clarify.
    }
    des.
    exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto.

    inv WFSMALLTGT. exploit DEFSYMB; eauto. intro SYMBSMALLTGT; des. rename SYMB into SYMBSMALLTGT.
    exploit SPLITHINT1; eauto. i; des.
    Fail clears blk_src.
    assert(blk_src = blk_src0).
    { symmetry. eapply SPLITHINT3; et. }
    clarify.

    inv LESRC.
    inv WFSRC. exploit DEFSYMB; eauto. i; des.
    assert(id = id0). { eapply Genv.genv_vars_inj. apply SYMBSMALLTGT. eauto. } clarify.
    assert(DSRC: defs sk_src id0).
    { apply NNPP. ii. erewrite SYMBDROP in *; eauto. ss. }
    exploit SYMBKEEP; eauto. i; des. rewrite BLKSRC in *. symmetry in H.
    assert(DTGT: defs sk_tgt id0).
    { apply NNPP. ii. inv LETGT. erewrite SYMBDROP0 in *; eauto. ss. }
    assert(ITGT: internals sk_tgt id0).
    {
      dup DTGT. unfold defs in DTGT. des_sumbool. apply prog_defmap_spec in DTGT. des.

      inv INCLTGT. exploit DEFS; et. i; des.
      assert(blk = blk_tgt).
      { inv LETGT. exploit SYMBKEEP0; et. i; des. congruence. }
      clarify.

      inv LETGT.
      exploit DEFKEPT0; et.
      { apply Genv.find_invert_symbol; eauto. }
      i; des.
      ss.
    }
    assert(ISRC: internals sk_src id0).
    {
      inv SIMSK.
      unfold internals in *. des_ifs_safe.
      exploit SPLITHINT; et. i; des. clear_tac.
      hexploit (KEPT id0); et. intro T. rewrite Heq in *.
      des_ifs. 
    }
    exploit DEFKEEP; et.
    { apply Genv.find_invert_symbol; eauto. }
    i; des. rewrite DEFSMALL.
    {
      inv LETGT.
      exploit DEFKEPT0; eauto.
      { eapply Genv.find_invert_symbol; eauto. rewrite <- SYMBKEEP0; et. }
      i; des.
      clarify.
      inv SIMSK.
      specialize (KEPT id0).
      destruct (classic (ss id0)).
      { exploit DROP; et. i; clarify. }
      exploit KEPT; et. i; clarify. congruence.
    }

  - (* PUBS *)
    exploit PUBKEPT; eauto.
    { eapply INCLSRC; et. }
    inv LE. eauto.
  - inv SIMSK. ss.
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto; ii; ss.
  - inv SIMFPTR; ss.
    des_ifs_safe; ss. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEF; eauto. i; des.
    inv SIM.
    rewrite DEFTGT.
    esplits; eauto.
    des_ifs.
  - inv SIMFPTR; ss; cycle 1.
    des_ifs_safe. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEFINV; eauto. i; des. clarify. psimpl. clarify.
    rewrite DEFSRC.
    esplits; eauto.
    des_ifs.
Qed.
Next Obligation.
  inv SIMSKENV.
  unfold System.skenv in *.
  esplits; eauto.
  econs; ii; ss; eauto; try rewrite Genv_map_defs_symb in *; apply_all_once Genv_map_defs_def; eauto.
  - des. exploit SIMDEF; eauto. i; des. clarify.
    esplits; eauto.
    eapply Genv_map_defs_def_inv in DEFTGT. rewrite DEFTGT. ss.
  - des. exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto.
    eapply Genv_map_defs_def_inv in DEFSRC. rewrite DEFSRC. ss.
  - eapply PUBKEPT; eauto.
Qed.
Next Obligation.
  destruct sm0, args_src, args_tgt; ss. inv MWF; ss. inv ARGS; ss. clarify.
  inv SIMSKENV; ss.
  exploit external_call_mem_inject_gen; eauto.
  { instantiate (1:= skenv_sys_tgt).
    rr. esplits; ii; ss.
    - unfold Genv.public_symbol.
      rewrite <- PUB.
      destruct (Genv.find_symbol skenv_sys_tgt id) eqn:T.
      + exploit SIMSYMB3; et. i; des. rewrite BLKSRC. ss.
      + des_ifs. des_sumbool. ii.
        exploit PUBKEPT; et.
        apply NNPP. ii.
        exploit SIMSYMB2; et. i; des. clarify.
    - exploit SIMSYMB1; eauto. i; des. esplits; et.
    - exploit SIMSYMB2; eauto.
      { ii. eapply PUBKEPT; eauto. unfold Genv.public_symbol in H. des_ifs. des_sumbool. ss. }
      i; des.
      esplits; eauto.
    - unfold Genv.block_is_volatile, Genv.find_var_info.
      destruct (Genv.find_def skenv_sys_src b1) eqn:T0.
      { exploit SIMDEF; try eassumption.
        i; des.
        des_ifs.
      }
      destruct (Genv.find_def skenv_sys_tgt b2) eqn:T1.
      { exploit SIMDEFINV; try eassumption.
        i; des.
        des_ifs.
      }
      ss.
  }
  i; des.




  (* TODO: almost exactly copied from SimMemInj. we may remove duplicate code some way *)
  do 2 eexists.
  dsplits; eauto.
  - instantiate (1:= Retv.mk _ _); ss. eauto.
  - instantiate (1:= mk _ _ _ _ _ _ _). econs; ss; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply inject_separated_frozen; eauto.
    + ii. eapply external_call_max_perm; eauto.
    + ii. eapply external_call_max_perm; eauto.
  - apply inject_separated_frozen in H5.
    econs; ss.
    + eapply after_private_src; ss; eauto.
    + eapply after_private_tgt; ss; eauto.
    + inv H2. xomega.
    + inv H3. xomega.
Qed.

End MEMINJ.

