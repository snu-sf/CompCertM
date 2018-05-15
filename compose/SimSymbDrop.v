Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimDef SimSymb.
Require Import SimMem.
Require Import SimMemInj.




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
.

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          /\ <<KEPT: ~ ss id>>
    )
    (SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\
           <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>)
    (SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>
           /\ <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>
             (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    )
    (SIMDEF: forall
        blk_src blk_tgt delta def_src isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, <<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: sim_def def_src def_tgt>>)
    (SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, <<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: sim_def def_src def_tgt>>)
.

Definition sim_skenv_splittable (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
    (<<SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          /\ <<KEPT: ~ ss id>>
    >>)
    /\
    (<<SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\
           <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>>>)
    /\
    (<<SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>
           /\ <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>
             (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    >>)
    /\
    (<<SIMDEF: forall
        blk_src blk_tgt delta def_src isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, <<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   (<<SIM: sim_def def_src def_tgt>>)>>)
    /\
    (<<SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, <<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: sim_def def_src def_tgt>>>>)
.

Theorem sim_skenv_splittable_spec
  :
    (sim_skenv_splittable <4= sim_skenv) /\ (sim_skenv <4= sim_skenv_splittable)
.
Proof.
  split; ii; inv PR; ss; des; econs; eauto.
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

Global Program Instance sim_def_PreOrder: RelationClasses.PreOrder sim_def.
Next Obligation.
  admit "easy".
Qed.
Next Obligation.
  admit "easy".
Qed.


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
  admit "See 'link_match_program' in Unusedglobproof.v.
Note that we have one more goal (exists ss) but it is OK, as the 'link_match_program' proof already proves it.".
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
  exploit SkEnv.project_spec_preserves_wf; try apply LESRC; eauto. intro WFSMALLSRC.
  exploit SkEnv.project_spec_preserves_wf; try apply LETGT; eauto. intro WFSMALLTGT.
(* THIS IS TOP *)
  inv SIMSKENV. ss.
  apply sim_skenv_splittable_spec.
  dsplits; eauto; ii; ss.
  -
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


  -
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

  -
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

  - 

    inv LESRC.
    inv WFSMALLSRC. exploit DEFSYMB; eauto. intro SYMBSMALL; des.
    destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des. rewrite SYMBSMALL in *. symmetry in SYMBBIG.
    inv WFSRC.
    exploit SYMBDEF0; eauto. i; des.
    exploit SIMDEF; eauto. i; des. clarify.

    exploit SPLITHINT; eauto. i; des.
    move DEFSRC at bottom. move H0 at bottom.
    assert(def_src = skd).
    { exploit DEFKEEP; eauto. eapply Genv.find_invert_symbol; eauto. i.
      rewrite DEFSRC in *. rewrite H0 in *. des. clarify. } clarify.
    esplits; eauto.

    inv LETGT.
    exploit SIMSYMB1; eauto. i; des.
    erewrite DEFKEEP0; eauto.
    { eapply Genv.find_invert_symbol; eauto.  }
    { apply NNPP. ii.
      exploit DEFDROP0; eauto.
      { eapply Genv.find_invert_symbol; eauto. }
      i; des. clarify.
      inv WFSMALLTGT.
      exploit SYMBDEF1; eauto. i; des. clarify.
    }

  -
    inv LETGT.

    assert(Genv.find_def skenv_link_tgt blk_tgt = Some def_tgt).
    {
      destruct (Genv.invert_symbol skenv_link_tgt blk_tgt) eqn:T.
      - erewrite <- DEFKEEP; eauto.
        apply Genv.invert_find_symbol in T.
        apply NNPP; ii. exploit SYMBDROP; eauto. i; des.
        exploit DEFDROP; eauto.
        { apply Genv.find_invert_symbol. eauto. } i; des. clarify.
      - exploit DEFORPHAN; eauto. i; des. clarify.
    }
    exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto.

    inv WFSMALLTGT. exploit DEFSYMB; eauto. intro SYMBSMALLTGT; des.
    exploit SPLITHINT1; eauto. i; des.
    Fail clears blk_src.
    assert(blk_src = blk_src0).
    (* { *)
    (*   assert(KEPT: ~ ss id). *)
    (*   { exploit SPLITHINT; eauto. i; des. ss. } *)
    (*   exploit SPLITHINT0; try apply BLKSRC; eauto. i; des. clarify. clear_tac. *)
    (*   exploit SPLITHINT0; eauto. i; des. clarify. clear_tac. *)
    (* } *)
    { assert(MEMWF: SimMem.wf sm).
      { admit "". }
      inv MEMWF. inv PUBLIC0.
      apply NNPP. ii.
      move SIMFPTR at bottom. move SIM0 at bottom.
      inv SIMFPTR. inv SIM0. rewrite Ptrofs.add_zero_l in *.
      About mi_no_overlap.
      assert(delta = 0).
      { admit "This is not true!".
        (* clear - H6. *)
        (* unfold Ptrofs.zero in *. *)
        (* hexploit (Ptrofs.intrange (Ptrofs.repr delta)); eauto. i. *)
        (* Local Transparent Ptrofs.repr. ss. Local Opaque Ptrofs.repr. *)
        (* Print Ptrofs.int. *)
        (* unfold Ptrofs.repr in *. ss. *)
        (* injection H6. ii. *)
        (* erewrite Ptrofs.Z_mod_modulus_eq in H0. *)
        (* rewrite Z.mod_small in *; ss. *)
        (* xomega. *)
        (* assert(Ptrofs.Z_mod_modulus_range' delta). *)
        (* dependent destruction H6. *)
        (* inv H6. clarify. *)
      }
      admit "Add disjointness in sim_skenv or relax meminj_no_overlap with Ptrofs.modulus or somehow...". }
    clarify.

    inv LESRC.
    inv WFSRC. exploit DEFSYMB; eauto. i; des.
    assert(id = id0). { eapply Genv.genv_vars_inj. apply SYMBSMALLTGT. eauto. } clarify.
    assert(defs sk_src id0).
    { apply NNPP. ii. erewrite SYMBDROP0 in *; eauto. ss. }
    exploit SYMBKEEP0; eauto. i; des. rewrite BLKSRC in *. symmetry in H2.
    erewrite DEFKEEP0; eauto.
    { apply Genv.find_invert_symbol; eauto. }
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
Qed.

