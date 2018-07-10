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
Require Import MapsC.


Require Import SimDef SimSymb.
Require Import SimMem.
Require Import SimMemId SimMemInj.


Set Implicit Arguments.


Inductive sim_skenv (skenv0 skenv1: SkEnv.t): Prop :=
| sim_skenv_intro
    (NEXT: skenv0.(Genv.genv_next) = skenv1.(Genv.genv_next))
    (SYMB: all1 (skenv0.(Genv.find_symbol) =1= skenv1.(Genv.find_symbol)))
    (DEFS: all1 (skenv0.(Genv.find_def) =1= skenv1.(Genv.find_def)))
    (PUBS: skenv0.(Genv.genv_public) = skenv1.(Genv.genv_public))
.

Goal sim_skenv = Genv.match_genvs eq.
Proof.
  apply Axioms.functional_extensionality; i.
  apply Axioms.functional_extensionality; i.
  apply AxiomsC.prop_ext.
  split; i; inv H; econs; eauto.
  - ii. unfold Genv.find_def in *. erewrite DEFS.
    destruct ((Genv.genv_defs x0) ! b) eqn:T; econs; eauto.
  - unfold Genv.find_def in *. i. specialize (mge_defs x1). inv mge_defs; ss.
  - admit "".
Qed.

Inductive sim_sk (u: unit) (sk_src sk_tgt: Sk.t): Prop :=
| closed_intro
    (SIM: match_program (fun _ => sim_fun) eq sk_src sk_tgt)
.

Global Program Instance SimSymbIdId: SimSymb.class SimMemId := {
  t := unit;
  le := top4;
  sim_sk := sim_sk;
  sim_skenv (_: SimMem.t) (_: unit) := sim_skenv;
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
  - econs; eauto.
    + erewrite ! Genv.init_mem_genv_next; eauto.
    + i. symmetry. apply (Genv.find_symbol_match SIM).
    + ii. hexploit (Genv.find_def_match_2 SIM x0); eauto. intro REL.
      inv REL; ss. inv H2; ss.
      * admit "remove sig then this will hold // or just now this will hold if we don't drop sig on opt".
      * inv H3; ss.
    + inv SIM; des; ss. rewrite ! Genv.globalenv_public. ss.
  - instantiate (1:= SimMemId.mk _ _). ss.
  - ss.
  - ss.
Unshelve.
Qed.
Next Obligation.
  inv LESRC.
  inv LETGT.
  inv SIMSKENV.
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
  - eq_closure_tac. ss. (* TODO: debug this *)
    rewrite PUBLIC. rewrite PUBS. rewrite PUBLIC0. ss.
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
  - ii. ss.
    assert(fptr_src = fptr_tgt).
    { ss. }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    erewrite <- DEFS; eauto. des_ifs. esplits; eauto.
    admit "just use eq".
  - ii.
    assert(fptr_src = fptr_tgt).
    { ss. }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    erewrite DEFS; eauto. des_ifs. esplits; eauto.
    admit "just use eq".
Qed.





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

Global Program Instance SimSymbIdInj: SimSymb.class SimMemInj := {
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
  - instantiate (1:= SimMemInj.mk (Mem.flat_inj m_src.(Mem.nextblock))
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

