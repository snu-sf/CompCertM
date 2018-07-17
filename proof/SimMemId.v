Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Asmregs.
Require Import Integers.

Require Import IntegersC LinkingC.
Require Import SimDef SimSymb Skeleton Mod ModSem.
Require Import SimMem.

Set Implicit Arguments.




Record t' := mk {
  src_mem: mem;
  tgt_mem: mem;
}.

Program Instance SimMemId : SimMem.class :=
{
  t := t';
  src := src_mem;
  tgt := tgt_mem;
  wf := fun (rel: t') => rel.(src_mem) = rel.(tgt_mem);
  le := fun (mrel0 mrel1: t') => True;
  lift := id;
  unlift := fun _ => id;
  sim_val := fun (_: t') => eq;
}.
Next Obligation.
  ss.
Qed.
(* Next Obligation. *)
(*   eexists (mkrelation _ _). *)
(*   esplits; ss; eauto. *)
(*   inv WF. ss. *)
(*   clear_tac. *)
(*   assert(NOCOVER0: forall id, <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>). *)
(*   { i. eapply NOCOVER. eauto. } *)
(*   clear NOCOVER. *)
(*   clear_tac. *)
(*   econs; eauto. *)
(*   - admit "This should hold; Maybe ""Genv.init_mem_match"" and ""Genv.init_mem_genv_next"" might help". *)
(*   - admit "This should hold;". *)
(* Qed. *)

















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
| sim_sk_intro
    (SIM: match_program (fun _ => sim_fun) eq sk_src sk_tgt)
.

Global Program Instance SimSymbId: SimSymb.class SimMemId := {
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
  - instantiate (1:= mk _ _). ss.
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

