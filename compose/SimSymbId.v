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
Require Import SimMemId.


Set Implicit Arguments.


(* Copied from Separation.v *)
Inductive globalenv_preserved {F V: Type} (ge: Genv.t F V) (j: meminj) (bound: block) : Prop :=
  | globalenv_preserved_intro
      (DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound)
.
(* This definition relies on meminj. *)

Print Genv.match_genvs. (* Genv.genv_symb is very annoying *)

(* Notation " 'all1' p" := (forall x0, p x0) (at level 50, no associativity). *)
(* Notation "p =1= q" := (fun x0 => eq (p x0) (q x0)) (at level 50, no associativity). *)

Inductive sim_skenv (skenv0 skenv1: SkEnv.t): Prop :=
| sim_skenv_intro
    (NEXT: skenv0.(Genv.genv_next) = skenv1.(Genv.genv_next))
    (SYMB: all1 (skenv0.(Genv.find_symbol) =1= skenv1.(Genv.find_symbol))) (* <--- gives bad name when "intros": x0 *)
    (* (SYMB: forall id, skenv0.(Genv.find_symbol) id = skenv1.(Genv.find_symbol) id) *)
    (DEFS: True) (* TODO: There are almost no info except unit. Also, flesh will overwrite these info. *)
.

Inductive sim_sk (u: unit) (sk_src sk_tgt: Sk.t): Prop :=
| closed_intro
    (SIM: match_program (fun _ => sim_fun) eq sk_src sk_tgt)
.

Global Program Instance SimSymbId (smclass: SimMem.class): SimSymb.class smclass := {
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
    + admit "easy; Genv.init_mem_genv_next".
    + i. admit "this should hold... Genv.find_symbol_match".
  - admit "add init in SimMem.".
  - admit "add init in SimMem.".
Unshelve.
  admit "add init in SimMem".
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
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
  - ii.
    assert(fptr_src = fptr_tgt).
    { admit "add to SimMem.init's spec". }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    admit "add to sim_skenv".
  - ii.
    assert(fptr_src = fptr_tgt).
    { admit "add to SimMem.init's spec". }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    admit "add to sim_skenv".
Qed.
