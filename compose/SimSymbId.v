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

Inductive sim_skenv (skenv0 skenv1: SkEnv.t): Prop :=
| sim_skenv_intro
    (NEXT: skenv0.(Genv.genv_next) = skenv1.(Genv.genv_next))
    (* (SYMB: skenv0.(Genv.find_symbol) =1= skenv1.(Genv.find_symbol)) <--- gives bad name when "intros": x0 *)
    (SYMB: forall id, skenv0.(Genv.find_symbol) id = skenv1.(Genv.find_symbol) id)
    (DEFS: True) (* TODO: There are almost no info except unit. Also, flesh will overwrite these info. *)
.

Global Program Instance SymbInjId: SimSymb.class := {
  t := unit;
  src_ids := fun _ _ => False;
  tgt_ids := fun _ _ => False;
  sim_symb := fun _ _ _ => True;
  sim_skenv (_: unit) := sim_skenv;
}
.
Next Obligation.
  inv LESRC.
  inv LETGT.
  inv SIMSKENV.
  econs; eauto.
  - eq_closure_tac.
  - i.
    destruct (Classical_Prop.classic (pubs id)); cycle 1.
    + exploit NPROJ; eauto. { ii; des; eauto. } i; des.
      exploit NPROJ0; eauto. { ii; des; eauto. } i; des.
      eq_closure_tac. (* TODO: debug this *)
      rewrite H0. rewrite H1. ss.
    + exploit PROJ; eauto. i; des.
      exploit PROJ0; eauto. i; des.
      eq_closure_tac. (* TODO: debug this *)
      rewrite <- H0. rewrite <- H1.
      ss.
Qed.

