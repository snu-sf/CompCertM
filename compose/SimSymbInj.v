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


Inductive sim_skenv (skenv0 skenv1: SkEnv.t): Prop :=
| sim_skenv_intro
    (NEXT: skenv0.(Genv.genv_next) = skenv1.(Genv.genv_next))
    (* (SYMB: skenv0.(Genv.find_symbol) =1= skenv1.(Genv.find_symbol)) <--- gives bad name when "intros": x0 *)
    (SYMB: forall id, skenv0.(Genv.find_symbol) id = skenv1.(Genv.find_symbol) id)
    (DEFS: True) (* TODO: There are almost no info except unit. Also, flesh will overwrite these info. *)
.

Global Program Instance SimSymbId: SimSymb.class := {
  t := unit;
  privs := bot2;
  sim_symb := bot3;
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

