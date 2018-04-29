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

Inductive closed (u: unit) (sk_src sk_tgt: Sk.t): Prop :=
| closed_intro
    (SIM: match_program (fun _ => sim_fun) eq sk_src sk_tgt)
.

Global Program Instance SimSymbId: SimSymb.class := {
  t := unit;
  coverage := bot2;
  kept := bot2;
  closed := closed;
  sim_skenv (_: unit) := sim_skenv;
}
.
Next Obligation.
  esplits; eauto. ss.
Qed.
Next Obligation.
  econs; ss; eauto.
  ii; ss.
  inv CLOSED.
  unfold match_program in *.
  generalize (Genv.globalenvs_match SIM); intro SIMGE.
  inv SIMGE.
  admit "this should hold.".
Qed.
Next Obligation.
  exists tt.
  split.
  - ss.
  - econs; eauto. inv CLOSED0. inv CLOSED1.
  admit "This should hold".
  Print TransfLink.
  (* exploit link_match_program; eauto. *)
Qed.
(* Next Obligation. *)
(*   inv CLOSED. clear_tac. *)
(*   assert(SIMID: forall id, (prog_defmap sk_src) ! id = (prog_defmap sk_tgt) ! id). *)
(*   { i. eapply NOCOVER; eauto. } clear NOCOVER. *)
(*   u. ss. *)
(*   econs; eauto. *)
(*   - admit "this should hold, if not, 1) add uniqueness condition on good_prog to make it hold. *)
(* 2) Replace Genv.globalenv with my_globalenv, which makes it unique". *)
(*   - intro id. *)
(*     specialize (SIMID id). *)
(*     generalize Genv.find_def_symbol. intro LEMMA. *)
(*     destruct ((prog_defmap sk_src) ! id) eqn:T. *)
(*     + eapply LEMMA in T. symmetry in SIMID. eapply LEMMA in SIMID. des. *)
(*       rewrite T. rewrite SIMID. ss. *)
(*     + *)
(*     admit "this should hold, if not, add uniqueness condition on good_prog to make it hold.". *)
(*     ss. *)
(* Qed. *)
Next Obligation.
  inv CLOSED.
  unfold match_program in *.
  generalize (Genv.globalenvs_match SIM); intro SIMGE.
  inv SIMGE.
  econs; eauto.
Qed.
Next Obligation.
  inv LESRC.
  inv LETGT.
  inv SIMSKENV.
  econs; eauto.
  - eq_closure_tac.
  - intro id.
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

