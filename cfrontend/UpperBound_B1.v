Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.

Set Implicit Arguments.

Local Opaque Z.mul.

Section PRESERVATION.

  Existing Instance Val.mi_final.

(** PLAN B-0*)

(*
B-0
* : Physical
+ : Logical 
c0 * empty
>=
c0 + empty
*)
  
(*
B-1
* : Physical
+ : Logical 
(c0 * c1) * ctx
>=
(c0 + c1) * ctx
*)

  Section PLANB1.

(** ********************* linking *********************************)    
  Variable prog1 : Csyntax.program.
  Variable prog2 : Csyntax.program.
  Variable prog' : Csyntax.program.
  Hypothesis LINK : link prog1 prog2 = Some prog'.
  Let tprog' : Syntax.program := List.map CsemC.module [prog2; prog1].
  Variable ctx : Syntax.program.

  Let prog : Syntax.program := CsemC.module prog' :: ctx.
  Let tprog : Syntax.program := tprog' ++ ctx.

(** ********************* linking *********************************)

  Variable sk_src: Sk.t.
  Hypothesis LINK_SK_SRC: link_sk prog = Some sk_src.
  (* TODO: consider linking fail case *)
  Let skenv_link_src := Sk.load_skenv sk_src.

  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link_tgt := Sk.load_skenv sk_tgt.
  
  Let ge := load_genv prog skenv_link_src.
  (* Let ge_ce : composite_env := prog_comp_env prog. *)
  (* Let tge_ce : composite_env := prog_comp_env prog. *)
  Let tge := load_genv tprog skenv_link_tgt.

  Inductive match_states_aux : Csem.State -> Sem.state -> nat -> Prop :=
  
  Inductive match_states : Sem.state -> Sem.state -> nat -> Prop :=
  | match_states_intro
      