Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import SimSymb.
Require Import Integers.
Require Import ASTC.
Require Import Maps.

Set Implicit Arguments.



Module Mod.
  (* TRANSLATION UNIT *)

  (* I intentionally left "datatype" in to_skel and to_moduleenv. *)
  (* 1) defining translation becomes more lightweight. *)
  (* Consider RTL -> RTL. to_skel/to_moduleenv remains the same *)
  (* 2) This definition will give an error when datatype is changed. *)
  Record t: Type := mk {
    datatype: Type;
    (* skel: Skel.t; *)
    get_sk: datatype -> Sk.t;
    get_modsem: SkEnv.t -> datatype -> ModSem.t;
    data: datatype;
  }
  .

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) skenv md.(data).

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.


