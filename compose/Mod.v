Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import Maps.

Require Import ModSem.

Set Implicit Arguments.



Module Mod.
  (* TRANSLATION UNIT *)

  (* I intentionally left "datatype" in to_skel and to_moduleenv. *)
  (* 1) defining translation becomes more lightweight. *)
  (* Consider RTL -> RTL. to_skel/to_moduleenv remains the same *)
  (* 2) This definition will give an error when datatype is changed. *)
  Record t: Type := mk {
    datatype: Type;
    get_sk: datatype -> Sk.t;
    get_modsem: SkEnv.t -> datatype -> ModSem.t;
    data: datatype;
    midx: Midx.t;
    get_modsem_codeseg_spec: forall skenv,
        <<PROJECTED: ((SkEnv.project skenv data.(get_sk)): CodeSeg.t) = data.(get_modsem skenv).(ModSem.codeseg)>>;
    get_modsem_skenv_link_spec: forall skenv_link,
        <<EQ: data.(get_modsem skenv_link).(ModSem.skenv_link) = skenv_link>>;
    get_modsem_midx_spec: forall skenv,
        <<EQ: data.(get_modsem skenv).(ModSem.midx) = midx>>;
  }.

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) skenv md.(data).

  Module Atomic.
  Section Atomic.

    Variable m: t.

    Program Definition trans: t :=
      mk m.(get_sk) (fun ske dat => ModSem.Atomic.trans (m.(get_modsem) ske dat)) m.(data) _ _ _ (midx := m.(midx)).
    Next Obligation. exploit get_modsem_codeseg_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_skenv_link_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_midx_spec; eauto. Qed.

  End Atomic.
  End Atomic.

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.
Coercion Mod.modsem: Mod.t >-> Funclass.

Hint Unfold Mod.sk Mod.modsem.

