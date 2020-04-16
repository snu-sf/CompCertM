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
    get_modsem: option Midx.t -> SkEnv.t -> datatype -> ModSem.t;
    data: datatype;
    midx: option Midx.t;
    get_modsem_skenv_spec: forall skenv midx,
        <<PROJECTED: SkEnv.project skenv data.(get_sk) = data.(get_modsem midx skenv).(ModSem.skenv)>>;
    get_modsem_skenv_link_spec: forall skenv_link midx,
        <<EQ: data.(get_modsem midx skenv_link).(ModSem.skenv_link) = skenv_link>>;
    get_modsem_midx_spec: forall skenv midx,
        <<EQ: data.(get_modsem midx skenv).(ModSem.midx) = midx>>;
  }.

  Lemma get_modsem_projected_sk
        (md: t) midx skenv
        (INCL: SkEnv.includes skenv (get_sk md (data md))):
      <<PROJECTED: SkEnv.project_spec skenv ((md.(get_sk) md.(data)))
                                      ((md.(get_modsem) midx skenv) md.(data)).(ModSem.skenv)>>.
  Proof.
    erewrite <- get_modsem_skenv_spec. eapply SkEnv.project_impl_spec; et.
  Qed.

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) md.(midx) skenv md.(data).

  Module Atomic.
  Section Atomic.

    Variable m: t.

    Program Definition trans: t :=
      mk m.(get_sk) (fun midx ske dat => ModSem.Atomic.trans (m.(get_modsem) midx ske dat)) m.(data) m.(midx) _ _ _.
    Next Obligation. exploit get_modsem_skenv_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_skenv_link_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_midx_spec; eauto. Qed.

  End Atomic.
  End Atomic.

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.
Coercion Mod.modsem: Mod.t >-> Funclass.

Hint Unfold Mod.sk Mod.modsem.

