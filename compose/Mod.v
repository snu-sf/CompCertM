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
    get_modsem_skenv_spec: forall skenv,
        <<PROJECTED: SkEnv.project skenv data.(get_sk) = data.(get_modsem skenv).(ModSem.skenv)>>;
    get_modsem_skenv_link_spec: forall skenv_link,
        <<EQ: data.(get_modsem skenv_link).(ModSem.skenv_link) = skenv_link>>;
    get_modsem_midx_spec: forall skenv d,
        <<EQ: d.(get_modsem skenv).(ModSem.midx) = midx>>;
  }.

  Lemma get_modsem_projected_sk
        (md: t) skenv
        (INCL: SkEnv.includes skenv (get_sk md (data md))):
      <<PROJECTED: SkEnv.project_spec skenv ((md.(get_sk) md.(data)))
                                      ((md.(get_modsem) skenv) md.(data)).(ModSem.skenv)>>.
  Proof.
    erewrite <- get_modsem_skenv_spec. eapply SkEnv.project_impl_spec; et.
  Qed.

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) skenv md.(data).

  Lemma modsem_skenv_spec
        (md: Mod.t) skenv
    :
      <<EQ: ModSem.skenv (Mod.modsem md skenv) = SkEnv.project skenv (Mod.sk md)>>
  .
  Proof.
    unfold modsem, sk. rewrite Mod.get_modsem_skenv_spec. ss.
  Qed.

  Lemma modsem_skenv_link_spec
        (md: Mod.t) skenv_link
    :
      <<EQ: ModSem.skenv_link (Mod.modsem md skenv_link) = skenv_link>>
  .
  Proof.
    unfold modsem. rewrite Mod.get_modsem_skenv_link_spec. ss.
  Qed.

  Lemma modsem_midx_spec
        (md: Mod.t) skenv_link
    :
      <<EQ: ModSem.midx (Mod.modsem md skenv_link) = md.(Mod.midx)>>
  .
  Proof.
    unfold modsem. rewrite Mod.get_modsem_midx_spec. ss.
  Qed.

  (* modsem -> mod *)
  Ltac simpl := try rewrite ! Mod.modsem_skenv_spec in *;
                try rewrite ! Mod.modsem_skenv_link_spec in *;
                try rewrite ! Mod.modsem_midx_spec in *;
                try rewrite <- ! Mod.get_modsem_skenv_spec in *;
                try rewrite ! Mod.get_modsem_skenv_link_spec in *;
                try rewrite ! Mod.get_modsem_midx_spec in *
  .



  Module Atomic.
  Section Atomic.

    Variable m: t.

    Program Definition trans: t :=
      mk m.(get_sk) (fun ske dat => ModSem.Atomic.trans (m.(get_modsem) ske dat)) m.(data) _ _ _ (midx := m.(midx)).
    Next Obligation. exploit get_modsem_skenv_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_skenv_link_spec; eauto. Qed.
    Next Obligation. exploit get_modsem_midx_spec; eauto. Qed.

  End Atomic.
  End Atomic.

  Section DUMMY.
    Variable md: Mod.t.
    Local Obligation Tactic := ii; des; ss; Mod.simpl; ss.
    Program Definition dummy: Mod.t :=
      {|
        Mod.datatype := unit;
        Mod.get_sk := fun _ => Sk.empty;
        Mod.get_modsem := fun skenv_link _ => ModSem.dummy skenv_link md.(Mod.midx);
        Mod.data := tt;
        Mod.midx := md.(Mod.midx);
      |}
    .
    Next Obligation.
    Qed.
  End DUMMY.

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.
Coercion Mod.modsem: Mod.t >-> Funclass.

Hint Unfold Mod.sk Mod.modsem.

