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
    (* skel: Skel.t; *)
    get_sk: datatype -> Sk.t;
    get_modsem: SkEnv.t -> datatype -> ModSem.t;
    data: datatype;
    get_modsem_skenv_spec: forall
      skenv
      ,
        <<PROJECTED: SkEnv.project skenv data.(get_sk) = data.(get_modsem skenv).(ModSem.skenv)>>
    ;
    get_modsem_skenv_link_spec: forall
        skenv_link
      ,
        <<EQ: data.(get_modsem skenv_link).(ModSem.skenv_link) = skenv_link>>
    (* TODO: What is the exact spec we need here? *)
    (* get_modsem_sk_skenv_iso: forall *)
    (*     skenv *)
    (*   , *)
    (*     <<ISO: sk_skenv_iso data.(get_sk) data.(get_modsem skenv).(ModSem.skenv)>> *)
    (* ; *)
  }
  .

  Lemma get_modsem_projected_sk
        (md: t)
        skenv
        (INCL: SkEnv.includes skenv (get_sk md (data md)))
    :
      <<PROJECTED: SkEnv.project_spec skenv ((md.(get_sk) md.(data)))
                                      ((md.(get_modsem) skenv) md.(data)).(ModSem.skenv)>>
  .
  Proof.
    erewrite <- get_modsem_skenv_spec.
    eapply SkEnv.project_impl_spec; et.
  Qed.

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) skenv md.(data).

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.
Coercion Mod.modsem: Mod.t >-> Funclass.

Hint Unfold Mod.sk Mod.modsem.

