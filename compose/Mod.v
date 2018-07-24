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
Require Import Maps.

Require Import ModSem.

Set Implicit Arguments.



Module Mod.
  (* TRANSLATION UNIT *)

  Inductive get_internals (sk: Sk.t) (skenv: SkEnv.t) (internals: block -> Prop): Prop :=
  | get_internals_intro
      (INTERNALS: forall
          id
        ,
          <<FIND: exists if_sig, sk.(prog_defmap) ! id = Some (Gfun (Internal if_sig))>> <->
          <<INTERNAL: internals id>>)
  .

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
    get_modsem_skenv: forall
      skenv_link
      ,
        (* SkEnv.project skenv data.(get_sk).(defs) = data.(get_modsem skenv).(ModSem.skenv) *)
        <<PROJECTED: SkEnv.project_spec skenv_link
                                        data.(get_sk).(defs)
                                        data.(get_modsem skenv_link).(ModSem.skenv)>>
    ;
    get_modsem_skenv_link: forall
      skenv_link
      ,
        data.(get_modsem skenv_link).(ModSem.skenv_link) = skenv_link
    ;

    (* TODO: What is the exact spec we need here? *)
    (* get_modsem_sk_skenv_iso: forall *)
    (*     skenv *)
    (*   , *)
    (*     <<ISO: sk_skenv_iso data.(get_sk) data.(get_modsem skenv).(ModSem.skenv)>> *)
    (* ; *)
  }
  .

  Definition sk (md: t): Sk.t := md.(get_sk) md.(data).

  Definition modsem (md: t) (skenv: SkEnv.t): ModSem.t := md.(get_modsem) skenv md.(data).

End Mod.

Coercion Mod.sk: Mod.t >-> Sk.t.

Hint Unfold Mod.sk Mod.modsem.

