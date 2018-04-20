(** copied && added "C" **)
Require Import String.
Require Import CoqlibC Maps Errors Integers Floats.
Require Archi.

(** newly added **)
Require Export AST.
Require Import Errors.
Require Import sflib.

Set Implicit Arguments.




Section FUNCTIONS.
  
  Definition is_external_ef (ef: external_function): bool :=
    match ef with
    | EF_external _ _ => true
    | _ => false
    end.

  Definition is_external F (f: fundef F): bool :=
    match f with
    | External ef => is_external_ef ef
    | _ => false
    end.

  Lemma transf_fundef_is_external
        A B
        (transf: A -> B)
        f
        (ISEXT: is_external (transf_fundef transf f))
    :
      <<ISEXT: is_external f>>
  .
  Proof.
    compute in ISEXT. des_ifs.
  Qed.

  Lemma transf_fundef_external
        A B
        (transf: A -> B)
        f ef
        (EXT: (transf_fundef transf f) = External ef)
    :
      f = External ef
  .
  Proof.
    compute in EXT. des_ifs.
  Qed.

  Lemma transf_partial_fundef_is_external
        A B
        (transf_partial: A -> res B)
        f tf
        (TRANSF: (transf_partial_fundef transf_partial f) = OK tf)
        (ISEXT: is_external tf)
    :
      <<ISEXT: is_external f>>
  .
  Proof.
    compute in ISEXT. des_ifs.
    compute in TRANSF. des_ifs.
  Qed.

  Lemma transf_partial_fundef_external
        A B
        (transf_partial: A -> res B)
        f ef
        (TRANSF: (transf_partial_fundef transf_partial f) = OK (External ef))
    :
      <<ISEXT: f = External ef>>
  .
  Proof.
    compute in TRANSF.
    des_ifs.
  Qed.

  Definition is_dtm_ef (ef: external_function): bool :=
    match ef with
    | EF_external _ _
    | EF_builtin _ _
    | EF_runtime _ _
    | EF_inline_asm _ _ _ => false
    | _ => true
    end
  .

  Definition is_dtm_fd F (fd: AST.fundef F): bool :=
    match fd with
    | External ef => is_dtm_ef ef
    | _ => true
    end
  .

End FUNCTIONS.




Section PROGRAMS.

  Variable F V: Type.
  Variable p: program F V.

  (* Definition is_private (p: program F V) (id: ident): Prop := *)
  (*   (exists gd, <<FIND: p.(prog_defmap)!id = Some gd>>) /\ <<PRIV: ~In id p.(prog_public)>> *)
  (* . *)

  (* (* This one is without parameter *) *)
  (* Definition is_private_plain (id: ident) (ids: list ident) (pubs: list ident): Prop := *)
  (*   <<IN: In id ids>> /\ <<PRIV: ~In id pubs>> *)
  (* . *)

  Definition good_prog (p: program F V): Prop :=
    incl p.(prog_public) (* (List.map fst p.(prog_defmap).(PTree.elements)) *) p.(prog_defs_names)
  (* It also makes sense to add list_norept of prog_defs_names. "prog_defmap_norepet" *)
  (* Actually both are enforced in Unusedglob. *)
  (*** valid_used_set in Unusedglobproof.v
  used_public: forall id,
    In id p.(prog_public) -> IS.In id u;
  used_defined: forall id,
    IS.In id u -> In id (prog_defs_names p) \/ id = p.(prog_main)
   ***)
  (*** norept is also enforced in the first place.
https://sflab.slack.com/archives/G25737B47/p1517939898000786
I think the same is true for prog_public thing too.
   ***)
  .

  Definition defs: ident -> Prop := fun id => exists gd, p.(prog_defmap)!id = Some gd.

  Definition privs: ident -> Prop :=
    <<DEFS: defs>> /1\ <<PRIVS: (fun id => ~ In id p.(prog_public))>>
  .

  Lemma privs_defs
    :
      <<LE: privs <1= defs>>
  .
  Proof.
    ii. inv PR. eauto.
  Qed.

End PROGRAMS.

Hint Unfold defs privs.
