(** copied && added "C" **)
Require Import String.
Require Import CoqlibC.
From compcertr Require Import
     Maps
     Errors
     Integers
     Floats.
From compcertr Require Archi.

(** newly added **)
From compcertr Require Export AST.
From compcertr Require Import Errors.
From compcertr Require Import sflib.

Set Implicit Arguments.

Generalizable Variables F.

Lemma prog_defmap_spec
      F V (p: program F V) id:
    In id (prog_defs_names p) <-> exists g, (prog_defmap p) ! id = Some g.
Proof.
  split; ii.
  - exploit prog_defmap_dom; eauto.
  - des. exploit in_prog_defmap; eauto. i.
    clear - H0. destruct p; ss. u. apply in_map_iff. esplits; eauto. ss.
Qed.

Lemma prog_defmap_image
      F V (p : AST.program F V) id g
      (GET: (prog_defmap p) ! id = Some g):
    <<IN: In id (prog_defs_names p)>>.
Proof. eapply prog_defmap_spec; et. Qed.


Lemma prog_defmap_update_snd
      X Y (f: X -> Y) (defs: list (positive * X)) id:
    (PTree_Properties.of_list (map (update_snd f) defs)) ! id =
    option_map f ((PTree_Properties.of_list defs) ! id).
Proof.
  unfold PTree_Properties.of_list.
  rewrite <- ! fold_left_rev_right in *. rewrite <- map_rev.  unfold PTree.elt.
  abstr (rev defs) xs. clear_tac.  generalize id.
  induction xs; ii; try rewrite PTree.gempty in *; ss.
  destruct a; ss.
  rewrite PTree.gsspec. des_ifs.
  { unfold option_map. rewrite PTree.gsspec. des_ifs. }
  rewrite IHxs. rewrite PTree.gsspec. des_ifs.
Qed.

Class HasExternal (X: Type): Type := {
  is_external: X -> bool;
}.




Section FUNCTIONS.

  Definition is_external_fd F (f: fundef F): bool :=
    match f with
    | External ef => is_external_ef ef
    | _ => false
    end.

  Lemma transf_fundef_is_external
        A B (transf: A -> B) f
        (ISEXT: is_external_fd (transf_fundef transf f)):
      <<ISEXT: is_external_fd f>>.
  Proof. compute in ISEXT. des_ifs. Qed.

  Lemma transf_fundef_external
        A B (transf: A -> B) f ef
        (EXT: (transf_fundef transf f) = External ef):
      f = External ef.
  Proof. compute in EXT. des_ifs. Qed.

  Lemma transf_partial_fundef_is_external_fd
        A B (transf_partial: A -> res B) f tf
        (TRANSF: (transf_partial_fundef transf_partial f) = OK tf)
        (ISEXT: is_external_fd tf):
      <<ISEXT: is_external_fd f>>.
  Proof. compute in ISEXT. des_ifs. compute in TRANSF. des_ifs. Qed.

  Lemma transf_partial_fundef_external
        A B (transf_partial: A -> res B) f ef
        (TRANSF: (transf_partial_fundef transf_partial f) = OK (External ef)):
      <<ISEXT: f = External ef>>.
  Proof. compute in TRANSF. des_ifs. Qed.

  Definition is_dtm_ef (ef: external_function): bool :=
    match ef with
    | EF_external _ _
    | EF_builtin _ _
    | EF_runtime _ _
    | EF_inline_asm _ _ _ => false
    | _ => true
    end.

  Definition is_dtm_fd F (fd: AST.fundef F): bool :=
    match fd with
    | External ef => is_dtm_ef ef
    | _ => true
    end.

End FUNCTIONS.

Definition is_external_gd `{HasExternal F} V (gd: globdef F V): bool :=
  match gd with
  | Gfun fd => is_external fd
  | Gvar _ => false
  end.

Arguments is_external_fd {F}.
Arguments is_external_gd {_} {_} {V}.
Hint Unfold is_external_gd is_external_fd.

Global Instance external_function_HasExternal: HasExternal external_function :=
  Build_HasExternal is_external_ef.
Global Instance fundef_HasExternal {F}: HasExternal (AST.fundef F) :=
  Build_HasExternal is_external_fd.
Global Instance globdef_HasExternal `{HasExternal F} {V}: HasExternal (globdef F V) :=
  Build_HasExternal is_external_gd.









Section PROGRAMS.

  Variable F V: Type.
  Variable p: program F V.

  Definition good_prog (p: program F V): Prop :=
    incl p.(prog_public) (prog_defs_names p).
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

  Definition defs: ident -> bool := fun id => In_dec ident_eq id (prog_defs_names p).
  Check (defs: ident -> Prop).
  Definition defs_old: ident -> Prop := fun id => exists gd, (prog_defmap p)!id = Some gd.
  Goal defs <1= defs_old.
  Proof.
    ii. exploit prog_defmap_dom; eauto. inv PR.
    unfold defs in *. des_sumbool; ss.
  Qed.

  Definition privs: ident -> bool :=
    fun id => andb (<<DEFS: defs id>>) (<<PRIVS: negb (In_dec ident_eq id p.(prog_public))>>).
  Definition privs_old: ident -> Prop :=
    <<DEFS: defs_old>> /1\ <<PRIVS: (fun id => ~ In id p.(prog_public))>>.

  Lemma privs_defs_old: <<LE: (privs_old <1= defs_old)>>.
  Proof. ii. inv PR. eauto. Qed.

End PROGRAMS.

Lemma defs_prog_defmap
      F V (prog: AST.program F V):
    forall id, (exists gd, (prog_defmap prog) ! id = Some gd) <-> defs prog id.
Proof.
  ii. etrans.
  { symmetry. eapply prog_defmap_spec. }
  unfold defs, prog_defs_names. split; i; des; des_sumbool; ss.
Qed.




Section PROGRAMS2.

  Context `{HasExternal F} {V: Type}.
  Variable p: program F V.

  Definition internals: ident -> bool :=
    fun id => match (prog_defmap p)!id with
              | Some gd => negb (is_external gd)
              | None => false
              end.

  Definition internals': ident -> bool :=
    fun id => is_some
                (List.find (fun idg => andb (ident_eq id (fst idg)) (is_external (snd idg))) p.(prog_defs)).

End PROGRAMS2.

Hint Unfold defs privs internals.
Hint Unfold defs_old privs_old internals'.

Lemma internals_defs
      `{HasExternal F} V
      (p: AST.program F V):
    (internals p) <1= (defs p).
Proof.
  u. ii. des_sumbool. eapply prog_defmap_spec. des_ifs; et.
Qed.

(* Only "is_internal" defs will remain in ModSem-SkEnv/Genv. *)
(* Note: Other module's gvar will flow in. Is it OK? *)
(* Proof: More def: less UB. C physical -> C logical: OK. // Asm logical -> Asm physical: OK. *)
(* Conceptually: OK. block should be passed through modules freely, just like passing fptr. *)
(* Definition is_internal (skd: globdef (AST.fundef (option signature)) unit): bool := *)
(*   match skd with *)
(*   | Gfun (Internal _) => true *)
(*   | Gfun (External _) => false *)
(*   | Gvar _ => true *)
(*   end *)
(* . *)

Lemma chunk_type_chunk: forall ty,
    (type_of_chunk (chunk_of_type ty)) = ty.
Proof. destruct ty; ss. Qed.
