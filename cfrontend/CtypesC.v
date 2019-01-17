Require Import Axioms CoqlibC MapsC Errors.
Require Import AST Linking.
Require Archi.
(** newly added **)
Require Export Ctypes.
(* Csem Csyntax ASTC. *)
Require Import Errors.
Require Import Values.
Require Import sflib.
Require Import Skeleton ASTC.

Set Implicit Arguments.

Generalizable Variables F.

Definition fundef_of_fundef F (f: Ctypes.fundef F): AST.fundef F :=
  match f with
  | Internal f => AST.Internal f
  | External ef _ _ _ => AST.External ef
  end
.

Coercion fundef_of_fundef: Ctypes.fundef >-> AST.fundef.


Definition globdef_of_globdef F V (gd: globdef (Ctypes.fundef F) V) : globdef (AST.fundef F) V :=
  match gd with
  | Gfun fd => Gfun (fundef_of_fundef fd)
  | Gvar v => Gvar v
  end.

(* Definition is_external F (gd: globdef (Ctypes.fundef F) type): bool := *)
(*   match gd with *)
(*   | Gfun fd => is_external_fd fd *)
(*   | Gvar _ => false *)
(*   end *)
(* . *)

Global Instance fundef_HasExternal {F}: HasExternal (Ctypes.fundef F) :=
  Build_HasExternal (fun fd => is_external_fd (fundef_of_fundef fd)).

(* Module CSkEnv. *)

(*   Definition revive {F} (skenv: SkEnv.t) (prog: Ctypes.program F): Genv.t (Ctypes.fundef F) type := *)
(*     skenv.(Genv_map_defs) (fun blk gd => (do id <- skenv.(Genv.invert_symbol) blk; *)
(*                                          do gd <- prog.(prog_defmap) ! id; *)
(*                                          assertion (negb (is_external gd)); *)
(*                                          Some gd)) *)
(*   . *)

(*   Lemma revive_no_external *)
(*         F (prog: Ctypes.program F) *)
(*         skenv blk gd *)
(*         (DEF: Genv.find_def (revive skenv prog) blk = Some gd) *)
(*         (EXTERNAL: is_external gd) *)
(*     : *)
(*       False *)
(*   . *)
(*   Proof. *)
(*     unfold revive in *. *)
(*     apply_all_once Genv_map_defs_def. des. *)
(*     u in *. des_ifs. *)
(*   Qed. *)

(* End CSkEnv. *)

(* Definition program_of_program' F (p: program F) : AST.program (AST.fundef F) type := *)
(*   {| AST.prog_defs := map (fun idg => update_snd (@globdef_of_globdef _ _) idg) p.(prog_defs); *)
(*      AST.prog_public := p.(prog_public); *)
(*      AST.prog_main := p.(prog_main) |}. *)

(* Coercion program_of_program': program >-> AST.program. *)

Module CSk.

  Definition of_program {F} (get_sg: F -> signature) (prog: Ctypes.program F): Sk.t :=
    mkprogram (skdefs_of_gdefs get_sg (map (update_snd (@globdef_of_globdef F type)) prog.(prog_defs))) prog.(prog_public) prog.(prog_main)
  .

  Lemma of_program_defs
        F
        get_sg
        (p: Ctypes.program F)
    :
      (of_program get_sg p).(defs) = p.(defs)
  .
  Proof.
    destruct p; ss.
    Local Opaque in_dec.
    u; ss.
    Local Transparent in_dec.
    apply Axioms.functional_extensionality. intro id; ss.
    Check (in_dec ident_eq id (map fst prog_defs)).
    rewrite map_map. rewrite map_map. ss.
  Qed.

  Let match_fundef F0 F1 (_: unit): Ctypes.fundef F0 -> AST.fundef F1 -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | Internal _, AST.Internal _ => true
      | External ef0 _ _ _, AST.External ef1 => external_function_eq ef0 ef1
      | _, _ => false
      end
  .

  Lemma of_program_prog_defmap
        F
        (p: Ctypes.program F)
        get_sg
    :
      <<SIM: forall id, option_rel (@Linking.match_globdef unit _ _ _ _ _
                                                           (@match_fundef _ _)
                                                           top2
                                                           tt)
                                   (p.(prog_defmap) ! id) ((of_program get_sg p).(prog_defmap) ! id)>>
  .
  Proof.
    ii.
    unfold prog_defmap, of_program, skdefs_of_gdefs. ss.
    rewrite prog_defmap_update_snd.
    rewrite prog_defmap_update_snd.
    destruct ((PTree_Properties.of_list (prog_defs p)) ! id) eqn:T; ss.
    - econs; et. unfold skdef_of_gdef.
      destruct g; ss; clarify; unfold fundef_of_fundef in *; des_ifs.
      + econs; et.
        { refl. }
        econs; et.
      + econs; et.
        { refl. }
        r. des_sumbool. refl.
      + econs; et. destruct v; ss.
    - econs; et.
  Unshelve.
    all: ss.
  Qed.
  Local Opaque prog_defmap.

  Lemma of_program_internals
        F
        get_sg
        (p: Ctypes.program F)
    :
      (of_program get_sg p).(internals) = p.(internals)
  .
  Proof.
    unfold internals.
    destruct p; ss.
    apply Axioms.functional_extensionality. intro id; ss.
    u.
    exploit (of_program_prog_defmap). i. inv H.
    - rewrite <- H2. rewrite <- H1. ss.
    - des_ifs_safe. inv H2; ss. unfold match_fundef in *. des_ifs. des_sumbool. clarify.
      ss. clarify.
  Qed.
  Local Transparent prog_defmap.

End CSk.


Module CSkEnv.

  Local Opaque prog_defs_names.
  Local Opaque prog_defmap.
  Lemma project_revive_precise
        F
        skenv (prog: Ctypes.program F)
        (* (DEFS0: forall id, In id prog.(prog_defs_names) -> is_some (skenv.(Genv.find_symbol) id)) *)
        (* (WF: wf skenv) *)
        skenv_link
        (* (PROJ: skenv = SkEnv.project skenv_link prog) *)
        get_sg
        (PROJ: SkEnv.project_spec skenv_link prog.(CSk.of_program get_sg) skenv)
        (* (WF: SkEnv.wf skenv_link) *)
        (INCL: SkEnv.includes skenv_link prog.(CSk.of_program get_sg))
    (* (PRECISE: SkEnv.genv_precise (SkEnv.revive skenv prog) prog *)
    :
      <<PRECISE: SkEnv.genv_precise (SkEnv.revive skenv prog) prog>>
  .
  Proof.
    assert(H: DUMMY_PROP) by ss.
    assert(DEFS: prog.(defs) <1= fun id => is_some (skenv.(Genv.find_symbol) id)).
    { ii; ss. u. des_ifs. exfalso.
      bar.
      inv PROJ.
      bar.
      inv INCL.
      bar.
      exploit SYMBKEEP; et.
      { rewrite CSk.of_program_defs. eauto. }
      intro EQ. des. rewrite Heq in *. symmetry in EQ.
      u in PR. des_sumbool. apply prog_defmap_spec in PR. des.
      hexploit (CSk.of_program_prog_defmap prog get_sg x0). intro REL. rewrite PR in *. inv REL. symmetry in H1.
      exploit DEFS; et. i; des. clarify.
    }
    econs; eauto; i; ss; cycle 1.
    - des.
      unfold SkEnv.revive in *.
      apply_all_once Genv_map_defs_def. des; ss.
      ss.
      rewrite Genv_map_defs_symb in *. u in *. des_ifs_safe. simpl_bool.
      apply_all_once Genv.invert_find_symbol.
      determ_tac Genv.genv_vars_inj.
    - rename H0 into DEFMAP. des.
      dup H. u in DEFS. unfold ident in *. spc DEFS.
      exploit DEFS; clear DEFS.
      { unfold proj_sumbool. des_ifs; ss. exfalso. apply n. eapply prog_defmap_spec; eauto. }
      i; des.
      des_ifs_safe.
      esplits; eauto.
      unfold SkEnv.revive. u.
      unfold Genv.find_def, Genv_map_defs. cbn. rewrite PTree_filter_map_spec.
      clear_tac.
      rewrite o_bind_ignore.
      exploit Genv.find_invert_symbol; et. intro INV.
      bar.
      inv PROJ.
      inv INCL.
      bar.
      assert(defs (CSk.of_program get_sg prog) id).
      { apply NNPP. ii. exploit SYMBDROP; et. i; des. clarify. }
      exploit SYMBKEEP; et. intro SYMBLINK; des. rewrite Heq in *. symmetry in SYMBLINK.
      exploit Genv.find_invert_symbol; et. intro INVLINK.
      hexploit (CSk.of_program_prog_defmap prog get_sg id); et. intro REL.
      rewrite DEFMAP in *. inv REL.
      rename H2 into MATCHGD. rename H1 into DEFMAP1.
      exploit DEFS; et. i; des. clarify.
      des_ifs_safe.
      inv MATCHGD; cycle 1.
      {
        des_ifs_safe.
        inv MATCH.
        exploit DEFKEEP; et.
        { rewrite CSk.of_program_internals. u. des_ifs. }
        i; des. uge. clarify.
      }
      {
        inv MATCH.
        destruct (is_external_fd f1) eqn:T.
        - etrans; cycle 1.
          { instantiate (1:= None). des_ifs. ss. des_ifs. }
          assert(is_external f2).
          { rr in H1. des_ifs; ss. des_sumbool. clarify. }
          rename fd2 into fd_big.
          rename f2 into fd_small. rename f1 into fd_small2.
          (* if (Genv.genv_defs skenv) is some, then it should be fd_big *)
          (* fd_big *)
          bar.
          des_ifs. uge.
          exploit DEFKEPT; et. i; des. clarify.
          rewrite CSk.of_program_internals in *.
          u in H4. des_ifs. bsimpl. ss. clarify.
        - etrans; cycle 1.
          { instantiate (1:= Some (Gfun f1)). des_ifs. ss. des_ifs. }
          des_ifs. exfalso.

          exploit DEFKEEP; et.
          { rewrite CSk.of_program_internals in *. u. des_ifs. ss. bsimpl. ss. }
          intro GD; des. uge. clarify.
      }
  Qed.

  Lemma project_revive_no_external
        F (prog: Ctypes.program F)
        skenv_link get_sg blk gd
        (DEF: Genv.find_def (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program get_sg prog)) prog) blk = Some gd)
        (EXTERNAL: is_external gd)
        (INCL: SkEnv.includes skenv_link (CSk.of_program get_sg prog))
        (WF: SkEnv.wf skenv_link)
    :
      False
  .
  Proof.
    assert(H: DUMMY_PROP) by ss.
    hexploit (@SkEnv.project_impl_spec skenv_link (CSk.of_program get_sg prog)); et. intro PROJ. des.
    exploit project_revive_precise; et. intro GEP; des.
    exploit SkEnv.project_spec_preserves_wf; et. intro WF0; des.
    inv WF0.
    dup DEF.
    unfold SkEnv.revive in DEF. apply Genv_map_defs_def in DEF. des.
    exploit DEFSYMB; et. i; des.
    inv GEP.
    exploit FIND_MAP_INV.
    { esplits; et. }
    i; des.
    uo. des_ifs.
    inv PROJ.
    exploit (SYMBKEEP id); et.
    { rewrite CSk.of_program_defs. u. des_sumbool. eapply prog_defmap_image; et. }
    i; des.
    exploit DEFKEPT; et.
    { apply Genv.find_invert_symbol. rewrite <- H1. et. }
    i; des.
    rewrite CSk.of_program_internals in *.
    u in H2. des_ifs.
  Qed.

End CSkEnv.
