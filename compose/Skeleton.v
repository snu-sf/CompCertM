Require Import CoqlibC.
Require Export GlobalenvsC.
Require Import Memory.
Require Import Ctypes.
Require Export ASTC.
Require Import MapsC.
Require Import Values.

Set Implicit Arguments.



Definition is_gvar F V (gd: globdef F V): bool :=
  match gd with
  | Gvar _ => true
  | _ => false
  end
.

(* I don't want it to be "AST.program"-dependent, because of Ctypes.program *)
(* TODO: In high level, prog_public can be dropped, as the data is already linked. Is it really so? *)
(* Definition flesh F V := list (ident * globdef F V)%type. *)

(* Skeleton Genv *)
Module SkEnv.

  (* TODO: Fix properly to cope with Ctypes.fundef *)
  Definition t := Genv.t (AST.fundef (option signature)) unit.

  Inductive wf (skenv: t): Prop :=
  | wf_intro
    (SYMBDEF: forall
        id blk
        (SYMB: skenv.(Genv.find_symbol) id = Some blk)
     ,
       <<DEF: exists skd, skenv.(Genv.find_def) blk = Some skd>>)
    (DEFSYMB: forall
        blk skd
        (DEF: skenv.(Genv.find_def) blk = Some skd)
     ,
       <<SYMB: exists id, skenv.(Genv.find_symbol) id = Some blk>>)
  .

  Inductive project_spec (skenv: t) (keep: ident -> Prop)
            (skenv_proj: t): Prop :=
  | project_spec_intro
      (* (PUBLIC: skenv_proj.(Genv.genv_public) = []) *)
      (* TODO: is this OK? Check if this info affects semantics except for linking *)
      (PUBLIC: skenv_proj.(Genv.genv_public) = skenv.(Genv.genv_public))
      (NEXT: skenv.(Genv.genv_next) = skenv_proj.(Genv.genv_next))
      (* (SYMBKEEP: forall *)
      (*     id *)
      (*     (KEEP: keep id) *)
      (*     blk *)
      (*     (BIG: skenv.(Genv.find_symbol) id = Some blk) *)
      (*   , *)
      (*     (<<SMALL: skenv_proj.(Genv.find_symbol) id = Some blk>>)) *)
      (SYMBKEEP: forall
          id
          (KEEP: keep id)
        ,
          (<<KEEP: skenv_proj.(Genv.find_symbol) id = skenv.(Genv.find_symbol) id>>))
      (SYMBDROP: forall
          id
          (DROP: ~ keep id)
        ,
          <<NONE: skenv_proj.(Genv.find_symbol) id = None>>)
      (* (DEFKEEP: forall *)
      (*     id blk *)
      (*     (INV: skenv.(Genv.invert_symbol) blk = Some id) *)
      (*     (KEEP: keep id) *)
      (*     gd *)
      (*     (BIG: skenv.(Genv.find_def) id = Some gd) *)
      (*   , *)
      (*     <<SMALL: skenv_proj.(Genv.find_def) id = Some gd>>) *)
      (DEFKEEP: forall
          id blk
          (INV: skenv.(Genv.invert_symbol) blk = Some id)
          (KEEP: keep id)
        ,
          <<SMALL: skenv_proj.(Genv.find_def) blk = skenv.(Genv.find_def) blk>>)
      (DEFDROP: forall
          id blk
          (INV: skenv.(Genv.invert_symbol) blk = Some id)
          (DROP: ~ keep id)
        ,
          <<SMALL: skenv_proj.(Genv.find_def) blk = None>>)
      (DEFORPHAN: forall (* TODO: is it needed? *)
          blk
          (INV: skenv.(Genv.invert_symbol) blk = None)
        ,
          <<SMALL: skenv_proj.(Genv.find_def) blk = None>>)
  .

  (* NOTE: it is total function! This is helpful because we don't need to state bsim of this, like
"(PROGRESS: project src succed -> project tgt succeed) /\ (BSIM: project tgt ~ projet src)".
I think "sim_skenv_monotone" should be sufficient.
   *)
  Definition project (skenv: t) (keep: ident -> bool): t :=
    (skenv.(Genv_filter_symb) (fun id => keep id))
    .(Genv_map_defs) (fun blk gd => (do id <- skenv.(Genv.invert_symbol) blk; assertion(keep id); Some gd))
  .

  Lemma project_impl_spec
        skenv (keep: ident -> bool)
    :
      <<PROJ: project_spec skenv keep (project skenv keep)>>
  .
  Proof.
    u.
    unfold project in *. ss.
    econs; eauto; unfold Genv.find_symbol, Genv.find_def, Genv_map_defs in *; ss; ii.
    - rewrite PTree_filter_key_spec. des_ifs.
    - rewrite PTree_filter_key_spec. des_ifs.
    - rewrite PTree_filter_map_spec. des_ifs.
      u. des_ifs.
    - rewrite PTree_filter_map_spec. des_ifs.
      u. des_ifs.
    - rewrite PTree_filter_map_spec. des_ifs.
      u. des_ifs.
  Qed.

  Lemma project_spec_preserves_wf
        skenv
        (WF: wf skenv)
        keep skenv_proj
        (PROJ: project_spec skenv keep skenv_proj)
    :
      <<WF: wf skenv_proj>>
  .
  Proof.
    inv WF. inv PROJ.
    econs; eauto.
    - ii.
      destruct (classic (keep id)).
      + erewrite SYMBKEEP in *; eauto.
        erewrite DEFKEEP; eauto.
        apply Genv.find_invert_symbol; ss.
      + erewrite SYMBDROP in *; eauto. ss.
    - ii.
      destruct (Genv.invert_symbol skenv blk) eqn:T; cycle 1.
      { exploit DEFORPHAN; eauto. i; des. clarify. }
      rename i into id.

      exploit Genv.invert_find_symbol; eauto. intro TT.
      destruct (classic (keep id)).
      + esplits; eauto. erewrite SYMBKEEP; eauto.
      + exploit DEFDROP; eauto. i; des.
        exploit SYMBDEF; eauto. i; des. clarify.
  Qed.

  (* Definition project (skenv: t) (ids: list ident): option SkEnv.t. *)
  (*   admit "". *)
  (* Defined. *)

  Definition internals (skenv: t): list block :=
    List.map fst (skenv.(Genv.genv_defs).(PTree.elements))
  .

  (* We will not need this for now. Fix it when we need it (dynamic linking/incremental compilation) *)
  Definition filter_symbols (skenv: t) (symbols: list ident): t :=
    skenv.(Genv_filter_symb) (fun id => List.in_dec ident_eq id symbols)
  .

  (* Note: We only remove definitions. One can still get the address of external identifier. *)
  Definition revive {F V} (skenv: SkEnv.t) (prog: AST.program (AST.fundef F) V): Genv.t (AST.fundef F) V :=
    skenv.(Genv_map_defs) (fun blk gd => (do id <- skenv.(Genv.invert_symbol) blk;
                                            do gd <- prog.(prog_defmap) ! id;
                                            assertion (negb (is_external gd));
                                            Some gd))
  .

  Print Genv.public_symbol.
  Definition privs (skenv: SkEnv.t): ident -> bool :=
    fun id =>
      match skenv.(Genv.find_symbol) id with
      | Some _ => negb (proj_sumbool (in_dec ident_eq id skenv.(Genv.genv_public)))
      | None => false
      end
  .

End SkEnv.

(* Hint Unfold SkEnv.revive. *)



Definition skdef_of_gdef {F V} (gdef: globdef (AST.fundef F) V): globdef (AST.fundef (option signature)) unit :=
  match gdef with
  | Gfun (Internal f) => Gfun (Internal None)
  | Gfun (External ef) => Gfun (External ef)
  | Gvar v => Gvar (mkglobvar tt v.(gvar_init) v.(gvar_readonly) v.(gvar_volatile))
  end
.

Definition skdefs_of_gdefs {F V} (gdefs: list (ident * globdef (AST.fundef F) V)):
  list (ident * globdef (AST.fundef (option signature)) unit) :=
  map (update_snd skdef_of_gdef) gdefs
.

(* Skeleton *)
Module Sk.

  Definition t := AST.program (AST.fundef (option signature)) unit.

  Definition load_skenv: t -> SkEnv.t := @Genv.globalenv (AST.fundef (option signature)) unit.
  (* No coercion! *)

  Definition load_mem: t -> option mem := @Genv.init_mem (AST.fundef (option signature)) unit.
  (* No coercion! *)

  Lemma load_skenv_wf
        sk
    :
      <<WF: SkEnv.wf sk.(load_skenv)>>
  .
  Proof.
    unfold load_skenv. u.
    admit "easy. follow induction proofs on Globalenvs.v".
  Qed.

  Definition of_program {F V} (prog: AST.program (AST.fundef F) V): t :=
    mkprogram (skdefs_of_gdefs prog.(prog_defs)) prog.(prog_public) prog.(prog_main)
  .

  Lemma of_program_defs
        F V
        (p: AST.program (AST.fundef F) V)
    :
      (of_program p).(defs) = p.(defs)
  .
  Proof.
    destruct p; ss.
    Local Opaque in_dec.
    u; ss.
    Local Transparent in_dec.
    apply Axioms.functional_extensionality. intro id; ss.
    Check (in_dec ident_eq id (map fst prog_defs)).
    rewrite map_map. ss.
  Qed.

End Sk.

Hint Unfold skdef_of_gdef skdefs_of_gdefs Sk.load_skenv Sk.load_mem.



(* They are just located, without any add/remove *)
About Genv.find_def_symbol.
Inductive sk_skenv_iso (sk: Sk.t) (skenv: SkEnv.t): Prop :=
| sk_skenv_iso_intro
    (ISO: forall
        id skd
      ,
        <<SK: sk.(prog_defmap) ! id = Some skd /\ is_internal skd>> <->
        <<SKENV: exists blk, skenv.(Genv.find_symbol) id = Some blk
                             /\ skenv.(Genv.find_def) blk = Some skd>>)
.




(* Question: How does genv affect semantics? *)
Module PLAYGROUND.

Require Import RTL.

Theorem eval_addressing_irr
        F V
        (ge0 ge1: Genv.t F V)
        (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  :
    <<OP: all3 (Op.eval_addressing ge0 =3= Op.eval_addressing ge1)>>
.
Proof.
  u.
  ii. unfold Op.eval_addressing. des_ifs.
  destruct x1; ss.
  { des_ifs. unfold Genv.symbol_address. rewrite SYMB. ss. }
Qed.

Theorem eval_operation_irr
        F V
        (ge0 ge1: Genv.t F V)
        (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  :
    <<OP: all4 (Op.eval_operation ge0 =4= Op.eval_operation ge1)>>
.
Proof.
  u.
  ii.
  destruct x1; ss.
  { des_ifs. unfold Genv.symbol_address. rewrite SYMB. ss. }
  { erewrite eval_addressing_irr; eauto. }
Qed.

Goal forall ge0 ge1 st0 tr st1
            (STEP: step ge0 st0 tr st1)
            (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  ,
    <<STEP: step ge1 st0 tr st1>>
.
Proof.
  i. inv STEP; try (by econs; eauto).
  - erewrite eval_operation_irr in *; eauto. econs; eauto.
  - erewrite eval_addressing_irr in *; eauto. econsby eauto.
  - erewrite eval_addressing_irr in *; eauto. econsby eauto.
  - econs; eauto.
    unfold find_function_ptr in *. des_ifs_safe. rewrite SYMB in *. ss.
  - econs; eauto.
    unfold find_function_ptr in *. des_ifs_safe. rewrite SYMB in *. ss.
  - eapply Events.eval_builtin_args_preserved with (ge2 := ge1) in H0; eauto.
    econs; eauto. eapply Events.external_call_symbols_preserved; eauto.
    econs; eauto.
    split.
    admit "Publics".
    Print Genv.block_is_volatile.
    admit "Genv.find_def with Gvar. (volatile)".
  - econs; eauto.
    unfold Genv.find_funct in *. des_ifs.
    unfold Genv.find_funct_ptr in *.
    admit "Genv.find_def with Gfun. internals".
  - unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    admit "Genv.find_def with Gfun. externals".
Abort.

End PLAYGROUND.



