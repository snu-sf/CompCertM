Require Recdef.
Require Import Zwf.
Require Import Axioms CoqlibC Errors MapsC ASTC Linking.
Require Import Integers Floats ValuesC Memory.
Require Import sflib.

Require Export Globalenvs.

Require Import sflib.
From Paco Require Import paco.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.

Set Implicit Arguments.




Definition is_call {F V} (ge: Genv.t F V) (fptr: val): Prop :=
  match fptr with
  | Vptr blk ofs true => Genv.find_funct_ptr ge blk = None
  | _ => False
  end
.

Hint Unfold is_call.

Section ISCALL.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
  Variable ge1: Genv.t F1 V1.
  Variable ge2: Genv.t F2 V2.
  Variable ctx: C.
  Variable match_fundef: C -> F1 -> F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Hypothesis (GEMATCH: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge1 ge2).

  Lemma is_call_lessdef_progress
        fptr1 fptr2
        (LD: Val.lessdef fptr1 fptr2)
        (SRCCALL: is_call ge1 fptr1)
    :
      <<TGTCALL: is_call ge2 fptr2>>
  .
  Proof.
    u in *. des. inv LD; ss. des_ifs.
    esplits; eauto.
    ss. des_ifs.
    unfold Genv.find_funct_ptr, Genv.find_def in *. inv GEMATCH.
    specialize (mge_defs b). inv mge_defs; ss.
    inv H1; ss. des_ifs.
  Qed.

  Lemma is_call_lessdef_bsim
        fptr1 fptr2
        (LD: Val.lessdef fptr1 fptr2)
        (TGTCALL: is_call ge2 fptr2)
    :
      <<SRCCALL: is_call ge1 fptr1>> \/ <<SRCUB: fptr1 = Vundef>>
  .
  Proof.
    u in *. des. inv LD; ss; cycle 1. { right; ss. } left. des_ifs.
    esplits; eauto.
    ss. des_ifs; try (by left; esplits; eauto).
    unfold Genv.find_funct_ptr, Genv.find_def in *. inv GEMATCH.
    specialize (mge_defs b). inv mge_defs; ss.
    inv H1; ss. des_ifs.
  Qed.

  Local Existing Instance Val.mi_normal.

  Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj): Prop :=
  | sken_inject_intro
      (DOMAIN: forall b, Plt b ge.(Genv.genv_next) -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 ge.(Genv.genv_next) -> b1 = b2)
  .

  Variable F: meminj.
  Hypothesis (GEINJ: skenv_inject ge1 F).

  Lemma is_call_inject_progress
        fptr1 fptr2
        (INJ: Val.inject F fptr1 fptr2)
        (SRCCALL: is_call ge1 fptr1)
    :
      <<TGTCALL: is_call ge2 fptr2>>
  .
  Proof.
    u in *. des. inv INJ; ss. des_ifs.
    esplits; eauto.
    ss. des_ifs.
    unfold Genv.find_funct_ptr, Genv.find_def in *. inv GEMATCH.
    des_ifs_safe.
    inv GEINJ.
    exploit Genv.genv_defs_range; eauto. i.
    exploit IMAGE; eauto. { eauto with congruence lia. }
    exploit DOMAIN; eauto. { rewrite <- mge_next. eauto with congruence lia. }
    i; clarify.
    specialize (mge_defs b2). inv mge_defs; ss; eauto with congruence.
    - des_ifs. inv H3; ss. rewrite <- H2 in *. clarify.
  Qed.

  Lemma is_call_inject_bsim
        fptr1 fptr2
        (INJ: Val.inject F fptr1 fptr2)
        (TGTCALL: is_call ge2 fptr2)
    :
      <<SRCCALL: is_call ge1 fptr1>> \/ <<SRCUB: fptr1 = Vundef>>
  .
  Proof.
    u in *. des. inv INJ; ss; cycle 1. { right; ss. } left.
    unfold Genv.find_funct_ptr, Genv.find_def in *. inv GEMATCH.
    des_ifs_safe.
    specialize (mge_defs b1). inv mge_defs; eauto with congruence.
    inv GEINJ.
    exploit Genv.genv_defs_range; eauto. i.
    exploit DOMAIN; eauto. i. clarify.

    des_ifs; eq_closure_tac.
    inv H2; ss.
  Qed.


End ISCALL.



Section MAP.

  Variable F1 V1 F2 V2: Type.

  Program Definition Genv_map_defs (ge0: Genv.t F1 V1)
          (f: block -> globdef F1 V1 -> option (globdef F2 V2)): Genv.t F2 V2 :=
  {|
    Genv.genv_public := ge0.(Genv.genv_public);
    Genv.genv_symb := ge0.(Genv.genv_symb);
    Genv.genv_defs := ge0.(Genv.genv_defs).(PTree_filter_map f);
    Genv.genv_next := ge0.(Genv.genv_next);
  |}
  .
  Next Obligation. eapply Genv.genv_symb_range; eauto. Qed.
  Next Obligation. rewrite PTree_filter_map_spec in H. u in *. des_ifs. eapply Genv.genv_defs_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_vars_inj; eauto. Qed.

  Lemma Genv_map_defs_def
        ge (f: block -> globdef F1 V1 -> option (globdef F2 V2))
        blk gd2
        (FIND: (ge.(Genv_map_defs) f).(Genv.find_def) blk = Some gd2)
    :
      exists gd1, <<FIND: ge.(Genv.find_def) blk = Some gd1>> /\ <<MAP: f blk gd1 = Some gd2>>
  .
  Proof.
    unfold Genv.find_def in *. unfold Genv_map_defs in *. ss.
    rewrite PTree_filter_map_spec in *. u in FIND. des_ifs.
    esplits; eauto.
  Qed.

  Lemma Genv_map_defs_def_inv
        ge
        blk gd
        (FIND: ge.(Genv.find_def) blk = Some gd)
    :
      <<FIND: forall (f: block -> globdef F1 V1 -> option (globdef F2 V2)),
        (ge.(Genv_map_defs) f).(Genv.find_def) blk = f blk gd>>
  .
  Proof.
    ii. unfold Genv.find_def in *. unfold Genv_map_defs in *. ss.
    rewrite PTree_filter_map_spec in *. u. des_ifs.
  Qed.

  Lemma Genv_map_defs_symb
        ge (f: block -> globdef F1 V1 -> option (globdef F2 V2))
    :
      <<FIND: all1 ((ge.(Genv_map_defs) f).(Genv.find_symbol) =1= ge.(Genv.find_symbol))>>
  .
  Proof.
    ii; ss.
  Qed.

  (* Note: genv_defs will have spurious data, but this is actually Compcert's interpretation. *)
  Program Definition Genv_filter_symb (ge0: Genv.t F1 V1)
          (f: ident -> bool): Genv.t F1 V1 :=
  {|
    Genv.genv_public := ge0.(Genv.genv_public);
    Genv.genv_symb := ge0.(Genv.genv_symb).(PTree_filter_key f);
    Genv.genv_defs := ge0.(Genv.genv_defs);
    Genv.genv_next := ge0.(Genv.genv_next);
  |}
  .
  Next Obligation. rewrite PTree_filter_key_spec in *. des_ifs. eapply Genv.genv_symb_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_defs_range; eauto. Qed.
  Next Obligation. rewrite PTree_filter_key_spec in *. des_ifs. eapply Genv.genv_vars_inj; eauto. Qed.


End MAP.



(* Below may not be needed *)
Section MATCH_PROGRAMS_BACKWARD.

Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
(* Variable transf_fundef: C -> F1 -> option F2. *)
(* Let match_fundef: C -> F1 -> F2 -> Prop := fun c f tf => transf_fundef c f = Some tf. *)
Variable match_fundef: C -> F1 -> F2 -> Prop.
Variable match_varinfo: V1 -> V2 -> Prop.
Variable ctx: C.
Variable p: program F1 V1.
Variable tp: program F2 V2.
Hypothesis progmatch: match_program_gen match_fundef match_varinfo ctx p tp.

Theorem find_def_match_backward:
  forall b tg,
  Genv.find_def (Genv.globalenv tp) b = Some tg ->
  exists g,
  Genv.find_def (Genv.globalenv p) b = Some g /\ match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  intros. generalize (Genv.find_def_match_2 progmatch b). rewrite H; intros R; inv R.
  exists x; auto.
Qed.

Theorem find_funct_ptr_match_backward:
  forall b tf,
  Genv.find_funct_ptr (Genv.globalenv tp) b = Some tf ->
  exists cunit f,
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. rewrite Genv.find_funct_ptr_iff in *. apply find_def_match_backward in H.
  destruct H as (tg & P & Q). inv Q.
  exists ctx', f1; intuition auto. apply Genv.find_funct_ptr_iff; auto.
Qed.

Theorem find_funct_match_backward:
  forall v tf,
  Genv.find_funct (Genv.globalenv tp) v = Some tf ->
  exists cunit f,
  Genv.find_funct (Genv.globalenv p) v = Some f /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H.
  rewrite Genv.find_funct_find_funct_ptr.
  apply find_funct_ptr_match_backward. auto.
Qed.

Theorem find_var_info_match_backward:
  forall b tv,
  Genv.find_var_info (Genv.globalenv tp) b = Some tv ->
  exists v,
  Genv.find_var_info (Genv.globalenv p) b = Some v /\ match_globvar match_varinfo v tv.
Proof.
  intros. rewrite Genv.find_var_info_iff in *. apply find_def_match_backward in H.
  destruct H as (tg & P & Q). inv Q.
  exists v1; split; auto. apply Genv.find_var_info_iff; auto.
Qed.

Lemma store_init_data_list_match_backward:
  forall idl m b ofs m',
  Genv.store_init_data_list (Genv.globalenv tp) m b ofs idl = Some m' ->
  Genv.store_init_data_list (Genv.globalenv p) m b ofs idl = Some m'.
Proof.
  induction idl; simpl; intros.
- auto.
- destruct (Genv.store_init_data (Genv.globalenv tp) m b ofs a) as [m1|] eqn:S; try discriminate.
  assert (X: Genv.store_init_data (Genv.globalenv p) m b ofs a = Some m1).
  { destruct a; auto. simpl; rewrite <- (Genv.find_symbol_match progmatch); auto. }
  rewrite X. auto.
Qed.

Lemma alloc_globals_match_backward:
  forall gl1 gl2, list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 ->
  forall m m',
  Genv.alloc_globals (Genv.globalenv tp) m gl2 = Some m' ->
  Genv.alloc_globals (Genv.globalenv p) m gl1 = Some m'.
Proof.
  induction 1; simpl; intros.
- auto.
- destruct (Genv.alloc_global (Genv.globalenv tp) m b1) as [m1|] eqn:?; try discriminate.
  assert (X: Genv.alloc_global (Genv.globalenv p) m a1 = Some m1).
  { destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; destruct H; simpl in *.
    subst id2. inv H2.
  - auto.
  - inv H; simpl in *.
    set (sz := init_data_list_size init) in *.
    destruct (Mem.alloc m 0 sz) as [m2 b] eqn:?.
    destruct (store_zeros m2 b 0 sz) as [m3|] eqn:?; try discriminate.
    destruct (Genv.store_init_data_list (Genv.globalenv tp) m3 b 0 init) as [m4|] eqn:?; try discriminate.
    erewrite store_init_data_list_match_backward; eauto.
  }
  rewrite X; eauto.
Qed.

Theorem init_mem_match_backward:
  forall m, Genv.init_mem tp = Some m -> Genv.init_mem p = Some m.
Proof.
  unfold Genv.init_mem; intros.
  eapply alloc_globals_match_backward; eauto. apply progmatch.
Qed.

End MATCH_PROGRAMS_BACKWARD.

Program Instance Senv_eq_equiv: RelationClasses.Equivalence Senv.equiv.
Next Obligation.
  ii.
  econs; eauto.
Qed.
Next Obligation.
  ii.
  inv H. des.
  econs; eauto.
Qed.
Next Obligation.
  ii.
  inv H. inv H0. des.
  econs; eauto.
  i. erewrite <- H1; eauto.
Qed.



(* Inductive good_genv {F V} (ge: Genv.t F V): Prop := *)
(* | good_genv_intro *)
(*     (FIND_SYMBOL: forall id b, *)
(*         Genv.find_symbol ge id = Some b -> (exists g, Genv.find_def ge b = Some g)) *)
(*     (FIND_DEF: forall b g, *)
(*         Genv.find_def ge b = Some g -> (exists id, Genv.find_symbol ge id = Some b)) *)
(* . *)

(* Inductive genv_precise {F V} (ge: Genv.t F V) (p: program F V): Prop := *)
(* | genv_compat_intro *)
(*     (FIND_MAP: forall id g, *)
(*         p.(prog_defmap) ! id = Some g -> *)
(*         (exists b, Genv.find_symbol ge id = Some b /\ Genv.find_def ge b = Some g)) *)
(*     (FIND_MAP_INV: forall id b g, *)
(*         (Genv.find_symbol ge id = Some b /\ Genv.find_def ge b = Some g) -> *)
(*         p.(prog_defmap) ! id = Some g) *)
(* . *)



(* Module PLAYGROUND0. *)

(* Section INJECT. *)

(*   Variables F1 V1 F2 V2: Type. *)
(*   Variable ge1: Genv.t F1 V1. *)
(*   Variable ge2: Genv.t F2 V2. *)

(*   (* Record meminj_preserves_globals (f: meminj) : Prop := { *) *)
(*   (*   symbols_inject_1: forall id b b' delta, *) *)
(*   (*     f b = Some(b', delta) -> Genv.find_symbol ge id = Some b -> *) *)
(*   (*     delta = 0 /\ Genv.find_symbol tge id = Some b'; *) *)
(*   (*   symbols_inject_2: forall id b, *) *)
(*   (*     kept id -> Genv.find_symbol ge id = Some b -> *) *)
(*   (*     exists b', Genv.find_symbol tge id = Some b' /\ f b = Some(b', 0); *) *)
(*   (*   symbols_inject_3: forall id b', *) *)
(*   (*     Genv.find_symbol tge id = Some b' -> *) *)
(*   (*     exists b, Genv.find_symbol ge id = Some b /\ f b = Some(b', 0); *) *)
(*   (*   defs_inject: forall b b' delta gd, *) *)
(*   (*     f b = Some(b', delta) -> Genv.find_def ge b = Some gd -> *) *)
(*   (*     Genv.find_def tge b' = Some gd /\ delta = 0 /\ *) *)
(*   (*     (forall id, ref_def gd id -> kept id); *) *)
(*   (*   defs_rev_inject: forall b b' delta gd, *) *)
(*   (*     f b = Some(b', delta) -> Genv.find_def tge b' = Some gd -> *) *)
(*   (*     Genv.find_def ge b = Some gd /\ delta = 0 *) *)
(*   (* }. *) *)

(*   (* Definition init_meminj : meminj := *) *)
(*   (*   fun b => *) *)
(*   (*     match Genv.invert_symbol ge b with *) *)
(*   (*     | Some id => *) *)
(*   (*       match Genv.find_symbol tge id with *) *)
(*   (*       | Some b' => Some (b', 0) *) *)
(*   (*       | None => None *) *)
(*   (*       end *) *)
(*   (*     | None => None *) *)
(*   (*     end. *) *)


(*   Record symbols_inject (f: meminj): Prop := { *)
(*     public: (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id); *)
(*     inject: (forall id b1 b2 delta, *)
(*                  f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 -> *)
(*                  delta = 0 /\ Senv.find_symbol ge2 id = Some b2); *)
(*     public_find: (forall id b1, *)
(*                      Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 -> *)
(*                      exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2); *)
(*   } *)
(*   . *)

(*   (* Definition symbols_inject (f: meminj): Prop := *) *)
(*   (*   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) *) *)
(*   (*   /\ (forall id b1 b2 delta, *) *)
(*   (*          f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 -> *) *)
(*   (*          delta = 0 /\ Senv.find_symbol ge2 id = Some b2) *) *)
(*   (*   /\ (forall id b1, *) *)
(*   (*          Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 -> *) *)
(*   (*          exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2) *) *)
(*   (*   /\ (forall b1 b2 delta, *) *)
(*   (*          f b1 = Some(b2, delta) -> *) *)
(*   (*          Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1). *) *)

(*   Inductive match_globalenvs (f: meminj) (bound: block): Prop := *)
(*   | mk_match_globalenvs *)
(*       (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0)) *)
(*       (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2) *)
(*       (SYMBOLS: forall id b, Genv.find_symbol ge1 id = Some b -> Plt b bound) *)
(*       (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge1 b = Some fd -> Plt b bound) *)
(*       (VARINFOS: forall b gv, Genv.find_var_info ge1 b = Some gv -> Plt b bound) *)
(*   . *)

(*   Lemma ABC *)
(*         f *)
(*         (GOODSRC: good_genv ge1) *)
(*         (GOODTGT: good_genv ge2) *)
(*         (RECIPE: recipe_consistent f recipe_normal) *)
(*         (INJ: symbols_inject f) *)
(*         (FLAT: f = (Mem.flat_inj ge1.(Genv.genv_next))) *)
(*     : *)
(*       match_globalenvs f ge1.(Genv.genv_next) *)
(*   . *)
(*   Proof. *)
(*     (* unfold symbols_inject in *. des. *) *)
(*     unfold Mem.flat_inj in *. des_ifs; ss. *)
(*     inv RECIPE. *)
(*     econs; i; des_ifs; ss. *)
(*     - destruct (Genv.public_symbol ge1 id) eqn:T. *)
(*       + hexploit public_find; try eassumption. *)
(*         i; des. unfold Mem.flat_inj in *. des_ifs. *)
(*       + exploit PRIVATES; eauto. i; des. des_ifs. *)
(*     - unfold Genv.find_funct_ptr in *. *)
(*       des_ifs. *)
(*       inv GOODSRC. *)
(*       exploit FIND_DEF; eauto. i; des. *)
(*       destruct (Genv.public_symbol ge1 id) eqn:T. *)
(*       + exploit public_find; try eassumption. *)
(*         i; des. unfold Mem.flat_inj in *. des_ifs. *)
(*       + exploit PRIVATES; eauto. i; des. des_ifs. *)
(*     - unfold Genv.find_var_info in *. *)
(*       des_ifs. *)
(*       inv GOODSRC. *)
(*       exploit FIND_DEF; eauto. *)
(*       i; des. *)
(*       destruct (Genv.public_symbol ge1 id) eqn:T. *)
(*       + exploit public_find; try eassumption. *)
(*         i; des. unfold Mem.flat_inj in *. des_ifs. *)
(*       + exploit PRIVATES; eauto. i; des. des_ifs. *)
(*   Qed. *)

(*   Lemma ABCD *)
(*         f *)
(*         (GOODSRC: good_genv ge1) *)
(*         (GOODTGT: good_genv ge2) *)
(*         (RECIPE: recipe_consistent f recipe_normal) *)
(*         (INJ: symbols_inject f) *)
(*     : *)
(*       match_globalenvs f ge1.(Genv.genv_next) *)
(*   . *)
(*   Proof. *)
(*     inv RECIPE. *)
(*     econs; i; des_ifs; ss. *)
(*   Abort. *)

(* End INJECT. *)

(* End PLAYGROUND0. *)


(* Module PLAYGROUND1. *)

(* Section INJECT. *)

(*   Variables F1 V1 F2 V2: Type. *)
(*   Variable prog1: program F1 V1. *)
(*   Variable prog2: program F2 V2. *)
(*   Variable ge1: Genv.t F1 V1. *)
(*   Variable ge2: Genv.t F2 V2. *)
(*   Hypothesis COMPAT1: genv_compat ge1 (prog_defmap prog1). *)
(*   Hypothesis COMPAT2: genv_compat ge2 (prog_defmap prog2). *)
(*   Hypothesis GOOD1: good_genv ge1. *)
(*   Hypothesis GOOD2: good_genv ge2. *)
(*   Variable match_gdef: ident * globdef F1 V1 -> ident * globdef F2 V2 -> Prop. *)
(*   (* (match_ident_globdef match_fundef match_varinfo ctx) *) *)
(*   Hypothesis MATCH: list_forall2 match_gdef (prog_defs prog1) (prog_defs prog2). *)

(*   Hypothesis SYMBINJ: symbols_inject ge1 ge2. *)

(* End INJECT. *)

(* End PLAYGROUND1. *)


Lemma find_symbol_eq_invert_symbol_eq
      F0 V0 F1 V1
      (ge0: Genv.t F0 V0) (ge1: Genv.t F1 V1)
      (FIND: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  :
    <<INVERT: all1 (Genv.invert_symbol ge0 =1= Genv.invert_symbol ge1)>>
.
Proof.
  ii.
  destruct (Genv.invert_symbol ge0 x0) eqn:T0.
  - apply Genv.invert_find_symbol in T0.
    rewrite FIND in T0.
    apply Genv.find_invert_symbol in T0.
    ss.
  - destruct (Genv.invert_symbol ge1 x0) eqn:T1.
    { apply Genv.invert_find_symbol in T1. rewrite <- FIND in *. apply Genv.find_invert_symbol in T1. clarify. }
    ss.
Qed.


Section MATCHPROG.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker (AST.fundef F1)} {LV: Linker V1}.
  Variable match_fundef: C -> AST.fundef F1 -> AST.fundef F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Variables (ctx: C) (p_src: AST.program (AST.fundef F1) V1) (p_tgt: AST.program (AST.fundef F2) V2).
  Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt).

  Lemma match_program_gen_defs
    :
      <<EQ: p_src.(defs) = p_tgt.(defs)>>
  .
  Proof.
    apply Axioms.functional_extensionality. ii; ss. u.
    (* hexploit (match_program_defmap _ _ ctx p_src p_tgt MATCH x). intro REL. *)
    inv MATCHPROG. des.
    assert((prog_defs_names p_src) = (prog_defs_names p_tgt)).
    { unfold prog_defs_names.
      clear - H.
      ginduction H; ii; ss.
      inv H; ss. f_equal; ss.
    }
    rewrite H2; ss.
  Qed.

End MATCHPROG.
