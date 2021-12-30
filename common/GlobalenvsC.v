Require Recdef.
Require Import Zwf CoqlibC MapsC ASTC.
From compcertr Require Import
     Axioms
     Errors
     Linking
     Floats
     Memory
     sflib.
Require Import IntegersC ValuesC.

From compcertr Require Export Globalenvs.

From Paco Require Import paco.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.

Set Implicit Arguments.



Ltac uge0 := unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_var_info in *.
Ltac uge1 := unfold Genv.find_def, Genv.find_symbol in *.
Ltac uge := uge0; uge1.
Ltac genext := try (by eapply Genv.genv_defs_range; eauto);
               try (by eapply Genv.genv_symb_range; eauto).








Section EXTERNAL.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
  Variable ge1: Genv.t F1 V1.
  Variable ge2: Genv.t F2 V2.
  Variable ctx: C.
  Variable match_fundef: C -> F1 -> F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Hypothesis (GEMATCH: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge1 ge2).

  Lemma fsim_external_funct_id
        v
        (FINDFSRC: Genv.find_funct ge1 v = None):
      <<FINDFTGT: Genv.find_funct ge2 v = None>>.
  Proof.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs_safe.
    hexploit (Genv.mge_defs GEMATCH); eauto. i. rewrite Heq in *. inv H. inv H2. des_ifs.
  Qed.

  Lemma fsim_internal_funct_id
        v fd_src
        (FINDFSRC: Genv.find_funct ge1 v = Some fd_src):
      exists fd_tgt ctx', (<<FINDFTGT: Genv.find_funct ge2 v = Some fd_tgt>>) /\
                          (<<MATCH: match_fundef ctx' fd_src fd_tgt>>) /\
                          (<<LO: linkorder ctx' ctx>>).
  Proof.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs_safe.
    hexploit (Genv.mge_defs GEMATCH); eauto. i. rewrite Heq in *. inv H. inv H2. esplits; eauto.
  Qed.

  Lemma bsim_internal_funct_id
        v fd_tgt
        (FINDFTGT: Genv.find_funct ge2 v = Some fd_tgt):
      exists fd_src ctx', (<<FINDFTGT: Genv.find_funct ge1 v = Some fd_src>>) /\
                          (<<MATCH: match_fundef ctx' fd_src fd_tgt>>) /\
                          (<<LO: linkorder ctx' ctx>>).
  Proof.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def in *. des_ifs_safe.
    hexploit (Genv.mge_defs GEMATCH); eauto. i. rewrite Heq in *. inv H. inv H2. esplits; eauto.
  Qed.

  Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj): Prop :=
  | sken_inject_intro
      (DOMAIN: forall b, Plt b ge.(Genv.genv_next) -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 ge.(Genv.genv_next) -> b1 = b2).

  Lemma fsim_external_inject_eq
        j v_src v_tgt fd
        (GE: skenv_inject ge1 j)
        (INJ: Val.inject j v_src v_tgt)
        (FIND: Genv.find_funct ge1 v_src = Some fd):
      v_src = v_tgt.
  Proof.
    inv INJ; ss. uge. des_ifs. inv GE. exploit DOMAIN; eauto; try genext. i. clarify.
  Qed.

  Lemma bsim_external_inject_eq
        j v_src v_tgt fd
        (GE: skenv_inject ge1 j)
        (INJ: Val.inject j v_src v_tgt)
        (FINDFTGT: Genv.find_funct ge2 v_tgt = Some fd):
      v_src = v_tgt \/ v_src = Vundef.
  Proof.
    inv INJ; ss; et. uge. des_ifs. inv GE.
    exploit IMAGE; eauto.
    { erewrite <- Genv.mge_next; et. genext. }
    i; clarify. exploit DOMAIN; eauto.
    { erewrite <- Genv.mge_next; et. genext. }
    i; clarify. psimpl. et.
  Qed.

  Lemma fsim_external_funct_inject
        j v_src v_tgt
        (GE: skenv_inject ge1 j)
        (INJ: Val.inject j v_src v_tgt)
        (FINDFSRC: Genv.find_funct ge1 v_src = None)
        (NUNDEF: v_src <> Vundef):
      <<FINDFTGT: Genv.find_funct ge2 v_tgt = None>>.
  Proof.
    r. apply NNPP. intro FINDTGT.
    destruct (Genv.find_funct ge2 v_tgt) eqn:FINDTGT0; ss. clear_tac.
    exploit bsim_external_inject_eq; eauto. i. inv GEMATCH. des; clarify; ss.
    uge. des_ifs_safe. unfold block in *. spc mge_defs. inv mge_defs; align_opt; clarify. des_ifs. inv H1.
  Qed.

  Lemma fsim_internal_funct_inject
        j v_src v_tgt fd_src
        (GE: skenv_inject ge1 j)
        (INJ: Val.inject j v_src v_tgt)
        (FINDFSRC: Genv.find_funct ge1 v_src = Some fd_src):
      exists fd_tgt ctx', (<<FINDFTGT: Genv.find_funct ge2 v_tgt = Some fd_tgt>>) /\
                          (<<MATCH: match_fundef ctx' fd_src fd_tgt>>) /\
                          (<<LO: linkorder ctx' ctx>>).
  Proof.
    exploit fsim_external_inject_eq; eauto. i. inv GEMATCH. inv INJ; ss. uge. des_ifs_safe.
    unfold block in *. spc mge_defs. inv mge_defs; align_opt; clarify. inv H1. esplits; eauto.
  Qed.

  Lemma bsim_internal_funct_inject
        j v_src v_tgt fd_tgt
        (GE: skenv_inject ge1 j)
        (INJ: Val.inject j v_src v_tgt)
        (FINDFSRC: Genv.find_funct ge2 v_tgt = Some fd_tgt):
      <<SRCUB: v_src = Vundef>> \/
      exists fd_src ctx', (<<FINDFTGT: Genv.find_funct ge1 v_src = Some fd_src>>) /\
                          (<<MATCH: match_fundef ctx' fd_src fd_tgt>>) /\
                          (<<LO: linkorder ctx' ctx>>).
  Proof.
    exploit bsim_external_inject_eq; eauto. i. des; eauto. right. clarify.
    inv GEMATCH. inv INJ; ss. uge. des_ifs_safe. psimpl.
    unfold block in *. spc mge_defs. inv mge_defs; align_opt; clarify. inv H1. esplits; eauto.
  Qed.

End EXTERNAL.

Section MAP.

  Variable F1 V1 F2 V2: Type.

  Program Definition Genv_map_defs (ge0: Genv.t F1 V1)
          (f: block -> globdef F1 V1 -> option (globdef F2 V2)): Genv.t F2 V2 :=
  {| Genv.genv_public := ge0.(Genv.genv_public);
     Genv.genv_symb := ge0.(Genv.genv_symb);
     Genv.genv_defs := (PTree_filter_map f ge0.(Genv.genv_defs));
     Genv.genv_next := ge0.(Genv.genv_next);
  |}.
  Next Obligation. eapply Genv.genv_symb_range; eauto. Qed.
  Next Obligation. rewrite PTree_filter_map_spec in H. u in *. des_ifs. eapply Genv.genv_defs_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_vars_inj; eauto. Qed.

  Lemma Genv_map_defs_def
        ge (f: block -> globdef F1 V1 -> option (globdef F2 V2)) blk gd2
        (FIND: (Genv.find_def (Genv_map_defs ge f)) blk = Some gd2):
      exists gd1, <<FIND: (Genv.find_def ge) blk = Some gd1>> /\ <<MAP: f blk gd1 = Some gd2>>.
  Proof.
    unfold Genv.find_def in *. unfold Genv_map_defs in *. ss.
    rewrite PTree_filter_map_spec in *. u in FIND. des_ifs. esplits; eauto.
  Qed.

  Lemma Genv_map_defs_def_inv
        ge blk gd
        (FIND: (Genv.find_def ge) blk = Some gd):
      <<FIND: forall (f: block -> globdef F1 V1 -> option (globdef F2 V2)),
        (Genv.find_def (Genv_map_defs ge f)) blk = f blk gd>>.
  Proof.
    ii. unfold Genv.find_def in *. unfold Genv_map_defs in *. ss.
    rewrite PTree_filter_map_spec in *. u. des_ifs.
  Qed.

  Lemma Genv_map_defs_symb
        ge (f: block -> globdef F1 V1 -> option (globdef F2 V2)):
      <<FIND: all1 ((Genv.find_symbol (Genv_map_defs ge f)) =1= (Genv.find_symbol ge))>>.
  Proof. ii; ss. Qed.

  (* Note: genv_defs will have spurious data, but this is actually Compcert's interpretation. *)
  Program Definition Genv_filter_symb (ge0: Genv.t F1 V1)
          (f: ident -> bool): Genv.t F1 V1 :=
  {| Genv.genv_public := ge0.(Genv.genv_public);
     Genv.genv_symb := (PTree_filter_key f ge0.(Genv.genv_symb));
     Genv.genv_defs := ge0.(Genv.genv_defs);
     Genv.genv_next := ge0.(Genv.genv_next);
  |}.
  Next Obligation. rewrite PTree_filter_key_spec in *. des_ifs. eapply Genv.genv_symb_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_defs_range; eauto. Qed.
  Next Obligation. rewrite PTree_filter_key_spec in *. des_ifs. eapply Genv.genv_vars_inj; eauto. Qed.

  Program Definition Genv_update_publics (ge0: Genv.t F1 V1) (pubs: list ident): Genv.t F1 V1 :=
  {| Genv.genv_public := pubs;
     Genv.genv_symb := ge0.(Genv.genv_symb);
     Genv.genv_defs := ge0.(Genv.genv_defs);
     Genv.genv_next := ge0.(Genv.genv_next);
  |}.
  Next Obligation. eapply Genv.genv_symb_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_defs_range; eauto. Qed.
  Next Obligation. eapply Genv.genv_vars_inj; eauto. Qed.

  Lemma Genv_update_publics_def
        ge0 pubs:
      Genv.find_def (Genv_update_publics ge0 pubs) = Genv.find_def ge0.
  Proof. apply functional_extensionality. i. ss. Qed.

  Lemma Genv_update_publics_symb
        ge0 pubs:
      Genv.find_symbol (Genv_update_publics ge0 pubs) = Genv.find_symbol ge0.
  Proof. apply functional_extensionality. i. ss. Qed.

End MAP.

(* Hint Unfold Genv_update_publics. *)
Ltac gesimpl := try rewrite Genv_update_publics_def in *;
                try rewrite Genv_update_publics_symb in *.



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
  forall b tg, Genv.find_def (Genv.globalenv tp) b = Some tg ->
  exists g, Genv.find_def (Genv.globalenv p) b = Some g /\ match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  intros. generalize (Genv.find_def_match_2 progmatch b). rewrite H; intros R; inv R.
  exists x; auto.
Qed.

Theorem find_funct_ptr_match_backward:
  forall b tf, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tf ->
  exists cunit f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. rewrite Genv.find_funct_ptr_iff in *. apply find_def_match_backward in H.
  destruct H as (tg & P & Q). inv Q.
  exists ctx', f1; intuition auto. apply Genv.find_funct_ptr_iff; auto.
Qed.

Theorem find_funct_match_backward:
  forall v tf, Genv.find_funct (Genv.globalenv tp) v = Some tf ->
  exists cunit f, Genv.find_funct (Genv.globalenv p) v = Some f /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H. rewrite Genv.find_funct_find_funct_ptr.
  apply find_funct_ptr_match_backward. auto.
Qed.

Theorem find_var_info_match_backward:
  forall b tv, Genv.find_var_info (Genv.globalenv tp) b = Some tv ->
  exists v, Genv.find_var_info (Genv.globalenv p) b = Some v /\ match_globvar match_varinfo v tv.
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
  induction idl; simpl; intros; auto.
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
  induction 1; simpl; intros; auto.
- destruct (Genv.alloc_global (Genv.globalenv tp) m b1) as [m1|] eqn:?; try discriminate.
  assert (X: Genv.alloc_global (Genv.globalenv p) m a1 = Some m1).
  { destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; destruct H; simpl in *.
    subst id2. inv H2; auto. inv H; simpl in *.
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
  unfold Genv.init_mem; intros. eapply alloc_globals_match_backward; eauto. apply progmatch.
Qed.

End MATCH_PROGRAMS_BACKWARD.







Lemma find_symbol_eq_invert_symbol_eq
      F0 V0 F1 V1
      (ge0: Genv.t F0 V0) (ge1: Genv.t F1 V1)
      (FIND: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1)):
    <<INVERT: all1 (Genv.invert_symbol ge0 =1= Genv.invert_symbol ge1)>>.
Proof.
  ii. destruct (Genv.invert_symbol ge0 x0) eqn:T0.
  - apply Genv.invert_find_symbol in T0. rewrite FIND in T0.
    apply Genv.find_invert_symbol in T0. ss.
  - destruct (Genv.invert_symbol ge1 x0) eqn:T1; ss.
    apply Genv.invert_find_symbol in T1. rewrite <- FIND in *. apply Genv.find_invert_symbol in T1. clarify.
Qed.


Section MATCHPROG.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker (AST.fundef F1)} {LV: Linker V1}.
  Variable match_fundef: C -> AST.fundef F1 -> AST.fundef F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Variables (ctx: C) (p_src: AST.program (AST.fundef F1) V1) (p_tgt: AST.program (AST.fundef F2) V2).
  Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt).

  Lemma match_program_gen_defs:
      <<EQ: (defs p_src) = (defs p_tgt)>>.
  Proof.
    apply Axioms.functional_extensionality. ii; ss. u. inv MATCHPROG. des.
    (* hexploit (match_program_defmap _ _ ctx p_src p_tgt MATCH x). intro REL. *)
    replace (prog_defs_names p_src) with (prog_defs_names p_tgt); ss.
    unfold prog_defs_names. clear - H. ginduction H; ii; ss. inv H; ss. f_equal; ss.
  Qed.

End MATCHPROG.

Lemma Global_match_genvs_refl
      F V (ge0: Genv.t F V):
    Genv.match_genvs eq ge0 ge0.
Proof.
  econs; eauto. ii. destruct ((Genv.genv_defs ge0) ! b) eqn:T; econs; eauto.
Qed.

Lemma genv_eq
      F V (ge1 ge2: Genv.t F V)
      (PUB: ge1.(Genv.genv_public) = ge2.(Genv.genv_public))
      (NEXT: ge1.(Genv.genv_next) = ge2.(Genv.genv_next))
      (SYMB: ge1.(Genv.genv_symb) = ge2.(Genv.genv_symb))
      (DEFS: ge1.(Genv.genv_defs) = ge2.(Genv.genv_defs)):
    ge1 = ge2 .
Proof. destruct ge1, ge2; ss. clarify. f_equal; apply proof_irr. Qed.

Arguments fsim_external_inject_eq [_].

Lemma senv_eta
      se tse
      (EQ0: se.(Senv.find_symbol) = tse.(Senv.find_symbol))
      (EQ1: se.(Senv.public_symbol) = tse.(Senv.public_symbol))
      (EQ2: se.(Senv.invert_symbol) = tse.(Senv.invert_symbol))
      (EQ3: se.(Senv.block_is_volatile) = tse.(Senv.block_is_volatile))
      (EQ4: se.(Senv.nextblock) = tse.(Senv.nextblock)):
    se = tse.
Proof. destruct se, tse; ss. clarify. f_equal; apply Axioms.proof_irr. Qed.

Program Instance Senv_eq_equiv: RelationClasses.Equivalence Senv.equiv.
Next Obligation. ii. econs; eauto. Qed.
Next Obligation. ii. inv H. des. econs; eauto. Qed.
Next Obligation.
  ii. inv H. inv H0. des. econs; eauto. i. erewrite <- H1; eauto.
Qed.
