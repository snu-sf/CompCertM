Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import GlobalenvsC.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import LinkingC.
Require Import MapsC.


Require Import SimSymb.
Require Import System.


Set Implicit Arguments.


Definition sim_skenv (skenv0 skenv1: SkEnv.t): Prop := skenv0 = skenv1.

Lemma sim_skenv_equiv
      skenv_src skenv_tgt
      (SIMSKENV: sim_skenv skenv_src skenv_tgt):
    <<EQUIV: Senv.equiv skenv_src skenv_tgt>>.
Proof. rewrite SIMSKENV. eapply GlobalenvsC.Senv_eq_equiv_obligation_1. Qed.

Lemma system_sim_skenv
      skenv_src skenv_tgt
      (SIMSKENV: sim_skenv skenv_src skenv_tgt):
    <<SIMSKENV: sim_skenv (System.skenv (skenv_src)) (System.skenv (skenv_tgt))>>.
Proof. inv SIMSKENV. econs; eauto. Qed.

Record t' := mk {
  src: Sk.t;
  tgt: Sk.t;
}.

Definition wf (ss: t'): Prop := ss.(src) = ss.(tgt).

Definition le: t' -> t' -> Prop := top2.

Global Program Instance le_PreOrder: PreOrder le.

Lemma wf_link: forall ss0 ss1 sk_src
          (SIMSK: wf ss0)
          (SIMSK: wf ss1)
          (LINKSRC: link ss0.(src) ss1.(src) = Some sk_src),
          exists ss sk_tgt,
            <<LINKTGT: link ss0.(tgt) ss1.(tgt) = Some sk_tgt>> /\
            <<SKSRC: ss.(src) = sk_src>> /\
            <<SKTGT: ss.(tgt) = sk_tgt>> /\
            <<LE0: le ss0 ss>> /\
            <<LE1: le ss1 ss>> /\
            <<SIMSK: wf ss>>.
Proof.
  i. inv SIMSK. inv SIMSK0. eexists (mk _ _). esplits; ss; eauto.
Unshelve.
  all: ss.
Qed.

Lemma wf_load_sim_skenv: forall ss skenv_src skenv_tgt m_src
          (SIMSK: wf ss)
          (LOADSRC: (Sk.load_skenv ss.(src)) = skenv_src)
          (LOADTGT: (Sk.load_skenv ss.(tgt)) = skenv_tgt)
          (LOADMEMSRC: (Sk.load_mem ss.(src)) = Some m_src),
            (<<LOADMEMTGT: (Sk.load_mem ss.(tgt)) = Some m_src>>) /\
            (<<SIMSKENV: sim_skenv skenv_src skenv_tgt>>) /\
            (<<MAINSIM: (Genv.symbol_address skenv_src (prog_main ss.(src)) Ptrofs.zero)
                        = (Genv.symbol_address skenv_tgt (prog_main ss.(tgt)) Ptrofs.zero)>>).
Proof. i. u in *. inv SIMSK. esplits; eauto with congruence. Qed.

Lemma sim_skenv_monotone: forall ss_link skenv_link_src skenv_link_tgt ss skenv_src skenv_tgt
          (WFSRC: SkEnv.wf skenv_link_src)
          (WFTGT: SkEnv.wf skenv_link_tgt)
          (SIMSKENV: sim_skenv skenv_link_src skenv_link_tgt)
          (SIMSK: wf ss)
          (LE: le ss ss_link)
          (LESRC: SkEnv.project skenv_link_src ss.(src) = skenv_src)
          (LETGT: SkEnv.project skenv_link_tgt ss.(tgt) = skenv_tgt),
          <<SIMSKENV: sim_skenv skenv_src skenv_tgt>>.
Proof. i. clarify. rr. inv SIMSK. inv SIMSKENV. ss. Qed.

Lemma sim_skenv_func_bisim: forall skenv_src skenv_tgt
          (SIMSKENV: sim_skenv skenv_src skenv_tgt),
          <<DEF: SimSymb.skenv_func_bisim eq skenv_src skenv_tgt>>.
Proof.
  i. inv SIMSKENV. econs; eauto; ii; assert(fptr_src = fptr_tgt) by ss;
                     clarify; unfold Genv.find_funct, Genv.find_funct_ptr in *; des_ifs_safe; esplits; eauto.
Qed.


Local Opaque prog_defmap.

Section REVIVE.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
  Context `{HasExternal F1} `{HasExternal F2}.
  Variable match_fundef: C -> F1 -> F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Variables (ctx: C) (p_src: AST.program F1 V1) (p_tgt: AST.program F2 V2).
  Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt).
  Hypothesis MATCH_FUNDEF_EXTERNAL: forall ctx f_src f_tgt
      (MATCH: match_fundef ctx f_src f_tgt),
      is_external f_src = is_external f_tgt.

  Lemma sim_skenv_revive
        skenv_proj_src skenv_proj_tgt ge_src ge_tgt
        (REVIVESRC: ge_src = SkEnv.revive skenv_proj_src p_src)
        (REVIVETGT: ge_tgt = SkEnv.revive skenv_proj_tgt p_tgt)
        (SIMSKENV: sim_skenv skenv_proj_src skenv_proj_tgt):
      <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>>.
  Proof.
    clarify. inv SIMSKENV. econs; eauto. ii. ss.
    rewrite ! MapsC.PTree_filter_map_spec. rewrite ! o_bind_ignore.
    unfold Genv.find_def in *. des_ifs; try (by econs).
    destruct (Genv.invert_symbol skenv_proj_tgt b) eqn:T; cbn; try (by econs; eauto).
    apply match_program_defmap with (id := i) in MATCHPROG.
    inv MATCHPROG; cbn; try (by econs; eauto).
    (* inv H3; ss; cycle 1. *)
    (* { econs; eauto. econs; eauto. } *)
    (* erewrite MATCH_FUNDEF_EXTERNAL; eauto. *)
    (* des_ifs; try (by econs; eauto). *)
    (* econs; eauto. econs; eauto. *)
  Qed.

End REVIVE.

Require Import SimMod.
Notation mk_mp := (fun md_src md_tgt => ModPair.mk md_src md_tgt (mk md_src md_tgt)).
