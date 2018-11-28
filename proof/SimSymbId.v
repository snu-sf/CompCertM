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
      (SIMSKENV: sim_skenv skenv_src skenv_tgt)
  :
    <<EQUIV: Senv.equiv skenv_src skenv_tgt>>
.
Proof.
  About Genv.senv_match_genv.
  About Unnamed_thm.
  admit "this should hold".
Qed.

Lemma system_sim_skenv
      skenv_src skenv_tgt
      (SIMSKENV: sim_skenv skenv_src skenv_tgt)
  :
    <<SIMSKENV: sim_skenv (skenv_src).(System.skenv) (skenv_tgt).(System.skenv)>>
.
Proof.
  inv SIMSKENV.
  econs; eauto.
Qed.

Definition sim_sk (u: unit) (sk_src sk_tgt: Sk.t): Prop := sk_src = sk_tgt.

Definition le: unit -> Sk.t -> Sk.t -> unit -> Prop := top4.

Lemma sim_sk_link: forall
          ss0 (sk_src0 sk_tgt0: Sk.t)
          (SIMSK: sim_sk ss0 sk_src0 sk_tgt0)
          ss1 sk_src1 sk_tgt1
          (SIMSK: sim_sk ss1 sk_src1 sk_tgt1)
          sk_src
          (LINKSRC: link sk_src0 sk_src1 = Some sk_src)
        ,
          exists ss sk_tgt,
            <<LINKTGT: link sk_tgt0 sk_tgt1 = Some sk_tgt>> /\
            <<LE0: le ss0 sk_src0 sk_tgt0 ss>> /\
            <<LE1: le ss1 sk_src1 sk_tgt1 ss>> /\
            <<SIMSK: sim_sk ss sk_src sk_tgt>>
.
Proof.
  i.
  inv SIMSK. inv SIMSK0.
  SearchAbout TransfLink.
  esplits; ss; eauto.
Unshelve.
  all: ss.
Qed.

Lemma sim_sk_load_sim_skenv: forall
          ss sk_src sk_tgt
          (SIMSK: sim_sk ss sk_src sk_tgt)
          skenv_src skenv_tgt
          (LOADSRC: sk_src.(Sk.load_skenv) = skenv_src)
          (LOADTGT: sk_tgt.(Sk.load_skenv) = skenv_tgt)
          m_src
          (LOADMEMSRC: sk_src.(Sk.load_mem) = Some m_src)
        ,
            (<<LOADMEMTGT: sk_tgt.(Sk.load_mem) = Some m_src>>) /\
            (<<SIMSKENV: sim_skenv skenv_src skenv_tgt>>)
.
Proof.
  i. u in *. inv SIMSK.
  Print Genv.init_mem_transf.
  Print Genv.init_mem_transf_partial.
  About Genv.init_mem_match.
  esplits; eauto. rr. ss.
Qed.

Lemma sim_skenv_monotone: forall
          ss_link skenv_link_src skenv_link_tgt
          (WFSRC: SkEnv.wf skenv_link_src)
          (WFTGT: SkEnv.wf skenv_link_tgt)
          (SIMSKENV: sim_skenv skenv_link_src skenv_link_tgt)
          ss sk_src sk_tgt
          (SIMSK: sim_sk ss sk_src sk_tgt)
          (LE: le ss sk_src sk_tgt ss_link)
          skenv_src skenv_tgt
          (LESRC: SkEnv.project skenv_link_src sk_src.(defs) = skenv_src)
          (LETGT: SkEnv.project skenv_link_tgt sk_tgt.(defs) = skenv_tgt)
        ,
          <<SIMSKENV: sim_skenv skenv_src skenv_tgt>>
.
Proof.
  i. clarify. rr. inv SIMSK. inv SIMSKENV. ss.
Qed.

Lemma sim_skenv_func_bisim: forall
          skenv_src skenv_tgt
          (SIMSKENV: sim_skenv skenv_src skenv_tgt)
        ,
          <<DEF: SimSymb.skenv_func_bisim eq skenv_src skenv_tgt>>
.
Proof.
  i.
  inv SIMSKENV.
  econs; eauto.
  - ii. ss.
    assert(fptr_src = fptr_tgt).
    { ss. }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    esplits; eauto.
  - ii.
    assert(fptr_src = fptr_tgt).
    { ss. }
    clarify. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
    esplits; eauto.
Qed.


Local Opaque prog_defmap.

Section REVIVE.

  Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
  Context `{HasExternal F1} `{HasExternal F2}.
  Variable match_fundef: C -> F1 -> F2 -> Prop.
  Variable match_varinfo: V1 -> V2 -> Prop.
  Variables (ctx: C) (p_src: AST.program F1 V1) (p_tgt: AST.program F2 V2).
  Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt).
  Hypothesis MATCH_FUNDEF_EXTERNAL: forall
      ctx f_src f_tgt
      (MATCH: match_fundef ctx f_src f_tgt)
    ,
      is_external f_src = is_external f_tgt
  .

  Lemma sim_skenv_revive
        skenv_proj_src skenv_proj_tgt
        ge_src ge_tgt
        (REVIVESRC: ge_src = SkEnv.revive skenv_proj_src p_src)
        (REVIVETGT: ge_tgt = SkEnv.revive skenv_proj_tgt p_tgt)
        (SIMSKENV: sim_skenv skenv_proj_src skenv_proj_tgt)
    :
      <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>>
  .
  Proof.
    clarify.
    inv SIMSKENV.
    econs; eauto.

    ii. ss.
    rewrite ! MapsC.PTree_filter_map_spec. rewrite ! o_bind_ignore.
    unfold Genv.find_def in *. des_ifs; try (by econs).
    destruct (Genv.invert_symbol skenv_proj_tgt b) eqn:T; cbn; try (by econs; eauto).
    apply match_program_defmap with (id := i) in MATCHPROG.
    inv MATCHPROG; cbn; try (by econs; eauto).
    inv H3; ss; cycle 1.
    { econs; eauto. econs; eauto. }
    erewrite MATCH_FUNDEF_EXTERNAL; eauto.
    des_ifs; try (by econs; eauto).
    econs; eauto. econs; eauto.
  Qed.

End REVIVE.



(* Require Import CtypesC. *)

(* Section REVIVEC. *)

(*   Context {C F1 F2 V2: Type} {LC: Linker C} {LF: Linker (AST.fundef F1)}. *)
(*   Variable match_fundef: C -> Ctypes.fundef F1 -> AST.fundef F2 -> Prop. *)
(*   Variable match_varinfo: type -> V2 -> Prop. *)
(*   Variables (ctx: C) (p_src: Ctypes.program F1) (p_tgt: AST.program (AST.fundef F2) V2). *)
(*   Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt). *)
(*   Hypothesis MATCH_FUNDEF_EXTERNAL: forall *)
(*       ctx f_src f_tgt *)
(*       (MATCH: match_fundef ctx f_src f_tgt) *)
(*     , *)
(*       is_external_fd f_src = is_external_fd f_tgt *)
(*   . *)

(*   Lemma sim_skenv_revive_c *)
(*         skenv_proj_src skenv_proj_tgt *)
(*         ge_src ge_tgt *)
(*         (REVIVESRC: ge_src = CSkEnv.revive skenv_proj_src p_src) *)
(*         (REVIVETGT: ge_tgt = SkEnv.revive skenv_proj_tgt p_tgt) *)
(*         (SIMSKENV: sim_skenv skenv_proj_src skenv_proj_tgt) *)
(*     : *)
(*       <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>> *)
(*   . *)
(*   Proof. *)
(*     clarify. *)
(*     inv SIMSKENV. *)
(*     econs; eauto. *)

(*     ii. ss. *)
(*     rewrite ! MapsC.PTree_filter_map_spec. rewrite ! o_bind_ignore. *)
(*     unfold Genv.find_def in *. des_ifs; try (by econs). *)
(*     (* Set Printing Implicit. *) *)
(*     (* cbn. *) *)
(*     destruct (Genv.invert_symbol skenv_proj_tgt b) eqn:T; cbn; try (by econs; eauto). *)
(*     apply match_program_defmap with (id := i) in MATCHPROG. *)
(*     inv MATCHPROG; cbn; try (by econs; eauto). *)
(*     inv H1; ss; cycle 1. *)
(*     { econs; eauto. econs; eauto. } *)
(*     erewrite MATCH_FUNDEF_EXTERNAL; eauto. *)
(*     des_ifs; try (by econs; eauto). *)
(*     econs; eauto. econs; eauto. *)
(*   Qed. *)

(* End REVIVEC. *)



(* Section REVIVECC. *)

(*   Context {C F1 F2: Type} {LC: Linker C} {LF: Linker (AST.fundef F1)}. *)
(*   Variable match_fundef: C -> Ctypes.fundef F1 -> Ctypes.fundef F2 -> Prop. *)
(*   Variable match_varinfo: type -> type -> Prop. *)
(*   Variables (ctx: C) (p_src: Ctypes.program F1) (p_tgt: Ctypes.program F2). *)
(*   Hypothesis (MATCHPROG: match_program_gen match_fundef match_varinfo ctx p_src p_tgt). *)
(*   Hypothesis MATCH_FUNDEF_EXTERNAL: forall *)
(*       ctx f_src f_tgt *)
(*       (MATCH: match_fundef ctx f_src f_tgt) *)
(*     , *)
(*       is_external_fd f_src = is_external_fd f_tgt *)
(*   . *)

(*   Lemma sim_skenv_revive_cc *)
(*         skenv_proj_src skenv_proj_tgt *)
(*         ge_src ge_tgt *)
(*         (REVIVESRC: ge_src = CSkEnv.revive skenv_proj_src p_src) *)
(*         (REVIVETGT: ge_tgt = CSkEnv.revive skenv_proj_tgt p_tgt) *)
(*         (SIMSKENV: sim_skenv skenv_proj_src skenv_proj_tgt) *)
(*     : *)
(*       <<SIMGE: Genv.match_genvs (match_globdef match_fundef match_varinfo ctx) ge_src ge_tgt>> *)
(*   . *)
(*   Proof. *)
(*     clarify. *)
(*     inv SIMSKENV. *)
(*     econs; eauto. *)

(*     ii. ss. *)
(*     rewrite ! MapsC.PTree_filter_map_spec. rewrite ! o_bind_ignore. *)
(*     unfold Genv.find_def in *. des_ifs; try (by econs). *)
(*     (* Set Printing Implicit. *) *)
(*     (* cbn. *) *)
(*     destruct (Genv.invert_symbol skenv_proj_tgt b) eqn:T; cbn; try (by econs; eauto). *)
(*     apply match_program_defmap with (id := i) in MATCHPROG. *)
(*     inv MATCHPROG; cbn; try (by econs; eauto). *)
(*     inv H1; ss; cycle 1. *)
(*     { econs; eauto. econs; eauto. } *)
(*     erewrite MATCH_FUNDEF_EXTERNAL; eauto. *)
(*     des_ifs; try (by econs; eauto). *)
(*     econs; eauto. econs; eauto. *)
(*   Qed. *)

(* End REVIVECC. *)

