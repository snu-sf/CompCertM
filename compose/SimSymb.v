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
Require Import LinkingC.
Require Import Maps.

Require Import SimDef SimMem.

Set Implicit Arguments.


Module SimSymb.

  (* I wanted to use "t" as ss0/ss_linked, but forward reference is impossible. *)
  Inductive link_exact_preserved (ss0: ident -> ident -> Prop) (sk_src: Sk.t) (sk_tgt: Sk.t) (ss_linked: ident -> ident -> Prop): Prop :=
  | link_exact_preserved_intro
      (EXACT: forall
          id_src id_tgt
          (SRCIN: sk_src.(privs_old) id_src)
          (TGTIN: sk_tgt.(privs_old) id_tgt)
        ,
          <<EXACT: ss0 id_src id_tgt <-> ss_linked id_src id_tgt>>)
  .

  Definition injective_func X Y (inj: X -> option Y): Prop := forall
      x0 x1 y
      (INJ0: inj x0 = Some y)
      (INJ1: inj x1 = Some y)
    ,
      x0 = x1
  .

  (* TODO: better name *)
  Inductive injective_rel X Y (inj: X -> Y -> Prop): Prop :=
  | injective_domain
      (DOMAIN: forall
          x0 x1 y
          (INJ0: inj x0 y)
          (INJ1: inj x1 y)
        ,
          x0 = x1)
  | injective_image
      (IMAGE: forall
          x y0 y1
          (INJ0: inj x y0)
          (INJ1: inj x y1)
        ,
          y0 = y1)
  .

  Inductive wf' (sim_symb: ident -> ident -> Prop) (privs_old: ident -> Prop) :=
  | wf_intro
      (CLOSED: forall
          id_src id_tgt
          (SIM: sim_symb id_src id_tgt)
        ,
          <<SRC: privs_old id_src>> /\ <<TGT: privs_old id_tgt>>)
      (INJ: injective_rel sim_symb)
  .



  (* Properties that are needed in meta-theory. *)
Module DEPRECATED.
  Inductive sim_sk_weak (coverage kept: ident -> Prop) (sk_src sk_tgt: Sk.t): Prop :=
  | sim_sk_weak_intro
      (WF: (kept <1= coverage))
      (* We can pull "WF" out, it dosen't require sk_src/sk_tgt. But is it meaningful? *)
      (INSRC: (coverage <1= sk_src.(privs_old)))
      (INTGT: (coverage <1= sk_tgt.(privs_old)))
      (* Is both are needed? *)
      (NOCOVER: forall
          id
          (PUBS: ~ coverage id)
        ,
          <<SIM: sim_odef (sk_src.(prog_defmap) ! id) (sk_tgt.(prog_defmap) ! id)>>)
      (* Further, we can say equality instead of sim, for public defs. Is it needed? *)
      (KEPT: forall
          id
          (* (COVER: coverage id) *)
          (KEPT: kept id)
        ,
          <<SIM: sim_odef (sk_src.(prog_defmap) ! id) (sk_tgt.(prog_defmap) ! id)>>)
      (NOKEPT: forall
          id
          (COVER: coverage id)
          (NOKEPT: ~ kept id)
        ,
          <<NOKEPT: None = sk_tgt.(prog_defmap) ! id>>)
      (MAINKEPT: <<KEPT: kept sk_src.(prog_main)>> \/ <<NOCOVER: ~ coverage sk_src.(prog_main)>>)
      (* TODO: Remove PUB/MAIN from SimModPair *)
      (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
      (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
  .

  Lemma sim_sk_weak_def_bsim
        coverage kept sk_src sk_tgt
        (CLOSED: sim_sk_weak coverage kept sk_src sk_tgt)
        id def_tgt
        (DEFTGT: sk_tgt.(prog_defmap) ! id = Some def_tgt)
    :
      exists def_src, <<DEFSRC: sk_src.(prog_defmap) ! id = Some def_src>> /\ <<SIM: sim_def def_src def_tgt>>
  .
  Proof.
    inv CLOSED.
    destruct (classic (coverage id)).
    - destruct (classic (kept id)).
      + exploit KEPT; eauto. intro SIM.
        inv SIM.
        { eq_closure_tac. esplits; eauto. }
        exfalso. congruence.
      + exploit NOKEPT; eauto. i. congruence.
    - exploit NOCOVER; eauto. intro SIM.
      inv SIM.
      { eq_closure_tac. esplits; eauto. }
      exfalso. congruence.
  Qed.

  Lemma sim_sk_weak_enables_link
        (sk_src0 sk_tgt0: Sk.t)
        kept0 coverage0
        (CLOSED0: sim_sk_weak coverage0 kept0 sk_src0 sk_tgt0)
        sk_src1 sk_tgt1
        kept1 coverage1
        (CLOSED1: sim_sk_weak coverage1 kept1 sk_src1 sk_tgt1)
        sk_src
        (LINKSRC: link sk_src0 sk_src1 = Some sk_src)
    :
      exists sk_tgt, <<LINKTGT: link sk_tgt0 sk_tgt1 = Some sk_tgt>>
  .
  Proof.
    Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
    exploit (link_prog_inv sk_src0 sk_src1); eauto. intro LINKSPEC; des. inv LINKSPEC. des.
    exploit (link_prog_succeeds sk_tgt0 sk_tgt1); eauto.
    - inv CLOSED0. inv CLOSED1. ss.
      eq_closure_tac.
    - i.
      exploit sim_sk_weak_def_bsim; try apply H; eauto. i; des.
      exploit sim_sk_weak_def_bsim; try apply H0; eauto. i; des.
      exploit BOTHHIT; eauto. i; des.
      inv CLOSED0. inv CLOSED1. ss.
      esplits; eauto.
      + rewrite <- PUB; ss.
      + rewrite <- PUB0; ss.
      + exploit sim_def_preserves_link; eauto. i; des_safe. ii. clarify.
  Qed.

End DEPRECATED.

  Inductive sim_sk_weak (coverage: ident -> Prop) (sk_src sk_tgt: Sk.t): Prop :=
  | sim_sk_weak_intro
      (* (INSRC: (coverage <1= sk_src.(privs_old))) *)
      (COVERAGE: (coverage <1= sk_tgt.(privs_old)))
      (PRIVS_OLD: sk_tgt.(privs_old) <1= sk_src.(privs_old))
      (NOCOVER: forall
          id
          (PUBS: ~ coverage id)
        ,
          <<SIM: sim_odef (sk_src.(prog_defmap) ! id) (sk_tgt.(prog_defmap) ! id)>>)
      (COVER: forall
          id
          (COVER: coverage id)
          def_tgt
          (DEFTGT: sk_tgt.(prog_defmap) ! id = Some def_tgt)
        ,
          exists def_src, <<DEFSRC: sk_src.(prog_defmap) ! id = Some def_src>>)
      (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
      (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
  .

  Lemma sim_sk_weak_def_bsim
        coverage sk_src sk_tgt
        (CLOSED: sim_sk_weak coverage sk_src sk_tgt)
        id def_tgt
        (DEFTGT: sk_tgt.(prog_defmap) ! id = Some def_tgt)
    :
      exists def_src, <<DEFSRC: sk_src.(prog_defmap) ! id = Some def_src>>
                     /\ <<SIM: ~(coverage id) -> sim_def def_src def_tgt>>
  .
  Proof.
    inv CLOSED.
    destruct (classic (coverage id)).
    - exploit COVER; eauto. i; des.
      esplits; eauto. ii. ss.
    - exploit NOCOVER; eauto. intro SIM.
      inv SIM.
      { eq_closure_tac. esplits; eauto. }
      exfalso. congruence.
  Qed.

  Lemma sim_sk_weak_enables_link
        (sk_src0 sk_tgt0: Sk.t)
        coverage0
        (CLOSED0: sim_sk_weak coverage0 sk_src0 sk_tgt0)
        sk_src1 sk_tgt1
        coverage1
        (CLOSED1: sim_sk_weak coverage1 sk_src1 sk_tgt1)
        sk_src
        (LINKSRC: link sk_src0 sk_src1 = Some sk_src)
    :
      exists sk_tgt, <<LINKTGT: link sk_tgt0 sk_tgt1 = Some sk_tgt>>
  .
  Proof.
    Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
    exploit (link_prog_inv sk_src0 sk_src1); eauto. intro LINKSPEC; des. inv LINKSPEC. des.
    exploit (link_prog_succeeds sk_tgt0 sk_tgt1); eauto.
    - inv CLOSED0. inv CLOSED1. ss.
      eq_closure_tac.
    - i.
      exploit sim_sk_weak_def_bsim; try apply H; eauto. i; des.
      exploit sim_sk_weak_def_bsim; try apply H0; eauto. i; des.
      exploit BOTHHIT; eauto. i; des.
      inv CLOSED0. inv CLOSED1. ss.
      exploit SIM. { intro T. eapply COVERAGE in T. inv T; des. eapply H5. rewrite <- PUB; ss. } i; des.
      exploit SIM0. { intro T. eapply COVERAGE0 in T. inv T; des. eapply H6. rewrite <- PUB0; ss. } i; des.
      esplits; eauto.
      + rewrite <- PUB; ss.
      + rewrite <- PUB0; ss.
      + exploit sim_def_preserves_link; eauto. i; des_safe. ii. clarify.
  Qed.


  (* Inductive load_exact_preserved `{SS: SimSymb.SimSymb} `{SM: SimMem.SimMem} *)
  (*           (ss0: SimSymb.t) (sk_src sk_tgt: Sk.t) *)
  (*           (sm0: SimMem.t) (skenv_src skenv_tgt: SkEnv.t): Prop := *)
  (* | exact_preserved_intro *)
  (*     (COMPAT: forall *)
  (*         id_src id_tgt b_src b_tgt *)
  (*         (SRCB: skenv_src.(Genv.find_symbol) id_src = Some b_src) *)
  (*         (TGTB: skenv_tgt.(Genv.find_symbol) id_tgt = Some b_tgt) *)
  (*       , *)
  (*         sm0.(SimMem.sim_val) (Vptr b_src Ptrofs.zero true) (Vptr b_tgt Ptrofs.zero true) <-> *)
  (*         ss0.(SimSymb.sim_symb) id_src id_tgt) *)
  (* . *)

  (* Inductive sim_skenv *)
  (*           (kept: ident -> Prop) (sm: SimMem.t) *)
  (*           (skenv_src skenv_tgt: SkEnv.t): Prop := *)
  (* | sim_skenv_intro *)
  (*     (SIMSYMB1: forall *)
  (*         id blk_src blk_tgt delta *)
  (*         (SIMVAL: SimMem.sim_val sm (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)) *)
  (*         (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src) *)
  (*       , *)
  (*         <<DELTA: delta = 0>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) *)
  (*     (SIMSYMB2: forall *)
  (*         id *)
  (*         (KEPT: kept id) *)
  (*         blk_src *)
  (*         (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src) *)
  (*       , *)
  (*         exists blk_tgt, *)
  (*           <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\ *)
  (*           <<SIM: SimMem.sim_val sm (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>) *)
  (*     (SIMSYMB3: forall *)
  (*         id blk_tgt *)
  (*         (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt) *)
  (*       , *)
  (*         exists blk_src, *)
  (*           <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>> /\ *)
  (*           <<SIM: SimMem.sim_val sm (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>) *)
  (* . *)

  (* Inductive sim_skenv_spec (coverage kept: ident -> Prop) (skenv_src skenv_tgt: SkEnv.t): Prop := *)
  (* | sim_skenv_spec_intro *)
  (*     (SPEC: forall *)
  (*         id *)
  (*         (KEPT: kept id) *)
  (*       , *)
  (*         skenv_src.(Genv.find_symbol) id = skenv_src.(Genv.find_symbol) id) *)
  (* . *)

  Inductive sk_def_bsim (sk_src sk_tgt: Sk.t): Prop :=
  | sk_def_bsim_intro
      (DEFBSIM: forall
          id def_tgt
          (DEFTGT: sk_tgt.(prog_defmap) ! id = Some def_tgt)
        ,
          exists def_src, <<DEFSRC: sk_src.(prog_defmap) ! id = Some def_src>> /\
                                    <<SIM: sim_def def_src def_tgt>>)
  .


(* I think this is the minimal spec required for lock-step modsem finding *)
  Inductive skenv_func_bsim `{SimMem.class} (sm0: SimMem.t) (skenv_src skenv_tgt: SkEnv.t): Prop :=
  | skenv_def_bsim_intro
      (FUNCBSIM: forall
          fptr_src fptr_tgt def_tgt
          (SIMFPTR: sm0.(SimMem.sim_val) fptr_src fptr_tgt)
          (FUNCTGT: skenv_tgt.(Genv.find_funct) fptr_tgt = Some def_tgt)
          (SAFESRC: exists _def_src, skenv_src.(Genv.find_funct) fptr_src = Some _def_src)
        ,
          exists def_src, <<FUNCSRC: skenv_src.(Genv.find_funct) fptr_src = Some def_src>> /\
                          <<SIM: sim_fun def_src def_tgt>>)
      (FUNCPROGRESS: forall
          fptr_src fptr_tgt
          (SIMFPTR: sm0.(SimMem.sim_val) fptr_src fptr_tgt)
          (SAFESRC: exists _def_src, skenv_src.(Genv.find_funct) fptr_src = Some _def_src)
        ,
          exists def_tgt, <<PROGRESS: skenv_tgt.(Genv.find_funct) fptr_tgt = Some def_tgt>>)
  .

(* These statements are direct copy from Unusedglobproof.v - defs_inject, EXCEPT for ref_def *)
  Inductive skenv_func_fsim `{SimMem.class} (sm0: SimMem.t) (skenv_src skenv_tgt: SkEnv.t): Prop :=
  | skenv_def_fsim_intro
      (FUNCSIM: forall
          fptr_src fptr_tgt def_src
          (SIMFPTR: sm0.(SimMem.sim_val) fptr_src fptr_tgt)
          (FUNCSRC: skenv_src.(Genv.find_funct) fptr_src = Some def_src)
        ,
          exists def_tgt, <<FUNCSRC: skenv_tgt.(Genv.find_funct) fptr_tgt = Some def_tgt>> /\
                          <<SIM: sim_fun def_src def_tgt>>)
  .

  (* TODO: Try moving t into argument? sim_symb coercion gets broken and I don't know how to fix it. *)
  Class class (SM: SimMem.class) :=
    {
      t: Type;
      le: t -> Sk.t -> Sk.t -> t -> Prop;

      le_trans: forall
          ss0 sk_src0 sk_tgt0 ss1 sk_src1 sk_tgt1 ss2
          (LE0: le ss0 sk_src0 sk_tgt0 ss1)
          (LE1: le ss1 sk_src1 sk_tgt1 ss2)
          (LINKORD0: linkorder sk_src0 sk_src1)
          (LINKORD1: linkorder sk_tgt0 sk_tgt1)
        ,
          <<LE: le ss0 sk_src0 sk_tgt0 ss2>>
      ;

      sim_sk: t -> Sk.t -> Sk.t -> Prop;
      (* Do we need this ? *)
      (* sim_sk_def_bsim: forall *)
      (*     ss sk_src sk_tgt *)
      (*     (SIMSK: sim_sk ss sk_src sk_tgt) *)
      (*   , *)
      (*     <<DEF: sk_def_bsim sk_src sk_tgt>> *)
      (* ; *)
      sim_sk_link: forall
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
      ;

      sim_skenv: SimMem.t -> t -> SkEnv.t -> SkEnv.t -> Prop;

      sim_sk_load_sim_skenv: forall
          ss sk_src sk_tgt
          (SIMSK: sim_sk ss sk_src sk_tgt)
          skenv_src skenv_tgt
          (LOADSRC: sk_src.(Sk.load_skenv) = skenv_src)
          (LOADTGT: sk_tgt.(Sk.load_skenv) = skenv_tgt)
          m_src
          (LOADMEMSRC: sk_src.(Sk.load_mem) = Some m_src)
        ,
          exists m_tgt sm,
            (<<LOADMEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt>>) /\
            (<<SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt>>) /\
            (<<MEMSRC: sm.(SimMem.src_mem) = m_src>>) /\
            (<<MEMTGT: sm.(SimMem.tgt_mem) = m_tgt>>)
      ;

      mle_preserves_sim_skenv: forall
          sm0 sm1
          (MLE: SimMem.le sm0 sm1)
          ss skenv_src skenv_tgt
          (SIMSKENV: sim_skenv sm0 ss skenv_src skenv_tgt)
        ,
          <<SIMSKENV: sim_skenv sm1 ss skenv_src skenv_tgt>>
      ;

      mlift_preserves_sim_skenv: forall
          sm0
          ss skenv_src skenv_tgt
          (SIMSKENV: sim_skenv sm0 ss skenv_src skenv_tgt)
        ,
          <<SIMSKENV: sim_skenv (SimMem.lift sm0) ss skenv_src skenv_tgt>>
      ;


      (* sim_skenv_monotone_ss: forall *)
      (*     sm ss_link skenv_src skenv_tgt *)
      (*     (SIMSKENV: sim_skenv sm ss_link skenv_src skenv_tgt) *)
      (*     ss *)
      (*     (LE: linkorder ss ss_link) *)
      (*   , *)
      (*     <<SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt>> *)
      (* (* Note: this should be trivial. kept becomes smaller *) *)
      (* ; *)

      (* (* TODO: Can we separate sim_skenv_monotone_skenv, like sim_skenv_monotone_ss? *) *)
      (* sim_skenv_monotone_skenv: forall *)
      (*     sm ss skenv_link_src skenv_link_tgt *)
      (*     (SIMSKENV: sim_skenv sm ss skenv_link_src skenv_link_tgt) *)
      (*     (* F_src V_src F_tgt V_tgt *) *)
      (*     (* (flesh_src: list (ident * globdef (AST.fundef F_src) V_src)) *) *)
      (*     (* (flesh_tgt: list (ident * globdef (AST.fundef F_tgt) V_tgt)) *) *)
      (*     sk_src sk_tgt *)
      (*     (SIMSK: sim_sk ss sk_src sk_tgt) *)
      (*     skenv_src skenv_tgt *)
      (*     (LESRC: skenv_link_src.(SkEnv.project) sk_src.(defs) skenv_src) *)
      (*     (LETGT: skenv_link_tgt.(SkEnv.project) sk_tgt.(defs) skenv_tgt) *)
      (*   , *)
      (*     <<SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt>> *)
      (* ; *)
          
      (* TODO: Can we separate sim_skenv_monotone_skenv, like sim_skenv_monotone_ss? *)
      sim_skenv_monotone: forall
          sm ss_link skenv_link_src skenv_link_tgt
          (WFSRC: SkEnv.wf skenv_link_src)
          (WFTGT: SkEnv.wf skenv_link_tgt)
          (SIMSKENV: sim_skenv sm ss_link skenv_link_src skenv_link_tgt)
          (* F_src V_src F_tgt V_tgt *)
          (* (flesh_src: list (ident * globdef (AST.fundef F_src) V_src)) *)
          (* (flesh_tgt: list (ident * globdef (AST.fundef F_tgt) V_tgt)) *)
          ss sk_src sk_tgt
          (SIMSK: sim_sk ss sk_src sk_tgt)
          (LE: le ss sk_src sk_tgt ss_link)
          skenv_src skenv_tgt
          (LESRC: SkEnv.project_spec skenv_link_src sk_src.(defs) skenv_src)
          (LETGT: SkEnv.project_spec skenv_link_tgt sk_tgt.(defs) skenv_tgt)
        ,
          <<SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt>>
      ;

      (* sim_skenv_def_bsim: forall *)
      (*     sm ss skenv_src skenv_tgt *)
      (*     (SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt) *)
      (*   , *)
      (*     <<DEF: skenv_def_bsim sm skenv_src skenv_tgt>> *)
      (* ; *)

      sim_skenv_func_fsim: forall
          sm ss skenv_src skenv_tgt
          (SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt)
        ,
          <<DEF: skenv_func_fsim sm skenv_src skenv_tgt>>
      ;
      (* TODO: Remove below later. *)
      sim_skenv_func_bsim: forall
          sm ss skenv_src skenv_tgt
          (SIMSKENV: sim_skenv sm ss skenv_src skenv_tgt)
        ,
          <<DEF: skenv_func_bsim sm skenv_src skenv_tgt>>
      ;
    }
  .

  (* Module TMP. *)
  (*   Section TMP. *)
  (*   Context `{SS: class}. *)
  (*   Axiom ss0: t. *)
  (*   Axiom i: ident. *)
  (*   Fail Check (ss0 i). *)
  (*   Coercion sim_symb: t >-> Funclass. *)
  (*   Check (ss0 i). *)
  (*   End TMP. *)
  (* End TMP. *)


End SimSymb.

(* Coercion SimSymb.sim_symb: SimSymb.t >-> Funclass. *)

(* Module TMP. *)
(*   Variable T: Type. *)
(*   Context `{SS: SimSymb.class T}. *)
(*   Axiom ss0: T. *)
(*   Axiom i: ident. *)
(*   Check (SimSymb.sim_symb ss0 i). *)
(*   Fail Check (ss0 i). *)
(*   Coercion SimSymb.sim_symb: SimSymb.class >-> Funclass. *)
(*   Fail Check (ss0 i). *)
(* End TMP. *)


(* Print Coercions. *)

(* Variables X: Type. *)
(* Context `{SimSymb X}. *)
(* Variable x: X. *)
(* Variable i0: ident. *)
(* Fail Check (x i0). *)
(* Check (sim_symb x i0). *)
(* (* Coercion sim_symb: SimSymb >-> Funclass. *) *)
(* (* Fail Check (x i0). *) *)
(* Coercion sim_symb: X >-> Funclass. *)
(* Print Coercions. *)
(* Coercion sim_symb: forall (X: Type) `{SimSymb X}, X >-> Funclass. *)


(* TODO: name? *)
(* Inductive closed `{SimSymb.class} (ss: SimSymb.t) (sk_src sk_tgt: Sk.t): Prop := *)
(* | closed_intro *)
(*     (WF: SimSymb.wf ss) *)
(*     (INSRC: all1 (ss.(SimSymb.coverage) <1= sk_src.(privs_old))) *)
(*     (INTGT: all1 (ss.(SimSymb.coverage) <1= sk_tgt.(privs_old))) *)
(*     (NOCOVER: forall *)
(*         id *)
(*         (PUBS: ~ ss.(SimSymb.coverage) id) *)
(*       , *)
(*         <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>) *)
(*     (KEPT: forall *)
(*         id *)
(*         (COVER: ss.(SimSymb.coverage) id) *)
(*         (KEPT: ss.(SimSymb.kept) id) *)
(*       , *)
(*         <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>) *)
(*     (NOKEPT: forall *)
(*         id *)
(*         (COVER: ss.(SimSymb.coverage) id) *)
(*         (NOKEPT: ~ ss.(SimSymb.kept) id) *)
(*       , *)
(*         <<NOKEPT: None = sk_tgt.(prog_defmap) ! id>>) *)
(* . *)

