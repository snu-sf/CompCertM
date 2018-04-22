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


Set Implicit Arguments.


Module SimSymb.

  (* I wanted to use "t" as ss0/ss_linked, but forward reference is impossible. *)
  Inductive link_exact_preserved (ss0: ident -> ident -> Prop) (sk_src: Sk.t) (sk_tgt: Sk.t) (ss_linked: ident -> ident -> Prop): Prop :=
  | link_exact_preserved_intro
      (EXACT: forall
          id_src id_tgt
          (SRCIN: sk_src.(privs) id_src)
          (TGTIN: sk_tgt.(privs) id_tgt)
        ,
          <<EXACT: ss0 id_src id_tgt <-> ss_linked id_src id_tgt>>)
  .

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

  Inductive wf' (sim_symb: ident -> ident -> Prop) (privs: ident -> Prop) :=
  | wf_intro
      (CLOSED: forall
          id_src id_tgt
          (SIM: sim_symb id_src id_tgt)
        ,
          <<SRC: privs id_src>> /\ <<TGT: privs id_tgt>>)
      (INJ: injective_rel sim_symb)
  .

  (* TODO: Try moving t into argument? sim_symb coercion gets broken and I don't know how to fix it. *)
  Class class :=
    {
      t: Type;
      coverage: t -> ident -> Prop;
      kept: t -> ident -> Prop;
      wf := fun ss => ss.(kept) <1= ss.(coverage);
      (* wf: t -> Prop := fun ss => wf' ss.(sim_symb) ss.(privs); *)
      (* closed (ss: t) (sk_src: Sk.t) (sk_tgt: Sk.t): Prop; *)
      linker :> Linker t;
      (* link (ss0 ss1 ss_link: t): Prop; *)
      (* link_spec: forall *)
      (*     ss0 sk_src0 sk_tgt0 *)
      (*     ss1 sk_src1 sk_tgt1 *)
      (*     (WF0: wf ss0) *)
      (*     (WF1: wf ss1) *)
      (*     sk_link_src sk_link_tgt *)
      (*     (LINKSRC: link sk_src0 sk_tgt0 = Some sk_link_src) *)
      (*     (LINKTGT: link sk_tgt0 sk_tgt0 = Some sk_link_tgt) *)
      (*   , *)
      (*     exists ss_link, (<<WF: wf ss_link>>) /\ *)
      (*                     (<<LINK: link ss0 ss1 = Some ss_link>>) /\ *)
      (*                     (<<EXACT0: link_exact_preserved ss0.(sim_symb) sk_src0 sk_tgt0 ss_link.(sim_symb)>>) /\ *)
      (*                     (<<EXACT1: link_exact_preserved ss1.(sim_symb) sk_src1 sk_tgt1 ss_link.(sim_symb)>>) *)
      (* ; *)
      sim_skenv: t -> SkEnv.t -> SkEnv.t -> Prop;
      sim_skenv_monotone_ss: forall
          ss_link skenv_src skenv_tgt
          (SIMSKENV: sim_skenv ss_link skenv_src skenv_tgt)
          ss
          (LE: linkorder ss ss_link)
        ,
          <<SIMSKENV: sim_skenv ss skenv_src skenv_tgt>>
      ;
      (* TODO: Can we separate sim_skenv_monotone_skenv, like sim_skenv_monotone_ss? *)
      sim_skenv_monotone: forall
          ss_link skenv_src skenv_tgt
          (SIMSKENV: sim_skenv ss_link skenv_src skenv_tgt)
          (* F_src V_src F_tgt V_tgt *)
          (* (flesh_src: list (ident * globdef (AST.fundef F_src) V_src)) *)
          (* (flesh_tgt: list (ident * globdef (AST.fundef F_tgt) V_tgt)) *)
          skenv_proj_src skenv_proj_tgt
          pubs
          (LESRC: skenv_src.(SkEnv.project) (ss_link.(coverage) \1/ pubs) skenv_proj_src)
          (LETGT: skenv_tgt.(SkEnv.project) (ss_link.(coverage) \1/ pubs) skenv_proj_tgt)
          ss
          (LE: linkorder ss ss_link)
        ,
          <<SIMSKENV: sim_skenv ss skenv_proj_src skenv_proj_tgt>>
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


