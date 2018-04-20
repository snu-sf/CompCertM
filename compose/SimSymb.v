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
Require SimMem.


Set Implicit Arguments.

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

Class SimSymb (SM: SimMem.SimMem) :=
{
  t: Type;
  sim_symb: t -> ident -> ident -> Prop;
  wf: t -> Prop;
  closed (ss: t) (sk_src: Sk.t) (sk_tgt: Sk.t): Prop;
  linker :> Linker t;
  (* link (ss0 ss1 ss_link: t): Prop; *)
  link_spec: forall
      ss0 sk_src0 sk_tgt0
      ss1 sk_src1 sk_tgt1
      (WF0: wf ss0)
      (WF1: wf ss1)
      (CLOSED0: closed ss0 sk_src0 sk_tgt0)
      (CLOSED1: closed ss1 sk_src1 sk_tgt1)
      sk_link_src sk_link_tgt
      (LINKSRC: link sk_src0 sk_tgt0 = Some sk_link_src)
      (LINKTGT: link sk_tgt0 sk_tgt0 = Some sk_link_tgt)
    ,
      exists ss_link, (<<WF: wf ss_link>>) /\
                      (<<CLOSED: closed ss_link sk_link_src sk_link_tgt>>) /\
                      (<<LINK: link ss0 ss1 = Some ss_link>>) /\
                      (<<EXACT0: link_exact_preserved ss0.(sim_symb) sk_src0 sk_tgt0 ss_link.(sim_symb)>>) /\
                      (<<EXACT1: link_exact_preserved ss1.(sim_symb) sk_src1 sk_tgt1 ss_link.(sim_symb)>>)
  ;
  load_exact_preserved: forall
      ss sk_src sk_tgt
      (WF: wf ss)
      (CLOSED: closed ss sk_src sk_tgt)
      skenv_src skenv_tgt m_src m_tgt
      (LOADSRC: skenv_src = sk_src.(Sk.load_skenv) /\ sk_src.(Sk.load_mem) = Some m_src)
      (LOADTGT: skenv_tgt = sk_tgt.(Sk.load_skenv) /\ sk_tgt.(Sk.load_mem) = Some m_tgt)
    ,
      exists sm,
        (<<SRCM: sm.(SimMem.src_mem) = m_src>>) /\
        (<<TGTM: sm.(SimMem.tgt_mem) = m_tgt>>) /\
        (<<EXACT: forall
            id_src id_tgt b_src b_tgt
            (SRCFIND: skenv_src.(Genv.find_symbol) id_src = Some b_src)
            (TGTFIND: skenv_tgt.(Genv.find_symbol) id_tgt = Some b_tgt)
          ,
            sm.(SimMem.sim_val) (Vptr b_src Ptrofs.zero true) (Vptr b_tgt Ptrofs.zero true) <->
            ss.(sim_symb) id_src id_tgt>>)
  ;
}
.

Module TMP.
  Context `{SM: SimMem.SimMem}.
  Context `{SS: @SimSymb SM}. (* ############## TODO 1) I declared it explicit but it requires @ 2) When I declare it implicit, it still requires @ *)
  Axiom ss0: t.
  Axiom i: ident.
  Fail Check (ss0 i).
  Coercion sim_symb: t >-> Funclass.
  Check (ss0 i).
End TMP.

