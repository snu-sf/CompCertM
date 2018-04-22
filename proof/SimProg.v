Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import SimSymb.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod Pair ModSem SimMem SimModSem SimMod.

Set Implicit Arguments.






Section SIM.

  Context `{SS: SimSymb.class} `{SM: SimMem.class}.

  Inductive sim_progpair (pp: ProgPair.t): Prop :=
  | intro_sim_modpairs
      (SIMMPS: List.Forall sim_modpair pp)
  .



  Variable pp: ProgPair.t.
  Hypothesis WF: ProgPair.wf pp.
  Hypothesis SIMPROG: sim_progpair pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).



  Theorem sim_load
        sem_src
        (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold sem in *.
    des_ifs.
    { esplits; eauto. }
    exfalso.
    unfold init_sk in *.
    admit "".
  Qed.

  Variable ss_link: SimSymb.t.
  Variable sem_src sem_tgt: semantics.
  Variable sk_src sk_tgt: Sk.t.
  Hypothesis CLOSED: closed ss_link sk_src sk_tgt.
  Hypothesis LINKSRC: p_src.(init_sk) = Some sk_src.
  Hypothesis LINKTGT: p_tgt.(init_sk) = Some sk_tgt.
  Hypothesis LOADSRC: sem p_src = Some sem_src.
  Hypothesis LOADTGT: sem p_tgt = Some sem_tgt.
  Hypothesis SSLINK: pp.(ProgPair.ss_link) = Some ss_link.

  Inductive sim_ge (ge_src ge_tgt: Ge.t): Prop :=
  | sim_ge_intro
      (SKENV: SimSymb.sim_skenv ss_link ge_src.(Ge.skenv) ge_tgt.(Ge.skenv))
      (MSS: List.Forall2 sim_modsem ge_src.(Ge.mss) ge_tgt.(Ge.mss))
  .

  Let skenv_src := sk_src.(Sk.load_skenv).
  Let skenv_tgt := sk_tgt.(Sk.load_skenv).
  Variable m_src m_tgt: mem.
  Hypothesis LOADMEMSRC: sk_src.(Sk.load_mem) = Some m_src.
  Hypothesis LOADMEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt.
  Let ge_src := (p_src.(load_genv) skenv_src).
  (* TODO: I want to use "sem_src.(globalenv)" here, without unfolding it. *)
  Let ge_tgt := (p_tgt.(load_genv) skenv_tgt).

  Theorem sim_progpair_sim_ge
    :
      sim_ge ge_src ge_tgt
  .
  Proof.
    assert(SIMSKENV: SimSymb.sim_skenv ss_link ge_src.(Ge.skenv) ge_tgt.(Ge.skenv)).
    { exploit SimMem.load_respects_ss; eauto. i; des. ss. }
    econs; eauto.
    inv SIMPROG.
    cbn.
    clear - SIMMPS SIMSKENV SSLINK.
    unfold ProgPair.ss_link in *.
    assert(LINKORDER: forall
              ss
              (IN: List.In ss (map ModPair.ss pp))
            ,
              <<LO: linkorder ss ss_link>>).
    { i. admit "link_list_linkorder". }
    subst skenv_src skenv_tgt ge_src ge_tgt p_src p_tgt.
    ginduction pp; ii; ss.
    unfold flip. inv SIMMPS.
    econs; eauto.
    - eapply H1; eauto.
      eapply SimSymb.sim_skenv_monotone_ss; eauto.
      admit "link_list_linkorder".
    - eapply IHt; eauto.
      admit "link_list_linkorder".
  Qed.

End SIM.



