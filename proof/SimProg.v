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



  Lemma link_list_cons
        X `{Linker X}
        hd tl restl res
        (TL: link_list tl = Some restl)
        (HD: link hd restl = Some res)
    :
      <<LINK: link_list (hd :: tl) = Some res>>
  .
  Proof.
    admit "This should hold".
  Qed.

  Lemma link_list_cons_inv
        X `{Linker X}
        hd tl res
        (LINK: link_list (hd :: tl) = Some res)
    :
      exists restl, <<TL: link_list tl = Some restl>> /\ <<HD: link hd restl = Some res>>
  .
  Proof.
    admit "This should hold".
  Qed.

  Theorem sim_load_sk
          sk_src
          (LOADSRC: p_src.(init_sk) = Some sk_src)
    :
      exists sk_tgt, <<LOADTGT: p_tgt.(init_sk) = Some sk_tgt>>
  .
  Proof.
    unfold init_sk in *.
    subst p_src p_tgt.
    ginduction pp; ii; ss.
    eapply link_list_cons_inv in LOADSRC. des.
    exploit IHt; eauto.
    { inv WF. ss. }
    { inv SIMPROG. inv SIMMPS. ss. }
    i; des.
    esplits; eauto.
    eapply link_list_cons; eauto.
    admit "TODO: Strengthen conclusion so that IH becomes stronger too. Somehow sk_src ~ sk_tgt".
  Unshelve.
    all: ss.
  Qed.

  Theorem sim_load
        sem_src
        (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold sem in *.
    des_ifs_safe.
    exploit sim_load_sk; eauto. i; des.
    esplits; eauto. des_ifs.
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















  Inductive sim_gepair (gep: GePair.t): Prop :=
  | sim_gepair_intro
      (SKENV: SimSymb.sim_skenv gep.(GePair.ss) gep.(GePair.skenv_src) gep.(GePair.skenv_tgt))
      (MSS: List.Forall sim_modsempair gep.(GePair.msps))
  .

  Let skenv_src := sk_src.(Sk.load_skenv).
  Let skenv_tgt := sk_tgt.(Sk.load_skenv).
  Variable m_src m_tgt: mem.
  Hypothesis LOADMEMSRC: sk_src.(Sk.load_mem) = Some m_src.
  Hypothesis LOADMEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt.
  Let mss_src := p_src.(load_modsem) skenv_src.
  Let mss_tgt := p_tgt.(load_modsem) skenv_tgt.
  Let ge_src := (p_src.(load_genv) skenv_src).
  (* TODO: I want to use "sem_src.(globalenv)" here, without unfolding it. *)
  Let ge_tgt := (p_tgt.(load_genv) skenv_tgt).

  Theorem sim_progpair_sim_ge
    :
      exists ss msps,
        <<SIM: sim_gepair (GePair.mk skenv_src skenv_tgt ss msps)>>
        /\ <<SRC: List.map ModSemPair.src msps = mss_src>>
        /\ <<TGT: List.map ModSemPair.tgt msps = mss_tgt>>
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

  Theorem sim_modsem

End SIM.



