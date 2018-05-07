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
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Program.
Require Import Syntax Sem Mod ModSem.
Require Import SimSymb SimMem SimModSem SimMod SimProg Ord.

Set Implicit Arguments.




Module LoadPair.
Section LOADPAIR.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.

  Record t: Type := mk {
    sm: SimMem.t;
    msps: list ModSemPair.t;
    idx: Type;
    ord: idx -> idx -> Prop;
  }
  .

  Definition ge_src (lp: t): Ge.t := (List.map (ModSemPair.src) lp.(msps)).
  Definition ge_tgt (lp: t): Ge.t := (List.map (ModSemPair.tgt) lp.(msps)).

  Inductive sim (lp: t): Prop :=
  | intro_sim
      (SIMSKENV: List.Forall (fun msp => ModSemPair.sim_skenv msp lp.(sm)) lp.(msps))
      (WF: well_founded lp.(ord))
      (SIMMSS: List.Forall (ModSemPair.sim) lp.(msps))
      (IDX: List.Forall (fun msp => msp.(ModSemPair.idx) = lp.(idx)) lp.(msps))
      (ORD: List.Forall (fun msp => msp.(ModSemPair.ord) ~= lp.(ord)) lp.(msps))
      (DISJSRC: lp.(ge_src).(Ge.disjoint))
      (DISJTGT: lp.(ge_src).(Ge.disjoint))
  .

  (* Definition src (lp: t): Ge.t := (Ge.mk lp.(skenv_src) (List.map (ModSemPair.src) lp.(msps))). *)
  (* Definition tgt (lp: t): Ge.t := (Ge.mk lp.(skenv_tgt) (List.map (ModSemPair.tgt) lp.(msps))). *)

  Definition update_ord (lp: t) (idx: Type) (ord: idx -> idx -> Prop): t :=
    (mk lp.(sm) (List.map (fun msp => msp.(ModSemPair.update_ord) ord) lp.(msps)) ord)
  .

  Definition cons_msp (lp: t) (msp: ModSemPair.t): t :=
     (mk lp.(sm) (msp :: lp.(msps)) lp.(ord))
  .

  Lemma update_ord_spec
        lp0
        (SIM: sim lp0)
        (idx0: Type) (ord0: idx0 -> idx0 -> Prop)
        (EMBED: embedded lp0.(ord) ord0)
        (WF: well_founded ord0)
    :
      <<SIM: sim (lp0.(update_ord) ord0)>>
  .
  Proof.
    destruct lp0; ss. inv SIM; ss.
    econs; ss; eauto.
    { admit "trivial". }
    { eapply ModSemPair.update_ord_spec_list; eauto. }
    { clear - IDX. clear IDX.
      apply Forall_forall. i. apply list_in_map_inv in H. des. clarify. }
    { clear - IDX. clear IDX.
      apply Forall_forall. i. apply list_in_map_inv in H. des. clarify. }
    { admit "trivial". }
    { admit "trivial". }
  Qed.

End LOADPAIR.
End LoadPair.

Hint Unfold LoadPair.ge_src LoadPair.ge_tgt.



Section SIMLP.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.


Theorem find_fptr_owner_bsim
        lp
        (SIMLP: lp.(LoadPair.sim))
        fptr_src fptr_tgt
        (SIMFPTR: lp.(LoadPair.sm).(SimMem.sim_val) fptr_src fptr_tgt)
        n
        (FINDTGT: Ge.find_fptr_owner lp.(LoadPair.ge_tgt) fptr_tgt n)
  :
    <<FINDSRC: Ge.find_fptr_owner lp.(LoadPair.ge_src) fptr_src n>>
.
Proof.
  inv SIMLP.
  ss.
Qed.



End SIMLP.


Section SIMGE.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.

  (* Variable pp: ProgPair.t. *)
  (* Hypothesis SIMPROG: ProgPair.sim pp. *)
  (* Let p_src := pp.(ProgPair.src). *)
  (* Let p_tgt := pp.(ProgPair.tgt). *)
  (* Variable sk_src sk_tgt: Sk.t. *)
  (* Hypothesis LINKSRC: p_src.(link_sk) = Some sk_src. *)
  (* Hypothesis LINKTGT: p_tgt.(link_sk) = Some sk_tgt. *)
  (* Let skenv_src := sk_src.(Sk.load_skenv). *)
  (* Let skenv_tgt := sk_tgt.(Sk.load_skenv). *)
  (* Let mss_src := p_src.(load_modsem) skenv_src. *)
  (* Let mss_tgt := p_tgt.(load_modsem) skenv_tgt. *)
  (* Let ge_src := (p_src.(load_genv) skenv_src). *)
  (* (* TODO: I want to use "sem_src.(globalenv)" here, without unfolding it. *) *)
  (* Let ge_tgt := (p_tgt.(load_genv) skenv_tgt). *)



  (* TODO: Using "let" breaks tactics like "des" and "generalize dependent", even after "subst"ing it, *)
  (* but I don't know why... *)

  Theorem sim_progpair_sim_lpair
          pp
          (SIMPROG: ProgPair.sim pp)
          p_src p_tgt
          (PSRC: p_src = pp.(ProgPair.src))
          (PTGT: p_tgt = pp.(ProgPair.tgt))
          sk_src sk_tgt
          (LINKSRC: p_src.(link_sk) = Some sk_src)
          (LINKTGT: p_tgt.(link_sk) = Some sk_tgt)
          skenv_src skenv_tgt
          (SKENVSRC: skenv_src = sk_src.(Sk.load_skenv))
          (SKENVTGT: skenv_tgt = sk_tgt.(Sk.load_skenv))
          (* mss_src mss_tgt *)
          (* (MSSSRC: mss_src = p_src.(load_modsems) skenv_src) *)
          (* (MSSTGT: mss_tgt = p_tgt.(load_modsems) skenv_tgt) *)
          
    :
      exists lp,
        <<SRC: lp.(Lpair.mss_src) = p_src.(load_modsems) skenv_src>>
        /\ <<TGT: lp.(Lpair.mss_tgt) = p_tgt.(load_modsems) skenv_tgt>>
        /\ <<SS: pp.(ProgPair.ss_link) = Some lp.(Lpair.ss)>> 
        /\ <<SIM: Lpair.sim lp>>
  .
  Proof.
    subst. u. ss.
    assert(exists ss_link, <<LINKSS: pp.(ProgPair.ss_link) = Some ss_link>> /\
                           <<SIMSK: SimSymb.sim_sk ss_link sk_src sk_tgt>> /\
                           <<LINKORDER: Forall (fun mp => linkorder mp.(ModPair.ss) ss_link) pp>>).
    { u.
      revert_until pp.
      induction pp; ii; ss.
      inv SIMPROG.
      apply link_list_cons_inv in LINKSRC. apply link_list_cons_inv in LINKTGT. des.
      exploit IHpp; eauto.
      i; des.
      rename pp into pp_tl. rename a into pp_hd. rename ss_link into ss_link_tl.
      exploit SimSymb.link_preserves_sim_sk; revgoals.
      { i; des. esplits; eauto.
        - eapply link_list_cons; eauto.
        - econs; eauto.
          + exploit link_linkorder; try apply LINKSS; eauto. i; des. ss.
          + eapply Forall_impl; eauto.
            i. ss. eapply linkorder_trans; eauto.
            exploit link_linkorder; try apply LINKSS; eauto. i; des. ss.
      }
      all: eauto.
      apply H1.
      (* assert(exists ss_link, <<LINK: link pp_hd.(ModPair.ss) ss_link_tl = Some ss_link>>). *)
      (* { *)
      (*   eapply SimSymb.link_success; eauto. *)
      (*   admit "closed -> coverage <1= privs. Privs are disjoint, assuming they are good_prog". *)
      (* } *)
      (* des. exploit link_list_cons; eauto. *)
      (* esplits; eauto. *)
      (* exploit SimSymb.link_preserves_closed; revgoals. *)
      (* [..|i; des; esplits; eauto]. *)
      (* admit "TODO: closed is monotone!!". *)
    }
    des.
    remember (Genv.globalenv sk_src) as skenv_src.
    remember (Genv.globalenv sk_tgt) as skenv_tgt.
    Check (List.map (fun m => Mod.get_modsem m skenv_src (Mod.data m)) (List.map (ModPair.src) pp)).
    clear Heqskenv_src Heqskenv_tgt.
    u. rewrite LINKSS.
    clear LINKSRC LINKTGT LINKSS SIMSK.
    (* eexists (Lpair.mk _ _ ss_link _). esplits; ss. *)
    induction pp; ii; ss.
    { eexists (Lpair.mk _ _ _ [] _).
      esplits; ss; eauto.
      - econs; ss; eauto.
        apply lt_wf.
    }
    inv SIMPROG. inv LINKORDER.
    exploit IHpp; eauto. i; des.
    inv H1.
    specialize (SIMMS skenv_src skenv_tgt). des.
    set (idx_link lp.(Lpair.idx) msp.(ModSemPair.idx)) as idx.
    set (ord_link lp.(Lpair.ord) msp.(ModSemPair.ord)) as ord.
    (* eapply ModSemPair.embedding_preserves_sim with (msp1:= (msp.(ModSemPair.update_ord) ord)) in SIM; cycle 1. *)
    (* { eapply ord_link_embedded; eauto. } *)
    eexists ((lp.(Lpair.update_ord) ord).(Lpair.cons_msp) (msp.(ModSemPair.update_ord) ord)).
    ss. u.
    esplits; eauto.
    - rewrite SRC. f_equal. rewrite map_map. ss.
    - rewrite TGT. f_equal. rewrite map_map. ss.
    - hexploit ord_link_wf; eauto. { apply H6. } { apply SIM. } intro WF; des.
      econs; ss; eauto.
      + econs; eauto.
        { eapply ModSemPair.embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. }
        inv H6.
        eapply ModSemPair.update_ord_spec_list; eauto.
        { eapply ord_link_embedded; eauto. }
      + inv H6. econs; eauto.
        apply Forall_forall. intros ? IN. apply list_in_map_inv in IN. des. clarify.
      + inv H6. econs; eauto.
        apply Forall_forall. intros ? IN. apply list_in_map_inv in IN. des. clarify.
  Unshelve.
   all: ss.
  Qed.
  (*     + econs; eauto. *)
  (*     * u. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*     * eapply Forall2_impl; try apply SIM. *)
  (*       ii. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)

  (*   eexists (Lpair.mk skenv_src skenv_tgt ss_link *)
  (*                      ((ModSemPair.update_ord msp ord) *)
  (*                         :: List.map (fun msp => msp.(ModSemPair.update_ord) ord) lp.(Lpair.msps)) ord). *)
  (*   ss. u. *)
  (*   esplits; eauto. *)
  (*   - rewrite SRC. f_equal. rewrite map_map. ss. *)
  (*   - rewrite TGT. f_equal. rewrite map_map. ss. *)
  (*   - hexploit ord_link_wf; eauto. { apply H6. } { apply SIM. } intro WF; des. *)
  (*     econs; ss; eauto. *)
  (*     + econs; eauto. *)
  (*       { eapply ModSemPair.embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. } *)
  (*       inv H6. *)
  (*     + inv H6. econs; eauto. *)
  (*     + econs; eauto. *)
  (*     * u. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*     * eapply Forall2_impl; try apply SIM. *)
  (*       ii. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*   + eapply ord_link_wf; eauto. *)
  (*   assert(SIMMS: exists (idx : Type) (order : idx -> idx -> Prop), *)
  (*             <<SIM: Forall2 (sim_modsem order) (pp.(ProgPair.src).(load_modsems) skenv_src) *)
  (*                                        (pp.(ProgPair.tgt).(load_modsems) skenv_tgt)>> *)
  (*             /\ <<WF: well_founded order>>). *)
  (*   { induction pp. *)
  (*     - esplits; eauto. *)
  (*       { econs; eauto. } *)
  (*       eapply lt_wf. *)
  (*     - inv SIMPROG. inv LINKORDER. *)
  (*       exploit IHpp; eauto. i; des. *)
  (*       inv H1. *)
  (*       exploit SIMMS; eauto. { eapply SimSymb.sim_skenv_monotone_ss; eauto. } i; des. clear SIMMS. *)
  (*       exists (idx_link idx idx0), (ord_link order order0). *)
  (*       ss. u. *)
  (*       esplits; eauto. *)
  (*       + econs; eauto. *)
  (*         * u. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*         * eapply Forall2_impl; try apply SIM. *)
  (*           ii. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*       + eapply ord_link_wf; eauto. *)
  (*   } *)
  (*   des. *)
  (*   esplits; eauto. *)
  (*   econs; eauto. *)
  (* Qed. *)



  (* Theorem sim_progpair_sim_lpair____________ *)
  (*         pp *)
  (*         (SIMPROG: ProgPair.sim pp) *)
  (*         p_src p_tgt *)
  (*         (PSRC: p_src = pp.(ProgPair.src)) *)
  (*         (PTGT: p_tgt = pp.(ProgPair.tgt)) *)
  (*         sk_src sk_tgt *)
  (*         (LINKSRC: p_src.(link_sk) = Some sk_src) *)
  (*         (LINKTGT: p_tgt.(link_sk) = Some sk_tgt) *)
  (*         ss *)
  (*         (SIMSK: SimSymb.sim_sk ss sk_src sk_tgt) *)
  (*         skenv_src skenv_tgt *)
  (*         (SKENVSRC: skenv_src = sk_src.(Sk.load_skenv)) *)
  (*         (SKENVTGT: skenv_tgt = sk_tgt.(Sk.load_skenv)) *)
  (*         mss_src mss_tgt *)
  (*         (MSSSRC: mss_src = p_src.(load_modsem) skenv_src) *)
  (*         (MSSTGT: mss_tgt = p_tgt.(load_modsem) skenv_tgt) *)
          
  (*   : *)
  (*     <<SIM: Lpair.sim (Lpair.mk skenv_src skenv_tgt ss mss_src mss_tgt)>> *)
  (* . *)
  (* Proof. *)
  (*   subst. u. ss. *)
  (*   assert(<<LINKSS: pp.(ProgPair.ss) = Some ss_link>> /\ *)
  (*                    <<SIMSK: SimSymb.sim_sk ss_link sk_src sk_tgt>> /\ *)
  (*                             <<LINKORDER: Forall (fun mp => linkorder mp.(ModPair.ss) ss_link) pp>>). *)
  (*   { u. *)
  (*     revert_until pp. *)
  (*     induction pp; ii; ss. *)
  (*     inv SIMPROG. *)
  (*     apply link_list_cons_inv in LINKSRC. apply link_list_cons_inv in LINKTGT. des. *)
  (*     exploit IHpp; eauto. *)
  (*     i; des. *)
  (*     rename pp into pp_tl. rename a into pp_hd. rename ss_link into ss_link_tl. *)
  (*     exploit SimSymb.link_preserves_sim_sk; revgoals. *)
  (*     { i; des. esplits; eauto. *)
  (*       - eapply link_list_cons; eauto. *)
  (*       - econs; eauto. *)
  (*         + exploit link_linkorder; try apply LINKSS; eauto. i; des. ss. *)
  (*         + eapply Forall_impl; eauto. *)
  (*           i. ss. eapply linkorder_trans; eauto. *)
  (*           exploit link_linkorder; try apply LINKSS; eauto. i; des. ss. *)
  (*     } *)
  (*     all: eauto. *)
  (*     apply H1. *)
  (*     (* assert(exists ss_link, <<LINK: link pp_hd.(ModPair.ss) ss_link_tl = Some ss_link>>). *) *)
  (*     (* { *) *)
  (*     (*   eapply SimSymb.link_success; eauto. *) *)
  (*     (*   admit "closed -> coverage <1= privs. Privs are disjoint, assuming they are good_prog". *) *)
  (*     (* } *) *)
  (*     (* des. exploit link_list_cons; eauto. *) *)
  (*     (* esplits; eauto. *) *)
  (*     (* exploit SimSymb.link_preserves_closed; revgoals. *) *)
  (*     (* [..|i; des; esplits; eauto]. *) *)
  (*     (* admit "TODO: closed is monotone!!". *) *)
  (*   } *)
  (*   des. exists ss_link. *)
  (*   remember (Genv.globalenv sk_src) as skenv_src. *)
  (*   remember (Genv.globalenv sk_tgt) as skenv_tgt. *)
  (*   assert(SIMSKENV: SimSymb.sim_skenv ss_link skenv_src skenv_tgt). *)
  (*   { eapply SimSymb.load_respects_ss; eauto. } *)
  (*   clear Heqskenv_src Heqskenv_tgt. clear LINKSRC LINKTGT LINKSS SIMSK. *)
  (*   assert(SIMMS: exists (idx : Type) (order : idx -> idx -> Prop), *)
  (*             <<SIM: Forall2 (sim_modsem order) (pp.(ProgPair.src).(load_modsem) skenv_src) *)
  (*                                        (pp.(ProgPair.tgt).(load_modsem) skenv_tgt)>> *)
  (*             /\ <<WF: well_founded order>>). *)
  (*   { induction pp. *)
  (*     - esplits; eauto. *)
  (*       { econs; eauto. } *)
  (*       eapply lt_wf. *)
  (*     - inv SIMPROG. inv LINKORDER. *)
  (*       exploit IHpp; eauto. i; des. *)
  (*       inv H1. *)
  (*       exploit SIMMS; eauto. { eapply SimSymb.sim_skenv_monotone_ss; eauto. } i; des. clear SIMMS. *)
  (*       exists (idx_link idx idx0), (ord_link order order0). *)
  (*       ss. u. *)
  (*       esplits; eauto. *)
  (*       + econs; eauto. *)
  (*         * u. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*         * eapply Forall2_impl; try apply SIM. *)
  (*           i. eapply embedding_preserves_sim; eauto. eapply ord_link_embedded; eauto. *)
  (*       + eapply ord_link_wf; eauto. *)
  (*   } *)
  (*   des. *)
  (*   econs; eauto. *)
  (* Qed. *)

End SIMGE.

(* Section SIMGE. *)

(*   Context `{SS: SimSymb.class} `{SM: @SimMem.class SS}. *)

(*   (* Hypothesis CLOSED: closed ss_link sk_src sk_tgt. *) *)

(*   Theorem sim_progpair_sim_ge *)
(*     : *)
(*       exists ss_link, *)
(*         <<SIM: Lpair.sim (Lpair.mk skenv_src skenv_tgt ss_link mss_src mss_tgt)>> *)
(*   . *)
(*   Proof. *)
(*     ss. *)
(*     subst_locals. u. ss. *)
(*     assert(exists ss_link, pp.(ProgPair.ss_link) = Some ss_link). *)
(*     { u. *)
(*       generalize dependent sk_src. (* TODO: This does not work!! Is this a bug?? *) Undo 1. *)
(*       revert_until pp. *)
(*       induction pp; ii; ss. *)
(*       inv SIMPROG. *)
(*       apply link_list_cons_inv in LINKSRC. apply link_list_cons_inv in LINKTGT. *)
(*       des. (* TODO: des does not work!! Is this a bug?? *) *)
(*       destruct  *)
(*       exploit IHt; eauto. *)
(*       - ss. *)
(*       - ss. *)
(*     } *)
(*     assert(SIMSKENV: exists ss, SimSymb.sim_skenv ss sk_src.(Sk.load_skenv) sk_tgt.(Sk.load_skenv)). *)
(*     induction pp; ii; ss. *)
(*     - inv WF. inv SIMMPS. unfold init_sk in *. ss. *)
(*       all ltac:(fun H => apply link_list_cons_inv in H). *)
(*       des. (* TODO: Why des does not work? *) *)
(*       destruct LINKSRC, LINKTGT; clear LINKSRC LINKTGT; des. *)
(*       exploit IHt; eauto. *)
(*       i; des. *)
(*       esplits; eauto. *)
(*       { inv  *)
(*     assert(SIMSKENV: SimSymb.sim_skenv ss_link ge_src.(Ge.skenv) ge_tgt.(Ge.skenv)). *)
(*     { exploit SimMem.load_respects_ss; eauto. i; des. ss. } *)
(*     econs; eauto. *)
(*     inv SIMPROG. *)
(*     cbn. *)
(*     clear - SIMMPS SIMSKENV SSLINK. *)
(*     unfold ProgPair.ss_link in *. *)
(*     assert(LINKORDER: forall *)
(*               ss *)
(*               (IN: List.In ss (map ModPair.ss pp)) *)
(*             , *)
(*               <<LO: linkorder ss ss_link>>). *)
(*     { i. admit "link_list_linkorder". } *)
(*     subst skenv_src skenv_tgt ge_src ge_tgt p_src p_tgt. *)
(*     ginduction pp; ii; ss. *)
(*     unfold flip. inv SIMMPS. *)
(*     econs; eauto. *)
(*     - eapply H1; eauto. *)
(*       eapply SimSymb.sim_skenv_monotone_ss; eauto. *)
(*       admit "link_list_linkorder". *)
(*     - eapply IHt; eauto. *)
(*       admit "link_list_linkorder". *)
(*   Qed. *)


(*   Variable ss_link: SimSymb.t. *)
(*   Variable sem_src sem_tgt: semantics. *)
(*   Hypothesis LOADSRC: sem p_src = Some sem_src. *)
(*   Hypothesis LOADTGT: sem p_tgt = Some sem_tgt. *)
(*   Hypothesis SSLINK: pp.(ProgPair.ss_link) = Some ss_link. *)

(*   Variable m_src m_tgt: mem. *)
(*   Hypothesis LOADMEMSRC: sk_src.(Sk.load_mem) = Some m_src. *)
(*   Hypothesis LOADMEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt. *)

(*   Theorem sim_modsem *)

(* End SIMGE. *)

