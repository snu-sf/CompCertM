Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Smallstep.
Require Import Integers.
Require Import Events.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem SimMod SimModSemUnified SimProg.
Require Import SemProps Ord.
Require Import Sound Preservation.
Require Import Memory.

Set Implicit Arguments.



(* TODO: Move to CoqlibC !!! *)
Lemma nth_error_map_some
      A B (f: A -> B) la n b
      (NTH: nth_error (map f la) n = Some b)
  :
    exists a, <<NTH: nth_error la n = Some a>> /\ <<MAP: f a = b>>
.
Proof.
  ginduction la; ii; ss.
  { destruct n; ss. }
  destruct n; ss; clarify.
  { esplits; eauto. }
  eapply IHla; eauto.
Qed.

Section ADQSOUND.

  Context `{SMOS: SimMemOhs.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).
  Hypothesis (WFSKSRC: forall md (IN: In md p_src), <<WF: Sk.wf md>>).
  Hypothesis (WFSKTGT: forall md (IN: In md p_tgt), <<WF: Sk.wf md>>).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := (Sk.load_skenv sk_link_src).
  Let skenv_link_tgt := (Sk.load_skenv sk_link_tgt).

  Variable ss_link: SimSymb.t.
  Hypothesis (SIMSKENV: exists sm, SimSymb.sim_skenv sm ss_link skenv_link_src skenv_link_tgt).

  Hypothesis INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src)).
  Hypothesis INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt)).
  Hypothesis SSLE: forall mp (IN: In mp pp), SimSymb.le mp.(ModPair.ss) ss_link.

  Let WFSKLINKSRC: Sk.wf sk_link_src. eapply link_sk_preserves_wf_sk; et. Qed.
  Let WFSKLINKTGT: Sk.wf sk_link_tgt. eapply link_sk_preserves_wf_sk; et. Qed.

  (* Let ge: Ge.t := sem_src.(Smallstep.globalenv). *)

  Inductive sound_ge (su0: Sound.t) (m0: mem): Prop :=
  | sound_ge_intro
      (GE: Forall (fun ms => su0.(Sound.skenv) m0 ms.(ModSem.skenv) /\ su0.(Sound.skenv) m0 ms.(ModSem.skenv_link))
                  (fst sem_src.(Smallstep.globalenv)))
  .

  Lemma lepriv_preserves_sound_ge
        m0 su0 su1
        (GE: sound_ge su0 m0)
        (LE: Sound.lepriv su0 su1):
      <<GE: sound_ge su1 m0>>.
  Proof.
    inv GE. econs; eauto. rewrite Forall_forall in *. ii. split; eapply Sound.skenv_lepriv; try apply GE0; eauto.
  Qed.

  Lemma hle_preserves_sound_ge
        m0 su0 su1
        (WF: Sound.wf su0)
        (GE: sound_ge su0 m0)
        (LE: Sound.hle su0 su1):
      <<GE: sound_ge su1 m0>>.
  Proof.
    eapply lepriv_preserves_sound_ge; eauto. eapply Sound.hle_lepriv; et.
  Qed.

  Lemma mle_preserves_sound_ge
        m0 m1 su0
        (GE: sound_ge su0 m0)
        (LE: Sound.mle su0 m0 m1):
      <<GE: sound_ge su0 m1>>.
  Proof.
    inv GE. econs; eauto. rewrite Forall_forall in *. ii. split; eapply Sound.skenv_mle; try apply GE0; eauto.
  Qed.

  (* stack can go preservation when su0 is given *)
  Inductive sound_stack (args: Args.t): list Frame.t -> Prop :=
  | sound_stack_nil
      (EXSU: exists su_ex, Sound.args su_ex args /\ sound_ge su_ex (Args.get_m args)):
      sound_stack args []
  | sound_stack_cons
      args_tail tail ms lst0
      (TL: sound_stack args_tail tail)
      (FORALLSU: forall su0
          (SUARGS: Sound.args su0 args_tail)
          (SUGE: sound_ge su0 (Args.get_m args_tail)),
          (<<HD: forall
                 sound_state_all
                 (PRSV: local_preservation_noguarantee ms sound_state_all),
                 <<SUST: sound_state_all su0 (Args.get_m args_tail) lst0>>>>)
          /\
          (<<K: forall
                 sound_state_all
                 (PRSV: local_preservation_noguarantee ms sound_state_all),
                 (* (<<SUST: sound_state_all su0 args.(Args.get_m) lst0>>) *)
                 (* /\ *)
                 exists su_gr,
                   (<<ARGS: Sound.args su_gr args>>) /\
                   (<<LE: Sound.lepriv su0 su_gr>>) /\
                   (<<K: forall oh retv lst1 su_ret
                       (LE: Sound.hle su_gr su_ret)
                       (SURETV: Sound.retv su_ret retv)
                       (MLE: Sound.mle su_gr (Args.get_m args) (Retv.get_m retv))
                       (AFTER: ms.(ModSem.after_external) lst0 oh retv lst1),
                       (* sound_state_all su0 args.(Args.get_m) lst1>>) *)
                       sound_state_all su0 (Args.get_m args_tail) lst1>>)
             >>)
          /\
          (<<MLE: Sound.mle su0 (Args.get_m args_tail) (Args.get_m args)>>)
      )
      (EXSU: exists su_ex, Sound.args su_ex args_tail /\ sound_ge su_ex (Args.get_m args_tail))
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex):
      sound_stack args ((Frame.mk ms lst0) :: tail).

  Inductive sound_state: state -> Prop :=
  | sound_state_normal
      args_tail tail ms lst0 m_arg msohs
      (TL: sound_stack args_tail tail)
      (EXSU: exists su_ex, Sound.args su_ex args_tail /\ sound_ge su_ex m_arg)
      (FORALLSU: forall su0
          (SUARGS: Sound.args su0 args_tail)
          (SUGE: sound_ge su0 (Args.get_m args_tail)),
          (<<HD: forall
              sound_state_all
              (PRSV: local_preservation_noguarantee ms sound_state_all),
              <<SUST: sound_state_all su0 m_arg lst0>>>>))
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
      (ABCD: (Args.get_m args_tail) = m_arg)
    :
      sound_state (State ((Frame.mk ms lst0) :: tail) msohs)
  | sound_state_call
      m_tail frs args msohs
      (* (ARGS: Sound.args su0 args) *)
      (STK: sound_stack args frs)
      (* (MLE: Sound.mle su0 m_tail args.(Args.get_m)) *)
      (EQ: (Args.get_m args) = m_tail)
      (EXSU: exists su_ex, Sound.args su_ex args /\ sound_ge su_ex m_tail):
      sound_state (Callstate args frs msohs).

  Lemma sound_init
        st0
        (INIT: sem_src.(Smallstep.initial_state) st0):
    <<SU: sound_state st0>>.
  Proof.
    inv INIT. clarify. clear skenv_link_tgt p_tgt skenv_link_tgt sem_tgt LINKTGT INCLTGT WFSKTGT SIMSKENV.
    hexploit Sound.init_spec; eauto. i; des. esplits; eauto.
    assert(WFSKE: SkEnv.wf (Sk.load_skenv sk_link_src)).
    { eapply SkEnv.load_skenv_wf; et. }
    assert(GE: sound_ge su_init m_init).
    { econs. rewrite Forall_forall. intros ? IN. ss. des_ifs. u in IN.
      rewrite in_map_iff in IN.
      des; ss; clarify.
      + s. split; ss; try apply Sound.system_skenv; eauto.
      + assert(INCL: SkEnv.includes (Sk.load_skenv sk_link_src) (Mod.sk x0)).
        { unfold p_src in IN0. unfold ProgPair.src in *. rewrite in_map_iff in IN0. des. clarify. eapply INCLSRC; et. }
        split; ss.
        * eapply Sound.skenv_project; eauto.
          { eapply link_load_skenv_wf_mem; et. }
          rewrite <- Mod.get_modsem_skenv_spec; ss. eapply SkEnv.project_impl_spec; et.
        * rewrite Mod.get_modsem_skenv_link_spec. ss.
    }
    econs; eauto. econs; eauto.
    (* - eapply Sound.greatest_adq; eauto. *)
    (* - econs; eauto. *)
    (* - eapply vle_preserves_sound_ge; eauto. *)
    (*   eapply Sound.greatest_adq; eauto. *)
  Unshelve.
    all: ss.
  Qed.

  Lemma sound_progress
        st0 tr st1
        (SUST: sound_state st0)
        (STEP: Step sem_src st0 tr st1):
      <<SUST: sound_state st1>>.
  Proof.
    inv STEP.
    - (* CALL *)
      inv SUST. ss. des. exploit FORALLSU; eauto. { eapply local_preservation_noguarantee_weak; eauto. } intro T; des.
      inv EX. exploit CALL; eauto. i; des. esplits; eauto. econs; eauto; cycle 1.
      + esplits; eauto. eapply lepriv_preserves_sound_ge; eauto.
        { eapply mle_preserves_sound_ge; eauto. }
      + econs; eauto; cycle 1.
        { esplits; eauto. econs; eauto. }
        ii. esplits; eauto.
        * ii. exploit FORALLSU; try apply SUARGS; eauto.
        * ii. exploit FORALLSU; try apply SUARGS; eauto. intro U; des.
          inv PRSV. exploit CALL0; eauto. i; des. esplits; eauto. ii. eapply K0; eauto.
        * exploit FORALLSU; eauto.
          { eapply local_preservation_noguarantee_weak; eauto. econs; eauto. }
          i; des. exploit CALL; eauto. i; des. ss.
    - (* INIT *)
      inv SUST. ss. des_ifs. esplits; eauto. econs; eauto.
      + ii. esplits; eauto.
        * ii. inv PRSV. inv SUGE. rewrite Forall_forall in *.
          exploit GE; eauto. { ss. des_ifs. eapply MSFIND. } intro T; des. eapply INIT0; et.
      + inv MSFIND. ss. rr in SIMPROG. rewrite Forall_forall in *. des; clarify.
        { eapply system_local_preservation. }
        u in MODSEM.
        rewrite in_map_iff in MODSEM.
        des; clarify. rename x into md_src.
        assert(exists mp, In mp pp /\ mp.(ModPair.src) = md_src).
        { clear - MODSEM0. rr in pp. rr in p_src. subst p_src. rewrite in_map_iff in *. des. eauto. }
        des. exploit SIMPROG; eauto. intros MPSIM. inv MPSIM.
        destruct SIMSKENV. exploit SIMMS.
        { eapply INCLSRC; et. }
        { eapply INCLTGT; et. }
        { eapply SkEnv.load_skenv_wf; et. }
        { eapply SkEnv.load_skenv_wf; et. }
        { eapply SSLE; eauto. }
        { eauto. }
        intro SIM; des.
        try by (inv SIM; ss; esplits; eauto).
        try by (inv SIMMSP; ss; esplits; eauto).
    - (* INTERNAL *)
      inv SUST. ss. esplits; eauto. econs; eauto. i. des.
      exploit FORALLSU; eauto. { eapply local_preservation_noguarantee_weak; eauto. } intro U; des. esplits; eauto. i. ss. inv PRSV.
      eapply STEP; eauto.
      + eapply FORALLSU; eauto. econs; eauto.
      + split; ii; ModSem.tac.
    - (* RETURN *)
      inv SUST. ss. rename ms into ms_top. rename args_tail into args_tail_top.
      inv TL. ss. unfold Frame.update_st. s. des. esplits; eauto. econs; eauto. ii. esplits; eauto.
      + ii. exploit FORALLSU0; eauto. i; des. exploit K; eauto. i; des. inv EX.
        exploit RET; eauto.
        { eapply FORALLSU; eauto.
          { eapply lepriv_preserves_sound_ge. { eapply mle_preserves_sound_ge; eauto. } eauto. }
          { eapply local_preservation_noguarantee_weak; eauto. econs; et. } }
        i; des.
        eapply K0; eauto.
  Unshelve.
    all: ss.
  Qed.

  (* Lemma sound_progress_star *)
  (*       st0 tr st1 *)
  (*       (SUST: sound_state st0) *)
  (*       (STEP: Star sem_src st0 tr st1): *)
  (*     <<SUST: sound_state st1>>. *)
  (* Proof. *)
  (*   induction STEP. *)
  (*   - esplits; eauto. *)
  (*   - clarify. i. exploit sound_progress; eauto. *)
  (* Qed. *)

  (* Lemma sound_progress_plus *)
  (*       st0 tr st1 *)
  (*       (SUST: sound_state st0) *)
  (*       (STEP: Plus sem_src st0 tr st1): *)
  (*     <<SUST: sound_state st1>>. *)
  (* Proof. *)
  (*   eapply sound_progress_star; eauto. eapply plus_star; eauto. *)
  (* Qed. *)

  Theorem preservation: @preservation sem_src sound_state.
  Proof.
    econs.
    - eapply sound_init.
    - eapply sound_progress.
  Qed.

End ADQSOUND.
