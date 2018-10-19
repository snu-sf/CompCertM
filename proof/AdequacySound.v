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
Require Import SimSymb SimMem SimMod SimModSem SimProg (* SimLoad *) SimProg.
Require Import SemProps Ord.
Require Import Sound Preservation.
Require Import Memory.

Set Implicit Arguments.




Section ADQSOUND.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := sk_link_src.(Sk.load_skenv).
  Let skenv_link_tgt := sk_link_tgt.(Sk.load_skenv).

  (* Let ge: Ge.t := sem_src.(Smallstep.globalenv). *)

  Inductive sound_ge (su0: Sound.t) (m0: mem): Prop :=
  | sound_ge_intro
      (GE: Forall (fun ms => su0.(Sound.skenv) m0 ms.(ModSem.skenv)) sem_src.(Smallstep.globalenv).(fst))
  .

  Lemma le_preserves_sound_ge
        m0 su0 su1
        (GE: sound_ge su0 m0)
        (LE: Sound.le su0 su1)
    :
      <<GE: sound_ge su1 m0>>
  .
  Proof.
    inv GE.
    econs; eauto.
    rewrite Forall_forall in *.
    ii. eapply Sound.skenv_le; eauto.
  Qed.

  Lemma mle_preserves_sound_ge
        m0 m1 su0
        (GE: sound_ge su0 m0)
        (LE: Sound.mle su0 m0 m1)
    :
      <<GE: sound_ge su0 m1>>
  .
  Proof.
    inv GE.
    econs; eauto.
    rewrite Forall_forall in *.
    ii. eapply Sound.skenv_mle; eauto.
  Qed.

  (* stack can go preservation when su0 is given *)
  Inductive sound_stack (su0: Sound.t) (args: Args.t): list Frame.t -> Prop :=
  | sound_stack_nil
      (GE: sound_ge su0 args.(Args.m))
    :
      sound_stack su0 args []
  | sound_stack_cons
      su_tail args_tail tail
      ms lst0
      (TL: sound_stack su_tail args_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          <<SUST: sound_state_all su0 args_tail.(Args.m) lst0>>)
      (K: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          (* (<<SUST: sound_state_all su0 args.(Args.m) lst0>>) *)
          (* /\ *)
          (<<K: forall
              retv lst1
              su_greatest
              (GR: Sound.get_greatest su0 args su_greatest)
              su_ret
              (LE: Sound.le su_greatest su_ret)
              (SURETV: Sound.retv su_ret retv)
              (MLE: Sound.mle su_greatest args.(Args.m) retv.(Retv.m))
              (AFTER: ms.(ModSem.after_external) lst0 retv lst1)
            ,
              (* sound_state_all su0 args.(Args.m) lst1>>) *)
              sound_state_all su0 args_tail.(Args.m) lst1>>)
      )
      (GR: Sound.get_greatest su_tail args_tail su0)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
      (GE: sound_ge su0 args.(Args.m))
      (* sound_state_ex *)
      (* (PRSV: local_preservation ms sound_state_ex) *)
      (* (HD: sound_state_ex su0 lst0) *)
    :
      sound_stack su0 args ((Frame.mk ms lst0) :: tail)
  .

  Inductive sound_state (su0: Sound.t): mem -> state -> Prop :=
  | sound_state_normal
      su_tail args_tail tail
      ms lst0
      m_arg
      (GR: Sound.get_greatest su_tail args_tail su0)
      (TL: sound_stack su_tail args_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          <<SUST: sound_state_all su0 m_arg lst0>>)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
      (ABCD: args_tail.(Args.m) = m_arg)
      (GE: sound_ge su0 m_arg)
    :
      sound_state su0 m_arg (State ((Frame.mk ms lst0) :: tail))
  | sound_state_call
      su_tail m_tail frs
      args
      (GR: Sound.get_greatest su_tail args su0)
      (ARGS: Sound.args su0 args)
      (STK: sound_stack su_tail args frs)
      (* (MLE: Sound.mle su0 m_tail args.(Args.m)) *)
      (EQ: args.(Args.m) = m_tail)
      (GE: sound_ge su0 m_tail)
    :
      sound_state su0 m_tail (Callstate args frs)
  .

  Lemma sound_init
        st0
        (INIT: sem_src.(Smallstep.initial_state) st0)
    :
      exists su0 m_init0, <<MEM: Sk.load_mem sk_link_src = Some m_init0>> /\ <<SU: sound_state su0 m_init0 st0>>
  .
  Proof.
    inv INIT. clarify. clear skenv_link_tgt p_tgt skenv_link_tgt sem_tgt LINKTGT.
    hexploit Sound.init_spec; eauto. i; des.
    exploit Sound.greatest_ex; eauto.
    { esplits; eauto. refl. }
    i; des.
    esplits; eauto.
    assert(WF: SkEnv.wf (Sk.load_skenv sk_link_src)).
    { eapply Sk.load_skenv_wf. }
    assert(GE: sound_ge su_init m_init).
    {
      econs. rewrite Forall_forall. intros ? IN. ss. des_ifs. u in IN.
      rewrite in_map_iff in IN.
      des; ss; clarify.
      + s. rewrite <- Sound.system_skenv; eauto.
      + eapply Sound.skenv_project; eauto.
        eapply Mod.get_modsem_projected_sk; eauto.
    }
    econs; eauto.
    - eapply Sound.greatest_adq; eauto.
    - econs; eauto.
    - eapply le_preserves_sound_ge; eauto.
      eapply Sound.greatest_adq; eauto.
  Unshelve.
    all: ss.
  Qed.

  Lemma sound_progress
        su0 st0 m_arg0 tr st1
        (SUST: sound_state su0 m_arg0 st0)
        (STEP: Step sem_src st0 tr st1)
    :
      <<SUST: exists su1 m_arg1, sound_state su1 m_arg1 st1>>
  .
  Proof.
    inv STEP.
    - (* CALL *)
      inv SUST. ss.
      exploit (@Sound.greatest_ex _ su0 args); eauto.
      { des. dup EX. inv EX. exploit CALL; eauto.
        { eapply HD; eauto. }
        i; des.
        eapply Sound.greatest_adq in GR0. des.
        esplits; eauto.
      }
      i; des.
      generalize (Sound.greatest_ex su0 args). i; des.
      exists su_gr.
      exists args.(Args.m).
      esplits; eauto.
      econs; eauto; swap 2 3.
      { eapply Sound.greatest_adq; eauto. }
      { dup EX. inv EX. exploit CALL; eauto.
        { eapply HD; eauto. }
        i; des.
        eapply le_preserves_sound_ge; eauto.
        - eapply mle_preserves_sound_ge; eauto.
        - eapply Sound.greatest_adq; eauto.
      }
      econs; eauto.
      {
        ii. dup PRSV. bar. inv PRSV. exploit CALL; eauto; cycle 1.
        { i; des.
          assert(su_gr0 = su_greatest).
          { eapply Sound.greatest_dtm; eauto. }
          clarify.
          eapply K; eauto.
        }
        eapply HD; eauto.
      }
      { eapply mle_preserves_sound_ge; eauto.
        dup EX. inv EX. exploit CALL; eauto.
        { eapply HD; eauto. }
        i; des.
        ss.
      }
      (* intros ? ?. *)
      (* bar. dup PRSV. inv PRSV. bar. exploit CALL; eauto. { eapply HD; eauto. } i; des. *)
      (* dsplits; eauto. *)
      (* ii. *)
      (* assert(su_greatest = su_gr0). *)
      (* { eapply Sound.greatest_dtm; eauto. } *)
      (* clarify. *)
      (* eapply K; eauto. *)
    - (* INIT *)
      inv SUST. ss. des_ifs.

      esplits; eauto.
      econs; eauto.
      + ii. inv PRSV. exploit INIT0; eauto.
        { inv GE. rewrite Forall_forall in *. eapply GE0. inv MSFIND. ss. des_ifs. }
      + inv MSFIND. ss. rr in SIMPROG. rewrite Forall_forall in *.
        des; clarify.
        { eapply system_local_preservation. }
        u in MODSEM.
        rewrite in_map_iff in MODSEM. des; clarify. rename x into md_src.
        assert(exists mp, In mp pp /\ mp.(ModPair.src) = md_src).
        { clear - MODSEM0. rr in pp. rr in p_src. subst p_src. rewrite in_map_iff in *. des. eauto. }
        des.
        exploit SIMPROG; eauto. intros MPSIM. inv MPSIM.
        exploit SIMMS.
        { eapply SimSymb.le_refl. }
        { admit "somehow. 1) fat module / skinny modsem. 2) require as premise". }
        i; des. inv H0. ss. esplits; eauto.
    - (* INTERNAL *)
      inv SUST. ss.
      esplits; eauto. econs; eauto.
      i. dup PRSV. inv PRSV. eapply STEP; eauto.
      + eapply HD; eauto.
      + split; ii; ModSem.tac.
    - (* RETURN *)
      inv SUST. ss. rename ms into ms_top.
      rename args_tail into args_tail_top.
      bar.
      inv TL. ss.
      unfold Frame.update_st. s.
      bar.
      des. dup EX. inv EX. exploit RET; eauto.
      { eapply HD; eauto. }
      bar.
      i; des.
      esplits; eauto. econs; try apply TL0; eauto.
      + ii. specialize (K sound_state_all PRSV).
        eapply K; eauto.
      +
        inv TL0; ss.
        { eapply le_preserves_sound_ge; eauto.
          eapply Sound.greatest_adq; eauto.
        }
        eapply le_preserves_sound_ge; eauto.
        eapply Sound.greatest_adq; eauto.
  Unshelve.
    all: ss.
    admit "related to above admit".
  Qed.

  Lemma sound_progress_star
        su0 st0 m_arg0 tr st1
        (SUST: sound_state su0 m_arg0 st0)
        (STEP: Star sem_src st0 tr st1)
    :
      <<SUST: exists su1 m_arg1, sound_state su1 m_arg1 st1>>
  .
  Proof.
    generalize dependent m_arg0.
    generalize dependent su0.
    induction STEP.
    - esplits; eauto.
    - clarify. i. exploit sound_progress; eauto. i; des. eapply IHSTEP; eauto.
  Qed.

  Lemma sound_progress_plus
        su0 st0 m_arg0 tr st1
        (SUST: sound_state su0 m_arg0 st0)
        (STEP: Plus sem_src st0 tr st1)
    :
      <<SUST: exists su1 m_arg1, sound_state su1 m_arg1 st1>>
  .
  Proof.
    eapply sound_progress_star; eauto. eapply plus_star; eauto.
  Qed.

End ADQSOUND.
