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

  (* stack can go preservation when su0 is given *)
  Inductive sound_stack (su0: Sound.t) (args: Args.t): list Frame.t -> Prop :=
  | sound_stack_nil
    :
      sound_stack su0 args []
  | sound_stack_cons
      su_tail args_tail tail
      ms lst0
      (TL: sound_stack su_tail args_tail tail)
      (K: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          (* (<<SUST: sound_state_all su0 args.(Args.m) lst0>>) *)
          (* /\ *)
          (<<K: forall
              retv lst1
              su_greatest
              (GR: Sound.get_greatest args su_greatest)
              (SURETV: Sound.retv su_greatest retv)
              (MLE: Sound.mle su_greatest args.(Args.m) retv.(Retv.m))
              (AFTER: ms.(ModSem.after_external) lst0 retv lst1)
            ,
              (* sound_state_all su0 args.(Args.m) lst1>>) *)
              sound_state_all su0 args_tail.(Args.m) lst1>>)
      )
      (GR: Sound.get_greatest args_tail su0)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
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
      (GR: Sound.get_greatest args_tail su0)
      (TL: sound_stack su_tail args_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          <<SUST: sound_state_all su0 m_arg lst0>>)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
      (ABCD: args_tail.(Args.m) = m_arg)
    :
      sound_state su0 m_arg (State ((Frame.mk ms lst0) :: tail))
  | sound_state_call
      su_tail m_tail frs
      args
      (GR: Sound.get_greatest args su0)
      (ARGS: Sound.args su0 args)
      (STK: sound_stack su_tail args frs)
    :
      sound_state su0 m_tail (Callstate args frs)
  .

  Lemma sound_init
        st0
        (INIT: sem_src.(Smallstep.initial_state) st0)
    :
      exists m_init su0, sound_state su0 m_init st0
  .
  Proof.
    inv INIT.
    hexploit (Sound.greatest_ex (Args.mk (Genv.symbol_address (Sk.load_skenv sk_link) (prog_main sk_link) Ptrofs.zero)
                                         []
                                         m_init)); eauto. i; des.
    esplits; eauto. econs; s; eauto.
    - eapply Sound.greatest_spec; eauto.
    - econs; eauto.
  Unshelve.
    all: ss.
    all: try exact Sound.top.
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
      generalize (Sound.greatest_ex args). i; des.
      exists su_gr.
      exists args.(Args.m).
      esplits; eauto.
      econs; eauto.
      { eapply Sound.greatest_spec; eauto. }
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
      ii. specialize (K sound_state_all PRSV).
      eapply K; eauto.
  Unshelve.
    all: ss.
    admit "related to above admit".
  Qed.

End ADQSOUND.
