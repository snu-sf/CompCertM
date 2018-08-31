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
  Inductive sound_stack (su0: Sound.t) (args: Args.t) (m_arg: mem): list Frame.t -> Prop :=
  | sound_stack_nil
    :
      sound_stack su0 args m_arg []
  | sound_stack_cons
      su_tail m_tail args_tail tail
      ms lst0
      (TL: sound_stack su_tail args_tail m_tail tail)
      (K: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          (<<SUST: sound_state_all su0 m_arg lst0>>)
          /\
          (<<K: forall
              retv lst1
              su_greatest
              (GR: Sound.get_greatest args su_greatest)
              (SURETV: Sound.retv su_greatest retv)
              (MLE: Sound.mle su_greatest args.(Args.m) retv.(Retv.m))
              (AFTER: ms.(ModSem.after_external) lst0 retv lst1)
            ,
              sound_state_all su0 m_arg lst1>>)
      )
      (GR: Sound.get_greatest args_tail su0)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
      (* sound_state_ex *)
      (* (PRSV: local_preservation ms sound_state_ex) *)
      (* (HD: sound_state_ex su0 lst0) *)
    :
      sound_stack su0 args m_arg ((Frame.mk ms lst0) :: tail)
  .

  Inductive sound_state (su0: Sound.t): mem -> state -> Prop :=
  | sound_state_normal
      su_tail args_tail m_tail tail
      ms lst0
      m_arg
      (GR: Sound.get_greatest args_tail su0)
      (TL: sound_stack su_tail args_tail m_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          <<SUST: sound_state_all su0 m_arg lst0>>)
      (EX: exists sound_state_ex, local_preservation ms sound_state_ex)
    :
      sound_state su0 m_arg (State ((Frame.mk ms lst0) :: tail))
  | sound_state_call
      su_tail m_tail frs
      args
      (GR: Sound.get_greatest args su0)
      (ARGS: Sound.args su0 args)
      (STK: sound_stack su_tail args m_tail frs)
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
    esplits; eauto. econs; s; eauto.
    - admit "this should hold".
    - eapply Sound.top_args.
    - econs; eauto.
  Unshelve.
    all: try exact Sound.top.
    all: try exact Mem.empty.
  Qed.

  Lemma sound_progress
        su0 st0 m_init0 tr st1
        (SUST: sound_state su0 m_init0 st0)
        (STEP: Step sem_src st0 tr st1)
    :
      <<SUST: exists su1 m_init1, sound_state su1 m_init1 st1>>
  .
  Proof.
    inv STEP.
    - (* CALL *)
      inv SUST. ss.
      generalize (Sound.greatest_ex args). i; des.
      exists su_gr.
      esplits; eauto.
      econs; eauto.
      { eapply Sound.greatest_spec; eauto. }
      econs; eauto.
      ii.
      dsplits; eauto.
      inv PRSV. exploit CALL; eauto. i; des.
      ii.
      assert(su_greatest = su_gr0).
      { eapply Sound.greatest_dtm; eauto. }
      clarify.
      eapply K; eauto.
    - (* INIT *)
      inv SUST. ss. des_ifs.

      esplits; eauto.
      econs; eauto.
      + ii. inv PRSV. exploit INIT0; eauto.
      + inv MSFIND. ss. rr in SIMPROG. rewrite Forall_forall in *.
        des; clarify.
        { eapply system_local_preservation. }
        u in MODSEM.
        rewrite in_map_iff in MODSEM. des; clarify.
        exploit SIMPROG.
        { admit "somehow". }
        i; des. inv H.
        admit "somehow".
      (* inv STK. *)
      (* { esplits; eauto. econs; eauto. *)
      (*   - econs; eauto. *)
      (*   - ii. inv PRSV. dsplits; eauto. *)
      (*     + ii. *)
      (*       (* exploit CALL; eauto. *) *)
      (*       admit "". *)
      (* } *)
      (* esplits; eauto. econs; eauto. econs; eauto. *)
      (* { econs; eauto. } *)
      (* i. inv PRSV. dsplits; eauto. *)
      (* ii. exploit CALL; eauto. *)
    - (* INTERNAL *)
      inv SUST. ss.
      esplits; eauto. econs; eauto.
      i. dup PRSV. inv PRSV. eapply STEP; eauto.
      + eapply HD; eauto.
      + split; ii; ModSem.tac.
    - (* RETURN *)
      inv SUST. ss. rename ms into ms_top.
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
      rp; eauto.
  Unshelve.
  Qed.
      dup PRSV. inv PRSV.
      exploit RET; ss; eauto.
      exploit K; eauto. i; des.
      eapply K0; eauto.
      exploit RET; eauto.
      { eapply HD; eauto. }
      {
      inv STK. inv TL.
      esplits; eauto. econs; eauto. econs; eauto. ss.
      assert(RETV: Sound.retv su0 retv).
      { admit "". }
      i. dup PRSV. inv PRSV.
    - 
    - (* INTERNAL *)
      inv SUST. inv STK. ss.
      esplits; eauto.
      econs; eauto.
      econs; eauto.
      ss.
      ii. dup PRSV. inv PRSV. eapply STEP; eauto.
      + eapply HD; eauto.
      + split; ii; ModSem.tac.
    - (* RETURN *)
      inv SUST. inv STK. inv TL.
      esplits; eauto. econs; eauto. econs; eauto. ss.
      assert(RETV: Sound.retv su0 retv).
      { admit "". }
      i. dup PRSV. inv PRSV.
  Qed.

End ADQSOUND.