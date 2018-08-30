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
  Inductive sound_stack (su0: Sound.t): list Frame.t -> Prop :=
  | sound_stack_nil
    :
      sound_stack su0 []
  | sound_stack_cons
      su_tail
      ms lst0 tail
      (TL: sound_stack su_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          (<<SUST: sound_state_all su0 lst0>>)
          /\
          (<<K: forall
              retv lst1
              args
              (SURETV: Sound.retv su0 retv)
              (MLE: Sound.mle su0 args.(Args.m) retv.(Retv.m))
              (AFTER: ms.(ModSem.after_external) lst0 retv lst1)
            ,
              sound_state_all su_tail lst1>>)
      )
      (* sound_state_ex *)
      (* (PRSV: local_preservation ms sound_state_ex) *)
      (* (HD: sound_state_ex su0 lst0) *)
    :
      sound_stack su0 ((Frame.mk ms lst0) :: tail)
  .

  Inductive sound_state (su0: Sound.t): state -> Prop :=
  | sound_state_normal
      su_tail ms lst0 tail
      (TL: sound_stack su_tail tail)
      (HD: forall
          sound_state_all
          (PRSV: local_preservation ms sound_state_all)
        ,
          <<SUST: sound_state_all su0 lst0>>)
    :
      sound_state su0 (State ((Frame.mk ms lst0) :: tail))
  | sound_state_call
      su_tail frs
      (STK: sound_stack su_tail frs)
      args
      (ARGS: Sound.args su0 args)
    :
      sound_state su0 (Callstate args frs)
  .

  Lemma sound_init
        st0
        (INIT: sem_src.(Smallstep.initial_state) st0)
    :
      exists su0, sound_state su0 st0
  .
  Proof.
    inv INIT.
    esplits; eauto. econs; eauto.
    - econs; eauto.
    - eapply Sound.top_args.
  Unshelve.
    all: exact Sound.top.
  Qed.

  Lemma sound_progress
        su0 st0 tr st1
        (SUST: sound_state su0 st0)
        (STEP: Step sem_src st0 tr st1)
    :
      <<SUST: exists su1, sound_state su1 st1>>
  .
  Proof.
    inv STEP.
    - (* CALL *)
      inv SUST. ss.
      assert(exists su_greatest, su_greatest.(Sound.args) args).
      { admit "". }
      des.
      exists su_greatest. econs; eauto. econs; eauto.
      ii.
      dsplits; eauto.
      inv PRSV. exploit CALL; eauto. i; des.
      assert(su_lifted = su_greatest).
      { admit "". }
      clarify.
      ii. inv PRSV.
      dup PRSV. inv PRSV. dsplits; eauto. i. exploit CALL; eauto. i; des.
    - (* INIT *)
      inv SUST. ss. des_ifs.
      inv STK.
      { esplits; eauto. econs; eauto. econs; eauto.
        - econs; eauto.
        - ii. inv PRSV. dsplits; eauto.
          + ii.
            (* exploit CALL; eauto. *)
            admit "".
      }
      esplits; eauto. econs; eauto. econs; eauto.
      { econs; eauto. }
      i. inv PRSV. dsplits; eauto.
      ii. exploit CALL; eauto.
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