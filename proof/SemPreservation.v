Require Import CoqlibC.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Smallstep.
Require Import Simulation.
Require Import Integers.
Require Import EventsC.
Require Import MapsC.
Require Import BehaviorsC.

Require Import ModSem Mod Sem.

Require Import Any.

Set Implicit Arguments.



Module SemPrsv.
Section PRSV.

  Local Open Scope pair_scope.

  Theorem sound_genv: forall
      p sk_link mss
      (LINK: link_sk p = Some sk_link)
      (MSS: (Sem.sem p).(Smallstep.globalenv)#1 = mss)
    ,
      (<<NTHIDX: forall
          n ms
          (NTH: nth_error mss n = Some ms)
        ,
          (<<IDX: ms.(ModSem.midx) = n>>)>>)
      /\
      (<<IDXNTH: forall
          n ms
          (IN: In ms mss)
          (IDX: ms.(ModSem.midx) = n)
        ,
          (<<NTH: nth_error mss n = Some ms>>)>>)
      /\
      (<<UNIQ: forall
          ms0 ms1
          (IN0: In ms0 mss)
          (IN1: In ms1 mss)
          (IDX: ms0.(ModSem.midx) = ms1.(ModSem.midx))
        ,
          ms0 = ms1>>)
      (* /\ *)
      (* (<<FIND: forall *)
      (*     n ms *)
      (*     (FIND: find (fun ms => (ms.(ModSem.midx) =? n)%nat) mss = Some ms) *)
      (*   , *)
      (*     (<<NTH: nth_error mss n = Some ms>>)>>) *)
  .
  Proof.
    ii. dsplits.
    -
      ii. des. subst mss. ss. des_ifs.
      destruct n; ss; clarify.
      clear - NTH.
      unfold load_modsems in *.
      rewrite Midx.nth_error_mapi_iff in *. des. clarify.
      eapply Mod.get_modsem_midx_spec; ss.
    -
      ii. des. subst mss. ss. des_ifs.
      unfold load_genv, load_modsems in *. ss.
      destruct (ModSem.midx ms) eqn:T; ss.
      { des; ss; clarify. rewrite Midx.in_mapi_iff in IN. des; ss. clarify.
        unfold Mod.modsem in *. rewrite Mod.get_modsem_midx_spec in T. xomega. }
      des; ss; clarify.
      rewrite Midx.in_mapi_iff in IN. des; ss. clarify.
      unfold Mod.modsem in *. rewrite Mod.get_modsem_midx_spec in T. clarify.
      eapply Midx.nth_error_mapi_iff. esplits; eauto.
    -
      ii. des. subst mss. ss. des_ifs.
      exploit SPLITHINT0; try apply IN0; eauto. intro T0.
      exploit SPLITHINT0; try apply IN1; eauto. intro T1.
      des; clarify.
  Qed.

  Variable p: program.

  (* Variable sk_link: Sk.t. *)
  (* Hypothesis LINK: (link_sk p) = Some sk_link. *)
  (* Let skenv_link := (Sk.load_skenv sk_link). *)
  Let sem := Sem.sem p.

  Definition frames (st: state): list Frame.t :=
    match st with
    | Callstate _ frs _ => frs
    | State frs _ => frs
    end
  .

  Definition sound_state (st: state): Prop :=
    (<<WTY: forall
        n ms
        (NTH: nth_error (sem.(globalenv) #1) n = Some ms)
      ,
        (<<TY: projT1 ((get_ohs st) n) = ms.(ModSem.owned_heap)>>)>>)
    /\
    (<<LINK: exists sk_link, link_sk p = Some sk_link>>)
    /\
    (<<FRAMES: Forall (fun fr => In fr.(Frame.ms) (sem.(globalenv) #1)) (frames st)>>)
  .

  Theorem sound_initial
          st
          (INIT: sem.(Smallstep.initial_state) st)
    :
      <<SS: sound_state st>>
  .
  Proof.
    inv INIT. rr. ss.
    split; eauto.
    des_ifs. ss.
    ii.
    generalize sound_genv; intro SG.
    exploit SG; ss; eauto.
    intro T. des. des_ifs.
    clear SG.
    exploit NTHIDX; eauto. intro T; des. clarify.
    unfold load_owned_heaps. des_ifs; cycle 1.
    {
      exfalso. folder.
      clear - NTH Heq.
      exploit nth_error_Some. rewrite NTH. intro Q. ss.
      desH Q. clear Q0. exploit Q; eauto. { ss. } intro QQ.
      erewrite nth_error_None in *; eauto. ss. xomega.
    }
    unfold upcast. ss.
    f_equal.
    clarify.
  Qed.

  Theorem sound_progress
          st0 tr st1
          (SS: sound_state st0)
          (STEP: Step sem st0 tr st1)
    :
      <<SS: sound_state st1>>
  .
  Proof.
    generalize (sound_genv p); intro SG.
    inv STEP; ss.
    - (* call *)
      rr in SS; des. rr; ss; des_ifs.
      split; eauto. ii.
      unfold Midx.update. des_ifs.
      + exploit SG; ss; eauto. intro T. des. ss.
        exploit nth_error_In; eauto. intro IN.
        r. f_equal. eapply UNIQ; eauto.
        { rewrite Forall_forall in *.
          eapply FRAMES; ss; eauto. }
        exploit NTHIDX; eauto.
      + eapply WTY; eauto.
    - (* init *)
      rr in SS; des. rr; ss; des_ifs.
      esplits; eauto.
      econs; ss; eauto.
      inv MSFIND. ss.
    - (* internal *)
      rr in SS; des. rr; ss; des_ifs.
      esplits; eauto.
      inv FRAMES.
      econs; ss; eauto.
    - (* return *)
      rr in SS; des. rr; ss; des_ifs.
      esplits; eauto; cycle 1.
      { inv FRAMES. inv H2. econs; eauto. }
      ii.
      unfold Midx.update. des_ifs.
      + exploit SG; ss; eauto. intro T. des. ss.
        exploit nth_error_In; eauto. intro IN.
        f_equal. eapply UNIQ; eauto.
        { rewrite Forall_forall in *.
          eapply FRAMES; ss; eauto. }
        exploit NTHIDX; eauto.
      + eapply WTY; eauto.
  Qed.

End PRSV.
End SemPrsv.
