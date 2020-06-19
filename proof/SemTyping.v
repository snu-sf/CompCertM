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



Local Transparent upcast.

Section PRSV.

  Local Open Scope pair_scope.

  Let sound_genv: forall
      p sk_link mss
      (LINK: link_sk p = Some sk_link)
      (MSS: (Sem.sem p).(Smallstep.globalenv) = mss)
      (UNIQ: Midx.NoDup (map ModSem.midx mss))
    ,
      (* (<<NTHIDX: forall *)
      (*     n ms *)
      (*     (NTH: nth_error mss n = Some ms) *)
      (*   , *)
      (*     (<<IDX: ms.(ModSem.midx) = n>>)>>) *)
      (* /\ *)
      (* (<<IDXNTH: forall *)
      (*     n ms *)
      (*     (IN: In ms mss) *)
      (*     (IDX: ms.(ModSem.midx) = n) *)
      (*   , *)
      (*     (<<NTH: nth_error mss n = Some ms>>)>>) *)
      (* /\ *)
      (<<UNIQ: forall
          ms0 ms1 mi
          (IN0: In ms0 mss)
          (IN1: In ms1 mss)
          (IDX0: ms0.(ModSem.midx) = Some mi)
          (IDX1: ms1.(ModSem.midx) = Some mi)
        ,
          ms0 = ms1>>)
      /\
      (<<UNIQ: forall
          ms0 ms1
          (IN0: In ms0 mss)
          (IN1: In ms1 mss)
          (IDX: ms0.(ModSem.midx) = ms1.(ModSem.midx))
        ,
          ms0.(ModSem.owned_heap) = ms1.(ModSem.owned_heap)>>)
      /\
      (<<MD: forall
          ms
          (IN: In ms mss)
        ,
          (<<SYS: ms = System.modsem (Sk.load_skenv sk_link)>>) \/
          (<<MD: exists md, (<<IN: In md p>>) /\ (<<MS: ms = Mod.modsem md (Sk.load_skenv sk_link)>>)>>)>>)
  .
  Proof.
    ii. dsplits; ii.
    (* - *)
    (*   ii. des. subst mss. ss. des_ifs. *)
    (*   destruct n; ss; clarify. *)
    (*   clear - NTH. *)
    (*   unfold load_modsems in *. *)
    (*   rewrite Midx.nth_error_mapi_iff in *. des. clarify. *)
    (*   eapply Mod.get_modsem_midx_spec; ss. *)
    (* - *)
    (*   ii. des. subst mss. ss. des_ifs. *)
    (*   unfold load_genv, load_modsems in *. ss. *)
    (*   destruct (ModSem.midx ms) eqn:T; ss. *)
    (*   { des; ss; clarify. rewrite Midx.in_mapi_iff in IN. des; ss. clarify. *)
    (*     unfold Mod.modsem in *. rewrite Mod.get_modsem_midx_spec in T. xomega. } *)
    (*   des; ss; clarify. *)
    (*   rewrite Midx.in_mapi_iff in IN. des; ss. clarify. *)
    (*   unfold Mod.modsem in *. rewrite Mod.get_modsem_midx_spec in T. clarify. *)
    (*   eapply Midx.nth_error_mapi_iff. esplits; eauto. *)
    (* - *)
    (*   ii. des. subst mss. ss. des_ifs. *)
    (*   exploit SPLITHINT0; try apply IN0; eauto. intro T0. *)
    (*   exploit SPLITHINT0; try apply IN1; eauto. intro T1. *)
    (*   des; clarify. *)
    - ss. rewrite LINK in *. clear LINK. ss. clarify.
      ss. des; clarify; eauto. abstr (load_modsems p (Sk.load_skenv sk_link)) mss.
      unfold Midx.NoDup in *. ss. clear_tac.
      move ms0 at top. move ms1 at top.
      ginduction mss; ii; ss. des_ifs.
      + inv UNIQ. unfold id in *. des; clarify.
        * exfalso. eapply H1. eapply in_filter_map_iff; eauto. esplits; eauto.
          rewrite in_map_iff. exists ms1. esplits; eauto. congruence.
        * exfalso. eapply H1. eapply in_filter_map_iff; eauto. esplits; eauto.
          rewrite in_map_iff. exists ms0. esplits; eauto.
        * exploit (IHmss ms0 ms1); eauto.
      + unfold id in *. des; clarify. eapply IHmss; eauto.
    - destruct (ms0.(ModSem.midx)) eqn:T.
      { exploit (SPLITHINT ms0 ms1); et. i; clarify. }
      erewrite ms0.(ModSem.midx_none); eauto with congruence.
      erewrite ms1.(ModSem.midx_none); eauto with congruence.
    - clarify. ss. des_ifs. ss. des; ss; et.
      unfold load_modsems, flip in *. rewrite in_map_iff in *. des; clarify.
      right. esplits; et.
  Qed.

  Variable p: program.

  (* Variable sk_link: Sk.t. *)
  (* Hypothesis LINK: (link_sk p) = Some sk_link. *)
  (* Let skenv_link := (Sk.load_skenv sk_link). *)
  Let sem := Sem.sem p.

  Definition get_frames (st: state): list Frame.t :=
    match st with
    | Callstate _ frs _ => frs
    | State frs _ => frs
    end
  .

  Definition sound_state (st: state): Prop :=
    (* (<<WTY: forall *)
    (*     n ms *)
    (*     (NTH: nth_error (sem.(globalenv) #1) n = Some ms) *)
    (*   , *)
    (*     (<<TY: projT1 ((get_ohs st) n) = ms.(ModSem.owned_heap)>>)>>) *)
    (* /\ *)
    (<<WTY: forall
        ms
        (IN: In ms (sem.(globalenv)))
      ,
        (<<TY: projT1 (Midx.get (get_ohs st) ms.(ModSem.midx)) = ms.(ModSem.owned_heap)>>)>>)
    /\
    (<<WTYNONE: (Midx.get (get_ohs st) None) = upcast tt>>)
    /\
    (<<LINK: exists sk_link, link_sk p = Some sk_link>>)
    /\
    (<<FRAMES: Forall (fun fr => In fr.(Frame.ms) (sem.(globalenv))) (get_frames st)>>)
    /\
    (* (<<NTHIDX: forall *)
    (*     n ms *)
    (*     (NTH: nth_error (sem.(globalenv) #1) n = Some ms) *)
    (*   , *)
    (*     (<<IDX: ms.(ModSem.midx) = n>>)>>) *)
    (* /\ *)
    (* (<<IDXNTH: forall *)
    (*     n ms *)
    (*     (IN: In ms (sem.(globalenv) #1)) *)
    (*     (IDX: ms.(ModSem.midx) = n) *)
    (*   , *)
    (*     (<<NTH: nth_error (sem.(globalenv) #1) n = Some ms>>)>>) *)
    (* /\ *)
    (* (<<UNIQ: forall *)
    (*     ms0 ms1 *)
    (*     (IN0: In ms0 (sem.(globalenv) #1)) *)
    (*     (IN1: In ms1 (sem.(globalenv) #1)) *)
    (*     (IDX: ms0.(ModSem.midx) = ms1.(ModSem.midx)) *)
    (*   , *)
    (*     ms0 = ms1>>) *)
    (<<UNIQ: forall
        ms0 ms1 mi
        (IN0: In ms0 (sem.(globalenv)))
        (IN1: In ms1 (sem.(globalenv)))
        (IDX0: ms0.(ModSem.midx) = Some mi)
        (IDX1: ms1.(ModSem.midx) = Some mi)
      ,
        ms0 = ms1>>)
    /\
    (<<UNIQ: forall
          ms0 ms1
          (IN0: In ms0 (sem.(globalenv)))
          (IN1: In ms1 (sem.(globalenv)))
          (IDX: ms0.(ModSem.midx) = ms1.(ModSem.midx))
        ,
          ms0.(ModSem.owned_heap) = ms1.(ModSem.owned_heap)>>)
    /\
    (<<MD: forall
          sk_link ms
          (IN: In ms (sem.(globalenv)))
          (LINK: link_sk p = Some sk_link)
        ,
          (<<SYS: ms = System.modsem (Sk.load_skenv sk_link)>>) \/
          (<<MD: exists md, (<<IN: In md p>>) /\ (<<MS: ms = Mod.modsem md (Sk.load_skenv sk_link)>>)>>)>>)
  .

  Lemma sound_initial_aux
        mss0 mss1
        ohs0 ohs1
        (* (DISJ: Midx.NoDup (map ModSem.midx (mss0 ++ (rev mss1)))) *)
        (UNIQ: forall
            ms0 ms1 mi
            (IN0: In ms0 (mss0 ++ (rev mss1)))
            (IN1: In ms1 (mss0 ++ (rev mss1)))
            (IDX0: ms0.(ModSem.midx) = Some mi)
            (IDX1: ms1.(ModSem.midx) = Some mi)
          ,
            ms0 = ms1)
        (LOAD: fold_left (fun s i => Midx.update s i.(ModSem.midx) (upcast i.(ModSem.initial_owned_heap)))
                         mss1 ohs0 = ohs1)
        (WTY: forall
            ms
            (IN: In ms (mss0))
          ,
            (<<TY: projT1 (Midx.get ohs0 ms.(ModSem.midx)) = ms.(ModSem.owned_heap)>>))
    :
      (<<WTY: forall
          ms
          (IN: In ms (mss0 ++ mss1))
        ,
          (<<TY: projT1 (Midx.get ohs1 ms.(ModSem.midx)) = ms.(ModSem.owned_heap)>>)>>)
  .
  Proof.
    clear sound_genv sem p.
    unfold load_owned_heaps in *.
    rewrite <- fold_left_rev_right in *. rewrite <- rev_involutive with (l := mss1).
    abstr (rev mss1) x. clear mss1. rename x into mss1.
    ii.
    - ginduction mss1; ii; ss; des.
      { rewrite in_app_iff in *. des; clarify; eauto. }
      destruct (classic (a = ms)).
      { clarify. unfold Midx.update. des_ifs. }
      unfold Midx.update in *. des_ifs_safe.
      des_ifs.
      { ss.
        destruct (a.(ModSem.midx)) eqn:U; ss.
        - exploit (UNIQ a ms); ss; et.
          { rewrite in_app_iff. right; ss; et. }
          { repeat rewrite in_app_iff in *; ss; des; eauto; clarify. rewrite <- in_rev in *; eauto. }
        - erewrite ms.(ModSem.midx_none); eauto with congruence.
          erewrite a.(ModSem.midx_none); eauto with congruence.
      }
      erewrite (IHmss1 mss0); et.
      { ii. eapply UNIQ; et; repeat rewrite in_app_iff in *; ss; des; eauto. }
      { repeat rewrite in_app_iff in *; ss; des; eauto; clarify. }
  Qed.

  Theorem sound_initial
          st
          (INIT: sem.(Smallstep.initial_state) st)
    :
      <<SS: sound_state st>>
  .
  Proof.
    set (mss := sem.(globalenv)) in *.
    inv INIT. rr. ss. des_ifs.
    generalize sound_genv; intro SG.
    hexploit SG; ss; eauto.
    { rewrite Heq. ss. }
    intro UNIQ. des. des_ifs.
    clear SG.
    esplits; ss; eauto.
    -
      ii.
      hexploit (Midx.list_to_set_spec2
                  (map (fun ms => (ms.(ModSem.midx), upcast (ms.(ModSem.initial_owned_heap)))) mss)); et.
      { rewrite map_map. ss. }
      { ii. rewrite in_map_iff in *. des_safe. clarify. exploit ModSem.midx_none; et. intro T; des_safe.
        instantiate (1:= upcast tt).
        clear - T.
        remember (ModSem.initial_owned_heap x) as U in *. clear HeqU.
        remember (ModSem.owned_heap x) as V in *. clear HeqV.
        subst. destruct U; ss.
      }
      { instantiate (1:= upcast ms.(ModSem.initial_owned_heap)).
        instantiate (1:= ms.(ModSem.midx)).
        ss. des; clarify; ss; et. right. rewrite in_map_iff. esplits; et.
      }
      unfold mss. intro T. unfold load_owned_heaps. subst mss. rewrite T. ss.
    -
      hexploit (Midx.list_to_set_spec2
                  (map (fun ms => (ms.(ModSem.midx), upcast (ms.(ModSem.initial_owned_heap)))) mss)); et.
      { rewrite map_map. ss. }
      { ii. rewrite in_map_iff in *. des_safe. clarify. exploit ModSem.midx_none; et. intro T; des_safe.
        clear - T.
        remember (ModSem.initial_owned_heap x) as U in *. clear HeqU.
        remember (ModSem.owned_heap x) as V in *. clear HeqV.
        subst. destruct U; ss.
      }
      { ss. left. f_equal. }

    (* hexploit (sound_initial_aux [] (Sem.sem p).(Smallstep.globalenv)#1); eauto. *)
    (* { ss. des_ifs. ii. rewrite <- in_rev in *. eauto. } *)
    (* { ii. ss. } *)
    (* intro T. i. exploit (T ms); eauto. { ss. des_ifs. } intro U. rewrite <- U. ss. des_ifs. *)
    - ii. exploit MD; et. i; des_safe; et.
  Qed.

  Theorem sound_progress
          st0 tr st1
          (SS: sound_state st0)
          (STEP: Step sem st0 tr st1)
    :
      <<SS: sound_state st1>>
  .
  Proof.
    inv STEP; ss.
    - (* call *)
      rr in SS; des. rr; ss; des_ifs.
      esplits; eauto. ii.
      unfold Midx.update. des_ifs; ss.
      + erewrite UNIQ0; eauto.
        { rewrite Forall_forall in *.
          eapply FRAMES; ss; eauto. }
      + eapply WTY; et.
      + unfold Midx.update. des_ifs; et.
        exploit ModSem.midx_none; et. intro T; des_safe.
        clear - T.
        revert oh.
        rewrite T. i. des_u; ss.
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
      { unfold Midx.update. des_ifs.
        exploit ModSem.midx_none; et. intro T; des_safe.
        clear - T.
        revert oh0.
        rewrite T. i. des_u; ss. }
      { inv FRAMES. inv H2. econs; eauto. }
      ii.
      unfold Midx.update. des_ifs; ss.
      + eapply UNIQ0; et.
        { rewrite Forall_forall in *.
          eapply FRAMES; ss; eauto. }
      + eapply WTY; eauto.
  Qed.

  Theorem sound_progress_star
          st0 tr st1
          (SS: sound_state st0)
          (STAR: Star sem st0 tr st1)
    :
      <<SS: sound_state st1>>
  .
  Proof.
    induction STAR; ii; ss.
    eapply IHSTAR. eapply sound_progress; eauto.
  Qed.

End PRSV.

Theorem preservation {p}: @preservation (sem p) (sound_state p).
Proof.
  econs.
  - ii. eapply sound_initial; eauto.
  - ii. eapply sound_progress; eauto.
Qed.
