Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import SmallstepC.
Require Import Integers.
Require Import Events.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem SimMod SimModSem SimProg (* SimLoad *) SimProg.
Require Import ModSemProps SemProps Ord.
Require Import Sound Preservation AdequacySound.
Require Import Program.

Set Implicit Arguments.






Section SIMGE.

  Context `{SM: SimMem.class}.
  Context `{SU: Sound.class}.
  Context {SS: SimSymb.class SM}.
  (* Inductive sim_gepair (sm0: SimMem.t) (ge_src ge_tgt: list ModSem.t): Prop := *)
  Inductive sim_ge (sm0: SimMem.t): Ge.t -> Ge.t -> Prop :=
  | sim_ge_src_stuck
      ge_tgt
      skenv_link_src skenv_link_tgt
    :
      sim_ge sm0 ([], skenv_link_src) (ge_tgt, skenv_link_tgt)
  | sim_ge_intro
      msps
      (SIMSKENV: List.Forall (fun msp => ModSemPair.sim_skenv msp sm0) msps)
      (SIMMSS: List.Forall (ModSemPair.sim) msps)
      ge_src ge_tgt
      (GESRC: ge_src = (map (ModSemPair.src) msps))
      (GETGT: ge_tgt = (map (ModSemPair.tgt) msps))
      skenv_link_src skenv_link_tgt
      (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm0 ss_link skenv_link_src skenv_link_tgt)
      (MFUTURE: List.Forall (fun msp => SimMem.future msp.(ModSemPair.sm) sm0) msps)
    :
      sim_ge sm0 (ge_src, skenv_link_src) (ge_tgt, skenv_link_tgt)
  (* | sim_ge_intro *)
  (*     msps *)
  (*     (SIMSKENV: List.Forall (fun msp => ModSemPair.sim_skenv msp sm0) msps) *)
  (*     (SIMMSS: List.Forall (ModSemPair.sim) msps) *)
  (*     ge_src ge_tgt *)
  (*     skenv_link_src skenv_link_tgt *)
  (*     (GESRC: ge_src = System.modsem skenv_link_src :: (map (ModSemPair.src) msps)) *)
  (*     (GETGT: ge_tgt = System.modsem skenv_link_tgt :: (map (ModSemPair.tgt) msps)) *)
  (*     ss_link *)
  (*     (SIMSYS: SimSymb.sim_skenv sm0 ss_link skenv_link_src skenv_link_tgt) *)
  (*   : *)
  (*     sim_ge sm0 ge_src ge_tgt  *)
  .



  Lemma find_fptr_owner_fsim
        sm0 ge_src ge_tgt
        (SIMGE: sim_ge sm0 ge_src ge_tgt)
        fptr_src fptr_tgt
        (SIMFPTR: SimMem.sim_val sm0 fptr_src fptr_tgt)
        ms_src
        (FINDSRC: Ge.find_fptr_owner ge_src fptr_src ms_src)
    :
      exists msp,
        <<SRC: msp.(ModSemPair.src) = ms_src>>
        /\ <<FINDTGT: Ge.find_fptr_owner ge_tgt fptr_tgt msp.(ModSemPair.tgt)>>
        /\ <<SIMMS: ModSemPair.sim msp>>
        /\ <<SIMSKENV: ModSemPair.sim_skenv msp sm0>>
        /\ <<MFUTURE: SimMem.future msp.(ModSemPair.sm) sm0>>
  .
  Proof.
    inv SIMGE.
    { inv FINDSRC; ss. }
    rewrite Forall_forall in *.
    inv FINDSRC.
    ss.
    rewrite in_map_iff in MODSEM. des. rename x into msp.
    esplits; eauto.
    clarify.
    specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS.
    specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV.

    exploit SimSymb.sim_skenv_func_bisim; try apply SIMSKENV. intro SIMFUNC; des.
    inv SIMFUNC. exploit FUNCFSIM; eauto. i; des. clear_tac. inv SIM.
    econs; eauto.
    - apply in_map_iff. esplits; eauto.

  Qed.

  Lemma msp_in_sim
        sm0 ge_src ge_tgt
        (SIMGE: sim_ge sm0 ge_src ge_tgt)
        msp
        fptr_src fptr_tgt
        (INSRC: Ge.find_fptr_owner ge_src fptr_src msp.(ModSemPair.src))
        (INTGT: Ge.find_fptr_owner ge_tgt fptr_tgt msp.(ModSemPair.tgt))
    :
      <<SIMMS: ModSemPair.sim msp>> /\ <<SIMSKENV: ModSemPair.sim_skenv msp sm0>>
  .
  Proof.
    inv INSRC. inv INTGT.
    inv SIMGE.
    { ss. }
    rewrite Forall_forall in *.
    {
    ss. rewrite in_map_iff in *. des.
  Abort.

  Theorem mfuture_preserves_sim_ge
          sm0 ge_src ge_tgt
          (SIMGE: sim_ge sm0 ge_src ge_tgt)
          sm1
          (MFUTURE: SimMem.future sm0 sm1)
    :
      <<SIMGE: sim_ge sm1 ge_src ge_tgt>>
  .
  Proof.
    inv SIMGE.
    { econs; eauto. }
    econs 2; try reflexivity; eauto.
    - rewrite Forall_forall in *. ii.
      eapply ModSemPair.mfuture_preserves_sim_skenv; eauto.
    - des. esplits; eauto. eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
    - rewrite Forall_forall in *. ii.
      etrans; eauto.
  Qed.

  (* Theorem mle_preserves_sim_ge *)
  (*         sm0 ge_src ge_tgt *)
  (*         (SIMGE: sim_ge sm0 ge_src ge_tgt) *)
  (*         sm1 *)
  (*         (MLE: SimMem.le sm0 sm1) *)
  (*   : *)
  (*     <<SIMGE: sim_ge sm1 ge_src ge_tgt>> *)
  (* . *)
  (* Proof. *)
  (*   inv SIMGE. *)
  (*   { econs; eauto. } *)
  (*   econs 2; try reflexivity; eauto. *)
  (*   - rewrite Forall_forall in *. ii. *)
  (*     eapply SimSymb.mle_preserves_sim_skenv; eauto. *)
  (*     eapply SIMSKENV; eauto. *)
  (*   - des. esplits; eauto. eapply SimSymb.mle_preserves_sim_skenv; eauto. *)
  (*   - rewrite Forall_forall in *. ii. *)
  (*     etrans; eauto. apply rtc_once. eauto. *)
  (* Qed. *)

  (* Theorem mlift_preserves_sim_ge *)
  (*         sm0 ge_src ge_tgt *)
  (*         (MWF: SimMem.wf sm0) *)
  (*         (SIMGE: sim_ge sm0 ge_src ge_tgt) *)
  (*   : *)
  (*     <<SIMGE: sim_ge (SimMem.lift sm0) ge_src ge_tgt>> *)
  (* . *)
  (* Proof. *)
  (*   inv SIMGE. *)
  (*   { econs; eauto. } *)
  (*   econs 2; try reflexivity; eauto. *)
  (*   - rewrite Forall_forall in *. ii. *)
  (*     u. *)
  (*     eapply SimSymb.mlift_preserves_sim_skenv; eauto. *)
  (*     eapply SIMSKENV; eauto. *)
  (*   - des. esplits; eauto. eapply SimSymb.mlift_preserves_sim_skenv; eauto. *)
  (*   - rewrite Forall_forall in *. ii. *)
  (*     etrans; eauto. apply rtc_once. eauto. *)
  (* Qed. *)

  (* Lemma load_modsems_sim_ge_aux *)
  (*       pp *)
  (*       (SIMPROG: ProgPair.sim pp) *)
  (*       p_src p_tgt *)
  (*       (PSRC: p_src = pp.(ProgPair.src)) *)
  (*       (PTGT: p_tgt = pp.(ProgPair.tgt)) *)
  (*       sk_link_src sk_link_tgt *)
  (*       (SKSRC: link_sk p_src = Some sk_link_src) *)
  (*       (SKTGT: link_sk p_tgt = Some sk_link_tgt) *)
  (*  : *)
  (*      (* (load_modsems (ProgPair.src pp) (Genv.globalenv sk_link_src)) = ModSemPair.src *) *)
  (*    True *)
  (* . *)
  (* Proof. *)
  (*   admit "". *)
  (* Qed. *)

  Lemma sim_ge_cons
        sm_init tl_src tl_tgt
        (SAFESRC: tl_src <> [])
        msp
        (SIMMSP: ModSemPair.sim msp)
        skenv_link_src skenv_link_tgt
        (SIMGETL: sim_ge sm_init (tl_src, skenv_link_src) (tl_tgt, skenv_link_tgt))
        (SIMSKENV: ModSemPair.sim_skenv msp sm_init)
        (MFUTURE: SimMem.future (ModSemPair.sm msp) sm_init)
    :
      <<SIMGE: sim_ge sm_init (msp.(ModSemPair.src) :: tl_src, skenv_link_src)
                      (msp.(ModSemPair.tgt) :: tl_tgt, skenv_link_tgt)>>
  .
  Proof.
    red.
    inv SIMGETL; ss.
    econstructor 2 with (msps := msp :: msps); eauto.
  Qed.

  (* Lemma sim_ge_cons *)
  (*       sm_init hd_src hd_tgt tl_src tl_tgt *)
  (*       (SAFESRC: tl_src <> []) *)
  (*       (SIMGEHD: sim_ge sm_init [hd_src] [hd_tgt]) *)
  (*       (SIMGETL: sim_ge sm_init tl_src tl_tgt) *)
  (*   : *)
  (*     <<SIMGE: sim_ge sm_init (hd_src :: tl_src) (hd_tgt :: tl_tgt)>> *)
  (* . *)
  (* Proof. *)
  (*   red. *)
  (*   inv SIMGEHD. destruct msps; ss. destruct msps; ss. clarify. inv SIMMSS. inv SIMSKENV. *)
  (*   inv SIMGETL; ss. *)
  (*   econstructor 2 with (msps := t :: msps); eauto. *)
  (*   inv MFUTURE. econs; eauto. *)
  (* Qed. *)

  Lemma to_msp_tgt
        skenv_tgt skenv_src pp sm_init
    :
          map ModSemPair.tgt (map (ModPair.to_msp skenv_src skenv_tgt sm_init) pp) =
          map (fun md => Mod.modsem md skenv_tgt) (ProgPair.tgt pp)
  .
  Proof.
    ginduction pp; ii; ss.
    f_equal. erewrite IHpp; eauto.
  Qed.

  Lemma to_msp_src
        skenv_tgt skenv_src pp sm_init
    :
          map ModSemPair.src (map (ModPair.to_msp skenv_src skenv_tgt sm_init) pp) =
          map (fun md => Mod.modsem md skenv_src) (ProgPair.src pp)
  .
  Proof.
    ginduction pp; ii; ss.
    f_equal. erewrite IHpp; eauto.
  Qed.

  Lemma to_msp_sim_skenv
        sm_init mp skenv_src skenv_tgt
        (WFSRC: SkEnv.wf skenv_src)
        (WFTGT: SkEnv.wf skenv_tgt)
        (INCLSRC: SkEnv.includes skenv_src mp.(ModPair.src).(Mod.sk))
        (INCLTGT: SkEnv.includes skenv_tgt mp.(ModPair.tgt).(Mod.sk))
        (SIMMP: ModPair.sim mp)
        ss_link
        (LESS: SimSymb.le (ModPair.ss mp) (Mod.get_sk (ModPair.src mp) (Mod.data (ModPair.src mp)))
                          (Mod.get_sk (ModPair.tgt mp) (Mod.data (ModPair.tgt mp))) ss_link)
        (SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_src skenv_tgt)
      :
        <<SIMSKENV: ModSemPair.sim_skenv (ModPair.to_msp skenv_src skenv_tgt sm_init mp) sm_init>>
  .
  Proof.
    (* inv SIMMP. specialize (SIMMS skenv_src skenv_tgt). *)
    u.
    econs; ss; eauto; cycle 1.
    { rewrite ! Mod.get_modsem_skenv_link_spec. eauto. }
    eapply SimSymb.sim_skenv_monotone; revgoals.
    - eapply Mod.get_modsem_skenv_spec.
    - eapply Mod.get_modsem_skenv_spec.
    - ss.
    - ss.
    - eauto. (* eapply SimSymb.le_refl. *)
    - apply SIMMP.
    - eauto.
    - eauto.
    - eauto.
  Qed.

  Theorem init_sim_ge_strong
          pp
          (NOTNIL: pp <> [])
          (SIMPROG: ProgPair.sim pp)
          p_src p_tgt
          (PSRC: p_src = pp.(ProgPair.src))
          (PTGT: p_tgt = pp.(ProgPair.tgt))
          sk_link_src sk_link_tgt
          ss_link
          (SSLE: Forall (fun mp => SimSymb.le (ModPair.ss mp) (ModPair.src mp) (ModPair.tgt mp) ss_link) pp)
          (SIMSK: SimSymb.sim_sk ss_link sk_link_src sk_link_tgt)
          (SKSRC: link_sk p_src = Some sk_link_src)
          (SKTGT: link_sk p_tgt = Some sk_link_tgt)
          skenv_link_src skenv_link_tgt
          (SKENVSRC: Sk.load_skenv sk_link_src = skenv_link_src)
          (SKENVTGT: Sk.load_skenv sk_link_tgt = skenv_link_tgt)
          m_src
          (LOADSRC: Sk.load_mem sk_link_src = Some m_src)
    :
      exists sm_init ss_link, <<SIMGE: sim_ge sm_init
                                              (load_genv p_src (Sk.load_skenv sk_link_src))
                                              (load_genv p_tgt (Sk.load_skenv sk_link_tgt))>>
               /\ <<MWF: SimMem.wf sm_init>>
               /\ <<LOADTGT: Sk.load_mem sk_link_tgt = Some sm_init.(SimMem.tgt)>>
               /\ <<MSRC: sm_init.(SimMem.src) = m_src>>
               /\ (<<SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_link_src skenv_link_tgt>>)
               /\ (<<INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src mp.(ModPair.src).(Mod.sk)>>)
               /\ (<<INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt mp.(ModPair.tgt).(Mod.sk)>>)
  .
  Proof.
    assert(INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src mp.(ModPair.src).(Mod.sk)).
    { ii. clarify. eapply link_includes; eauto.
      unfold ProgPair.src. rewrite in_map_iff. esplits; et. }
    assert(INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt mp.(ModPair.tgt).(Mod.sk)).
    { ii. clarify. eapply link_includes; eauto.
      unfold ProgPair.tgt. rewrite in_map_iff. esplits; et. }
    clarify.
    exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. rename sm into sm_init. clarify.
    esplits; eauto.
    unfold load_genv in *. ss.
    bar.
    assert(exists msp_sys,
              (<<SYSSRC: msp_sys.(ModSemPair.src) = System.modsem (Sk.load_skenv sk_link_src)>>)
              /\ (<<SYSTGT: msp_sys.(ModSemPair.tgt) = System.modsem (Sk.load_skenv sk_link_tgt)>>)
              /\ <<SYSSIM: ModSemPair.sim msp_sys>> /\ <<SIMSKENV: ModSemPair.sim_skenv msp_sys sm_init>>
              /\ (<<MFUTURE: SimMem.future msp_sys.(ModSemPair.sm) sm_init>>)
          ).
    { exploit SimSymb.system_sim_skenv; eauto. i; des.
      eexists (ModSemPair.mk _ _ ss_link sm_init). ss.
      esplits; eauto.
      (* eapply SimSymb.sim_skenv_func_bisim in SIMSKENV. des. *)
      (* clears sm_init; clear sm_init. *)
      - exploit system_local_preservation. intro SYSSU; des.
        econs; ss.
        { eauto. }
        ii. inv SIMSKENV0. ss.
        split; cycle 1.
        { ii; des. esplits; eauto. econs; eauto. }
        ii. sguard in SAFESRC. des. inv INITTGT.
        esplits; eauto.
        { refl. }
        { econs. }
        pfold.
        econs; eauto.
        i. split.
        { u. esplits; ii; des; ss; eauto. inv H0. }
        econs; ss; cycle 1.
        { eapply System.modsem_receptive; et. }
        ii. inv STEPSRC.
        exploit SimSymb.system_axiom; eauto.
        (* { eapply external_call_symbols_preserved; eauto. *)
        (*   symmetry. apply System.skenv_globlaenv_equiv. } *)
        i; des.
        inv SIMARGS.
        assert(SIMGE: SimSymb.sim_skenv sm_arg ss_link (System.globalenv (Sk.load_skenv sk_link_src))
                                        (System.globalenv (Sk.load_skenv sk_link_tgt))).
        { eapply SimSymb.mfuture_preserves_sim_skenv; eauto. }
        hexpl SimSymb.sim_skenv_func_bisim SIMGE0.
        inv SIMGE0. exploit FUNCFSIM; eauto. i; des. clarify.
        esplits; eauto.
        { left. apply plus_one. econs.
          - eapply System.modsem_determinate; et.
          - ss. econs; eauto.
            (* eapply external_call_symbols_preserved; eauto. *)
            (* apply System.skenv_globlaenv_equiv. *)
        }
        { eapply SimMem.unlift_spec; eauto. }
        left. pfold.
        econs 4.
        { eapply SimMem.unlift_spec; eauto. }
        { eapply SimMem.unlift_wf; eauto. }
        { econs; eauto. }
        { econs; eauto. }
        { clear - RETV. admit "ez - add as lemma in SimMem". }
    }
    des.
    rewrite <- SYSSRC. rewrite <- SYSTGT.
    eapply sim_ge_cons; ss.
    - ii. destruct pp; ss.
    - clear_until_bar. clear TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT.
      ginduction pp; ii; ss.
      unfold link_sk in *. ss.
      rename a into mp.
      destruct (classic (pp = [])).
      { clarify. ss. clear IHpp. inv SSLE. inv H2. cbn in *. clarify.
        set (skenv_src := (Sk.load_skenv (ModPair.src mp))) in *.
        set (skenv_tgt := (Sk.load_skenv (ModPair.tgt mp))) in *.
        inv SIMPROG. inv H3. rename H2 into SIMMP. inv SIMMP.
        econstructor 2 with (msps := (map (ModPair.to_msp skenv_src skenv_tgt sm_init) [mp])); eauto; ss; revgoals.
        - econs; eauto.
        - econs; eauto. eapply SIMMS; eauto.
          + eapply SkEnv.load_skenv_wf; et.
          + eapply SkEnv.load_skenv_wf; et.
        - econs; eauto. econs; ss; eauto; cycle 1.
          { unfold Mod.modsem. rewrite ! Mod.get_modsem_skenv_link_spec. eauto. }
          r. ss. eapply SimSymb.sim_skenv_monotone; eauto.
          + eapply SkEnv.load_skenv_wf.
          + eapply SkEnv.load_skenv_wf.
          + eapply Mod.get_modsem_skenv_spec.
          + eapply Mod.get_modsem_skenv_spec.
      }
      rename H into NNIL.
      apply link_list_cons_inv in SKSRC; cycle 1. { destruct pp; ss. } des. rename restl into sk_src_tl.
      apply link_list_cons_inv in SKTGT; cycle 1. { destruct pp; ss. } des. rename restl into sk_tgt_tl.
      inv SIMPROG. rename H1 into SIMMP. rename H2 into SIMPROG.
      inv SSLE. rename H1 into SSLEHD. rename H2 into SSLETL.
      unfold flip.
      Check (mp :: pp).
      set (skenv_src := (Sk.load_skenv sk_link_src)) in *.
      set (skenv_tgt := (Sk.load_skenv sk_link_tgt)) in *.
      assert(WFSRC: SkEnv.wf skenv_src).
      { eapply SkEnv.load_skenv_wf. }
      assert(WFTGT: SkEnv.wf skenv_tgt).
      { eapply SkEnv.load_skenv_wf. }
      econstructor 2 with
          (msps := (map (ModPair.to_msp skenv_src skenv_tgt sm_init) (mp :: pp))); eauto; revgoals.
      + ss. econs; eauto. rewrite Forall_forall in *. ii. rewrite in_map_iff in H. des. clarify. ss. refl.
      + ss. f_equal. rewrite to_msp_tgt; ss.
      + ss. f_equal. rewrite to_msp_src; ss.
      + ss. econs; ss; eauto.
        * eapply SIMMP; eauto.
        * rewrite Forall_forall in *.
          i. apply in_map_iff in H. des.
          specialize (SIMPROG x0). special SIMPROG; ss. clarify. eapply SIMPROG; eauto.
      + ss. econs; ss; eauto.
        * eapply to_msp_sim_skenv; eauto.
        * rewrite Forall_forall in *. i. rewrite in_map_iff in *. des. clarify.
          eapply to_msp_sim_skenv; eauto.
  Unshelve.
    all: try apply idx_bot.
  Qed.

End SIMGE.












Section ADQMATCH.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  (* Hypothesis SIMPROG: ProgPair.sim pp. *)
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := sk_link_src.(Sk.load_skenv).
  Let skenv_link_tgt := sk_link_tgt.(Sk.load_skenv).
  Compute sem_src.(Smallstep.state).

  Print Frame.t.
  (* Record t : Type := mk { ms : ModSem.t;  lst : ModSem.state ms;  rs_init : regset } *)

  (* Interpretation: the stack called top with following regset/regset/SimMem.t as arguments. *)
  (* (SimMem.t is lifted. lifting/unlifting is caller's duty) *)
  (* Simulation can go continuation when SimMem.t bigger than argument is given, (after unlifting it) *)
  (* with after_external fed with regsets sent. *)
  Inductive lxsim_stack: SimMem.t ->
                         list Frame.t -> list Frame.t -> Prop :=
  | lxsim_stack_nil
      sm0
    :
      lxsim_stack sm0 [] []
  | lxsim_stack_cons
      tail_src tail_tgt tail_sm
      (STACK: lxsim_stack tail_sm tail_src tail_tgt)
      ms_src lst_src0
      ms_tgt lst_tgt0
      sm_at sm_arg
      (MWF: SimMem.wf sm_arg)
      (GE: sim_ge sm_at sem_src.(globalenv) sem_tgt.(globalenv))
      (MLE: SimMem.le tail_sm sm_at)
      (MLE: SimMem.le sm_at sm_arg)
      sm_init
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_init)
      sound_state_local
      (PRSV: local_preservation ms_src sound_state_local)
      (K: forall
          sm_ret retv_src retv_tgt
          (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
          (MWF: SimMem.wf sm_ret)
          (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret)
          lst_src1
          (* (SU: forall *)
          (*     su_ret *)
          (*     (LE: Sound.le su_gr su_ret) *)
          (*     (RETV: Sound.retv su_ret retv_src) *)
          (*     (MLE: Sound.mle su_gr (Args.m args) (Retv.m retv_src)) *)
          (*   , *)
          (*     exists su m_arg, sound_state_local su m_arg lst_src1) *)
          (* (SU: exists su m_arg, sound_state_local su m_arg lst_src1) *)
          (SU: exists su m_arg, sound_state_local su m_arg lst_src0)
          (AFTERSRC: ms_src.(ModSem.after_external) lst_src0 retv_src lst_src1)
        ,
          exists lst_tgt1 sm_after i1,
            (<<AFTERTGT: ms_tgt.(ModSem.after_external) lst_tgt0 retv_tgt lst_tgt1>>)
            /\
            (<<MLE: SimMem.le sm_at sm_after>>)
            /\
            (<<LXSIM: lxsim ms_src ms_tgt (fun st => exists su m_arg, sound_state_local su m_arg st)
                            tail_sm i1 lst_src1 lst_tgt1 sm_after>>))
    :
      lxsim_stack sm_init
                  ((Frame.mk ms_src lst_src0) :: tail_src)
                  ((Frame.mk ms_tgt lst_tgt0) :: tail_tgt)

  .

  Lemma lxsim_stack_le
        sm0 frs_src frs_tgt
        (SIMSTACK: lxsim_stack sm0 frs_src frs_tgt)
        sm1
        (MLE: SimMem.le sm0 sm1)
    :
      <<SIMSTACK: lxsim_stack sm1 frs_src frs_tgt>>
  .
  Proof.
    inv SIMSTACK.
    { econs 1; eauto. }
    econs 2; eauto.
    etransitivity; eauto.
  Qed.

  Inductive lxsim_lift: idx -> sem_src.(Smallstep.state) -> sem_tgt.(Smallstep.state) -> SimMem.t -> Prop :=
  | lxsim_lift_intro
      sm0
      (GE: sim_ge sm0 sem_src.(globalenv) sem_tgt.(globalenv))
      tail_src tail_tgt tail_sm
      (STACK: lxsim_stack tail_sm tail_src tail_tgt)
      (MLE: SimMem.le tail_sm sm0)
      i0
      ms_src lst_src
      ms_tgt lst_tgt
      sound_state_local
      (PRSV: local_preservation ms_src sound_state_local)
      (TOP: lxsim ms_src ms_tgt (fun st => exists su m_arg, sound_state_local su m_arg st) tail_sm
                  i0 lst_src lst_tgt sm0)
    :
      lxsim_lift i0
                 (State ((Frame.mk ms_src lst_src) :: tail_src))
                 (State ((Frame.mk ms_tgt lst_tgt) :: tail_tgt))
                 sm0
  | lxsim_lift_callstate
       sm_arg
       (GE: sim_ge sm_arg sem_src.(globalenv) sem_tgt.(globalenv))
       tail_src tail_tgt tail_sm
       (STACK: lxsim_stack tail_sm tail_src tail_tgt)
       (MLE: SimMem.le tail_sm sm_arg)
       (MWF: SimMem.wf sm_arg)
       args_src args_tgt
       (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
    :
      lxsim_lift idx_bot
                 (Callstate args_src tail_src)
                 (Callstate args_tgt tail_tgt)
                 sm_arg
  .

End ADQMATCH.













Section ADQINIT.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis NOTNIL: pp <> [].
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (lxsim_lift pp).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.
  Print Sem.initial_state.

  Let skenv_link_src := sk_link_src.(Sk.load_skenv).
  Let skenv_link_tgt := sk_link_tgt.(Sk.load_skenv).

  Theorem init_lxsim_lift_forward
          st_init_src
          (INITSRC: sem_src.(Smallstep.initial_state) st_init_src)
    :
      exists idx st_init_tgt sm_init,
        <<INITTGT: sem_tgt.(Dinitial_state) st_init_tgt>>
        /\ (<<SIM: lxsim_lift idx st_init_src st_init_tgt sm_init>>)
        /\ (<<INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src mp.(ModPair.src).(Mod.sk)>>)
        /\ (<<INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt mp.(ModPair.tgt).(Mod.sk)>>)
  .
  Proof.
    ss.
    inv INITSRC; ss. clarify.
    rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC.

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    exploit init_sim_ge_strong; eauto. i; des. clarify.
    ss. des_ifs.

    set(Args.mk (Genv.symbol_address (Sk.load_skenv sk_link_src) (prog_main sk_link_src) Ptrofs.zero)
                [] sm_init.(SimMem.src)) as args_src in *.
    set(Args.mk (Genv.symbol_address (Sk.load_skenv sk_link_tgt) (prog_main sk_link_tgt) Ptrofs.zero)
                [] sm_init.(SimMem.tgt)) as args_tgt in *.
    assert(SIMARGS: SimMem.sim_args args_src args_tgt sm_init).
    { econs; ss; eauto.
      - admit "ez - strengthen sim_skenv specs".
      - rewrite <- SimMem.sim_val_list_spec. econs; eauto. }

    esplits; eauto.
    - econs; ss; cycle 1.
      { ii. eapply initial_state_determ; ss; eauto. }
      econs; eauto; cycle 1.
      { clear - SIMPROG WF. i. subst_locals. u in *. rewrite in_map_iff in *. des. clarify.
        rewrite Forall_forall in *. exploit SIMPROG; et. intro SIM.
        inv SIM.
        eapply SimSymb.sim_sk_preserves_wf; et. eapply WF; et. rewrite in_map_iff. esplits; et.
      }
      apply_all_once SimSymb.sim_skenv_func_bisim. des. inv SIMSKENV.
      exploit FUNCFSIM; eauto.
      { apply SIMARGS. }
      i; des. clarify.
    - econs; eauto.
      + ss. folder. des_ifs.
      + hnf. econs; eauto.
      + reflexivity.
    (* exploit SIM; eauto. i; des. *)
    (* bar. *)
    (* exploit INITPROGRESS; eauto. i; des. *)
    (* bar. *)
    (* exploit find_fptr_owner_fsim; eauto. { econs; eauto. } i; des. *)

    (* remember (ModSemPair.src msp) as srcm. revert Heqsrcm. clarify. i. clears msp. *)

    (* inv SIMMS. inv FINDTGT. *)
    (* exploit SIM; eauto. i; des. *)
    (* exploit INITPROGRESS; eauto. i; des. *)
    (* exploit INITSIM; eauto. i; des. *)
    (* assert(st_init_src = st_init_src0). *)
    (* { eapply ModSem.initial_frame_dtm; eauto. } *)
    (* clarify. *)

    (* esplits; eauto. *)
    (* - econs; ss; cycle 1. *)
    (*   { ii. eapply initial_state_determ; ss; eauto. } *)
    (*   econs; eauto. *)
    (*   econs; eauto. *)
    (* - econs; eauto. *)
    (*   + ss. des_ifs. *)
    (*   + econs; eauto. *)
    (*   + reflexivity. *)
  Qed.

End ADQINIT.




Section ADQSTEP.

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

  Let lxsim_lift := (lxsim_lift pp).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := sk_link_src.(Sk.load_skenv).
  Let skenv_link_tgt := sk_link_tgt.(Sk.load_skenv).
  Hypothesis (INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src mp.(ModPair.src).(Mod.sk)).
  Hypothesis (INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt mp.(ModPair.tgt).(Mod.sk)).

  Theorem lxsim_lift_xsim
          i0 st_src0 st_tgt0 sm0
          (LXSIM: lxsim_lift i0 st_src0 st_tgt0 sm0)
          (SUST: __GUARD__ (exists su0 m_arg, sound_state pp su0 m_arg st_src0))
    :
      <<XSIM: xsim sem_src sem_tgt ord i0 st_src0 st_tgt0>>
  .
  Proof.
    generalize dependent sm0.
    generalize dependent st_src0.
    generalize dependent st_tgt0.
    generalize dependent i0.
    pcofix CIH. i. pfold.
    inv LXSIM; ss; cycle 1.
    { (* init *)
      folder.
      des_ifs. right.
      econs; eauto.
      { i. ss. inv FINALTGT. }
      i.
      econs; eauto; cycle 1.
      { ii.
        specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
        - inv SAFESRC.
        - des_ifs. right. inv SAFESRC.
          exploit find_fptr_owner_fsim; eauto. { apply SIMARGS. } i; des. clarify.
          inv SIMMS.
          inv MSFIND. inv FINDTGT.
          exploit SIM; eauto. i; des.
          exploit INITPROGRESS; eauto. i; des.
          esplits; eauto.
          econs; eauto.
          econs; eauto.
      }
      i. inv STEPTGT.
      specialize (SAFESRC _ (star_refl _ _ _)). des.
      { inv SAFESRC. }
      bar.
      inv SAFESRC.
      ss. des_ifs.
      bar.
      exploit find_fptr_owner_fsim; eauto. { apply SIMARGS. } i; des. clarify.
      exploit find_fptr_owner_determ; ss; eauto.
      { rewrite Heq. apply FINDTGT. }
      { rewrite Heq. apply MSFIND. }
      i; des. clarify.

      (* revert_until_bar. *)
      (* on_last_hyp ltac:(fun H => clear H). *)
      (* clear_until_bar. *)
      (* on_last_hyp ltac:(fun H => clear H). *)
      (* i. *)

      inv SIMMS.
      specialize (SIM sm0).
      inv MSFIND. inv MSFIND0.
      exploit SIM; eauto. i; des.

      exploit INITBSIM; eauto. i; des.
      clears st_init0; clear st_init0.

      esplits; eauto.
      - left. apply plus_one. econs; eauto. econs; eauto.
      - right. eapply CIH.
        { unsguard SUST. unfold __GUARD__. des.
          eapply sound_progress; eauto.
          ss. folder. des_ifs. econs 2; eauto. econs; eauto.
        }
        instantiate (1:= sm_init).
        econs; try apply SIM0; eauto.
        + ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once. eauto.
        + eapply lxsim_stack_le; eauto.

    }

    folder.
    rewrite LINKSRC in *. rewrite LINKTGT in *.
    punfold TOP. inv TOP.


    - (* fstep *)
      left.
      exploit SU0.
      { unsguard SUST. des. inv SUST.
        simpl_depind. clarify. specialize (HD sound_state_local). esplits; eauto. eapply HD; eauto. }
      i; des. clear SU0.
      econs; ss; eauto.
      + ii. des. inv FINALSRC; ss. exfalso. eapply SAFESRC0. u. eauto.
      + inv FSTEP.
        * econs 1; cycle 1.
          { eapply lift_receptive_at; eauto. }
          ii. ss. rewrite LINKSRC in *.
          des.
          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. eapply SAFESRC; eauto. }
          { exfalso. eapply SAFESRC0. u. eauto. }
          exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_tgt st_tgt1) :: tail_tgt)).
          esplits; eauto.
          { des.
            - left. eapply lift_dplus; eauto.
            - right. esplits; eauto. eapply lift_dstar; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto.
          { unsguard SUST. des_safe. eapply sound_progress; eauto.
            eapply lift_step; eauto. }
          econs; eauto.
          { ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once; eauto. }
          etransitivity; eauto.
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_dstar; eauto. }
          right. eapply CIH; eauto. econs; eauto. folder. ss; des_ifs.


    - (* bstep *)
      right. ss.
      econs; ss; eauto.
      + ii. inv FINALTGT. ss. ModSem.tac.
      + ii.
        inv BSTEP.
        * econs 1; eauto; cycle 1.
          { ii. right. des. esplits; eauto. eapply lift_step; eauto. }
          ii. inv STEPTGT; ModSem.tac.
          ss. exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_src st_src1) :: tail_src)).
          esplits; eauto.
          { des.
            - left. eapply lift_plus; eauto.
            - right. esplits; eauto. eapply lift_star; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto.
          { unsguard SUST. des_safe. destruct H.
            - eapply sound_progress_plus; eauto.
              eapply lift_plus; eauto.
            - des_safe. eapply sound_progress_star; eauto.
              eapply lift_star; eauto.
          }
          econs; eauto.
          { folder. ss; des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once; eauto. }
          etransitivity; eauto.
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_star; eauto. }
          right. eapply CIH; eauto.
          { unsguard SUST. des_safe.
            eapply sound_progress_star; eauto.
            eapply lift_star; eauto.
          }
          econs; eauto. folder. ss; des_ifs.


    - (* call *)
      left.
      econs; eauto.
      { ii. inv FINALSRC. ss. ModSem.tac. }
      econs; eauto; cycle 1.
      { eapply lift_receptive_at. eapply at_external_receptive_at; et. }
      i.
      inv STEPSRC; ss; ModSem.tac.
      des_ifs.
      hexploit1 SU0.
      { unsguard SUST. des_safe. inv SUST. simpl_depind. clarify.
        esplits. eapply HD; eauto. }
      rename SU0 into CALLFSIM.

      exploit CALLFSIM; eauto.
      (* { clear - GE. inv GE. des. ss. eapply SimSymb.sim_skenv_func_bisim; eauto. } *)
      i; des.
      esplits; eauto.
      + left. apply plus_one.
        econs; ss; eauto.
        { eapply lift_determinate_at; et. eapply at_external_determinate_at; et. }
        des_ifs.
        econs 1; eauto.
      + right. eapply CIH; eauto.
        { unsguard SUST. des_safe. eapply sound_progress; eauto.
          ss. folder. des_ifs_safe. econs; eauto. }
        {
          instantiate (1:= (SimMem.lift sm_arg)).
          econs 2; eauto.
          * ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto.
            econs 2.
            { left. et. }
            econs 2; et.
          * instantiate (1:= (SimMem.lift sm_arg)).
            econs; [eassumption|..]; revgoals.
            { ii. exploit K; eauto.
              (* { unsguard SUST. des_safe. inv SUST. simpl_depind. clarify. *)
              (*   dup PRSV. inv PRSV. *)
              (*   exploit CALL; eauto. *)
              (*   { eapply HD; eauto. } *)
              (*   i; des. esplits. eapply K0; eauto. *)

              (* } *)
              i; des_safe. pclearbot. esplits; try apply LXSIM; eauto. }
            { ss. }
            { reflexivity. }
            { et. }
            { et. }
            { ss. folder. des_ifs. }
            { eauto. }
          * reflexivity.
          * eapply SimMem.lift_wf; eauto.
          * inv SIMARGS. econs; ss; eauto.
            { eapply SimMem.lift_sim_val; eauto. }
            { admit "ez - eapply SimMem.lift_sim_val_list; eauto.". }
            { erewrite SimMem.lift_src. ss. }
            { erewrite SimMem.lift_tgt. ss. }
        }


    - (* return *)
      left.
      econs; eauto.
      { ii. ss. inv FINALSRC0. ss. determ_tac ModSem.final_frame_dtm. clear_tac.
        inv STACK.
        econs; ss; eauto.
        - econs; ss; eauto.
          admit "ez - obligate to SimMem.val".
        - i. inv FINAL0; inv FINAL1; ss.
          exploit ModSem.final_frame_dtm; [apply FINAL|apply FINAL0|..]. i; clarify.
          congruence.
        - ii. des_ifs.
          inv H; ss; ModSem.tac.
      }
      econs; eauto; cycle 1.
      { eapply lift_receptive_at. eapply final_frame_receptive_at; et. }
      i. ss. des_ifs.
      inv STEPSRC; ModSem.tac. ss.
      inv STACK; ss. folder. des_ifs.
      determ_tac ModSem.final_frame_dtm. clear_tac.
      exploit K; try apply SIMRETV; eauto.
      { etransitivity; eauto. }
      {
        unsguard SUST. des_safe. inv SUST. simpl_depind. clarify.
        inv TL. simpl_depind. clarify.
        esplits; eauto. eapply HD0; eauto.
      }
      i; des.
      esplits; eauto.
      + left. apply plus_one.
        econs; eauto.
        { eapply lift_determinate_at. eapply final_frame_determinate_at; et. }
        econs 4; ss; eauto.
      + right. eapply CIH; eauto.
        { unsguard SUST. des_safe. eapply sound_progress; eauto.
          ss. folder. des_ifs_safe. econs; eauto. }
        instantiate (1:= sm_after).
        econs; ss; cycle 3.
        { eauto. }
        { eauto. }
        { folder. des_ifs. eapply mfuture_preserves_sim_ge; et. econs 2; et. }
        { eauto. }
        { etrans; eauto. }
  Qed.

End ADQSTEP.




Section ADQ.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Theorem adequacy_local
    :
      mixed_simulation sem_src sem_tgt
  .
  Proof.
    subst_locals.
    econstructor 1 with (order := ord); eauto.
    econs; eauto.
    { eapply wf_ord; eauto. }
    destruct (classic (pp <> [])); cycle 1.
    { apply NNPP in H. clarify.
      ss.
      econs; eauto.
      ii. ss. inv INITSRC. ss.
    }
    rename H into NOTNIL.
    econs 1; ss; eauto.
    ii.
    inv INITSRC.
    exploit sim_link_sk; eauto. i; des.
    exploit init_lxsim_lift_forward; eauto. { econs; eauto. } i; des.
    hexploit lxsim_lift_xsim; eauto.
    exploit sound_init; eauto.
    { ss. econs; eauto. }
    i; des. rr. esplits; eauto.
  Unshelve.
    all: ss.
  Qed.

End ADQ.
