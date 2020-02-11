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
Require Import SimSymb SimMem SimModUnified SimModSemUnified SimProgUnified.
Require Import ModSemProps SemProps Ord.
Require Import Sound Preservation AdequacySound.
Require Import Program RUSC.
Require Import SimModSemUnified.

Set Implicit Arguments.





Section SIMGE.

  Context `{SMOS: SimMemOhs.class}.
  Context `{SU: Sound.class}.
  Context {SS: SimSymb.class SM}.
  Inductive sim_ge (sm0: SimMem.t): Ge.t -> Ge.t -> Prop :=
  | sim_ge_src_stuck
      ge_tgt skenv_link_src skenv_link_tgt:
      sim_ge sm0 ([], skenv_link_src) (ge_tgt, skenv_link_tgt)
  | sim_ge_intro
      msps ge_src ge_tgt skenv_link_src skenv_link_tgt
      (SIMSKENV: List.Forall (fun msp => ModSemPair.sim_skenv msp sm0) msps)
      (SIMMSS: List.Forall (ModSemPair.sim) msps)
      (GESRC: ge_src = (map (ModSemPair.src) msps))
      (GETGT: ge_tgt = (map (ModSemPair.tgt) msps))
      (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm0 ss_link skenv_link_src skenv_link_tgt)
      (MFUTURE: List.Forall (fun msp => SimMem.future msp.(ModSemPair.sm) sm0) msps)
      (SESRC: List.Forall (fun ms => (ModSem.to_semantics ms).(symbolenv) = skenv_link_src) ge_src)
      (SETGT: List.Forall (fun ms => (ModSem.to_semantics ms).(symbolenv) = skenv_link_tgt) ge_tgt):
      sim_ge sm0 (ge_src, skenv_link_src) (ge_tgt, skenv_link_tgt).

  Lemma find_fptr_owner_fsim
        sm0 ge_src ge_tgt fptr_src fptr_tgt ms_src
        (SIMGE: sim_ge sm0 ge_src ge_tgt)
        (SIMFPTR: SimMem.sim_val sm0 fptr_src fptr_tgt)
        (FINDSRC: Ge.find_fptr_owner ge_src fptr_src ms_src):
      exists msp,
        <<SRC: msp.(ModSemPair.src) = ms_src>>
        /\ <<FINDTGT: Ge.find_fptr_owner ge_tgt fptr_tgt msp.(ModSemPair.tgt)>>
        /\ <<SIMMS: ModSemPair.sim msp>>
        /\ <<SIMSKENV: ModSemPair.sim_skenv msp sm0>>
        /\ <<MFUTURE: SimMem.future msp.(ModSemPair.sm) sm0>>.
  Proof.
    inv SIMGE.
    { inv FINDSRC; ss. }
    rewrite Forall_forall in *. inv FINDSRC. ss.
    rewrite in_map_iff in MODSEM. des. rename x into msp. esplits; eauto. clarify.
    specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS.
    specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV.

    exploit SimSymb.sim_skenv_func_bisim; try apply SIMSKENV. intro SIMFUNC; des.
    inv SIMFUNC. exploit FUNCFSIM; eauto. i; des. clear_tac. inv SIM. econs; eauto.
    apply in_map_iff. esplits; eauto.

  Qed.

  Theorem mfuture_preserves_sim_ge
          sm0 ge_src ge_tgt sm1
          (SIMGE: sim_ge sm0 ge_src ge_tgt)
          (MFUTURE: SimMem.future sm0 sm1):
      <<SIMGE: sim_ge sm1 ge_src ge_tgt>>.
  Proof.
    inv SIMGE.
    { econs; eauto. }
    econs 2; try reflexivity; eauto.
    - rewrite Forall_forall in *. ii. eapply ModSemPair.mfuture_preserves_sim_skenv; eauto.
    - des. esplits; eauto. eapply SimSymb.mfuture_preserves_sim_skenv; eauto.
    - rewrite Forall_forall in *. ii. etrans; eauto.
  Qed.

  Lemma sim_ge_cons
        sm_init tl_src tl_tgt msp skenv_link_src skenv_link_tgt
        (SAFESRC: tl_src <> [])
        (SIMMSP: ModSemPair.sim msp)
        (SIMGETL: sim_ge sm_init (tl_src, skenv_link_src) (tl_tgt, skenv_link_tgt))
        (SIMSKENV: ModSemPair.sim_skenv msp sm_init)
        (MFUTURE: SimMem.future (ModSemPair.sm msp) sm_init)
        (SESRC: (symbolenv (ModSemPair.src msp)) = skenv_link_src)
        (SETGT: (symbolenv (ModSemPair.tgt msp)) = skenv_link_tgt):
      <<SIMGE: sim_ge sm_init (msp.(ModSemPair.src) :: tl_src, skenv_link_src)
                      (msp.(ModSemPair.tgt) :: tl_tgt, skenv_link_tgt)>>.
  Proof. red. inv SIMGETL; ss. econstructor 2 with (msps := msp :: msps); eauto. Qed.

  Lemma to_msp_src: forall midx skenv_tgt skenv_src pp sm_init,
          map ModSemPair.src (Midx.mapi_aux (fun midx => ModPair.to_msp midx skenv_src skenv_tgt sm_init) midx pp) =
          Midx.mapi_aux (fun midx md => Mod.modsem md midx skenv_src) midx (ProgPair.src pp).
  Proof. i. ginduction pp; ii; ss. f_equal. erewrite IHpp; eauto. Qed.

  Lemma to_msp_tgt: forall midx skenv_tgt skenv_src pp sm_init,
          map ModSemPair.tgt (Midx.mapi_aux (fun midx => ModPair.to_msp midx skenv_src skenv_tgt sm_init) midx pp) =
          Midx.mapi_aux (fun midx md => Mod.modsem md midx skenv_tgt) midx (ProgPair.tgt pp).
  Proof. i. ginduction pp; ii; ss. f_equal. erewrite IHpp; eauto. Qed.

  Lemma to_msp_sim_skenv
        sm_init mp midx skenv_src skenv_tgt ss_link
        (WFSRC: SkEnv.wf skenv_src)
        (WFTGT: SkEnv.wf skenv_tgt)
        (INCLSRC: SkEnv.includes skenv_src (Mod.sk mp.(ModPair.src)))
        (INCLTGT: SkEnv.includes skenv_tgt (Mod.sk mp.(ModPair.tgt)))
        (SIMMP: ModPair.sim mp)
        (LESS: SimSymb.le (ModPair.ss mp) ss_link)
        (SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_src skenv_tgt):
        <<SIMSKENV: ModSemPair.sim_skenv (ModPair.to_msp midx skenv_src skenv_tgt sm_init mp) sm_init>>.
  Proof.
    u. econs; ss; eauto; cycle 1.
    { rewrite ! Mod.get_modsem_skenv_link_spec. eauto. }
    inv SIMMP.
    eapply SimSymb.sim_skenv_monotone; revgoals; try rewrite SKSRC; try rewrite SKTGT; try eapply Mod.get_modsem_skenv_spec; try eapply SIMMP; ss; eauto.
  Qed.

  Theorem init_sim_ge_strong
          pp p_src p_tgt ss_link skenv_link_src skenv_link_tgt m_src
          (NOTNIL: pp <> [])
          (SIMPROG: ProgPair.sim pp)
          (PSRC: p_src = (ProgPair.src pp))
          (PTGT: p_tgt = (ProgPair.tgt pp))
          (SSLE: Forall (fun mp => SimSymb.le (ModPair.ss mp) ss_link) pp)
          (SIMSK: SimSymb.wf ss_link)
          (SKSRC: link_sk p_src = Some ss_link.(SimSymb.src))
          (SKTGT: link_sk p_tgt = Some ss_link.(SimSymb.tgt))
          (SKENVSRC: Sk.load_skenv ss_link.(SimSymb.src) = skenv_link_src)
          (SKENVTGT: Sk.load_skenv ss_link.(SimSymb.tgt) = skenv_link_tgt)
          (WFSKSRC: forall mp (IN: In mp pp), Sk.wf (ModPair.src mp))
          (WFSKTGT: forall mp (IN: In mp pp), Sk.wf (ModPair.tgt mp))
          (LOADSRC: Sk.load_mem ss_link.(SimSymb.src) = Some m_src):
      exists sm_init, <<SIMGE: sim_ge sm_init
                                      (load_genv p_src (Sk.load_skenv ss_link.(SimSymb.src)))
                                      (load_genv p_tgt (Sk.load_skenv ss_link.(SimSymb.tgt)))>>
         /\ <<MWF: SimMem.wf sm_init>>
         /\ <<LOADTGT: Sk.load_mem ss_link.(SimSymb.tgt) = Some sm_init.(SimMem.tgt)>>
         /\ <<MSRC: sm_init.(SimMem.src) = m_src>>
         /\ (<<SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_link_src skenv_link_tgt>>)
         /\ (<<INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src))>>)
         /\ (<<INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt))>>)
         /\ (<<SSLE: forall mp (IN: In mp pp), SimSymb.le mp.(ModPair.ss) ss_link>>)
         /\ (<<MAINSIM: SimMem.sim_val sm_init (Genv.symbol_address skenv_link_src ss_link.(SimSymb.src).(prog_main) Ptrofs.zero)
                                             (Genv.symbol_address skenv_link_tgt ss_link.(SimSymb.tgt).(prog_main) Ptrofs.zero)>>).
  Proof.
    assert(INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src))).
    { ii. clarify. eapply link_includes; eauto.
      unfold ProgPair.src. rewrite in_map_iff. esplits; et. }
    assert(INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt))).
    { ii. clarify. eapply link_includes; eauto.
      unfold ProgPair.tgt. rewrite in_map_iff. esplits; et. }
    clarify. exploit SimSymb.wf_load_sim_skenv; eauto. i; des. rename sm into sm_init. clarify.
    esplits; eauto; cycle 1.
    { rewrite Forall_forall in *. eauto. }
    unfold load_genv in *. ss. bar.
    assert(exists msp_sys,
              (<<SYSSRC: msp_sys.(ModSemPair.src) = System.modsem 0%nat (Sk.load_skenv ss_link.(SimSymb.src))>>)
              /\ (<<SYSTGT: msp_sys.(ModSemPair.tgt) = System.modsem 0%nat (Sk.load_skenv ss_link.(SimSymb.tgt))>>)
              /\ <<SYSSIM: ModSemPair.sim msp_sys>> /\ <<SIMSKENV: ModSemPair.sim_skenv msp_sys sm_init>>
              /\ (<<MFUTURE: SimMem.future msp_sys.(ModSemPair.sm) sm_init>>)).
    { exploit SimSymb.system_sim_skenv; eauto. i; des.
      eexists (ModSemPair.mk _ _ ss_link sm_init). ss. esplits; eauto.
      - exploit system_local_preservation. intro SYSSU; des. econs.
        { ss. }
        { ss. eauto. }
        { instantiate (2:= Empty_set). ii; ss. }
        ii. inv SIMSKENV0. ss.
        split; cycle 1.
        { ii; des. inv SAFESRC. rr in SIMARGS. des. inv SIMARGS0; ss. esplits; eauto. econs; eauto. }
        ii. sguard in SAFESRC. des. inv INITTGT.
        rr in SIMARGS; des. inv SIMARGS0; ss. clarify.
        esplits; eauto.
        { refl. }
        { econs; eauto. }
        pfold.
        econs; eauto.
        i.
        econs; ss; cycle 2.
        { eapply System.modsem_receptive; et. }
        { u. esplits; ii; des; ss; eauto. inv H0. }
        ii. inv STEPSRC.
        exploit SimSymb.system_axiom; eauto; [eapply SimMemOhs.wf_proj; eauto|..];
          swap 1 3; swap 2 4.
        { econs; eauto. }
        { ss. instantiate (1:= Retv.mk _ _). ss. eauto. }
        { ss. }
        { ss. }
        i; des.
        assert(SIMGE: SimSymb.sim_skenv sm_arg ss_link (System.globalenv (Sk.load_skenv ss_link.(SimSymb.src)))
                                        (System.globalenv (Sk.load_skenv ss_link.(SimSymb.tgt)))).
        { eapply SimSymb.mfuture_preserves_sim_skenv; eauto. }
        hexpl SimSymb.sim_skenv_func_bisim SIMGE0.
        inv SIMGE0. exploit FUNCFSIM; eauto. i; des. clarify.
        assert(exists smos1, <<MLE: SimMemOhs.le sm_arg smos1>>
                                    /\ <<MWF: SimMemOhs.wf smos1>>
                                              /\ <<MEQ: SimMemOhs.sm smos1 = sm1>>).
        { admit "We need good_properties. 어디서 증명하는게 적절한 레벨인지? refactor". }
        des.
        esplits; eauto.
        { left. apply plus_one. econs.
          - eapply System.modsem_determinate; et.
          - ss. econs; eauto. }
        left. pfold.
        assert(UNIT: (cast_sigT (ohs_tgt 0%nat)) = tt).
        { clear - TYTGT. eapply cast_sigT_eq.
          destruct (ohs_tgt 0%nat) eqn:T. simpl_depind. Undo 1.
          (* IT REMOVES SOME INFORMATION!!!!!!!!! (Hypothesis T) *)
          destruct TYTGT. ss. clarify. destruct p; ss.
        }
        econs 4.
        { refl. }
        { eauto. }
        { ss. rewrite UNIT. ss. }
        { ss. rewrite UNIT. ss. }
        { inv RETV; ss. unfold Retv.mk in *. clarify. rr. esplits; eauto.
          - econs; ss; eauto.
          - admit "Somehow need to know that smos1 has same type.
See good_properties --> sm_match.
".
          - admit "Somehow need to know that smos1 has same type.
See good_properties --> sm_match.
".
        }
    }
    des. rewrite <- SYSSRC. rewrite <- SYSTGT. eapply sim_ge_cons; ss.
    - ii. destruct pp; ss.
    - clear_until_bar. clear TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT.
      ginduction pp; ii; ss. unfold link_sk in *. ss. rename a into mp. destruct (classic (pp = [])).
      { clarify. ss. clear IHpp. inv SSLE. inv H2. cbn in *. clarify.
        rename H0 into SKSRC. rename H2 into SKTGT.
        rewrite <- SKSRC in *. rewrite <- SKTGT in *.
        set (skenv_src := (Sk.load_skenv (ModPair.src mp))) in *.
        set (skenv_tgt := (Sk.load_skenv (ModPair.tgt mp))) in *.
        inv SIMPROG. inv H3. rename H2 into SIMMP. inv SIMMP.
        econstructor 2 with (msps := (map (ModPair.to_msp 1%nat skenv_src skenv_tgt sm_init) [mp])); eauto; ss; revgoals; econs; eauto.
        - u. erewrite Mod.get_modsem_skenv_link_spec; ss.
        - u. erewrite Mod.get_modsem_skenv_link_spec; ss.
        -  eapply SIMMS; eauto; eapply SkEnv.load_skenv_wf; et.
        - econs; ss; eauto; cycle 1.
          { unfold Mod.modsem. rewrite ! Mod.get_modsem_skenv_link_spec. eauto. }
          r. ss. eapply SimSymb.sim_skenv_monotone; try rewrite SKSRC0; try rewrite SKTGT0;
                   try apply SIMSKENV; try eapply SkEnv.load_skenv_wf; try eapply Mod.get_modsem_skenv_spec; eauto.
      }
      rename H into NNIL.
      apply link_list_cons_inv in SKSRC; cycle 1. { destruct pp; ss. } des. rename restl into sk_src_tl.
      apply link_list_cons_inv in SKTGT; cycle 1. { destruct pp; ss. } des. rename restl into sk_tgt_tl.
      inv SIMPROG. rename H1 into SIMMP. rename H2 into SIMPROG. inv SSLE. rename H1 into SSLEHD. rename H2 into SSLETL. unfold flip.
      set (skenv_src := (Sk.load_skenv (SimSymb.src ss_link))) in *.
      set (skenv_tgt := (Sk.load_skenv (SimSymb.tgt ss_link))) in *.
      assert(WFSRC: SkEnv.wf skenv_src).
      { eapply SkEnv.load_skenv_wf; et.
        eapply (link_list_preserves_wf_sk ((ModPair.src mp) :: (ProgPair.src pp))); et.
        - unfold link_sk. ss. eapply link_list_cons; et.
        - ii; ss. des; clarify; et. unfold ProgPair.src in *. rewrite in_map_iff in *. des. clarify. et.
      }
      assert(WFTGT: SkEnv.wf skenv_tgt).
      { eapply SkEnv.load_skenv_wf; et.
        eapply (link_list_preserves_wf_sk ((ModPair.tgt mp) :: (ProgPair.tgt pp))); et.
        - unfold link_sk. ss. eapply link_list_cons; et.
        - ii; ss. des; clarify; et. unfold ProgPair.tgt in *. rewrite in_map_iff in *. des. clarify. et.
      }
      econstructor 2 with
          (msps := (Midx.mapi_aux (fun midx => ModPair.to_msp midx skenv_src skenv_tgt sm_init) (1%nat) (mp :: pp))); eauto; revgoals.
      + rewrite Forall_forall in *. i. ss. des; clarify.
        { u. erewrite Mod.get_modsem_skenv_link_spec; ss. }
        u in H. rewrite Midx.in_mapi_aux_iff in H. des; clarify.
        { u. erewrite Mod.get_modsem_skenv_link_spec; ss. }
      + rewrite Forall_forall in *. i. ss. des; clarify.
        { u. erewrite Mod.get_modsem_skenv_link_spec; ss. }
        u in H. rewrite Midx.in_mapi_aux_iff in H. des; clarify.
        { u. erewrite Mod.get_modsem_skenv_link_spec; ss. }
      + ss. econs; eauto. rewrite Forall_forall in *. ii. rewrite Midx.in_mapi_aux_iff in H. des. clarify. ss. refl.
      + ss. unfold load_modsems. unfold Midx.mapi. ss. f_equal. rewrite to_msp_tgt; ss.
      + ss. f_equal. rewrite to_msp_src; ss.
      + ss. econs; ss; eauto.
        * eapply SIMMP; eauto.
        * rewrite Forall_forall in *. i. apply Midx.in_mapi_aux_iff in H. des.
          exploit nth_error_in; eauto. intro IN.
          specialize (SIMPROG a). special SIMPROG; ss. clarify. eapply SIMPROG; eauto.
      + ss. econs; ss; eauto.
        * eapply to_msp_sim_skenv; eauto.
        * rewrite Forall_forall in *. i. apply Midx.in_mapi_aux_iff in H. des. clarify.
          exploit nth_error_in; eauto. intro IN.
          eapply to_msp_sim_skenv; eauto.
    - rewrite SYSSRC. ss.
    - rewrite SYSTGT. ss.
  Unshelve.
    all: try apply idx_bot.
    all: try (by ii; ss).
  Qed.

End SIMGE.












Section ADQMATCH.

  Context `{SMOS: SimMemOhs.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := (Sk.load_skenv sk_link_src).
  Let skenv_link_tgt := (Sk.load_skenv sk_link_tgt).

  Inductive lxsim_stack: SimMemOhs.t ->
                         list Frame.t -> list Frame.t -> Prop :=
  | lxsim_stack_nil
      sm0:
      lxsim_stack sm0 [] []
  | lxsim_stack_cons
      tail_src tail_tgt tail_sm ms_src lst_src0 ms_tgt lst_tgt0 sm_at sm_arg sm_arg_lift sm_init sidx
      midx
      (STACK: lxsim_stack tail_sm tail_src tail_tgt)
      (MWF: SimMemOhs.wf sm_arg)
      (GE: sim_ge (SimMemOhs.sm sm_at) sem_src.(globalenv) sem_tgt.(globalenv))
      (MLE: SimMemOhs.le tail_sm sm_at)
      (MLE: SimMemOhs.le sm_at sm_arg)
      (MLELIFT: SimMemOhs.lepriv sm_arg sm_arg_lift)
      (MLE: SimMemOhs.le sm_arg_lift sm_init)
      (sound_states_local: sidx -> Sound.t -> Memory.Mem.mem -> ms_src.(ModSem.state) -> Prop)
      (PRSV: forall si, local_preservation_noguarantee ms_src (sound_states_local si))
      (K: forall sm_ret ohs_src1 retv_src (ohs_tgt1: Ohs) retv_tgt lst_src1
          (OHSWFSRC: LeibEq (projT1 (ohs_src1 midx)) ms_src.(ModSem.owned_heap))
          (OHSWFTGT: LeibEq (projT1 (ohs_tgt1 midx)) ms_tgt.(ModSem.owned_heap))
          (MLE: SimMem.le sm_arg_lift sm_ret)
          (MWF: SimMem.wf sm_ret)
          (SIMRETV: SimMem.sim_retv retv_src retv_tgt sm_ret)
          (SU: forall si, exists su m_arg, (sound_states_local si) su m_arg lst_src0)
          (AFTERSRC: ms_src.(ModSem.after_external) lst_src0 (cast_sigT (ohs_src1 midx)) retv_src lst_src1),
          exists lst_tgt1 sm_after i1,
            (<<AFTERTGT: ms_tgt.(ModSem.after_external) lst_tgt0 (cast_sigT (ohs_tgt1 midx)) retv_tgt lst_tgt1>>)
            /\ (<<MLEPUB: SimMemOhs.le sm_at sm_after>>)
            /\ (<<LXSIM: lxsim ms_src ms_tgt (fun st => forall si, exists su m_arg, (sound_states_local si) su m_arg st)
                            i1 lst_src1 lst_tgt1 sm_after>>))
      (SESRC: (ModSem.to_semantics ms_src).(symbolenv) = skenv_link_src)
      (SETGT: (ModSem.to_semantics ms_tgt).(symbolenv) = skenv_link_tgt):
      lxsim_stack sm_init
                  ((Frame.mk ms_src lst_src0) :: tail_src)
                  ((Frame.mk ms_tgt lst_tgt0) :: tail_tgt).

  Lemma lxsim_stack_le
        sm0 frs_src frs_tgt sm1
        (SIMSTACK: lxsim_stack sm0 frs_src frs_tgt)
        (MLE: SimMemOhs.le sm0 sm1):
      <<SIMSTACK: lxsim_stack sm1 frs_src frs_tgt>>.
  Proof.
    inv SIMSTACK.
    { econs 1; eauto. }
    econs 2; eauto. etransitivity; eauto.
  Qed.

  Inductive lxsim_lift: idx -> sem_src.(Smallstep.state) -> sem_tgt.(Smallstep.state) -> SimMem.t -> Prop :=
  | lxsim_lift_intro
      sm0 tail_src tail_tgt tail_sm i0 ms_src lst_src ms_tgt lst_tgt sidx ohs_src0 ohs_tgt0
      (GE: sim_ge (SimMemOhs.sm sm0) sem_src.(globalenv) sem_tgt.(globalenv))

      (STACK: lxsim_stack tail_sm tail_src tail_tgt)
      (MLE: SimMemOhs.le tail_sm sm0)
      (sound_states_local: sidx -> Sound.t -> Memory.Mem.mem -> ms_src.(ModSem.state) -> Prop)
      (PRSV: forall si, local_preservation_noguarantee ms_src (sound_states_local si))
      (TOP: lxsim ms_src ms_tgt (fun st => forall si, exists su m_arg, (sound_states_local si) su m_arg st)
                  i0 lst_src lst_tgt sm0)
      (OHSRC: ohs_src0 = sm0.(SimMemOhs.ohs_src))
      (OHTGT: ohs_tgt0 = sm0.(SimMemOhs.ohs_tgt))
      (SESRC: (ModSem.to_semantics ms_src).(symbolenv) = skenv_link_src)
      (SETGT: (ModSem.to_semantics ms_tgt).(symbolenv) = skenv_link_tgt):
      lxsim_lift i0 (State ((Frame.mk ms_src lst_src) :: tail_src) ohs_src0) (State ((Frame.mk ms_tgt lst_tgt) :: tail_tgt) ohs_tgt0) sm0
  | lxsim_lift_callstate
       sm_arg tail_src tail_tgt tail_sm args_src args_tgt ohs_src0 ohs_tgt0
       (GE: sim_ge (SimMemOhs.sm sm_arg) sem_src.(globalenv) sem_tgt.(globalenv))
       (STACK: lxsim_stack tail_sm tail_src tail_tgt)
       (MLE: SimMemOhs.le tail_sm sm_arg)
       (MWF: SimMemOhs.wf sm_arg)
       (OHSRC: ohs_src0 = sm_arg.(SimMemOhs.ohs_src))
       (OHTGT: ohs_tgt0 = sm_arg.(SimMemOhs.ohs_tgt))
       (* (SIMARGS: SimMemOhs.sim_args args_src args_tgt sm_arg) *)
       (SIMARGS: SimMem.sim_args args_src args_tgt sm_arg)
    :
      lxsim_lift idx_bot (Callstate args_src tail_src ohs_src0) (Callstate args_tgt tail_tgt ohs_tgt0) sm_arg.

End ADQMATCH.













Section ADQINIT.

  Context `{SMOMS: SimMemOhs.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis NOTNIL: pp <> [].
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (lxsim_lift pp).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := (Sk.load_skenv sk_link_src).
  Let skenv_link_tgt := (Sk.load_skenv sk_link_tgt).

  Theorem init_lxsim_lift_forward
          st_init_src
          (INITSRC: sem_src.(Smallstep.initial_state) st_init_src):
      exists idx st_init_tgt sm_init,
        <<INITTGT: sem_tgt.(Dinitial_state) st_init_tgt>>
        /\ (<<SIM: lxsim_lift sk_link_src sk_link_tgt idx st_init_src st_init_tgt sm_init>>)
        /\ (<<INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src))>>)
        /\ (<<INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt))>>).
  Proof.
    ss. inv INITSRC; ss. clarify. rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC.

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    assert(WFTGT: forall md, In md p_tgt -> <<WF: Sk.wf md >>).
    { clear - SIMPROG WF. i. subst_locals. u in *. rewrite in_map_iff in *. des. clarify.
      rewrite Forall_forall in *. exploit SIMPROG; et. intro SIM. inv SIM.
      unfold Mod.sk in *. rewrite <- SKTGT in *.
      eapply SimSymb.wf_preserves_wf; et. rewrite SKSRC in *. eapply WF; et. rewrite in_map_iff. esplits; et.
    }
    rewrite <- SKSRC in *. rewrite <- SKTGT in *.
    exploit init_sim_ge_strong; eauto.
    { ii. eapply WF; et. unfold p_src. unfold ProgPair.src. rewrite in_map_iff. et. }
    { ii. eapply WFTGT; et. unfold p_tgt. unfold ProgPair.tgt. rewrite in_map_iff. et. }
    i; des. clarify. ss. des_ifs.

    set(Args.mk (Genv.symbol_address (Sk.load_skenv (SimSymb.src ss_link)) (prog_main (SimSymb.src ss_link)) Ptrofs.zero)
                [] sm_init.(SimMem.src)) as args_src in *.
    set(Args.mk (Genv.symbol_address (Sk.load_skenv (SimSymb.tgt ss_link)) (prog_main (SimSymb.tgt ss_link)) Ptrofs.zero)
                [] sm_init.(SimMem.tgt)) as args_tgt in *.
    assert(SIMARGS: SimMem.sim_args args_src args_tgt sm_init).
    { econs; ss; eauto.
      - rewrite <- SimMem.sim_val_list_spec. econs; eauto. }

    esplits; eauto.
    - econs; ss; cycle 1.
      { ii. eapply initial_state_determ; ss; eauto. }
      econs; eauto; cycle 1.
      apply_all_once SimSymb.sim_skenv_func_bisim. des. inv SIMSKENV.
      exploit FUNCFSIM; eauto.
      i; des. clarify.
    - econs; eauto.
      + ss. folder. des_ifs.
      + hnf. econs; eauto.
      + reflexivity.
  Qed.

End ADQINIT.




Section ADQSTEP.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (lxsim_lift pp).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Let skenv_link_src := (Sk.load_skenv sk_link_src).
  Let skenv_link_tgt := (Sk.load_skenv sk_link_tgt).
  Variable ss_link: SimSymb.t.
  Hypothesis (SIMSKENV: exists sm, SimSymb.sim_skenv sm ss_link skenv_link_src skenv_link_tgt).

  Hypothesis (INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src))).
  Hypothesis (INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt))).
  Hypothesis (SSLE: forall mp (IN: In mp pp), SimSymb.le mp.(ModPair.ss) ss_link).

  Hypothesis (WFKSSRC: forall md (IN: In md (ProgPair.src pp)), <<WF: Sk.wf md >>).
  Hypothesis (WFKSTGT: forall md (IN: In md (ProgPair.tgt pp)), <<WF: Sk.wf md >>).

  Theorem lxsim_lift_xsim
          i0 st_src0 st_tgt0 sm0
          (LXSIM: lxsim_lift sk_link_src sk_link_tgt i0 st_src0 st_tgt0 sm0)
    :
      <<XSIM: xsim sem_src sem_tgt ord (sound_state pp) top1 i0 st_src0 st_tgt0>>
  .
  Proof.
    generalize dependent sm0. generalize dependent st_src0. generalize dependent st_tgt0. generalize dependent i0.
    pcofix CIH. i. pfold. inv LXSIM; ss; cycle 1.
    { (* init *)
      folder. des_ifs. right. econs; eauto.
      i. econs; eauto; cycle 1.
      { ii. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
        - inv SAFESRC.
        - des_ifs. right. inv SAFESRC.
          exploit find_fptr_owner_fsim; eauto. { eapply SimMem.sim_args_sim_fptr; eauto. } i; des. clarify.
          inv SIMMS.
          inv MSFIND. inv FINDTGT.
          exploit SIM; eauto. i; des.
          exploit INITPROGRESS; eauto. i; des.
          esplits; eauto. econs; eauto. econs; eauto.
      }
      { i. ss. inv FINALTGT. }
      i. inv STEPTGT.
      specialize (SAFESRC _ (star_refl _ _ _ _)). des.
      { inv SAFESRC. }
      bar. inv SAFESRC. ss. des_ifs.
      bar.
      exploit find_fptr_owner_fsim; eauto. { eapply SimMem.sim_args_sim_fptr; eauto. } i; des. clarify.
      exploit find_fptr_owner_determ; ss; eauto.
      { rewrite Heq. apply FINDTGT. }
      { rewrite Heq. apply MSFIND. }
      i; des. clarify.

      inv SIMMS.
      specialize (SIM sm0).
      inv MSFIND. inv MSFIND0.
      exploit SIM; eauto. i; des.

      exploit INITBSIM; eauto. i; des.
      clears st_init0; clear st_init0. esplits; eauto.
      - left. apply plus_one. econs; eauto. econs; eauto.
      - right. eapply CIH.
        instantiate (1:= sm_init). econs; try apply SIM0; eauto.
        + ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once. et.
        + etrans; eauto.
        + ss. inv GE. folder. rewrite Forall_forall in *. eapply SESRC; et.
        + ss. inv GE. folder. rewrite Forall_forall in *. eapply SETGT; et.

    }

    sguard in SESRC. sguard in SETGT. folder. rewrite LINKSRC in *. rewrite LINKTGT in *.
    punfold TOP. rr in TOP. ii. hexploit1 TOP; eauto.
    { ii. exploit SSSRC. { eapply lift_star; eauto. } intro SUST0; des. inv SUST0. des.
      simpl_depind. clarify. hexploit FORALLSU; eauto. i; des.
      specialize (H (sound_states_local si)). esplits; eauto. eapply H; eauto. }
    inv TOP.

    - (* fstep *)
      left. exploit SU0.
      { ss. }
      i; des. clear SU0. right. econs; ss; eauto.
      + rename H into FSTEP. inv FSTEP.
        * econs 1; cycle 1.
          { ii. des. inv FINALSRC; ss. exfalso. eapply SAFESRC0. u. eauto. }
          ii. ss. rewrite LINKSRC in *. des. inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. eapply SAFESRC; eauto. }
          { exfalso. eapply SAFESRC0. u. eauto. }
          exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_tgt st_tgt1) :: tail_tgt)). esplits; eauto.
          { assert(T: DPlus ms_tgt lst_tgt tr st_tgt1 \/ (lst_tgt = st_tgt1 /\ tr = E0 /\ ord i1 i0)).
            { des; et. inv STAR; et. left. econs; et. }
            clear H. des.
            - left. split; cycle 1.
              { eapply lift_receptive_at; eauto. unsguard SESRC. s. des_ifs. }
              eapply lift_dplus; eauto.
              { unsguard SETGT. ss. des_ifs. }
            - right. esplits; eauto. clarify.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto.
          econs; eauto.
          { ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once; eauto. }
          { etransitivity; eauto. }
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_dplus; eauto. { unsguard SETGT. ss. des_ifs. } }
          right. eapply CIH; eauto. instantiate (1:=sm1). econs; eauto.
          { folder. ss; des_ifs. eapply mfuture_preserves_sim_ge; eauto.
            eapply rtc_once; eauto. }
          { etrans; eauto. }

    - (* bstep *)
      right. ss. hexploit1 SU0; ss.
      assert(SAFESTEP: safe sem_src (State ({| Frame.ms := ms_src; Frame.st := lst_src |} :: tail_src))
                       -> safe_modsem ms_src lst_src).
      { eapply safe_implies_safe_modsem; eauto. }
      econs; ss; eauto.
      i. exploit SU0; eauto. intro T. clear SU0. inv T.
      + econs 1; eauto; revgoals.
        { ii. des. clear - FINALTGT PROGRESS. inv FINALTGT. ss. ModSem.tac. }
        { ii. right. des. esplits; eauto. eapply lift_step; eauto. }
        ii. inv STEPTGT; ModSem.tac. ss. exploit STEP; eauto. i; des_safe.
        exists i1, (State ((Frame.mk ms_src st_src1) :: tail_src)).
        esplits; eauto.
        { des.
          - left. eapply lift_plus; eauto.
          - right. esplits; eauto. eapply lift_star; eauto.
        }
        pclearbot. right. eapply CIH with (sm0 := sm1); eauto.
        econs; eauto.
        { folder. ss; des_ifs. eapply mfuture_preserves_sim_ge; eauto. apply rtc_once; eauto. }
        etransitivity; eauto.
      + des. pclearbot. econs 2.
        { esplits; eauto. eapply lift_star; eauto. }
        right. eapply CIH; eauto.
        instantiate (1:=sm1). econs; eauto.
        { folder. ss; des_ifs. eapply mfuture_preserves_sim_ge; eauto. eapply rtc_once; eauto. }
        { etrans; eauto. }

    - (* call *)
      left. right. econs; eauto. econs; eauto; cycle 1.
      { ii. inv FINALSRC. ss. ModSem.tac. }
      i. inv STEPSRC; ss; ModSem.tac. des_ifs. hexploit1 SU0.
      { ss. }
      rename SU0 into CALLFSIM.

      exploit CALLFSIM; eauto. i; des. esplits; eauto.
      + left. split; cycle 1.
        { eapply lift_receptive_at. { unsguard SESRC. ss. des_ifs. } eapply at_external_receptive_at; et. }
        apply plus_one. econs; ss; eauto.
        { eapply lift_determinate_at; et. { unsguard SETGT. ss. des_ifs. } eapply at_external_determinate_at; et. }
        des_ifs. econs 1; eauto.
      + right. eapply CIH; eauto.
        { instantiate (1:= sm_arg). econs 2; eauto.
          * ss. folder. des_ifs. eapply mfuture_preserves_sim_ge; eauto. econs 2; et.
          * instantiate (1:= sm_arg). econs; [eassumption|..]; revgoals; ss.
            { ii. exploit K; eauto. i; des_safe. pclearbot. esplits; try apply LXSIM; eauto. }
            { reflexivity. }
            { et. }
            { refl. }
            { et. }
            { ss. folder. des_ifs. }
            { eauto. }
          * reflexivity.
        }


    - (* return *)
      left. right. econs; eauto.
      econs; eauto; cycle 1.
      { ii. ss. inv FINALSRC0. ss. determ_tac ModSem.final_frame_dtm. clear_tac.
        inv STACK.
        econs; ss; eauto.
        - econs; ss; eauto.
          inv SIMRETV; ss.
          eapply SimMem.sim_val_int; et.
        - i. inv FINAL0; inv FINAL1; ss.
          exploit ModSem.final_frame_dtm; [apply FINAL|apply FINAL0|..]. i; clarify. congruence.
        - ii. des_ifs. inv H; ss; ModSem.tac.
      }
      i. ss. des_ifs. inv STEPSRC; ModSem.tac. ss.
      inv STACK; ss. folder. sguard in SESRC0. sguard in SETGT0. des_ifs.
      determ_tac ModSem.final_frame_dtm. clear_tac.
      exploit K; try apply SIMRETV; eauto.
      { etransitivity; eauto. etrans; eauto. }
      { exploit SSSRC. { eapply star_refl. } intro T; des. inv T. des. simpl_depind. clarify.
        inv TL. simpl_depind. clarify. des.
        exploit FORALLSU0; eauto. i; des. esplits; eauto. eapply HD; eauto.
      }
      i; des. esplits; eauto.
      + left. split; cycle 1.
        { eapply lift_receptive_at. { unsguard SESRC. ss. des_ifs. } eapply final_frame_receptive_at; et. }
        apply plus_one. econs; eauto.
        { eapply lift_determinate_at. { unsguard SETGT. ss. des_ifs. } eapply final_frame_determinate_at; et. }
        econs 4; ss; eauto.
      + right. eapply CIH; eauto.
        instantiate (1:= sm_after). econs; ss; cycle 3; eauto.
        { folder. des_ifs. eapply mfuture_preserves_sim_ge; et. econs 2; et. }
        { etrans; eauto. }
  Qed.

End ADQSTEP.



Require Import BehaviorsC SemProps.

Section ADQ.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (lxsim_lift pp).
  Hint Unfold lxsim_lift.

  Let skenv_link_src := (Sk.load_skenv sk_link_src).
  Let skenv_link_tgt := (Sk.load_skenv sk_link_tgt).
  Variable ss_link: SimSymb.t.
  Hypothesis (SIMSKENV: exists sm, SimSymb.sim_skenv sm ss_link skenv_link_src skenv_link_tgt).

  Hypothesis (INCLSRC: forall mp (IN: In mp pp), SkEnv.includes skenv_link_src (Mod.sk mp.(ModPair.src))).
  Hypothesis (INCLTGT: forall mp (IN: In mp pp), SkEnv.includes skenv_link_tgt (Mod.sk mp.(ModPair.tgt))).
  Hypothesis (SSLE: forall mp (IN: In mp pp), SimSymb.le mp.(ModPair.ss) ss_link).

  Hypothesis (WFSKSRC: forall md (IN: In md (ProgPair.src pp)), <<WF: Sk.wf md >>).
  Hypothesis (WFSKTGT: forall md (IN: In md (ProgPair.tgt pp)), <<WF: Sk.wf md >>).

  Theorem adequacy_local_aux: mixed_simulation sem_src sem_tgt.
  Proof.
    subst_locals. econstructor 1 with (order := ord); eauto. generalize wf_ord; intro WF.
    econstructor; eauto.
    - eapply preservation; eauto.
    - eapply preservation_top.
    - econs 1; ss; eauto. ii.
      exploit init_lxsim_lift_forward; eauto. { destruct pp; ss. } i; des.
      assert(WFTGT: forall md, In md (ProgPair.tgt pp) -> <<WF: Sk.wf md >>).
      { inv INITTGT. inv INIT. ss. }
      hexploit lxsim_lift_xsim; eauto.
    - ss. i; des. inv SAFESRC.
      exploit sim_link_sk; eauto. i; des. des_ifs.
      exploit SimSymb.wf_load_sim_skenv; eauto. i; des. clarify.
      symmetry. exploit SimSymb.sim_skenv_public_symbols; et. intro T. s. rewrite T. ss.
  Unshelve.
    all: ss.
  Qed.

End ADQ.



Section BEH.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Context `{SU: Sound.class}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := (ProgPair.src pp).
  Let p_tgt := (ProgPair.tgt pp).
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.

  Theorem adequacy_local: BehaviorsC.improves sem_src sem_tgt.
  Proof.
    eapply improves_free_theorem; i.
    eapply bsim_improves; eauto. eapply mixed_to_backward_simulation; eauto.

    des. inv INIT. ss. exploit sim_link_sk; eauto. i; des. clarify.
    exploit init_lxsim_lift_forward; eauto. { destruct pp; ss. } { econs; eauto. } i; des.
    exploit SimSymb.wf_load_sim_skenv; eauto. i; des. clarify.
    eapply adequacy_local_aux; ss; eauto.
    { rewrite Forall_forall in *. ss. }
    { inv INITTGT. inv INIT. ss. }
  Qed.

End BEH.



Program Definition mkPR (MR: SimMem.class) (SR: SimSymb.class MR) (MP: Sound.class)
  : program_relation.t := program_relation.mk
                            (fun (p_src p_tgt: program) =>
                               forall (WF: forall x (IN: In x p_src), Sk.wf x),
                               exists pp,
                                 (<<SIMS: @ProgPair.sim MR SR MP pp>>)
                                 /\ (<<SRCS: (ProgPair.src pp) = p_src>>)
                                 /\ (<<TGTS: (ProgPair.tgt pp) = p_tgt>>)) _ _ _.
Next Obligation.
(* horizontal composition *)
  exploit REL0; eauto. { i. eapply WF. rewrite in_app_iff. eauto. } intro T0; des.
  exploit REL1; eauto. { i. eapply WF. rewrite in_app_iff. eauto. } intro T1; des.
  clarify. unfold ProgPair.sim in *. rewrite Forall_forall in *. eexists (_ ++ _). esplits; eauto.
  - rewrite Forall_forall in *. i. rewrite in_app_iff in *. des; [apply SIMS|apply SIMS0]; eauto.
  - unfold ProgPair.src. rewrite map_app. ss.
  - unfold ProgPair.tgt. rewrite map_app. ss.
Qed.
Next Obligation.
(* adequacy *)
  destruct (classic (forall x (IN: In x p_src), Sk.wf x)) as [WF|NWF]; cycle 1.
  { eapply sk_nwf_improves; auto. }
  specialize (REL WF). des. clarify.
  eapply (@adequacy_local MR SR MP). auto.
Qed.
Next Obligation. exists []. splits; ss. Qed.
Arguments mkPR: clear implicits.


Definition relate_single (MR: SimMem.class) (SR: SimSymb.class MR) (MP: Sound.class)
           (p_src p_tgt: Mod.t) : Prop :=
  forall (WF: Sk.wf p_src),
  exists mp,
    (<<SIM: @ModPair.sim MR SR MP mp>>)
    /\ (<<SRC: mp.(ModPair.src) = p_src>>)
    /\ (<<TGT: mp.(ModPair.tgt) = p_tgt>>).
Arguments relate_single : clear implicits.

Lemma relate_single_program MR SR MP p_src p_tgt
      (REL: relate_single MR SR MP p_src p_tgt):
    (mkPR MR SR MP) [p_src] [p_tgt].
Proof.
  unfold relate_single. ss. i.
  exploit REL; [ss; eauto|]. i. des. clarify.
  exists [mp]. esplits; ss; eauto.
Qed.
Arguments relate_single_program : clear implicits.

Lemma relate_each_program MR SR MP
      (p_src p_tgt: program)
      (REL: Forall2 (relate_single MR SR MP) p_src p_tgt):
    (mkPR MR SR MP) p_src p_tgt.
Proof.
  revert p_tgt REL. induction p_src; ss; i.
  - inv REL. exists []; splits; ss.
  - inv REL. exploit IHp_src; eauto. i. des.
    exploit H1; eauto. i. des. clarify.
    exists (mp :: pp); splits; ss. econs; eauto.
Qed.
Arguments relate_each_program : clear implicits.

Lemma relate_single_rtc_rusc (R: program_relation.t -> Prop) MR SR MP
      (p_src p_tgt: Mod.t)
      (REL: rtc (relate_single MR SR MP) p_src p_tgt)
      (RELIN: R (mkPR MR SR MP)):
    rusc R [p_src] [p_tgt].
Proof.
  induction REL; try refl.
  - etrans; eauto. eapply rusc_incl; eauto. eapply relate_single_program; eauto.
Qed.
Arguments relate_single_program : clear implicits.

Lemma relate_single_rusc (R: program_relation.t -> Prop) MR SR MP
      (p_src p_tgt: Mod.t)
      (REL: (relate_single MR SR MP) p_src p_tgt)
      (RELIN: R (mkPR MR SR MP)):
    rusc R [p_src] [p_tgt].
Proof.
  eapply relate_single_rtc_rusc; eauto. eapply rtc_once. eauto.
Qed.
Arguments relate_single_program : clear implicits.
