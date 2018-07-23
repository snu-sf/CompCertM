Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Asmregs.
Require Import Smallstep.
Require Import Integers.
Require Import Events.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem SimMod SimModSem SimProg (* SimLoad *) SimProg.
Require Import SemProps Ord.

Set Implicit Arguments.






(* TODO: move to coqlibc *)
Ltac revert_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => revert id'; revert_until_bar
                               end)
.

Ltac folder := all_once_fast ltac:(fun H => try (is_local_definition H; fold_all H)).














Section SIMGE.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  (* Inductive sim_gepair (sm0: SimMem.t) (ge_src ge_tgt: list ModSem.t): Prop := *)
  Inductive sim_ge (sm0: SimMem.t): Ge.t -> Ge.t -> Prop :=
  | sim_ge_src_stuck
      ge_tgt
    :
      sim_ge sm0 [] ge_tgt
  | sim_ge_intro
      msps
      (SIMSKENV: List.Forall (fun msp => ModSemPair.sim_skenv msp sm0) msps)
      (SIMMSS: List.Forall (ModSemPair.sim) msps)
      ge_src ge_tgt
      (GESRC: ge_src = (map (ModSemPair.src) msps))
      (GETGT: ge_tgt = (map (ModSemPair.tgt) msps))
    :
      sim_ge sm0 ge_src ge_tgt 
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
  .
  Proof.
    inv SIMGE.
    { inv FINDSRC; ss. }
    rewrite Forall_forall in *.
    inv FINDSRC.
    rewrite in_map_iff in MODSEM. des. rename x into msp.
    esplits; eauto.
    clarify.
    specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS.
    specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV.

    exploit SimSymb.sim_skenv_func_bisim; eauto. intro SIMFUNC; des.
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
    rewrite in_map_iff in *. des.
  Abort.

  Theorem mle_preserves_sim_ge
          sm0 ge_src ge_tgt
          (SIMGE: sim_ge sm0 ge_src ge_tgt)
          sm1
          (MLE: SimMem.le sm0 sm1)
    :
      <<SIMGE: sim_ge sm1 ge_src ge_tgt>>
  .
  Proof.
    inv SIMGE.
    { econs; eauto. }
    econs 2; try reflexivity; eauto.
    rewrite Forall_forall in *. ii.
    eapply SimSymb.mle_preserves_sim_skenv; eauto.
    eapply SIMSKENV; eauto.
  Qed.

  Theorem mlift_preserves_sim_ge
          sm0 ge_src ge_tgt
          (MWF: SimMem.wf sm0)
          (SIMGE: sim_ge sm0 ge_src ge_tgt)
    :
      <<SIMGE: sim_ge (SimMem.lift sm0) ge_src ge_tgt>>
  .
  Proof.
    inv SIMGE.
    { econs; eauto. }
    econs 2; try reflexivity; eauto.
    rewrite Forall_forall in *. ii.
    u.
    eapply SimSymb.mlift_preserves_sim_skenv; eauto.
    eapply SIMSKENV; eauto.
  Qed.

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
        sm_init hd_src hd_tgt tl_src tl_tgt
        (SAFESRC: tl_src <> [])
        (SIMGEHD: sim_ge sm_init [hd_src] [hd_tgt])
        (SIMGETL: sim_ge sm_init tl_src tl_tgt)
    :
      <<SIMGE: sim_ge sm_init (hd_src :: tl_src) (hd_tgt :: tl_tgt)>>
  .
  Proof.
    red.
    inv SIMGEHD. destruct msps; ss. destruct msps; ss. clarify. inv SIMMSS. inv SIMSKENV.
    inv SIMGETL; ss.
    econstructor 2 with (msps := t :: msps); eauto.
  Qed.

  Lemma to_msp_tgt
        skenv_tgt skenv_src pp
    :
          map ModSemPair.tgt (map (ModPair.to_msp skenv_src skenv_tgt) pp) =
          map (fun md => Mod.modsem md skenv_tgt) (ProgPair.tgt pp)
  .
  Proof.
    ginduction pp; ii; ss.
    f_equal. erewrite IHpp; eauto.
  Qed.

  Lemma to_msp_src
        skenv_tgt skenv_src pp
    :
          map ModSemPair.src (map (ModPair.to_msp skenv_src skenv_tgt) pp) =
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
        (SIMMP: ModPair.sim mp)
        ss_link
        (LESS: SimSymb.le (ModPair.ss mp) (Mod.get_sk (ModPair.src mp) (Mod.data (ModPair.src mp)))
                          (Mod.get_sk (ModPair.tgt mp) (Mod.data (ModPair.tgt mp))) ss_link)
        (SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_src skenv_tgt)
      :
        <<SIMSKENV: ModSemPair.sim_skenv (ModPair.to_msp skenv_src skenv_tgt mp) sm_init>>
  .
  Proof.
    (* inv SIMMP. specialize (SIMMS skenv_src skenv_tgt). *)
    u.
    eapply SimSymb.sim_skenv_monotone; revgoals.
    - eapply Mod.get_modsem_projected_sk.
    - eapply Mod.get_modsem_projected_sk.
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
               /\ <<SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_link_src skenv_link_tgt>>
  .
  Proof.
    clarify.
    exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. rename sm into sm_init. clarify.
    esplits; eauto.
    unfold load_genv in *.
    eapply sim_ge_cons.
    - ii. destruct pp; ss.
    - assert(exists msp_sys,
                (<<SYSSRC: msp_sys.(ModSemPair.src) = System.modsem (Genv.globalenv sk_link_src)>>)
                /\ (<<SYSTGT: msp_sys.(ModSemPair.tgt) = System.modsem (Genv.globalenv sk_link_tgt)>>)
                /\ <<SYSSIM: ModSemPair.sim msp_sys>> /\ <<SIMSKENV: ModSemPair.sim_skenv msp_sys sm_init>>).
      { admit "raw admit. this should hold.". }
      des.
      econstructor 2 with (msps := [msp_sys]); ss; eauto.
      + rewrite SYSSRC. ss.
      + rewrite SYSTGT. ss.
    - ginduction pp; ii; ss.
      unfold link_sk in *. ss.
      rename a into mp.
      apply link_list_cons_inv in SKSRC. des. rename restl into sk_src_tl.
      apply link_list_cons_inv in SKTGT. des. rename restl into sk_tgt_tl.
      inv SIMPROG. rename H1 into SIMMP. rename H2 into SIMPROG.
      inv SSLE. rename H1 into SSLEHD. rename H2 into SSLETL.
      unfold flip.
      Check (mp :: pp).
      set (skenv_src := (Sk.load_skenv sk_link_src)) in *.
      set (skenv_tgt := (Sk.load_skenv sk_link_tgt)) in *.
      assert(WFSRC: SkEnv.wf skenv_src).
      { eapply Sk.load_skenv_wf. }
      assert(WFTGT: SkEnv.wf skenv_tgt).
      { eapply Sk.load_skenv_wf. }
      econstructor 2 with
          (msps := (map (ModPair.to_msp skenv_src skenv_tgt) (mp :: pp))); eauto; revgoals.
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
  Qed.

End SIMGE.







Section SIMSKENVLINK.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  Definition sim_skenv_link (sm0: SimMem.t) (skenv_link_src skenv_link_tgt: SkEnv.t): Prop :=
    exists ss_link, SimSymb.sim_skenv sm0 ss_link skenv_link_src skenv_link_tgt
  .

  Theorem mle_preserves_sim_skenv_link
          sm0 ge_src ge_tgt
          (SIMSKENV: sim_skenv_link sm0 ge_src ge_tgt)
          sm1
          (MLE: SimMem.le sm0 sm1)
    :
      <<SIMSKENV: sim_skenv_link sm1 ge_src ge_tgt>>
  .
  Proof.
    inv SIMSKENV.
    econs; eauto.
    eapply SimSymb.mle_preserves_sim_skenv; eauto.
  Qed.

  Theorem mlift_preserves_sim_skenv_link
          sm0 ge_src ge_tgt
          (MWF: SimMem.wf sm0)
          (SIMSKENV: sim_skenv_link sm0 ge_src ge_tgt)
    :
      <<SIMSKENV: sim_skenv_link (SimMem.lift sm0) ge_src ge_tgt>>
  .
  Proof.
    inv SIMSKENV.
    econs; eauto.
    eapply SimSymb.mlift_preserves_sim_skenv; eauto.
  Qed.


End SIMSKENVLINK.





Section ADQMATCH.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

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
      sm_arg
      (MWF: SimMem.wf sm_arg)
      (GE: sim_ge sm_arg sem_src.(globalenv) sem_tgt.(globalenv))
      (SKENV: sim_skenv_link sm_arg skenv_link_src skenv_link_tgt)
      (MLE: SimMem.le tail_sm sm_arg)
      sm_init
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_init)
      (K: forall
          sm_ret retv_src retv_tgt
          (MLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
          (MWF: SimMem.wf sm_ret)
          (SIMRETV: sim_retv retv_src retv_tgt sm_ret)
          lst_src1
          (AFTERSRC: ms_src.(ModSem.after_external) lst_src0 retv_src lst_src1)
        ,
          exists i1 lst_tgt1,
            (<<AFTERTGT: ms_tgt.(ModSem.after_external) lst_tgt0 retv_tgt lst_tgt1>>)
            /\
            (<<LXSIM: lxsim ms_src ms_tgt tail_sm i1 lst_src1 lst_tgt1 (sm_arg.(SimMem.unlift) sm_ret)>>))
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
      (SKENV: sim_skenv_link sm0 skenv_link_src skenv_link_tgt)
      tail_src tail_tgt tail_sm
      (STACK: lxsim_stack tail_sm tail_src tail_tgt)
      (MLE: SimMem.le tail_sm sm0)
      i0
      ms_src lst_src
      ms_tgt lst_tgt
      (TOP: lxsim ms_src ms_tgt tail_sm
                  i0 lst_src lst_tgt sm0)
    :
      lxsim_lift i0
                 (State ((Frame.mk ms_src lst_src) :: tail_src))
                 (State ((Frame.mk ms_tgt lst_tgt) :: tail_tgt))
                 sm0
  | lxsim_lift_callstate
       sm_arg
       (GE: sim_ge sm_arg sem_src.(globalenv) sem_tgt.(globalenv))
       (SKENV: sim_skenv_link sm_arg skenv_link_src skenv_link_tgt)
       tail_src tail_tgt tail_sm
       (STACK: lxsim_stack tail_sm tail_src tail_tgt)
       (MLE: SimMem.le tail_sm sm_arg)
       (MWF: SimMem.wf sm_arg)
       args_src args_tgt
       (SIMARGS: sim_args args_src args_tgt sm_arg)
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

  Variable pp: ProgPair.t.
  Hypothesis NOTNIL: pp <> [].
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (@lxsim_lift _ _ pp sk_link_src sk_link_tgt).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.
  Print Sem.initial_state.

  Theorem init_lxsim_lift_forward
          st_init_src
          (INITSRC: sem_src.(Smallstep.initial_state) st_init_src)
    :
      exists idx st_init_tgt sm_init,
        <<INITTGT: sem_tgt.(Dinitial_state) st_init_tgt>>
        /\ <<SIM: lxsim_lift idx st_init_src st_init_tgt sm_init>>
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
    assert(SIMARGS: sim_args args_src args_tgt sm_init).
    { econs; ss; eauto. admit "strengthen sim_skenv specs". }

    esplits; eauto.
    - econs; ss; cycle 1.
      { ii. eapply initial_state_determ; ss; eauto. }
      econs; eauto.
      apply_all_once SimSymb.sim_skenv_func_bisim. des. inv SIMSKENV.
      exploit FUNCFSIM; eauto.
      { apply SIMARGS. }
      i; des. clarify.
    - econs; eauto.
      + ss. folder. des_ifs.
      + hnf. econs; eauto.
      + econs; eauto.
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

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.

  Let lxsim_lift := (@lxsim_lift _ _ pp sk_link_src sk_link_tgt).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.sem p_src.
  Let sem_tgt := Sem.sem p_tgt.


  Theorem lxsim_lift_xsim
          i0 st_src0 st_tgt0 sm0
          (LXSIM: lxsim_lift i0 st_src0 st_tgt0 sm0)
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
      econs; eauto; cycle 2.
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
      { i. ss. inv FINALTGT. }
      i.
      econs; eauto.
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

      clears st_init0; clear st_init0.
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

      esplits; eauto.
      - left. apply plus_one. econs; eauto. econs; eauto.
      - right. eapply CIH.
        instantiate (1:= sm_init).
        econs; try apply SIM0; eauto.
        + ss. folder. des_ifs. eapply mle_preserves_sim_ge; eauto.
        + eapply mle_preserves_sim_skenv_link; eauto.
        + eapply lxsim_stack_le; eauto.

    }

    folder.
    rewrite LINKSRC in *. rewrite LINKTGT in *.
    punfold TOP. inv TOP.


    - (* fstep *)
      left.
      econs; ss; eauto.
      + ii. des. inv FINALSRC; ss. exfalso. eapply SAFESRC0. u. eauto.
      + inv FSTEP.
        * econs 1; cycle 1.
          { eapply lift_receptive_at; eauto. }
          ii. ss. rewrite LINKSRC in *.
          des.
          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. eauto. }
          { exfalso. eapply SAFESRC0. u. eauto. }
          exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_tgt st_tgt1) :: tail_tgt)).
          esplits; eauto.
          { des.
            - left. eapply lift_dplus; eauto.
            - right. esplits; eauto. eapply lift_dstar; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto. econs; eauto.
          { ss. folder. des_ifs. eapply mle_preserves_sim_ge; eauto. }
          { eapply mle_preserves_sim_skenv_link; eauto. }
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
        * econs 1; eauto.
          ii. inv STEPTGT; ModSem.tac.
          ss. exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_src st_src1) :: tail_src)).
          esplits; eauto.
          { des.
            - left. eapply lift_plus; eauto.
            - right. esplits; eauto. eapply lift_star; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto. econs; eauto.
          { folder. ss; des_ifs. eapply mle_preserves_sim_ge; eauto. }
          { eapply mle_preserves_sim_skenv_link; eauto. }
          etransitivity; eauto.
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_star; eauto. }
          right. eapply CIH; eauto. econs; eauto. folder. ss; des_ifs.
      + ii. right. des. esplits; eauto. eapply lift_step; eauto.


    - (* call *)
      left.
      econs; eauto.
      { ii. inv FINALSRC. ss. ModSem.tac. }
      econs; eauto; cycle 1.
      { eapply lift_receptive_at. admit "Add in ModSem.v". }
      i.
      inv STEPSRC; ss; ModSem.tac.
      exploit CALLFSIM; eauto.
      i; des.
      eapply mle_preserves_sim_ge with (sm2:= sm_arg) in GE; eauto.
      eapply mle_preserves_sim_skenv_link with (sm2:= sm_arg) in SKENV; eauto.
      esplits; eauto.
      + left. apply plus_one.
        econs; ss; eauto.
        { admit "eapply lift_determinate_at // Add in ModSem.v". }
        des_ifs.
        econs 1; eauto.
      + right. eapply CIH; eauto.
        {
          instantiate (1:= (SimMem.lift sm_arg)).
          econs 2; eauto.
          * ss. folder. des_ifs. eapply mlift_preserves_sim_ge; eauto.
          * eapply mlift_preserves_sim_skenv_link; eauto.
          * instantiate (1:= (SimMem.lift sm_arg)).
            econs; [eassumption|..]; revgoals.
            { ii. exploit K; eauto. i; des_safe. pclearbot. esplits; eauto. }
            { reflexivity. }
            { etransitivity; eauto. }
            { ss. }
            { ss. folder. des_ifs. }
            { eauto. }
          * reflexivity.
          * eapply SimMem.lift_wf; eauto.
          * inv SIMARGS. econs; ss; eauto.
            { eapply SimMem.lift_sim_val; eauto. }
            { admit "eapply SimMem.lift_sim_val_list; eauto.". }
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
          admit "obligate to SimMem.val".
        - i. inv FINAL0; inv FINAL1; ss.
          exploit ModSem.final_frame_dtm; [apply FINAL|apply FINAL0|..]. i; clarify.
          congruence.
        - ii. des_ifs.
          inv H; ss; ModSem.tac.
      }
      econs; eauto; cycle 1.
      { eapply lift_receptive_at.
        admit "Add to ModSem.v". }
      i. ss. des_ifs.
      inv STEPSRC; ModSem.tac. ss.
      inv STACK; ss. folder. des_ifs.
      determ_tac ModSem.final_frame_dtm. clear_tac.
      exploit K; try apply SIMRETV; eauto.
      { etransitivity; eauto. }
      i; des.
      esplits; eauto.
      + left. apply plus_one.
        econs; eauto.
        { admit "Add to semprops. / Modsem". }
        econs 4; ss; eauto.
      + right. eapply CIH; eauto.
        instantiate (1:= (SimMem.unlift sm_arg sm0)).
        econs; ss; cycle 2.
        { eauto. }
        { etransitivity; eauto.
          eapply SimMem.unlift_spec; eauto.
          etransitivity; eauto. }
        { eauto. }
        { folder. des_ifs.
          eapply mle_preserves_sim_ge; eauto.
          eapply SimMem.unlift_spec; eauto.
          etransitivity; eauto. }
        { eapply mle_preserves_sim_skenv_link; eauto.
          eapply SimMem.unlift_spec; eauto.
          etransitivity; eauto. }
  Qed.

End ADQSTEP.




Section ADQ.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

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
  Qed.

End ADQ.

