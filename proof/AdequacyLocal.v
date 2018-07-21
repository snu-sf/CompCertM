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
 


  Lemma find_fptr_owner_bsim
        sm0 ge_src ge_tgt
        (SIMGE: sim_ge sm0 ge_src ge_tgt)
        fptr_src fptr_tgt
        (SIMFPTR: SimMem.sim_val sm0 fptr_src fptr_tgt)
        ms_tgt
        (FINDTGT: Ge.find_fptr_owner ge_tgt fptr_tgt ms_tgt)
        (SAFESRC: exists ms_src, Ge.find_fptr_owner ge_src fptr_src ms_src)
    :
      exists msp,
        <<FINDSRC: Ge.find_fptr_owner ge_src fptr_src msp.(ModSemPair.src)>>
        /\ <<FINDTGT: ModSemPair.tgt msp = ms_tgt>>
        /\ <<SIMMS: ModSemPair.sim msp>>
        /\ <<SIMSKENV: ModSemPair.sim_skenv msp sm0>>
  .
  Proof.
    inv SIMGE.
    { des. inv SAFESRC; ss. }
    rewrite Forall_forall in *.
    {
      assert(SAFESRC0: fptr_src <> Vundef).
      { ii; ss; clarify. des; ss. inv SAFESRC. ss. }
      clear SAFESRC.

      inv FINDTGT.
      rewrite in_map_iff in MODSEM. des. rename x into msp.
      clarify.
      
      specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS.
      specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV.
      exploit SimSymb.sim_skenv_func_bisim; eauto. intro SIMFUNC; des.
      inv SIMFUNC.
      exploit FUNCBSIM; try apply PROGRESS; eauto. i; des. clarify. clear_tac. inv SIM.
      exists msp. esplits; eauto.
      { econs; eauto. rewrite in_map_iff; eauto. }
    }
  Qed.

  Lemma find_fptr_owner_bsim_deprecated
        sm0 ge_src ge_tgt
        (SIMGE: sim_ge sm0 ge_src ge_tgt)
        fptr_src fptr_tgt
        (SIMFPTR: SimMem.sim_val sm0 fptr_src fptr_tgt)
        ms_tgt
        (FINDTGT: Ge.find_fptr_owner ge_tgt fptr_tgt ms_tgt)
        ms_src
        (SAFESRC: Ge.find_fptr_owner ge_src fptr_src ms_src)
    :
      exists msp,
        <<SRC: ModSemPair.src msp = ms_src>>
        /\ <<TGT: ModSemPair.tgt msp = ms_tgt>>
        /\ <<SIMMS: ModSemPair.sim msp>>
        /\ <<SIMSKENV: ModSemPair.sim_skenv msp sm0>>
  .
  Proof.
  (*   inv SIMGE. *)
  (*   rewrite Forall_forall in *. *)
  (*   clear SAFESRC. *)
  (*   inv FINDTGT. *)
  (*   rewrite in_map_iff in MODSEM. des. rename x into msp. *)
  (*   specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS. *)
  (*   specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV. *)
  (*   clarify. *)
  (*   esplits; eauto. *)


  (*   inv SIMGE. *)
  (*   rewrite Forall_forall in *. *)
  (*   dup SAFESRC. *)
  (*   inv SAFESRC. *)
  (*   rewrite in_map_iff in MODSEM. des. rename x into msp. *)
  (*   specialize (SIMMSS msp). exploit SIMMSS; eauto. clear SIMMSS. intro SIMMS. *)
  (*   specialize (SIMSKENV msp). exploit SIMSKENV; eauto. clear SIMSKENV. intro SIMSKENV. *)

  (*   inv FINDTGT. rewrite in_map_iff in *. des. rename msp into _msp. rename x into msp. clarify. *)
  (*   exploit SimSymb.sim_skenv_func_bsim; eauto. intro SIMFUNC; des. *)
  (*   inv SIMFUNC. exploit FUNCBSIM; eauto. i; des. clear_tac. inv SIM. *)
  (*   ttttttttttt *)

  (*   assert(exists blk_tgt, fptr_tgt = Vptr blk_tgt Ptrofs.zero true). *)
  (*   { inv FINDTGT. esplits; eauto. } des. clarify. *)
  (*   exploit SimSymb.sim_skenv_def_fsim; eauto. intro SIMDEF; des. *)
  (*   inv SIMDEF. exploit DEFFSIM; eauto. i; des. clear_tac. inv SIM. inv SIM0. *)

  (*   assert(FINDSRC: Ge.find_fptr_owner (map ModSemPair.tgt msps) *)
  (*                                      (Vptr blk_tgt Ptrofs.zero true) msp.(ModSemPair.tgt)). *)
  (*   { econs; eauto. rewrite in_map_iff. esplits; eauto. } *)
  (*   esplits; eauto. *)
  (*   assert(exists tp tsk, tp.(Sem.semantics).(globalenv) = (map ModSemPair.tgt msps) /\ link_sk tp = Some tsk). *)
  (*   { admit "". } *)
  (*   des. *)
  (*   eapply find_fptr_owner_determ with (p:= tp); eauto. *)
  (*   { ss. des_ifs. rewrite H. eauto. } *)
  (*   { ss. des_ifs. rewrite H. eauto. } *)
  (* Qed. *)
  Abort.



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
        * apply SIMMP.
        * rewrite Forall_forall in *.
          i. apply in_map_iff in H. des.
          specialize (SIMPROG x0). special SIMPROG; ss. clarify. eapply SIMPROG.
      + ss. econs; ss; eauto.
        * eapply to_msp_sim_skenv; eauto.
          rewrite Forall_forall in *. apply SSLE; ss; eauto.
        * rewrite Forall_forall in *. i. rewrite in_map_iff in *. des. clarify.
          eapply to_msp_sim_skenv; eauto.
          apply SSLE; ss; eauto.
  Qed.

End SIMGE.










Section ADQMATCH.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  (* Variable pp: ProgPair.t. *)
  (* Hypothesis SIMPROG: ProgPair.sim pp. *)
  (* Let p_src := pp.(ProgPair.src). *)
  (* Let p_tgt := pp.(ProgPair.tgt). *)

  Variable p_src p_tgt: program.
  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.
  Let sem_src := Sem.semantics p_src.
  Let sem_tgt := Sem.semantics p_tgt.
  Compute sem_src.(Smallstep.state).

  Print Frame.t.
  (* Record t : Type := mk { ms : ModSem.t;  lst : ModSem.state ms;  rs_init : regset } *)

  (* Interpretation: the stack called top with following regset/regset/SimMem.t as arguments. *)
  (* (SimMem.t is lifted. lifting/unlifting is caller's duty) *)
  (* Simulation can go continuation when SimMem.t bigger than argument is given, (after unlifting it) *)
  (* with after_external fed with regsets sent. *)
  Inductive lxsim_stack: regset -> regset -> SimMem.t ->
                         list Frame.t -> list Frame.t -> Prop :=
  | lxsim_stack_nil
      rs_init_src rs_init_tgt sm0
    :
      lxsim_stack rs_init_src rs_init_tgt sm0 [] []
  | lxsim_stack_cons
      tail_src tail_tgt tail_sm
      rs_init_src rs_init_tgt
      (STACK: lxsim_stack rs_init_src rs_init_tgt tail_sm tail_src tail_tgt)
      ms_src lst_src0
      ms_tgt lst_tgt0
      rs_arg_src rs_arg_tgt
      sm_arg
      (MWF: SimMem.wf sm_arg)
      (GE: sim_ge sm_arg sem_src.(globalenv) sem_tgt.(globalenv))
      (MLE: SimMem.le tail_sm sm_arg)
      sm_init
      (MLE: SimMem.le (SimMem.lift sm_arg) sm_init)
      (K: forall
          sm_ret rs_ret_src rs_ret_tgt
          (MEMLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
          (MEMWF: SimMem.wf sm_ret)
          (RSREL: sm_ret.(SimMem.sim_regset) rs_ret_src rs_ret_tgt)
          (SAFESRC: exists lst_src1,
              <<AFTERSRC: ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src
                                                         (sm_ret.(SimMem.src))
                                                         lst_src1>>)
        ,
          (<<KSTEP: forall
              lst_tgt1
              (AFTERTGT: ms_tgt.(ModSem.after_external) lst_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt))
                                                        lst_tgt1)
            ,
              exists i0 lst_src1,
                (<<AFTERSRC:
                   ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src))
                                                  lst_src1>>)
                /\
                (<<LXSIM: lxsim ms_src ms_tgt rs_init_src rs_init_tgt tail_sm
                                i0 lst_src1 lst_tgt1 (sm_arg.(SimMem.unlift) sm_ret)>>)>>)
          /\
          (<<KPROGRESS: (* forall *)
              (* st_src1 *)
              (* (AFTERSRC: ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src)) *)
              (*                                           st_src1) *)
            (* , *)
              exists lst_tgt1,
                (<<AFTERTGT:
                   ms_tgt.(ModSem.after_external) lst_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt))
                                                  lst_tgt1>>)>>))
    :
      lxsim_stack rs_arg_src rs_arg_tgt
                  sm_init
                  ((Frame.mk ms_src rs_init_src lst_src0) :: tail_src)
                  ((Frame.mk ms_tgt rs_init_tgt lst_tgt0) :: tail_tgt)

  .

  Lemma lxsim_stack_le
        rs_init_src rs_init_tgt sm0 frs_src frs_tgt
        (SIMSTACK: lxsim_stack rs_init_src rs_init_tgt sm0 frs_src frs_tgt)
        sm1
        (MLE: SimMem.le sm0 sm1)
    :
      <<SIMSTACK: lxsim_stack rs_init_src rs_init_tgt sm1 frs_src frs_tgt>>
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
      rs_init_src rs_init_tgt
      (STACK: lxsim_stack rs_init_src rs_init_tgt tail_sm tail_src tail_tgt)
      (MLE: SimMem.le tail_sm sm0)
      i0
      ms_src lst_src
      ms_tgt lst_tgt
      (TOP: lxsim ms_src ms_tgt rs_init_src rs_init_tgt tail_sm
                  i0 lst_src lst_tgt sm0)
    :
      lxsim_lift i0
                 (State ((Frame.mk ms_src rs_init_src lst_src) :: tail_src))
                 (State ((Frame.mk ms_tgt rs_init_tgt lst_tgt) :: tail_tgt))
                 sm0
  | lxsim_lift_callstate
       sm_arg
       (GE: sim_ge sm_arg sem_src.(globalenv) sem_tgt.(globalenv))
       tail_src tail_tgt tail_sm
       rs_arg_src rs_arg_tgt
       (STACK: lxsim_stack rs_arg_src rs_arg_tgt tail_sm tail_src tail_tgt)
       (MLE: SimMem.le tail_sm sm_arg)
       (MWF: SimMem.wf sm_arg)
       (SIMRS: (SimMem.sim_regset) sm_arg rs_arg_src rs_arg_tgt)
    :
      lxsim_lift idx_bot
                 (Callstate rs_arg_src sm_arg.(SimMem.src) tail_src)
                 (Callstate rs_arg_tgt sm_arg.(SimMem.tgt) tail_tgt)
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
  Let lxsim_lift := (@lxsim_lift _ _ p_src p_tgt).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.semantics p_src.
  Let sem_tgt := Sem.semantics p_tgt.
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
    inv INITSRC; ss.
    rename sk_link into sk_link_src.
    rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC.

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    exploit init_sim_ge_strong; eauto. i; des. clarify.
    ss. des_ifs.

    assert(SIMFPTR: SimMem.sim_val sm_init (Genv.symbol_address (Genv.globalenv sk_link_src)
                                                                (prog_main sk_link_src) Ptrofs.zero)
                                   (Genv.symbol_address (Genv.globalenv sk_link_tgt)
                                                        (prog_main sk_link_tgt) Ptrofs.zero)).
    { admit "strengthen sim_skenv specs". }

    assert(SIMRS: SimMem.sim_regset sm_init
        (init_regs (Genv.symbol_address (Sk.load_skenv sk_link_src) (prog_main sk_link_src) Ptrofs.zero))
        (init_regs (Genv.symbol_address (Sk.load_skenv sk_link_tgt) (prog_main sk_link_tgt) Ptrofs.zero))).
    { u. ii. ss.
      unfold Pregmap.set.
      des_ifs.
      - admit "strengthen sim_val".
      - admit "strengthen sim_val".
      - admit "strengthen sim_val".
    }

    esplits; eauto.
    - econs; ss; cycle 1.
      { ii. eapply initial_state_determ; ss; eauto. }
      econs; eauto.
    - econs; eauto.
      + ss. des_ifs.
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
  Let lxsim_lift := (@lxsim_lift _ _ p_src p_tgt).
  Hint Unfold lxsim_lift.
  Let sem_src := Sem.semantics p_src.
  Let sem_tgt := Sem.semantics p_tgt.
  Variable sk_link_src sk_link_tgt: Sk.t.
  Hypothesis LINKSRC: (link_sk p_src) = Some sk_link_src.
  Hypothesis LINKTGT: (link_sk p_tgt) = Some sk_link_tgt.


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
      des_ifs. left.
      econs; eauto.
      { ii. ss. inv FINALSRC. }
      econs; eauto; cycle 1.
      { eapply callstate_receptive_at. }
      ii. ss. des_ifs.
      inv STEPSRC.
      exploit find_fptr_owner_fsim; eauto. i; des. clarify.
      inv MSFIND. inv FINDTGT.
      inv SIMMS.


      specialize (SIM sm0).
      exploit SIM; eauto. i; des.

      (* specialize (SIM (SimMem.lift sm0)). *)
      (* exploit SIM; eauto. *)
      (* { eapply SimMem.lift_sim_val; eauto. } *)
      (* { ii. eapply SimMem.lift_sim_val; eauto. } *)
      (* { eapply SimMem.lift_wf; eauto. } *)
      (* { u. eapply SimSymb.mlift_preserves_sim_skenv; eauto. } *)
      (* { ss. erewrite SimMem.lift_src. eauto. } *)
      (* i; des. *)


      esplits; eauto.
      - left. eapply plus_one.
        econs; eauto; cycle 1.
        + econs; eauto.
          * ss. des_ifs. econs; eauto; ss.
          (* * erewrite SimMem.lift_tgt in INITTGT. eauto. *)
        + eapply callstate_determinate_at; eauto.
      - instantiate (1:= idx_init).
        right. eapply CIH.
        instantiate (1:= sm_init).
        econs 1; try apply SIM0; eauto.
        + ss. des_ifs. eapply mle_preserves_sim_ge; eauto.
        + eapply lxsim_stack_le; eauto.
    }
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
          exists i1, (State ((Frame.mk ms_tgt rs_init_tgt st_tgt1) :: tail_tgt)).
          esplits; eauto.
          { des.
            - left. eapply lift_dplus; eauto.
            - right. esplits; eauto. eapply lift_dstar; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto. econs; eauto.
          { ss; des_ifs. eapply mle_preserves_sim_ge; eauto. }
          etransitivity; eauto.
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_dstar; eauto. }
          right. eapply CIH; eauto. econs; eauto. ss; des_ifs.


    - (* bstep *)
      right. ss.
      econs; ss; eauto.
      + ii. inv FINALTGT. ss. ModSem.tac.
      + ii.
        inv BSTEP.
        * econs 1; eauto.
          ii. inv STEPTGT; ModSem.tac.
          ss. exploit STEP; eauto. i; des_safe.
          exists i1, (State ((Frame.mk ms_src rs_init_src st_src1) :: tail_src)).
          esplits; eauto.
          { des.
            - left. eapply lift_plus; eauto.
            - right. esplits; eauto. eapply lift_star; eauto.
          }
          pclearbot. right. eapply CIH with (sm0 := sm1); eauto. econs; eauto.
          { ss; des_ifs. eapply mle_preserves_sim_ge; eauto. }
          etransitivity; eauto.
        * des. pclearbot. econs 2.
          { esplits; eauto. eapply lift_star; eauto. }
          right. eapply CIH; eauto. econs; eauto. ss; des_ifs.
      + ii. right. des. esplits; eauto. eapply lift_step; eauto.


    - (* call *)
      right.
      econs; eauto; swap 2 3.
      { (* final *)
        ii. inv FINALTGT. ss. exfalso. eapply ModSem.call_return_disjoint; eauto. esplits; eauto. }
      { (* progress *)
        ii. right. u in SAFESRC. des.
        exploit CALLBSIM; eauto. i; des.
        specialize (SAFESRC0 _ (star_refl _ _ _)). des.
        { inv SAFESRC0. ss. exfalso. eapply ModSem.call_return_disjoint; eauto. u. esplits; eauto. }
        ss; des_ifs.
        inv SAFESRC0; ss; ModSem.tac.
        esplits; eauto. econs; ss; eauto. }

      (* ii. unfold safe in *. ss. specialize (SAFESRC _ (star_refl _ _ _)). des. *)
      (* { admit "final forward". } *)
      (* des_ifs. *)

      (* inv SAFESRC; ss; cycle 1. *)
      (* { exfalso. eapply ModSem.at_external_final_machine_disjoint; try apply FINAL; eauto. } *)
      (* { exfalso. eapply ModSem.step_at_external_disjoint; try apply FINAL; eauto. } *)

      econs 1; ss; eauto. i. des_ifs.
      inv STEPTGT; ss; ModSem.tac.
      clear SAFESRC.
      rename rs_arg into rs_arg_tgt.
      exploit CALLBSIM; eauto. i; des.

      eapply mle_preserves_sim_ge with (sm2:= sm_arg) in GE; eauto.
      (* Note: Coq bug STILL not fixed!!! there is no name like sm2. *)

      clarify.
      esplits; eauto.
      + left. apply plus_one. econs; ss; eauto.
      + right. eapply CIH; eauto.
        {
          instantiate (1:= (SimMem.lift sm_arg)).
          erewrite <- SimMem.lift_src. erewrite <- SimMem.lift_tgt.
          econs 2; eauto.
          * ss. des_ifs. eapply mlift_preserves_sim_ge; eauto.
          * instantiate (1:= (SimMem.lift sm_arg)).
            econs; [eassumption|..]; revgoals.
            { ii. exploit K; eauto. i; des_safe. esplits; eauto.
              ii. exploit KSTEP; eauto. i; des_safe. pclearbot. esplits; eauto.
            }
            { reflexivity. }
            { etransitivity; eauto. }
            { ss. des_ifs. }
            { eauto. }
          * reflexivity.
          * eapply SimMem.lift_wf; eauto.
          * ii. eapply SimMem.lift_sim_val; eauto. 
        }


    - (* return *)
      des_ifs.
      right.
      econs; eauto; swap 2 3.
      { (* final *)
        ii. inv FINALTGT0. ss. des_ifs.
        esplits; [apply star_refl|]; eauto.
        inv STACK.
        econs; ss; eauto.
        - admit "obligate to SimMem.val".
        - admit "obligate to SimMem.val".
      }
      { (* progress *)
        ii.
        specialize (SAFESRC _ (star_refl _ _ _)). des.
        { left. inv SAFESRC. inv STACK. ss.
          determ_tac ModSem.final_frame_dtm. clear_tac.
          esplits; eauto. econs; eauto.
          - admit "obligate to SimMem.val".
          - admit "obligate to SimMem.val". }

        right. ss. des_ifs.
        inv SAFESRC; ss.
        { exfalso. 
          eapply ModSem.call_return_disjoint; eauto. esplits; eauto. }
        { exfalso.
          eapply ModSem.step_return_disjoint; eauto. esplits; eauto. }
        determ_tac ModSem.final_frame_dtm. clear_tac.
        bar.
        move AFTER at bottom.
        move STACK at bottom.
        inv STACK. ss.
        exploit K; try apply RSREL; eauto.
        { etransitivity; eauto. }
        { erewrite <- mcompat_src in *; eauto. }
        i; des.
        esplits; eauto.
        econs 4; ss; eauto.
        erewrite <- mcompat_tgt in *; eauto.
      }
      i.
      econs 1; eauto. ss. des_ifs.
      ii. inv STEPTGT; ss.
      { exfalso. eapply ModSem.call_return_disjoint; eauto. esplits; eauto. }
      { exfalso. eapply ModSem.step_return_disjoint; eauto. esplits; eauto. }
      exploit ModSem.final_frame_dtm.
      { eapply FINALTGT. }
      { eapply FINAL. }
      i; des. clarify. clear_tac.
      inv STACK. ss.
      exploit K; try apply RSREL; eauto.
      { etransitivity; eauto. }
      { specialize (SAFESRC _ (star_refl _ _ _)).
        des; ss.
        { inv SAFESRC. }
        inv SAFESRC; ModSem.tac. ss.
        determ_tac ModSem.final_frame_dtm. erewrite <- mcompat_src in *; eauto.
      }
      i; des. exploit KSTEP; eauto. i; des.
      esplits; eauto.
      + left. apply plus_one.
        econs 4; ss; eauto.
        erewrite <- mcompat_src in *; eauto.
      + right. eapply CIH; eauto.
        instantiate (1:= (SimMem.unlift sm_arg sm0)).
        econs; ss; cycle 1.
        { eauto. }
        { etransitivity; eauto.
          eapply SimMem.unlift_spec; eauto.
          etransitivity; eauto. }
        { erewrite mcompat_tgt in AFTER; eauto. determ_tac ModSem.after_external_dtm. eauto. }
        { des_ifs.
          eapply mle_preserves_sim_ge; eauto.
          eapply SimMem.unlift_spec; eauto.
          etransitivity; eauto. }
  Unshelve.
    all: ss.
  Qed.

End ADQSTEP.




Section ADQ.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).
  Let sem_src := Sem.semantics p_src.
  Let sem_tgt := Sem.semantics p_tgt.

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
    exploit init_lxsim_lift_forward; eauto. i; des.
    ss.
    assert(exists sk_link_src, link_sk (ProgPair.src pp) = Some sk_link_src).
    { inv INITSRC. eauto. }
    assert(exists sk_link_tgt, link_sk (ProgPair.tgt pp) = Some sk_link_tgt).
    { inv INITTGT. inv INIT. eauto. }
    des.
    hexploit lxsim_lift_xsim; eauto.
  Qed.

End ADQ.

