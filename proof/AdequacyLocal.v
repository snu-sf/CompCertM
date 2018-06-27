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
Require Import SimDef SimSymb SimMem SimMod SimModSem SimProg (* SimLoad *) SimProg.
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
    u. rewrite <- ! Mod.get_modsem_projected_sk.
    eapply SimSymb.sim_skenv_monotone; revgoals.
    - apply SkEnv.project_impl_spec.
    - apply SkEnv.project_impl_spec.
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
               /\ <<LOADTGT: Sk.load_mem sk_link_tgt = Some sm_init.(SimMem.tgt_mem)>>
               /\ <<MSRC: sm_init.(SimMem.src_mem) = m_src>>
               /\ <<SIMSKENV: SimSymb.sim_skenv sm_init ss_link skenv_link_src skenv_link_tgt>>
  .
  Proof.
    clarify.
    exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. rename sm into sm_init. clarify.
    assert(MWF: SimMem.wf sm_init).
    { admit "obligate". }
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
                         sem_src.(Smallstep.state) -> sem_tgt.(Smallstep.state) -> Prop :=
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
      (K: forall
          sm_ret rs_ret_src rs_ret_tgt
          (MEMLE: SimMem.le (SimMem.lift sm_arg) sm_ret)
          (MEMWF: SimMem.wf sm_ret)
          (RSREL: sm_ret.(SimMem.sim_regset) rs_ret_src rs_ret_tgt)
          (SAFESRC: exists lst_src1,
              <<AFTERSRC: ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src
                                                         (sm_ret.(SimMem.src_mem))
                                                         lst_src1>>)
        ,
          (<<KSTEP: forall
              lst_tgt1
              (AFTERTGT: ms_tgt.(ModSem.after_external) lst_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt_mem))
                                                        lst_tgt1)
            ,
              exists i0 lst_src1,
                (<<AFTERSRC:
                   ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src_mem))
                                                  lst_src1>>)
                /\
                (<<LXSIM: lxsim ms_src ms_tgt rs_init_src rs_init_tgt tail_sm
                                i0 lst_src1 lst_tgt1 (sm_arg.(SimMem.unlift) sm_ret)>>)>>)
          /\
          (<<KPROGRESS: (* forall *)
              (* st_src1 *)
              (* (AFTERSRC: ms_src.(ModSem.after_external) lst_src0 rs_arg_src rs_ret_src (sm_ret.(SimMem.src_mem)) *)
              (*                                           st_src1) *)
            (* , *)
              exists lst_tgt1,
                (<<AFTERTGT:
                   ms_tgt.(ModSem.after_external) lst_tgt0 rs_arg_tgt rs_ret_tgt (sm_ret.(SimMem.tgt_mem))
                                                  lst_tgt1>>)>>))
    :
      lxsim_stack rs_arg_src rs_arg_tgt
                  (SimMem.lift sm_arg)
                  ((Frame.mk ms_src rs_init_src lst_src0) :: tail_src)
                  ((Frame.mk ms_tgt rs_init_tgt lst_tgt0) :: tail_tgt)

  .

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
                 ((Frame.mk ms_src rs_init_src lst_src) :: tail_src)
                 ((Frame.mk ms_tgt rs_init_tgt lst_tgt) :: tail_tgt)
                 sm0
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

  Theorem init_lxsim_lift_progress
          st_init_src
          (INITSRC: sem_src.(Smallstep.initial_state) st_init_src)
    :
      exists st_init_tgt,
        <<INITTGT: sem_tgt.(Smallstep.initial_state) st_init_tgt>>
  .
  Proof.
    inv INITSRC; ss.
    rename sk_link into sk_link_src.
    rename st_init into st_init_src.
    rename ms into ms_src. rename m into m_src.
    rename INIT into INITSRC. rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC.
    (* inv MSFIND. *)
    (* rename blk into blk_src. rename if_sig into if_sig_src. rename FPTR into FPTRSRC. *)
    (* rename MODSEM into MODSEMSRC. rename INTERNAL into INTERNALSRC. *)

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    exploit init_sim_ge_strong; eauto. i; des. clarify.
    ss. des_ifs.

    assert(SIMFPTR: SimMem.sim_val sm_init (Genv.symbol_address (Genv.globalenv sk_link_src)
                                                                (prog_main sk_link_src) Ptrofs.zero)
                                   (Genv.symbol_address (Genv.globalenv sk_link_tgt)
                                                        (prog_main sk_link_tgt) Ptrofs.zero)).
    { admit "strengthen sim_skenv specs". }

    exploit find_fptr_owner_fsim; eauto. i; des. clarify.
    inv SIMMS.
    inv MSFIND. inv FINDTGT.
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
    exploit SIM; eauto. i; des.
    bar.
    exploit INITPROGRESS; eauto. i; des.
    esplits; eauto. econs; eauto. econs; eauto.
  Qed.

  Theorem init_lxsim_lift_backward
          st_init_tgt
          (INITTGT: sem_tgt.(Smallstep.initial_state) st_init_tgt)
          (SAFESRC: __guard__ (exists _st_init_src, sem_src.(Smallstep.initial_state) _st_init_src))
    :
      exists idx st_init_src sm_init,
        <<INITTGT: sem_src.(Smallstep.initial_state) st_init_src>>
        /\ <<SIM: lxsim_lift idx st_init_src st_init_tgt sm_init>>
  .
  Proof.
    (* inv SAFESRC; ss. *)
    (* rename sk_link into sk_link_src. *)
    (* rename st_init into st_init_src. *)
    (* rename ms into ms_src. rename m into m_src. *)
    (* rename INIT into INITSRC. rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC. *)
    assert(exists sk_link_src m_src, <<INITSKSRC: link_sk p_src = Some sk_link_src>>
                                                  /\ <<LOADSRC: Sk.load_mem sk_link_src = Some m_src>>).
    { unguard. des. inv SAFESRC. esplits; eauto. } des.

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    exploit init_sim_ge_strong; eauto. i; des. clarify.
    ss. des_ifs.

    assert(SIMFPTR: SimMem.sim_val sm_init (Genv.symbol_address (Genv.globalenv sk_link_src)
                                                                (prog_main sk_link_src) Ptrofs.zero)
                                   (Genv.symbol_address (Genv.globalenv sk_link_tgt)
                                                        (prog_main sk_link_tgt) Ptrofs.zero)).
    { admit "strengthen sim_skenv specs". }

    inv INITTGT. clarify.
    exploit find_fptr_owner_bsim; eauto.
    { unguard. des. inv SAFESRC. clarify. esplits; eauto. } i; des. clarify.
    inv SIMMS.
    inv MSFIND. inv FINDSRC.
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
    bar.
    exploit SIM; eauto. i; des. clear INITPROGRESS.
    exploit INITSIM; eauto. i; des. clear INITSIM.

    destruct msp; ss.
    assert(idx = Ord.idx). { admit "easy". } clarify.
    assert(ord = Ord.ord). { admit "easy". } clarify.

    esplits; eauto.
    - econs; eauto. econs; eauto.
    - econs; eauto.
      + ss. des_ifs.
      + econs; eauto.
      + reflexivity.
  Qed.

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
    rename st_init into st_init_src.
    rename ms into ms_src. rename m into m_src.
    rename INIT into INITSRC. rename INITSK into INITSKSRC. rename INITMEM into INITMEMSRC.
    (* inv MSFIND. *)
    (* rename blk into blk_src. rename if_sig into if_sig_src. rename FPTR into FPTRSRC. *)
    (* rename MODSEM into MODSEMSRC. rename INTERNAL into INTERNALSRC. *)

    exploit sim_link_sk; eauto. i; des. fold p_tgt in LOADTGT.
    exploit init_sim_ge_strong; eauto. i; des. clarify.
    ss. des_ifs.

    assert(SIMFPTR: SimMem.sim_val sm_init (Genv.symbol_address (Genv.globalenv sk_link_src)
                                                                (prog_main sk_link_src) Ptrofs.zero)
                                   (Genv.symbol_address (Genv.globalenv sk_link_tgt)
                                                        (prog_main sk_link_tgt) Ptrofs.zero)).
    { admit "strengthen sim_skenv specs". }

    exploit find_fptr_owner_fsim; eauto. i; des. clarify.
    inv SIMMS.
    inv MSFIND. inv FINDTGT.
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
    exploit SIM; eauto. i; des.
    bar.
    exploit INITPROGRESS; eauto. i; des.
    bar.
    exploit find_fptr_owner_fsim; eauto. { econs; eauto. } i; des.

    remember (ModSemPair.src msp) as srcm. revert Heqsrcm. clarify. i. clears msp.

    inv SIMMS. inv FINDTGT.
    exploit SIM; eauto. i; des.
    exploit INITPROGRESS; eauto. i; des.
    exploit INITSIM; eauto. i; des.
    assert(st_init_src = st_init_src0).
    { eapply ModSem.initial_frame_dtm; eauto. }
    clarify.

    esplits; eauto.
    - econs; ss; cycle 1.
      { ii. eapply initial_state_determ; ss; eauto. }
      econs; eauto.
      econs; eauto.
    - econs; eauto.
      + ss. des_ifs.
      + econs; eauto.
      + reflexivity.
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
    inv LXSIM; ss. rewrite LINKSRC in *. rewrite LINKTGT in *.
    punfold TOP. inv TOP.


    - (* fstep *)
      left.
      econs; ss; eauto.
      + ii. des. inv FINALSRC; ss. exfalso. eapply SAFESRC0. u. eauto.
      + inv FSTEP.
        * econs 1. ii. ss. rewrite LINKSRC in *.
          des.
          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. eauto. }
          { exfalso. eapply SAFESRC0. u. eauto. }
          exploit STEP; eauto. i; des_safe.
          exists i1, ((Frame.mk ms_tgt rs_init_tgt st_tgt1) :: tail_tgt).
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
      + eapply lift_receptive_at; eauto.


    - (* bstep *)
      right. ss.
      econs; ss; eauto.
      + ii. inv FINALTGT. ss. ModSem.tac.
      + ii.
        inv BSTEP.
        * econs 1; eauto.
          ii. inv STEPTGT; ModSem.tac.
          ss. exploit STEP; eauto. i; des_safe.
          exists i1, ((Frame.mk ms_src rs_init_src st_src1) :: tail_src).
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
        esplits; eauto. econs; ss; eauto.
        - admit "find fptr owner progress".
        - admit "initial_frame progress". }

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

      exploit find_fptr_owner_bsim; eauto.
      { esplits; eauto. admit "use SAFESRC". }
      i; des.

      inv SIMMS.
      dup FINDSRC. dup MSFIND.
      inv FINDSRC0; ss. inv MSFIND0; ss.
      specialize (SIM (SimMem.lift sm_arg)).
      exploit SIM; eauto.
      { eapply SimMem.lift_sim_val; eauto. }
      (* { instantiate (2:= PC). rewrite FPTR; ss. des_ifs. unfold Genv.find_funct_ptr. des_ifs. } *)
      (* { rewrite FPTR0. ss. des_ifs. unfold Genv.find_funct_ptr. des_ifs. } *)
      { ii. eapply SimMem.lift_sim_val; eauto. }
      { eapply SimMem.lift_wf; eauto. }
      { u. eapply SimSymb.mlift_preserves_sim_skenv; eauto. }
      i; des_safe.
      exploit INITSIM; eauto. { rewrite SimMem.lift_tgt. eauto. } i; des_safe.
      esplits; eauto.
      + left. apply plus_one. econs; ss; eauto. { erewrite <- SimMem.lift_src. eauto. }
      + right. eapply CIH; eauto.
        {
          instantiate (1:= (SimMem.lift sm_arg)).
          econs.
          * ss. des_ifs. eapply mlift_preserves_sim_ge; eauto.
          * instantiate (1:= (SimMem.lift sm_arg)).
            econs; [eassumption|..]; revgoals.
            { ii. exploit K; eauto. i; des_safe. esplits; eauto.
              ii. exploit KSTEP; eauto. i; des_safe. pclearbot. esplits; eauto.
            }
            { etransitivity; eauto. }
            { ss. des_ifs. }
            { eauto. }
          * reflexivity.
          * eauto.
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
        exploit K; try apply RSREL0; eauto. { erewrite <- mcompat_src; eauto. } i; des.
        esplits; eauto.
        econs 3; ss; eauto.
        erewrite mcompat_tgt; eauto.
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
      exploit K; eauto.
      { specialize (SAFESRC _ (star_refl _ _ _)).
        des; ss.
        { inv SAFESRC. }
        inv SAFESRC; ModSem.tac. ss.
        determ_tac ModSem.final_frame_dtm. erewrite <- mcompat_src; eauto.
      }
      i; des. exploit KSTEP; eauto. i; des.
      esplits; eauto.
      + left. apply plus_one.
        econs 3; ss; eauto.
        erewrite mcompat_src; eauto.
      + right. eapply CIH; eauto.
        instantiate (1:= (SimMem.unlift sm_arg sm0)).
        econs; ss; cycle 1.
        { eauto. }
        { etransitivity; eauto.
          eapply SimMem.unlift_spec; eauto. }
        { erewrite mcompat_tgt in AFTER; eauto. determ_tac ModSem.after_external_dtm. eauto. }
        { des_ifs.
          eapply mle_preserves_sim_ge; eauto.
          eapply SimMem.unlift_spec; eauto. }
  Unshelve.
    all: ss.
  Qed.

End ADQSTEP.




Section ADEQUACY.

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
    econs 2; ss; eauto.
    -
  Qed.

  Theorem adequacy_local
          sem_src
          (LOADSRC: load p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: load p_tgt = Some sem_tgt>> /\ <<SIM: mixed_simulation sem_src sem_tgt>>
  .
  Proof.
    (* exploit sim_load; eauto. i; des. *)
    subst_locals. unfold load in *. des_ifs_safe.
    exploit sim_link_sk; eauto. i; des. des_ifs_safe. clarify.
    rename t into sk_src. rename sk_link_tgt into sk_tgt.
    esplits; eauto.


    exploit sim_progpair_sim_loadpair; eauto. i; des.
    assert(LPSIM := SIM).
    inv SIM.
    econs; eauto.
    econs; eauto.

    eapply xsim_init_forward; ss.
    ii. inv INITSRC. clarify.
    exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. clarify.
    exploit find_fptr_owner_bsim; eauto.
    { instantiate (2:= (Genv.symbol_address (Sk.load_skenv sk_src) (prog_main sk_src) Integers.Ptrofs.zero)).
      instantiate (1:= (Genv.symbol_address (Sk.load_skenv sk_tgt) (prog_main sk_tgt) Integers.Ptrofs.zero)).
      admit "main ptr should be related. obligate this to sim_skenv". }
    { admit "???". }
    { unfold LoadPair.ge_src. unfold load_genv, load_modsems in MSFIND.
      admit "???".
    }
    i; des.

    esplits; eauto.
    - econs; ss; eauto.
      + admit "".
      + admit "determinacy".
    -

    ii.
    inv ujjj
    eapply xsim_init_backward; ss.
    {
      ii. inv INITSRC. clarify.
      exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. clarify.
      exploit find_fptr_owner_bsim; eauto.
      { instantiate (2:= (Genv.symbol_address (Sk.load_skenv sk_src) (prog_main sk_src) Integers.Ptrofs.zero)).
        instantiate (1:= (Genv.symbol_address (Sk.load_skenv sk_tgt) (prog_main sk_tgt) Integers.Ptrofs.zero)).
        admit "main ptr should be related. obligate this to sim_skenv". }
      { }
      esplits; eauto. econs; ss; eauto.
      -
      admit "progress".
    }


    exploit sim_progpair_sim_gepair; eauto. i; des. ss.
    esplits; eauto. clarify.
    inv SIM; ss.
    econstructor 1 with (order := gep.(GePair.ord)); eauto.
    econs; eauto.
    eapply xsim_init_backward; ss.
    { (* progress *)
      i. inv INITSRC. ss.
      inv MSFIND. ss.
      unfold Genv.symbol_address in *. des_ifs.
      Print SimSymb.sim_sk_weak.
      apply SimSymb.sim_sk_sim_sk_weak in SIMSK.
      admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!".
    }
    { (* init *)
      i. inv INITTGT.
      rename ms into ms_tgt.
      assert(exists ms_src, <<SIMMS: sim_modsem order ms_src ms_tgt>>).
      { admit "". } i; des.
      inv SIMMS.
      inv MSFIND.
      unfold Genv.symbol_address in *. des_ifs.
      rename Heq0 into MAINTGT. rename blk into blk_tgt. rename m into m_tgt. rename INITMEM into MEMTGT.
      (* assert(exists blk_tgt m_tgt sm0, *)
      (*           <<WF: SimMem.wf sm0>> *)
      (*           /\ <<MEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt>> *)
      (*           /\ <<MAINTGT: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_tgt>> *)
      (*           /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>> *)
      (*           /\ <<MCOMPAT: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>). *)
      assert(exists blk_src m_src sm0,
                <<WF: SimMem.wf sm0>>
                /\ <<MEMSRC: sk_src.(Sk.load_mem) = Some m_src>>
                /\ <<MAINSRC: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_src>>
                /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>>
                /\ <<MCOMPAT: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>).
      { admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!". }
      i; des.

      hexploit SIM; eauto.
      { instantiate (1:= None). instantiate (1:= None). econs 2; eauto. }
      { instantiate (1:= (Asmregs.Pregmap.init Vundef)). instantiate (1:= (Asmregs.Pregmap.init Vundef)).
        admit "undef sim_val".
      }
      i; des.
      exploit STEP; eauto.
      { rewrite MCOMPAT0. eauto. }
      i; des.
      esplits; eauto.
      esplits; eauto.
      rename m into m_tgt.
      rename st_init into st_init_tgt.
      rename ms into ms_tgt.
      rename INITSK into INITSKTGT.
      rename INITMEM into INITMEMTGT.
      inv MSFIND. ss. clarify.
      rename MODSEM into MODSEMTGT.
      rename 
    }
    { (* init *)
      i. inv INITSRC. inv MSFIND. ss. clarify.
      unfold Genv.symbol_address in *. des_ifs.
      rename Heq into MAINSRC. rename blk into blk_src. rename m into m_src. rename INITMEM into MEMSRC.
      assert(exists blk_tgt m_tgt sm0,
                <<MEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt>>
                /\ <<MAINTGT: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_tgt>>
                /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>>
                /\ <<SIMMS: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>).
      { admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!". }
      des.
      esplits; eauto.
    }
    i. ss.
    tttttttttttttttttttttttt
    exploit sim_load; eauto. i; des.
    esplits; eauto.

    unfold sem in *. des_ifs. rename t into init_sk_tgt. rename t0 into init_sk_src.
    inv SIMPROG.
    inv SIMMOD. admit "".
    assert(Forall2 sim_modsem
    assert(exists wfo, 
    econs; eauto.
    econs; eauto.
    (* Each modsem has mixed sim *)

    assert(Forall3 sim_modsem p_src p_tgt).
    eapply Forall3_impl with (Q:= const sim_modsem) in SIMMOD.
    
  Qed.


End ADEQUACY.


Context `{Linker symbinj}.
Context `{SM: SimMem}.

(* Inductive sim_mod `{SM: SimMem} (si: symbinj) (m_src m_tgt: Mod.t): Prop := *)
(* | sim_mod_intro *)
(*     (SIMSK: sim_sk si m_src.(Mod.sk) m_tgt.(Mod.sk)) *)
(* . *)

Axiom sim_skenv: list symbinj -> SkEnv.t -> SkEnv.t -> Prop.
Axiom sim_modsem: symbinj -> ModSem.t -> ModSem.t -> Prop.



Inductive sim_prog (p_src p_tgt: program): Prop :=
| sim_prog_intro
    sis
    (SIMMOD: Forall3 sim_mod sis p_src p_tgt)
    si_prog
    (LINKSI: link_list sis = Some si_prog)
    (SIMMS: forall
        skenv_src skenv_tgt
        (SIMSKENV: sim_skenv sis skenv_src skenv_tgt)
      ,
        Forall2 (fun m_src m_tgt => sim_modsem (m_src.(Mod.get_modsem) skenv_src m_src.(Mod.data))
                                               (m_tgt.(Mod.get_modsem) skenv_tgt m_tgt.(Mod.data))) p_src p_tgt)
.

Section TRANSF.

  Variable p: program.

End TRANSF.

Section ADEQUACY.

  Variable p_src p_tgt: program.
  Hypothesis SIMPROG: sim_prog p_src p_tgt.

    Theorem xsim_properties_embedded
            L1 L2
            (EMBEDDED: embedded ord0 ord1)
            (XSIM: xsim_properties L1 L2 idx0 ord0)
      :
        <<XSIM: xsim_properties L1 L2 idx1 ord1>>
    .
    Proof.
      admit "easy".
    Qed.

  End LINK_WFO.

  Lemma sim_load
        sem_src
        (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold sem in *.
    des_ifs.
    { esplits; eauto. }
    exfalso.
    unfold init_sk in *.
    admit "".
  Qed.

  Theorem adequacy_machine
          sem_src
          (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>> /\ <<SIM: mixed_simulation sem_src sem_tgt>>
  .
  Proof.
    exploit sim_load; eauto. i; des.
    esplits; eauto.

    unfold sem in *. des_ifs. rename t into init_sk_tgt. rename t0 into init_sk_src.
    inv SIMPROG.
    inv SIMMOD. admit "".
    assert(Forall2 sim_modsem
    assert(exists wfo, 
    econs; eauto.
    econs; eauto.
    (* Each modsem has mixed sim *)

    assert(Forall3 sim_modsem p_src p_tgt).
    eapply Forall3_impl with (Q:= const sim_modsem) in SIMMOD.
    
  Qed.

End ADEQUACY.
