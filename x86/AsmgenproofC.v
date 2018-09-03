Require Import CoqlibC Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations MachC Conventions AsmC.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
Require Import sflib.
(* newly added *)
Require Export Asmgenproof AsmgenproofC0 AsmgenproofC1.
Require Import ModSem SimModSem SimSymbId SimMemExtends SimSymbId MemoryC.

Require Import Skeleton Mod ModSem SimMod SimSymb SimMem AsmregsC MatchSimModSem.

Local Opaque Z.mul.

Set Implicit Arguments.

Section PRESERVATION.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).

Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).

Definition msp: ModSemPair.t :=
  ModSemPair.mk (SM := SimMemExtends)
                (MachC.modsem return_address_offset skenv_link_src prog)
                (AsmC.modsem skenv_link_tgt tprog) tt sm_link.

Definition get_rs (ms: Mach.state) : Mach.regset :=
  match ms with
  | Mach.State _ _ _ _ rs _ => rs
  | Callstate _ _ rs _ => rs
  | Returnstate _ rs _ => rs
  end.

Record agree_eq (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#SP = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, (ms r) = (rs#(preg_of r))
}.

Inductive match_init_data init_sp init_ra
          init_rs_src init_sg_src init_rs_tgt : Prop :=
| match_init_data_intro
    (INITRA: init_ra = init_rs_tgt RA)
    (INITRAPTR: wf_RA (init_ra))
    (INITRS: agree_eq init_rs_src init_sp init_rs_tgt)
    (SIG: exists skd, skenv_link_tgt.(Genv.find_funct) (init_rs_tgt PC) = Some skd /\ SkEnv.get_sig skd = init_sg_src)
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: MachC.state) (st_tgt0: AsmC.state)
          (sm0: SimMem.t): Prop :=
| match_states_intro
    init_sp init_ra
    (INITDATA: match_init_data
                 init_sp init_ra
                 st_src0.(MachC.init_rs) st_src0.(init_sg) st_tgt0.(init_rs))
    (MATCHST: AsmgenproofC1.match_states ge init_sp init_ra st_src0.(MachC.st) st_tgt0)
    (MCOMPATSRC: st_src0.(MachC.st).(MachC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (IDX: measure st_src0.(MachC.st) = idx)
.

Lemma asm_step_dstep init_rs st0 st1 tr
      (STEP: Asm.step tge st0 tr st1)
  :
    Simulation.DStep (modsem skenv_link_tgt tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  econs.
  - eapply modsem_determinate.
  - econs; auto.
Qed.

Lemma asm_star_dstar init_rs st0 st1 tr
      (STEP: star Asm.step tge st0 tr st1)
  :
    Simulation.DStar (modsem skenv_link_tgt tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  induction STEP; econs; eauto.
  eapply asm_step_dstep; auto.
Qed.

Lemma asm_plus_dplus init_rs st0 st1 tr
      (STEP: plus Asm.step tge st0 tr st1)
  :
    Simulation.DPlus (modsem skenv_link_tgt tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  inv STEP. econs; eauto.
  - eapply asm_step_dstep; eauto.
  - eapply asm_star_dstar; eauto.
Qed.

Lemma MATCH_GENV: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof.
Admitted.

Theorem unfree_parallel_extends:
  forall m1 m2 b lo hi m1',
  Mem.extends m1 m2 ->
  Mem_unfree m1 b lo hi = Some m1' ->
  exists m2',
     Mem_unfree m2 b lo hi = Some m2'
  /\ Mem.extends m1' m2'.
Proof.
Admitted.

Lemma revive_signature v fd
      (FIND: Genv.find_funct tge v = Some (Internal fd))
  :
      Genv.find_funct skenv_link_tgt v = Some (Internal fd.(fn_sig)).
Admitted.

Lemma sim_find_funct_ptr b fd_src fd_tgt
      (FINDSRC: Genv.find_funct_ptr ge b = Some (Internal fd_src))
      (FINDTGT: Genv.find_funct_ptr tge b = Some (Internal fd_tgt))
  :
      fd_tgt.(fn_sig) = fd_src.(Mach.fn_sig).
Admitted.

Lemma sim_find_funct_ptr2 b fd_src
      (FINDSRC: Genv.find_funct_ptr ge b = Some (Internal fd_src))
  :
    exists fd_tgt,
      <<FINDF: Genv.find_funct_ptr tge b = Some (Internal fd_tgt)>> /\
      <<SIGEQ: fd_tgt.(fn_sig) = fd_src.(Mach.fn_sig)>>.
Admitted.

Lemma sim_find_funct v_src v_tgt fd_src fd_tgt (LE: Val.lessdef v_src v_tgt)
      (FINDSRC: Genv.find_funct ge v_src = Some (Internal fd_src))
      (FINDTGT: Genv.find_funct tge v_tgt = Some (Internal fd_tgt))
  :
      fd_tgt.(fn_sig) = fd_src.(Mach.fn_sig).
Proof.
  destruct v_src, v_tgt; ss. inv LE. des_ifs.
  eapply sim_find_funct_ptr; eauto.
Qed.
Lemma sim_find_funct2 v_src v_tgt fd_src (LE: Val.lessdef v_src v_tgt)
      (FINDSRC: Genv.find_funct ge v_src = Some (Internal fd_src))
  :
    exists fd_tgt,
      <<FINDF: Genv.find_funct tge v_tgt = Some (Internal fd_tgt)>> /\
      <<SIGEQ: fd_tgt.(fn_sig) = fd_src.(Mach.fn_sig)>>.
Proof.
  destruct (v_src); ss. des_ifs. inv LE.
  exploit sim_find_funct_ptr2; eauto.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := top4); eauto; ii.

  - apply lt_wf.

  - destruct sm_arg, args_src, args_tgt. inv SIMARGS. ss. clarify.
    inv INITTGT. des. ss. clarify. inv RAPTR.
    assert (SRCSTORE: exists rs_src m_src,
               MachC.store_arguments src rs_src vs (fn_sig fd) m_src /\
           agree_eq rs_src (Vptr (Mem.nextblock src)
                          Ptrofs.zero true) rs /\ Mem.extends m_src m).
    { admit "". } destruct SRCSTORE as [rs_src [m_src [SRCSTORE [AGREE EXTENDS]]]].
    inv AGREE.
    exists (MachC.mkstate
              rs_src (fn_sig fd)
              (Callstate
                 [dummy_stack
                    (Vptr (Mem.nextblock src)
                          Ptrofs.zero true) (rs RA)]
                 fptr rs_src m_src)).
    esplits; auto.
    + inv SAFESRC. ss.
      econs; auto.
      * eapply sim_find_funct; eauto.
      * ss.
      * ii. exploit PTRFREE; eauto.
        eapply Asm.to_preg_to_mreg.
        rewrite (agree_mregs0 mr) in *. auto.
    + instantiate (1:= mk m_src m).
      econs; ss; econs; ss; eauto; try by (econs; eauto).
      * exists (Internal fd.(fn_sig)). esplits; auto.
        eapply revive_signature. auto.
      * econs; ss.
        i. rewrite agree_mregs0. econs.

  - ss. des. inv SIMARGS. destruct sm_arg. ss. clarify.
    inv SAFESRC.
    exploit sim_find_funct2; eauto. i. des.
    assert (exists rs_tgt m_tgt,
               <<STORE: AsmC.store_arguments (Args.m args_tgt) rs_tgt (Args.vs args_tgt)
                                    (fn_sig fd_tgt) m_tgt>> /\
               <<RSPC: rs_tgt PC = Args.fptr args_tgt>> /\
               <<RSRA: rs_tgt RA = Vnullptr>> /\
               <<PTRFREE: forall (pr : preg) (mr : mreg),
                 Asm.to_mreg pr = Some mr ->
                 ~ In (R mr) (regs_of_rpairs (loc_arguments (fn_sig fd_tgt))) ->
                 ~ ValuesC.is_real_ptr (rs_tgt pr)>>).
    { admit "". } des.
    eexists. econs; eauto.
    + rewrite SIGEQ. auto.
    + rewrite RSRA. econs; ss.

  - inv MATCH; ss. destruct st_src0, st_tgt0, sm0. ss. inv MATCHST; ss.

  - ss. inv CALLSRC. inv MATCH. inv INITDATA. inv MATCHST. ss.
    destruct st_tgt0. ss. clarify.
    des.
    inv FPTR; ss. destruct (rs0 PC) eqn:PCEQ; ss. des_ifs.
    exploit Asmgenproof0.extcall_arguments_match; eauto. intros TGRARGS. des.
    exploit Mem.free_parallel_extends; eauto. intros TGTFREE. des.
    esplits; ss.
    + econs; eauto.
      * r in TRANSF. r in TRANSF.
        exploit (SimSymbId.sim_skenv_revive TRANSF); eauto.
        { ii. destruct f_src, f_tgt; ss; try unfold bind in *; des_ifs. }
        intro GE.
        apply (sim_external_id GE); ss.
      * exists skd0. des_ifs. esplits; auto.
        destruct SIMSKENVLINK.
        eapply SimSymb.simskenv_func_fsim; eauto.
        { econs. }
        { ss. }
      * inv AG. rewrite agree_sp0. clarify.
      * inv INITRAPTR. inv STACKS; ss.
        -- inv ATLR; auto. exfalso; auto.
        -- destruct ra; ss; try inv H0. inv ATLR. ss.
    + instantiate (1:=mk m1 m2'). econs; ss; eauto.
    + ss.

  - inv AFTERSRC. ss. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. inv SIMRET. destruct sm_ret. ss. clarify.
    exploit unfree_parallel_extends; try eapply UNFREE; eauto.
    intros TRTUNFREE. des.
    esplits; auto.
    + econs.
      * exists skd. esplits; eauto.
        replace (r PC) with fptr; auto.
        { destruct SIMSKENVLINK. eapply SimSymb.simskenv_func_fsim; eauto. econs; eauto. }
        inv FPTR; ss.
      * ss.
      * inv AG. rewrite agree_sp0. eauto.
      * eauto.
    + instantiate (1:= mk m1 m2'). inv INITRS. inv AG.
      econs; ss; eauto; econs; eauto.
      econs; eauto.
      unfold loc_external_result, regset_after_external, Mach.regset_after_external.
      apply agree_set_other; auto. apply agree_set_pair; auto.
      econstructor; ss; eauto.
      intros. rewrite to_preg_to_mreg.
      destruct (Conventions1.is_callee_save r0) eqn:T; eauto.
  - ss. inv FINALSRC. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. destruct sm0. ss. clarify.
    exploit Mem.free_parallel_extends; eauto. intros TGTFREE. des.
    esplits; auto.
    + econs.
      * inv INITRS. inv AG.
        i. eapply Val.lessdef_trans. rewrite <- agree_mregs0.
        eapply CALLEESAVE; auto. auto.
      * inv INITRS. inv STACKS; [|inv H7]; rewrite H0. ss.
      * exists skd. instantiate (1:=init_sg). esplits; auto.
      * instantiate (1 := m2'). eauto.
      * eapply RETV.
      * inv STACKS; [|inv H7].
        replace (r PC) with (init_rs0 RA).
        { inv INITRAPTR. destruct (init_rs0 RA); ss. des_ifs. }
        inv ATPC; auto.
        inv INITRAPTR. exfalso. auto.
      * inv STACKS; [|inv H7].
        inv ATPC; auto. inv INITRAPTR. exfalso. auto.
      * eauto.
      * inv INITRS. inv AG.
        rewrite agree_sp0.
        inv STACKS; [|inv H7]; rewrite H0. ss.
    + econs; simpl.
      * ss. inv AG. auto.
      * instantiate (1:= mk _ _). ss.
      * ss.
    + ss.

  - ss. esplits.
    + eapply MachC.modsem_receptive.
      intros f c ofs of' RAO0 RAO1. inv RAO0. inv RAO1.
      rewrite TC in *. rewrite TF in *. clarify.
      exploit code_tail_unique. apply TL. apply TL0.
      intros EQ. destruct ofs, of'. ss. clarify.
      f_equal. apply proof_irrelevance.

    + i. inv STEPSRC. inv MATCH. set (INITDATA0 := INITDATA). inv INITDATA0.
      inv INITRAPTR. inv INITRS0. clarify.
      exploit step_simulation; ss; try apply agree_sp_def0; eauto.
      { apply MATCH_GENV. }
      i. des; ss; esplits; auto; clarify.
      * left. instantiate (1 := mkstate st_tgt0.(init_rs) S2'). ss.
        destruct st_tgt0. eapply asm_plus_dplus; eauto.
      * instantiate (1 := mk (MachC.get_mem (MachC.st st_src1)) (get_mem S2')).
        econs; ss; eauto.
        rewrite <- INITRS. rewrite <- INITFPTR. auto.
      * right. split; eauto. apply star_refl.
      * instantiate (1 := mk (MachC.get_mem (MachC.st st_src1))
                             st_tgt0.(st).(get_mem)).
        econs; ss; eauto.
        rewrite <- INITRS. rewrite <- INITFPTR. auto.

  Unshelve.
    all: ss.
    apply 0%nat.
Qed.
    
End PRESERVATION.
