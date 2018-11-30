Require Import CoqlibC Errors.
Require Import Integers Floats AST Linking.
Require Import ValuesC Memory Events Globalenvs Smallstep.
Require Import Op Locations MachC Conventions AsmC.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
Require Import sflib.
(* newly added *)
Require Export Asmgenproof AsmgenproofC0 AsmgenproofC1.
Require Import ModSem SimModSem SimSymbId SimMemExt SimSymbId MemoryC ValuesC.

Require Import Skeleton Mod ModSem SimMod SimSymb SimMem AsmregsC MatchSimModSem.
Require SoundTop.

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
  ModSemPair.mk (SM := SimMemExt)
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
    (SIG: exists fd, tge.(Genv.find_funct) (init_rs_tgt PC) = Some (Internal fd) /\ fd.(fn_sig) = init_sg_src)
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
    (MATCHST: AsmgenproofC1.match_states ge skenv_link_src init_sp init_ra st_src0.(MachC.st) st_tgt0)
    (NOTVOL: not_volatile skenv_link_src (st_tgt0.(init_rs) RSP))
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

Let SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof.
  admit "this does not hold -- TODO: unify with RenumberproofC
-- TODO: by exploiting MFUTURE in SimModSem.v, we may able to simplify this.".
Qed.

Lemma transf_function_sig
      fd_src fd_tgt
      (TRANS: transf_function fd_src = OK fd_tgt)
  :
    fd_src.(Mach.fn_sig) = fd_tgt.(fn_sig)
.
Proof. repeat unfold transf_function, bind, transl_function in *. des_ifs. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := top4); eauto; ii.

  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - destruct sm_arg, args_src, args_tgt. inv SIMARGS. ss. clarify.
    inv INITTGT. des. ss. clarify. inv RAPTR.
    assert (SRCSTORE: exists rs_src m_src,
               MachC.store_arguments src rs_src (typify_list vs (sig_args (fn_sig fd))) (fn_sig fd) m_src /\
           agree_eq rs_src (Vptr (Mem.nextblock src)
                          Ptrofs.zero true) rs /\ Mem.extends m_src m).
    { clear - SAFESRC STORE VALS.
      admit "this should hold...".
    }
    destruct SRCSTORE as [rs_src [m_src [SRCSTORE [AGREE EXTENDS]]]].
    inv AGREE.
    exists (MachC.mkstate
              rs_src (fn_sig fd)
              (Callstate
                 [dummy_stack
                    (Vptr (Mem.nextblock src)
                          Ptrofs.zero true) (rs RA)]
                 fptr rs_src m_src)).
    inv FPTR; cycle 1.
    { clear - SAFESRC. inv SAFESRC. ss. }
    esplits; auto.
    + inv SAFESRC. ss.
      inv TYP. clear_tac.
      assert(SIG: fn_sig fd = Mach.fn_sig fd0).
      {
        hexploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. i; des.
        folder. ss; try unfold bind in *; des_ifs.
        symmetry. eapply transf_function_sig; eauto.
      }
      econs; auto.
      * eauto.
      * ss.
      * econs; eauto. ss. eauto with congruence.
      * ss.
      * ii. rewrite (agree_mregs0 mr) in *. exploit PTRFREE; eauto.
        i. des.
        -- rewrite Asm.to_preg_to_mreg in *. clarify.
        -- destruct mr; clarify.
        -- destruct mr; clarify.
    + instantiate (1:= mk m_src m).
      assert (NOTVOL: not_volatile skenv_link_src (Vptr (Mem.nextblock src) Ptrofs.zero true)).
      { econs. destruct (Senv.block_is_volatile skenv_link_src (Mem.nextblock src)) eqn: EQ; auto.
        exfalso. eapply Senv.block_is_volatile_below in EQ. subst ge.
        clear - SIMSKENVLINK MWF MEMWF EQ. apply Mem.mext_next in MWF. rewrite MWF in *.
        eapply Plt_strict. eapply Plt_Ple_trans. eapply EQ.
        destruct SIMSKENVLINK. inv H. ss. }
      econs; ss.
      * econs; ss; eauto. econs; eauto.
      * econs; eauto; ss; try by (econs; eauto).
        -- econs; eauto. i. rewrite agree_mregs0. econs.
        -- destruct SIMSKENVLINK. inv H. etrans; eauto.
           clear - MWF SRCSTORE.
           apply Mem.mext_next in MWF. rewrite <- MWF in *.
           inv SRCSTORE. rewrite <- NB.
           eapply Mem.nextblock_alloc in ALC. rewrite ALC. eapply Ple_succ.
      * rewrite agree_sp0. auto.

  - ss. des. inv SIMARGS. destruct sm_arg. ss. clarify.
    inv SAFESRC.
    hexploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. i; des. ss; unfold bind in *; des_ifs. rename f into fd_tgt.
    assert (exists rs_tgt m_tgt,
               (<<STORE: AsmC.store_arguments (Args.m args_tgt) rs_tgt (Args.vs args_tgt)
                                              (fn_sig fd_tgt) m_tgt>>) /\
               (<<RSPC: rs_tgt PC = Args.fptr args_tgt>>) /\
               (<<RSRA: rs_tgt RA = Vnullptr>>) /\
               (<<PTRFREE: forall pr (PTR: is_real_ptr (rs_tgt pr)),
                   (<<INARG: exists mr,
                       (<<MR: to_mreg pr = Some mr>>) /\
                       (<<ARG: In (R mr) (regs_of_rpairs (loc_arguments (Mach.fn_sig fd)))>>)>>) \/
                   (<<INPC: pr = PC>>) \/
                   (<<INRSP: pr = RSP>>)>>)).
    { admit "this should hold...". } des.
    eexists. econs; eauto.
    + folder. inv FPTR; ss. rewrite <- H1 in *. ss.
    + inv TYP. rp; eauto. repeat f_equal. symmetry. eapply transf_function_sig; eauto.
    + ss. destruct SIMSKENVLINK. inv H0.
      apply Mem.mext_next in MWF. rewrite <- MWF in *. auto.
    + rewrite RSRA. econs; ss.
    + erewrite <- transf_function_sig; eauto.
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
        apply (sim_external_funct_id GE); ss.
      * exists skd. des_ifs. esplits; auto.
        destruct SIMSKENVLINK.
        eapply SimSymb.simskenv_func_fsim; eauto.
        { econs. }
        { ss. }
      * inv AG. rewrite agree_sp0. clarify.
      * inv INITRAPTR. inv STACKS; ss.
        -- inv ATLR; auto. exfalso; auto.
        -- destruct ra; ss; try inv H0. inv ATLR. ss.
      * rewrite RSP in *. inv NOTVOL0. ss. unfold Genv.block_is_volatile in *.
        destruct SIMSKENVLINK. inv H. des_ifs.
    + instantiate (1:=mk m1 m2'). econs; ss; eauto.
    + ss.

  - inv AFTERSRC. ss. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. inv SIMRET. destruct sm_ret. ss. clarify.
    exploit Mem_unfree_parallel_extends; try eapply UNFREE; eauto.
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
      * econs; eauto.
      * unfold loc_external_result, regset_after_external, Mach.regset_after_external.
        apply agree_set_other; auto. apply agree_set_pair; auto.
        econstructor; ss; eauto.
        intros. rewrite to_preg_to_mreg.
        destruct (Conventions1.is_callee_save r0) eqn:T; eauto.
      * eapply Mem_nextblock_unfree in UNFREE. rewrite <- UNFREE. auto.
  - ss. inv FINALSRC. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. destruct sm0. ss. clarify.
    exploit Mem.free_parallel_extends; eauto. intros TGTFREE. des.
    esplits; auto.
    + econs.
      * inv INITRS. inv AG.
        i. eapply Val.lessdef_trans. rewrite <- agree_mregs0.
        eapply CALLEESAVE; auto. auto.
      * inv INITRS. inv STACKS; [|inv H7]; rewrite H0. ss.
      * exists fd. eauto.
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
