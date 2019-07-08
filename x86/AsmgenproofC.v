Require Import CoqlibC Errors.
Require Import Integers Floats AST Linking.
Require Import ValuesC Memory Events Globalenvs Smallstep.
Require Import Op Locations MachC Conventions ConventionsC AsmC.
Require Import Asmgen Asmgenproof0.
Require Import sflib.
(* newly added *)
Require Export Asmgenproof.
Require Import SimModSem SimMemExt SimSymbId MemoryC ValuesC MemdataC LocationsC StoreArguments Conventions1C.

Require Import Skeleton Mod ModSem SimMod SimSymb SimMem AsmregsC MatchSimModSem.
Require Import JunkBlock.
Require SoundTop.

Local Opaque Z.mul.
Local Existing Instance main_args_some.

Set Implicit Arguments.

Section PRESERVATION.

Variable skenv_link: SkEnv.t.
Variable prog: Mach.program.
Variable tprog: Asm.program.
Let md_src: Mod.t := (MachC.module prog return_address_offset).
Let md_tgt: Mod.t := (AsmC.module tprog).
Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).

Hypothesis TRANSF: match_prog prog tprog.

Let ge := (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) tprog).

Variable sm_link: SimMem.t.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (SM := SimMemExt)
                (md_src.(Mod.modsem) skenv_link)
                (md_tgt.(Mod.modsem) skenv_link)
                tt sm_link.

Definition get_rs (ms: Mach.state) : Mach.regset :=
  match ms with
  | Mach.State _ _ _ _ rs _ => rs
  | Callstate _ _ rs _ => rs
  | Returnstate _ rs _ => rs
  end.

Record agree_eq (ms: Mach.regset) (sp: val) (rs: Asm.regset) (sg: signature): Prop :=
  mkagree
    { agree_sp: rs#SP = sp;
      agree_sp_def: sp <> Vundef;
      agree_mregs_less:
        forall (r: mreg) (IN: In (R r) (regs_of_rpairs (loc_arguments sg))),
          Val.lessdef (ms r) (rs#(preg_of r));
      agree_mregs_eq:
        forall (r: mreg) (NOTIN: ~ In (R r) (regs_of_rpairs (loc_arguments sg))),
          (ms r) = (rs#(preg_of r));
    }.

Definition set_regset (rs0 rs1: Mach.regset) (sg: signature) (mr: mreg) : val :=
  if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
  then rs1 mr else rs0 mr.

Definition set_regset_undef (rs: Mach.regset) (sg: signature) (mr: mreg) : val :=
  if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
  then Vundef else rs mr.

Inductive match_init_data init_sp init_ra
          init_rs_src init_sg_src init_rs_tgt : Prop :=
| match_init_data_intro
    (INITRA: init_ra = init_rs_tgt RA)
    (INITRAPTR: <<TPTR: Val.has_type (init_ra) Tptr>> /\ <<RADEF: init_ra <> Vundef>>)
    (INITRS: agree_eq init_rs_src init_sp init_rs_tgt init_sg_src )
    (SIG: exists fd, tge.(Genv.find_funct) (init_rs_tgt PC) = Some (Internal fd) /\ fd.(fn_sig) = init_sg_src /\ init_sg_src.(sig_cstyle)).

Inductive stack_base (initial_parent_sp initial_parent_ra: val): list Mach.stackframe -> Prop :=
| stack_base_dummy:
    stack_base initial_parent_sp initial_parent_ra
      ((dummy_stack initial_parent_sp initial_parent_ra)::[])
| stack_base_cons
    fr ls
    (TL: stack_base initial_parent_sp initial_parent_ra ls):
    stack_base
      initial_parent_sp initial_parent_ra
      (fr::ls).

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: MachC.state) (st_tgt0: AsmC.state)
          (sm0: SimMem.t): Prop :=
| match_states_intro
    init_sp init_ra
    (* (initial_parent_sp_ptr : ValuesC.is_real_ptr (init_sp)) *)
    (initial_parent_ra_ptr: Val.has_type init_ra Tptr)
    (initial_parent_ra_def: init_ra <> Vundef)
    (initial_parent_ra_junk: forall blk ofs (RAVAL: init_ra = Vptr blk ofs),
        ~ Plt blk (Genv.genv_next skenv_link))
    (* (initial_parent_ra_junk1: tge.(Genv.find_funct) init_ra = None) *)
    (STACKWF: stack_base init_sp init_ra (get_stack st_src0.(MachC.st)))
    (INITDATA: match_init_data
                 init_sp init_ra
                 st_src0.(MachC.init_rs) st_src0.(init_sg) st_tgt0.(init_rs))
    (MATCHST: Asmgenproof.match_states ge st_src0.(MachC.st) st_tgt0)
    (* (SPPTR: ValuesC.is_real_ptr (st_tgt0.(init_rs) RSP)) *)
    (MCOMPATSRC: st_src0.(MachC.st).(MachC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(get_mem) = sm0.(SimMem.tgt))
    (IDX: measure st_src0.(MachC.st) = idx).

Lemma asm_step_dstep init_rs st0 st1 tr
      (STEP: Asm.step skenv_link tge st0 tr st1):
    Simulation.DStep (modsem skenv_link tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  econs.
  - eapply modsem_determinate; et.
  - econs; auto.
Qed.

Lemma asm_star_dstar init_rs st0 st1 tr
      (STEP: star Asm.step skenv_link tge st0 tr st1):
    Simulation.DStar (modsem skenv_link tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  induction STEP; econs; eauto. eapply asm_step_dstep; auto.
Qed.

Lemma asm_plus_dplus init_rs st0 st1 tr
      (STEP: plus Asm.step skenv_link tge st0 tr st1):
    Simulation.DPlus (modsem skenv_link tprog)
                     (mkstate init_rs st0) tr
                     (mkstate init_rs st1).
Proof.
  inv STEP. econs; eauto.
  - eapply asm_step_dstep; eauto.
  - eapply asm_star_dstar; eauto.
Qed.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk))
                      (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge.
Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. Qed.

Lemma transf_function_sig
      fd_src fd_tgt
      (TRANS: transf_function fd_src = OK fd_tgt):
  fd_src.(Mach.fn_sig) = fd_tgt.(fn_sig).
Proof. repeat unfold transf_function, bind, transl_function in *. des_ifs. Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := top4); eauto; ii; ss.

  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.

  - inv INITTGT; cycle 1.
    { ss. des_safe. inv SAFESRC. inv SIMARGS; ss. }
    des. inv SAFESRC. destruct sm_arg, args_src; ss. inv SIMARGS; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.

    assert (SRCSTORE: exists rs_src m_src,
               StoreArguments.store_arguments src rs_src (typify_list vs_src (sig_args (fn_sig fd))) (fn_sig fd) m_src /\
           agree_eq rs_src (Vptr (Mem.nextblock src)
                          Ptrofs.zero) rs (fn_sig fd) /\ Mem.extends m_src m0).
    { inv TYP.
      exploit store_arguments_parallel_extends.
      - eapply typify_has_type_list. eauto.
      - exploit SkEnv.revive_incl_skenv; try eapply INCLTGT; eauto. i. des. inv WF.
        eapply WFPARAM in H; eauto.
      - instantiate (1:= typify_list vs_src (sig_args (fn_sig fd))).
        eapply lessdef_list_typify_list; eauto. erewrite lessdef_list_length; eauto.
      - eapply MWF.
      - inv STORE. eauto.
      - i. des. exists (set_regset rs_src (to_mregset rs) (fn_sig fd)).
        esplits; eauto.
        + clear - ARGTGT. inv ARGTGT. econs; eauto.
          eapply extcall_arguments_same; eauto.
          i. unfold set_regset. des_ifs.
          eapply Loc.notin_not_in in n. contradiction.
        + inv STORE. econs; eauto.
          * inv MWF. rewrite mext_next. eauto.
          * intros X. inv X.
          * i. unfold set_regset. des_ifs.
            eapply val_inject_id. eapply AGREE.
          * i. unfold set_regset. des_ifs.
            eapply LocationsC.Loc_not_in_notin_R in NOTIN. contradiction.
    }

    destruct SRCSTORE as [rs_src [m_src [SRCSTORE [AGREE EXTENDS]]]]. inv AGREE.
    exists (MachC.mkstate
              rs_src (fn_sig fd)
              (Callstate
                 [dummy_stack (Vptr (Mem.nextblock src) Ptrofs.zero) (rs RA)]
                 fptr_src rs_src (assign_junk_blocks m_src n))).
    inv FPTR; ss.
    esplits; auto; ss.
    + inv TYP0. clear_tac.
      assert(SIG2: fn_sig fd = (Mach.fn_sig fd0)).
      { hexploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. i; des.
        folder. ss; try unfold bind in *; des_ifs.
        symmetry. eapply transf_function_sig; eauto.
      }
      econs; auto.
      * eauto.
      * ss.
      * ss.
      * econs; eauto; ss; eauto with congruence.
      * ss.
      * ii. erewrite (agree_mregs_eq0 mr) in *; auto. unfold NW. apply NNPP. intro T.
        exploit PTRFREE; eauto.
        { instantiate (1:= preg_of mr). intro U. contradict T.
          unfold is_junk_value in U. unfold is_junk_value. des_ifs. des. split; ss.
          - erewrite Mem.valid_block_extends; eauto.
          - erewrite Mem.valid_block_extends; eauto.
            eapply assign_junk_block_extends; et.
        }
        i. des.
        -- rewrite Asm.to_preg_to_mreg in *. clarify.
        -- destruct mr; clarify.
        -- destruct mr; clarify.
    + instantiate (1:= mk (assign_junk_blocks m_src n) (assign_junk_blocks m0 n)).
      econs; try eapply RADEF; ss; eauto.
      * econs; eauto.
      * econs; ss; eauto.
      * econs; eauto; ss; try by (econs; eauto).
        { eapply assign_junk_block_extends; et. }
        econs; eauto. i.
        destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (fn_sig fd))))); eauto.
        erewrite agree_mregs_eq0; auto.

  - ss. des. inv SAFESRC. inv SIMARGS; ss. destruct sm_arg; ss. clarify.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.
    hexploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. i; des. ss; unfold bind in *; des_ifs. rename f into fd_tgt.
    inv TYP.
    assert(SIG: fn_sig fd_tgt = (Mach.fn_sig fd)).
    { hexploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. i; des.
      folder. ss; try unfold bind in *; des_ifs.
      symmetry. eapply transf_function_sig; eauto.
    }
    assert (exists rs_tgt m_tgt,
               (<<STORE: AsmC.store_arguments tgt rs_tgt
                                              (typify_list vs_tgt (sig_args (Mach.fn_sig fd)))
                                              (* (Args.vs args_tgt) *)
                                              (Mach.fn_sig fd) m_tgt>>) /\
               (<<RSPC: rs_tgt PC = fptr_tgt>>) /\
               (<<RSRA: rs_tgt RA = Vnullptr>>) /\
               (<<PTRFREE: forall pr (PTR: ~ is_junk_value m0 (assign_junk_blocks m0 n) (rs_tgt pr)),
                   (<<INARG: exists mr,
                       (<<MR: to_mreg pr = Some mr>>) /\
                       (<<ARG: In (R mr) (regs_of_rpairs (loc_arguments (Mach.fn_sig fd)))>>)>>) \/
                   (<<INPC: pr = PC>>) \/
                   (<<INRSP: pr = RSP>>)>>)).
    { exploit StoreArguments.store_arguments_progress.
      - instantiate (2:=typify_list vs_tgt (sig_args (Mach.fn_sig fd))).
        eapply typify_has_type_list.
        erewrite <- lessdef_list_length; eauto.
      - exploit SkEnv.revive_incl_skenv; try eapply INCLTGT; eauto. i. des. inv WF.
        eapply WFPARAM in H0. eauto. ss. rewrite <- SIG. ss.
      - instantiate (1:= n). i. des.
        exists ((to_pregset (set_regset_undef rs0 (Mach.fn_sig fd)))
                  #PC <- fptr_tgt
                  #RA <- Vnullptr
                  #RSP <- (Vptr (Mem.nextblock tgt) Ptrofs.zero)).
        esplits; eauto.
        + split; ss. inv STR. econs; eauto. eapply extcall_arguments_same; eauto. i.
          { assert (NNIN: ~ Loc.notin (R r) (regs_of_rpairs (loc_arguments (Mach.fn_sig fd)))).
            { intros X. eapply Loc.notin_not_in; eauto. }
            unfold set_regset_undef, to_pregset, to_mregset, Pregmap.set, to_preg, preg_of, to_mreg in *.
            destruct r; eauto; des_ifs; try contradiction.
          }
        + i.
          assert (NNIN: forall mr, ~ Loc.notin (R mr) (regs_of_rpairs (loc_arguments (Mach.fn_sig fd))) -> In (R mr) (regs_of_rpairs (loc_arguments (Mach.fn_sig fd)))).
          { intros mr NIN. clear - NIN.
            eapply NNPP. intros X.
            eapply LocationsC.Loc_not_in_notin_R in X. des. contradiction. }
          clear - NNIN PTR.
          unfold set_regset_undef, to_pregset, to_mregset, Pregmap.set, to_preg, preg_of, to_mreg in *.
          destruct pr; des_ifs; ss; eauto.
          exfalso. apply PTR. ss.
    }
    des. eexists. econs; eauto; swap 1 2.
    + folder. inv FPTR; ss. eauto.
    + congruence.
    + rewrite RSRA. econs; ss.
    + rewrite RSRA. ss.
    + rewrite SIG. econs; eauto. rewrite <- LEN. symmetry. eapply lessdef_list_length. eauto.
    + erewrite <- transf_function_sig; eauto.
    + erewrite <- transf_function_sig; eauto. ii. hexploit PTRFREE0; et.
      ii. apply PTR. unfold is_junk_value in *. des_ifs.
      unfold Mem.valid_block. unfold Mem.valid_block in H0.
      rewrite assign_junk_blocks_nextblock in *.
      inv STORE. inv STORE0. inv H1. rewrite <- NB0. rewrite <- NB in *.
      erewrite Mem.nextblock_alloc; eauto.
      erewrite (Mem.nextblock_alloc src) in H0; eauto.
      inv MWF. rewrite <- mext_next. des; esplits; eauto; try xomega.
  - inv MATCH; ss. destruct st_src0, st_tgt0, sm0. ss. inv MATCHST; ss.

  - ss. inv CALLSRC. inv MATCH. inv INITDATA. inv MATCHST. ss.
    destruct st_tgt0. ss. clarify. des.
    inv FPTR; ss. destruct (rs0 PC) eqn:PCEQ; ss. des_ifs.

    exploit Asmgenproof0.extcall_arguments_match; eauto.
    intros TGRARGS. des.
    exploit Mem.free_parallel_extends; eauto. intros TGTFREE. des. esplits; ss.
    + econs; eauto.
      * r in TRANSF. r in TRANSF.
        exploit (SimSymbId.sim_skenv_revive TRANSF); eauto.
        { apply SIMSKENV. }
        intro GE. apply (fsim_external_funct_id GE); ss.
      * inv STACKS; ss.
        -- inv STACKWF; [|inv TL]. inv ATLR; auto; exfalso; auto.
        -- destruct ra; ss; try inv H0. inv ATLR. ss.
      * inv AG. rewrite agree_sp0. clarify.
    + instantiate (1:=mk m1 m2'). econs; ss; eauto.
    + ss.

  - inv AFTERSRC. ss. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. inv SIMRET; ss. destruct sm_ret. ss. clarify.
    exploit Mem_unfree_parallel_extends; try eapply UNFREE; eauto.
    intros TGTUNFREE. des. esplits; auto.
    + econs; ss; eauto.
      * exists skd. esplits; eauto. replace (r PC) with fptr; auto. inv FPTR; ss.
      * inv AG. rewrite agree_sp0. eauto.
    + instantiate (1:= mk m1 m2'). inv INITRS. inv AG.
      econs; ss; eauto; econs; eauto.
      * econs; eauto.
      * unfold loc_external_result, regset_after_external, Mach.regset_after_external.
        apply agree_set_other; auto. apply agree_set_pair; auto.
        econstructor; ss; eauto.
        intros. rewrite to_preg_to_mreg.
        destruct (Conventions1.is_callee_save r0) eqn:T; eauto.

  - ss. inv FINALSRC. des. clarify. destruct st_tgt0, st. inv MATCH. inv MATCHST.
    inv INITDATA. destruct sm0. ss. clarify.
    inv STACKWF; [|inv TL]. inv STACKS; [|inv H7; ss]. inv INITRS.
    exploit Mem.free_parallel_extends; eauto. intros TGTFREE. des.
    esplits; auto.
    + econs; ss; eauto.
      * replace (r PC) with (init_rs0 RA).
        { clear - initial_parent_ra_junk. unfold external_state. des_ifs.
          exploit initial_parent_ra_junk; ss; eauto.
          unfold Genv.find_funct_ptr, Genv.find_def in *. des_ifs.
          eapply Genv.genv_defs_range in Heq1. ss.
        }
        inv ATPC; auto.
        exfalso. auto.
      * inv ATPC; auto. exfalso. auto.
      * unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs.
        exfalso. exploit Genv.genv_defs_range; eauto. eapply initial_parent_ra_junk; ss.
      * inv AG. i.
        { eapply Val.lessdef_trans.
          - erewrite <- agree_mregs_eq0; auto. ii.
            eapply loc_args_callee_save_disjoint; eauto.
          - eauto.
        }
      * inv AG. rewrite agree_sp0. ss.
    + econs; simpl; ss.
      * ss. inv AG. auto.
      * instantiate (1:= mk _ _). ss.
      * ss.
    + ss.

  - left; i. ss. esplits.
    + eapply MachC.modsem_receptive; et.

    + i. inv STEPSRC. inv MATCH. set (INITDATA0 := INITDATA). inv INITDATA0.
      inv INITRAPTR. inv INITRS0. clarify.
      exploit step_simulation; ss; try apply agree_sp_def0; eauto.
      { eapply make_match_genvs; eauto. apply SIMSKENV. }
      i. des; ss; esplits; auto; clarify.
      * left. instantiate (1 := mkstate st_tgt0.(init_rs) S2'). ss.
        destruct st_tgt0. eapply asm_plus_dplus; eauto.
      * instantiate (1 := mk (MachC.get_mem (MachC.st st_src1)) (get_mem S2')).
        econs; ss; eauto.
        { instantiate (1:=init_rs st_tgt0 RSP).
          destruct st_src0, st_src1. clear - STEP STACKWF NOTDUMMY.
          inv STEP; ss; clarify.
          - econs. ss.
          - inv STACKWF; ss.
        }
        rewrite <- INITRS. rewrite <- INITFPTR. auto.
      * right. split; eauto. apply star_refl.
      * instantiate (1 := mk (MachC.get_mem (MachC.st st_src1))
                             st_tgt0.(st).(get_mem)).
        econs; ss; eauto.
        { instantiate (1:=init_rs st_tgt0 RSP).
          destruct st_src0, st_src1. clear - STEP STACKWF NOTDUMMY.
          inv STEP; ss; clarify.
          - econs. ss.
          - inv STACKWF; ss.
        }
        rewrite <- INITRS. rewrite <- INITFPTR. auto.

  Unshelve.
    all: ss.
Qed.

End PRESERVATION.



Section SIMMOD.

Variable prog: Mach.program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Definition mp: ModPair.t := ModPair.mk (MachC.module prog return_address_offset) (AsmC.module tprog) tt.

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - r. eapply Sk.match_program_eq; eauto.
    ii. destruct f1; ss.
    + clarify. right. unfold bind in MATCH. des_ifs. esplits; eauto.
      unfold transf_function, transl_function, bind in *. des_ifs.
    + clarify. left. esplits; eauto.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
