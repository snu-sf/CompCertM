Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC EventsC Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
(** newly added **)
Require Import Mach Simulation ValuesC.
Require Export Asm.
Require Import Skeleton ModSem Mod sflib.
Require Import LocationsC AsmregsC StoreArguments.
Require Import JunkBlock.

Set Implicit Arguments.

Local Obligation Tactic := ii; ss; des; inv_all_once; des; ss; clarify; eauto with congruence.

Definition get_mem (st: state): mem :=
  match st with
  | State _ m0 => m0
  end.

Definition st_rs (st0: state): regset :=
  match st0 with
  | State rs _ => rs
  end.

Definition st_m (st0: state): mem :=
  match st0 with
  | State _ m => m
  end.

Definition store_arguments (m0: mem) (rs: regset) (vs: list val) (sg: signature) (m2: mem) : Prop :=
  (<<STORE: StoreArguments.store_arguments m0 (to_mregset rs) vs sg m2>>) /\
  (<<RSRSP: rs RSP = Vptr m0.(Mem.nextblock) Ptrofs.zero>>).

Definition external_state F V (ge: Genv.t F V) (v : val) : bool :=
  match v with
  | Vptr blk ofs =>
    match (Genv.find_funct ge (Vptr blk Ptrofs.zero)) with
    | None => true
    | _ => false
    end
  | _ => true
  end.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  Let ge: genv := (SkEnv.revive skenv) p.

  Record state := mkstate {
    init_rs: regset;
    st:> Asm.state;
  }.

  Inductive step (se: Senv.t) (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_intro
      (STEP: Asm.step se ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs)).

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_cstyle
      fptr rs m0 m1 sg vs blk1 ofs init_rs
      (FPTR: rs # PC = fptr)
      (EXTERNAL: Genv.find_funct ge fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd /\ Sk.get_csig skd = Some sg)
      (RAPTR: <<TPTR: Val.has_type (rs RA) Tptr>> /\ <<RADEF: rs RA <> Vundef>>)
      (VALS: Asm.extcall_arguments rs m0 sg vs)
      (RSP: rs RSP = Vptr blk1 ofs)
      (ARGSRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | (Ptrofs.unsigned ofs)))
      (FREE: Mem.free m0 blk1 (Ptrofs.unsigned ofs) (Ptrofs.unsigned (ofs) + 4 * (size_arguments sg)) = Some m1)
    :
      at_external (mkstate init_rs (State rs m0)) (Args.Cstyle fptr vs m1)
  | at_external_asmstyle
      fptr rs m0
      init_rs
      (FPTR: rs # PC = fptr)
      (EXTERNAL: Genv.find_funct ge fptr = None)
      (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd /\ Sk.get_csig skd = None)
      (RAPTR: <<TPTR: Val.has_type (rs RA) Tptr>> /\ <<RADEF: rs RA <> Vundef>>)
    :
      at_external (mkstate init_rs (State rs m0)) (Args.Asmstyle rs m0)
  .

  Inductive initial_frame (args: Args.t): state -> Prop :=
  | initial_frame_cstyle
      fd m0 rs sg targs n m1 fptr_arg vs_arg m_arg
      (SIG: sg = fd.(fn_sig))
      (CSTYLE0: sg.(sig_cstyle) = true)
      (CSTYLE: args = Args.Cstyle fptr_arg vs_arg m_arg)
      (FINDF: Genv.find_funct ge fptr_arg = Some (Internal fd))
      (JUNK: assign_junk_blocks m0 n = m1)
      (RAPTR: <<TPTR: Val.has_type (rs RA) Tptr>> /\ <<RADEF: rs RA <> Vundef>>)
      (RANOTFPTR: forall blk ofs (RAVAL: rs RA = Vptr blk ofs),
          ~ Plt blk (Genv.genv_next skenv))
      (RSPC: rs # PC = fptr_arg)
      (TYP: typecheck vs_arg sg targs)
      (STORE: store_arguments m_arg rs targs sg m0)
      (PTRFREE: forall pr (PTR: ~ is_junk_value m0 m1 (rs pr)),
          (<<INARG: exists mr,
              (<<MR: to_mreg pr = Some mr>>) /\
              (<<ARG: In (R mr) (regs_of_rpairs (loc_arguments sg))>>)>>) \/
          (<<INPC: pr = PC>>) \/
          (<<INRSP: pr = RSP>>)):
      initial_frame args (mkstate rs (State rs m1))
  | initial_frame_asmstyle
      fd ra n m1 rs_arg rs m_arg
      (SIG: fd.(fn_sig).(sig_cstyle) = false)
      (ASMSTYLE: args = Args.Asmstyle rs_arg m_arg)
      (FINDF: Genv.find_funct ge (rs_arg # PC) = Some (Internal fd))
      (JUNK: assign_junk_blocks m_arg n = m1)
      (RAPTR: <<TPTR: Val.has_type ra Tptr>> /\ <<RADEF: ra <> Vundef>>)
      (RANOTFPTR: forall blk ofs (RAVAL: ra = Vptr blk ofs),
          ~ Plt blk (Genv.genv_next skenv))
      (RAJUNK: is_junk_value m_arg m1 ra)
      (RS: rs = rs_arg # RA <- ra)
    :
      initial_frame args (mkstate rs (State rs m1))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_cstyle
      (init_rs rs: regset) m0 m1 blk sg mr
      (INITSIG: exists fd, (Genv.find_funct ge) (init_rs # PC) = Some (Internal fd) /\ fd.(fn_sig) = sg /\ sg.(sig_cstyle) = true)
      (EXTERNAL: external_state ge (rs # PC))
      (RSRA: rs # PC = init_rs # RA)
      (RANOTFPTR: Genv.find_funct skenv_link (init_rs RA) = None)
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              Val.lessdef (init_rs (to_preg mr)) (rs (to_preg mr)))
      (INITRSP: init_rs # RSP = Vptr blk Ptrofs.zero)
      (RSRSP: rs # RSP = init_rs # RSP)
      (FREE: Mem.free m0 blk 0 (4 * size_arguments sg) = Some m1)
      (RETV: loc_result sg = One mr)
    :
      final_frame (mkstate init_rs (State rs m0)) (Retv.Cstyle (rs (to_preg mr)) m1)
  | final_frame_asmstyle
      (init_rs rs: regset) m0
      (INITSIG: exists fd, (Genv.find_funct ge) (init_rs # PC) = Some (Internal fd) /\ fd.(fn_sig).(sig_cstyle) = false)
      (EXTERNAL: external_state ge (rs # PC))
      (RSRA: rs # PC = init_rs # RA)
      (RANOTFPTR: Genv.find_funct skenv_link (init_rs RA) = None)
    :
      final_frame (mkstate init_rs (State rs m0)) (Retv.Asmstyle rs m0)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_cstyle
      init_rs rs0 m0 rs1 m1 retv retv_v retv_m sg blk ofs
      (CSTYLE: retv = (Retv.Cstyle retv_v retv_m))
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC)
                        = Some skd /\ Sk.get_csig skd = Some sg)
      (RS: rs1 = (set_pair (loc_external_result sg) retv_v (regset_after_external rs0)) #PC <- (rs0 RA))
      (RSRSP: rs0 RSP = Vptr blk ofs)
      (UNFREE: Mem_unfree retv_m blk (Ptrofs.unsigned ofs) (Ptrofs.unsigned (ofs) + 4 * (size_arguments sg)) = Some m1):
      after_external (mkstate init_rs (State rs0 m0))
                     retv
                     (mkstate init_rs (State rs1 m1))
  | after_external_asmstyle
      init_rs rs0 m0 rs1 retv retv_rs retv_m
      (ASMSTYLE: retv = (Retv.Asmstyle retv_rs retv_m))
      (SIG: exists skd, (Genv.find_funct skenv_link) (rs0 # PC) = Some skd /\ Sk.get_csig skd = None)
      (RS: rs1 = retv_rs # PC <- (rs0 # RA))
    :
      after_external (mkstate init_rs (State rs0 m0))
                     retv
                     (mkstate init_rs (State rs1 retv_m)).

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
    |}.
  Next Obligation.
    rewrite RSP in *. clarify. f_equal. eapply Asm.extcall_arguments_determ; eauto.
  Qed.
  Next Obligation.
    all: inv STEP; rewrite H2 in *; ss; des_ifs.
  Qed.
  Next Obligation.
    all: inv EXTERNAL; unfold external_state in *; des_ifs; inv STEP; ss; des_ifs; rewrite Heq in *; clarify.
  Qed.

  Lemma modsem_receptive: forall st, receptive_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H. destruct st0; ss. destruct s1; ss. clarify.
      inv STEP; try (exploit external_call_receptive; eauto; check_safe; intro T; des);
        try by (inv_match_traces; (eexists (mkstate _ _); econs; [econs|]; eauto; ss)).
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.

  Lemma modsem_determinate: forall st, determinate_at modsem st.
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0. destruct st0; ss. destruct s1; ss. destruct s2; ss. clarify.
      inv STEP; inv STEP0; eq_closure_tac; clarify_meq; try (determ_tac extcall_arguments_determ; check_safe); try (determ_tac eval_builtin_args_determ; check_safe);
        try (determ_tac external_call_determ; check_safe); esplits; eauto; try (econs; eauto); ii; eq_closure_tac; clarify_meq.
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try extlia.
  Qed.


End MODSEM.


Program Definition module (p: program): Mod.t :=
  {| Mod.data := p; Mod.get_sk := Sk.of_program fn_sig; Mod.get_modsem := modsem; |}.
