Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
(** newly added **)
Require Import Mach Simulation ValuesC.
Require Export Asm.
Require Import Skeleton ModSem Mod sflib.
Require Import LocationsC AsmregsC StoreArguments.
Require Import JunkBlock.

Set Implicit Arguments.

Definition get_mem (st: state): mem :=
  match st with
  | State _ m0 => m0
  end.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition st_rs (st0: state): regset :=
  match st0 with
  | State rs _ => rs
  end
.

Definition st_m (st0: state): mem :=
  match st0 with
  | State _ m => m
  end
.

Definition store_arguments (m0: mem) (rs: regset) (vs: list val) (sg: signature) (m2: mem) : Prop :=
  (<<STORE: store_arguments m0 (to_mregset rs) vs sg m2>>) /\
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

Section ASMEXTRA.

  Definition is_external (ge: genv) (st: state): Prop :=
    match Genv.find_funct ge (st.(st_rs) PC) with
    | Some (AST.External ef) => is_external_ef ef = true
    | _ => False
    end
  .

  Variable se: Senv.t.
  Variable ge: genv.
  Definition semantics_with_ge := Semantics_gen step bot1 final_state ge se.
  (* *************** ge is parameterized *******************)

  Lemma semantics_receptive
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      receptive_at semantics_with_ge st
  .
  Proof.
    admit "this should hold".
  Qed.

  Lemma semantics_determinate
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      determinate_at semantics_with_ge st
  .
  Proof.
    admit "this should hold".
  Qed.

End ASMEXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Record state := mkstate {
    init_rs: regset;
    st:> Asm.state;
    (* extret: bool; *)
  }.

  Inductive step (se: Senv.t) (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_intro
      (STEP: Asm.step se ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs))
      (* (ISRETURN: step_ret st0.(st) = st1.(extret)) *)
  .

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      rs m0 m1 sg vs blk0 blk1 ofs
      (FPTR: rs # PC = Vptr blk0 Ptrofs.zero)
      (EXTERNAL: Genv.find_funct ge (Vptr blk0 Ptrofs.zero) = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr blk0 Ptrofs.zero)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (ARGSRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (VALS: Asm.extcall_arguments rs m0 sg vs)
      (RSP: rs RSP = Vptr blk1 ofs)
      (RAPTR: <<TPTR: Val.has_type (rs RA) Tptr>> /\ <<RADEF: rs RA <> Vundef>>)
      (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | ofs.(Ptrofs.unsigned)))
      (FREE: Mem.free m0 blk1 ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
      init_rs
    :
      at_external (mkstate init_rs (State rs m0))
                  (Args.mk (Vptr blk0 Ptrofs.zero) vs m1)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd m0 rs sg
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (RSPC: rs # PC = args.(Args.fptr))
      targs
      (TYP: typecheck args.(Args.vs) sg targs)
      (STORE: store_arguments args.(Args.m) rs targs sg m0)
      n m1
      (JUNK: assign_junk_blocks m0 n = m1)
      (RAPTR: <<TPTR: Val.has_type (rs RA) Tptr>> /\ <<RADEF: rs RA <> Vundef>>)
      (* (RAJUNK: is_junk_value m0 m1 (rs RA)) *)
      (RANOTFPTR: forall blk ofs (RAVAL: rs RA = Vptr blk ofs),
          ~ Plt blk (Genv.genv_next skenv))
      (* (<<NOTFPTR0: ge.(Genv.find_funct) (rs RA) = None>>) *)
      (* (RAJUNK1: skenv_link.(Genv.find_funct) (rs RA) = None) *)
      (PTRFREE: forall pr (PTR: ~ is_junk_value m0 m1 (rs pr)),
          (<<INARG: exists mr,
              (<<MR: to_mreg pr = Some mr>>) /\
              (<<ARG: In (R mr) (regs_of_rpairs (loc_arguments sg))>>)>>) \/
          (<<INPC: pr = PC>>) \/
          (<<INRSP: pr = RSP>>))
    :
      initial_frame args (mkstate rs (State rs m1))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      (init_rs rs: regset) m0 m1 blk sg mr
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              Val.lessdef (init_rs mr.(to_preg)) (rs mr.(to_preg)))
      (INITRSP: init_rs # RSP = Vptr blk Ptrofs.zero)
      (INITSIG: exists fd, ge.(Genv.find_funct) (init_rs # PC)
                           = Some (Internal fd) /\ fd.(fn_sig) = sg)
      (FREE: Mem.free m0 blk 0 (4 * size_arguments sg) = Some m1)
      (RETV: loc_result sg = One mr)
      (EXTERNAL: external_state ge (rs # PC))
      (RSRA: rs # PC = init_rs # RA)
      (RANOTFPTR: Genv.find_funct skenv_link (init_rs RA) = None)
      (* (JUNK1: ge.(Genv.find_funct) (rs PC) = None) *)
      (* (RSRSP: Val.lessdef (rs # RSP) (init_rs # RSP)) *)
      (RSRSP: rs # RSP = init_rs # RSP)
    :
      final_frame (mkstate init_rs (State rs m0)) (Retv.mk (rs mr.(to_preg)) m1)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      init_rs rs0 m0 rs1 m1 retv
      sg blk ofs
      (SIG: exists skd, skenv_link.(Genv.find_funct) (rs0 # PC)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RS: rs1 = (set_pair (loc_external_result sg) retv.(Retv.v) (regset_after_external rs0)) #PC <- (rs0 RA))
      (RSRSP: rs0 RSP = Vptr blk ofs)
      (UNFREE: Mem_unfree retv.(Retv.m) blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
    :
      after_external (mkstate init_rs (State rs0 m0))
                     retv
                     (mkstate init_rs (State rs1 m1))
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge;
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
    |}
  .
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify. rewrite RSP in *. clarify.
    rewrite FPTR in *. clarify. f_equal. eapply Asm.extcall_arguments_determ; eauto.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    rewrite INITRSP in *. clarify.
    f_equal. rewrite RETV in *. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify. f_equal.
    rewrite RSRSP in *. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    exfalso. inv STEP; ss; rewrite FPTR in *; inv H2; des_ifs.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify. inv EXTERNAL.
    unfold external_state in *.
    des_ifs; inv STEP; ss; des_ifs; rewrite Heq in *; clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify.
    des. rewrite FPTR in *. ss. des_ifs. rewrite <- RSRA in *.
    ss. des_ifs.
  Qed.

  Hypothesis (INCL: SkEnv.includes skenv_link (Sk.of_program fn_sig p)).
  Hypothesis (WF: SkEnv.wf skenv_link).

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply SkEnv.project_revive_no_external; eauto.
  Qed.

  Lemma lift_receptive_at
        st
        (* b *)
        (RECEP: receptive_at (semantics_with_ge skenv_link ge) st)
    :
      forall init_rs, receptive_at modsem (mkstate init_rs st)
  .
  Proof.
    inv RECEP. i. econs; eauto; ii; ss.
    - inv H. ss. exploit sr_receptive_at; eauto. i; des.
      eexists (mkstate _ s2). econs; ss.
    - inv H. ss. exploit sr_traces_at; eauto.
  Unshelve.
    all: ss.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. destruct st. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge skenv_link ge) st0)
    :
      forall init_rs, determinate_at modsem (mkstate init_rs st0)
  .
  Proof.
    inv DTM. i. econs; eauto; ii; ss.
    - inv H. inv H0. ss.
      determ_tac sd_determ_at. esplits; eauto. i. clarify. destruct s1, s2; ss. f_equal; ss; eauto.
    - inv H. ss. exploit sd_traces_at; eauto.
  Unshelve.
    all: ss.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. destruct st. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed.


End MODSEM.

Section MODULE.

  Variable p: program.

  Program Definition module: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := Sk.of_program fn_sig;
      Mod.get_modsem := modsem;
    |}
  .

End MODULE.

(* move to AsmregsC *)
Lemma to_mreg_preg_of
      pr mr
      (MR: Asm.to_mreg pr = Some mr)
  :
    <<PR: preg_of mr = pr>>
.
Proof. destruct mr, pr; ss; des_ifs. Qed.
