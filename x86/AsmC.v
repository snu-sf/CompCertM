Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
(** newly added **)
Require Export Asm.
Require Import Simulation AsmregsC.
Require Import Skeleton ModSem Mod.

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

Section ASMEXTRA.

  Definition is_external (ge: genv) (st: state): Prop :=
    match Genv.find_funct ge (st.(st_rs) PC) with
    | Some (AST.External ef) => is_external_ef ef
    | _ => False
    end
  .

  Variable ge: genv.
  Definition semantics_with_ge := Semantics step bot1 final_state ge.
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
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(defs).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Record state := mkstate {
    init_rs: regset;
    st: Asm.state;
  }.

  Inductive at_external (skenv_link: SkEnv.t): state -> Args.t -> Prop :=
  | at_external_intro
      rs m0 m1 fptr sg vs blk ofs
      (FPTR: rs # PC = fptr)
      (EXTERNAL: Genv.find_funct ge fptr = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd /\ SkEnv.get_sig skd = sg)
      (VALS: extcall_arguments rs m0 sg vs)
      (RSP: rs RSP = Vptr blk ofs true)
      (FREE: Mem.free m0 blk ofs.(Ptrofs.unsigned) (1 + ofs.(Ptrofs.unsigned) + (size_arguments sg)) = Some m1)
      init_rs
    :
      at_external skenv_link (mkstate init_rs (State rs m0)) (Args.mk fptr vs m1)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd m0 m1 rs blk
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (ALLOC: Mem.alloc args.(Args.m) 0 (size_arguments fd.(fn_sig)) = (m0, blk))
      (PC: rs # PC = args.(Args.fptr))
      (RPS: rs # RSP = Vptr blk Ptrofs.zero true)
      (VALS: extcall_arguments rs m1 fd.(fn_sig) args.(Args.vs))
    :
      initial_frame args (mkstate rs (State rs m1))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      (init_rs rs: regset) m0 m1 blk sg mr
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              Val.lessdef (init_rs mr.(to_preg)) (rs mr.(to_preg)))
      (INITRSP: init_rs # RSP = Vptr blk Ptrofs.zero true)
      (INITSIG: exists skd, skenv_link.(Genv.find_funct) (init_rs # PC) = Some skd /\ SkEnv.get_sig skd = sg)
      (FREE: Mem.free m0 blk 0 (size_arguments sg) = Some m1)
      (RETV: loc_result sg = One mr)
    :
      final_frame (mkstate init_rs (State rs m0)) (Retv.mk (rs mr.(to_preg)) m1)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      init_rs rs0 m0 rs1 m1 retv
      sg blk ofs
      (SIG: exists skd, skenv_link.(Genv.find_funct) (rs0 # PC) = Some skd /\ SkEnv.get_sig skd = sg)
      (RS: rs1 = (set_pair (loc_external_result sg) retv.(Retv.v) (Asmregs.regset_after_external rs0)))
      (RSP: rs0 RSP = Vptr blk ofs true)
      (UNFREE: Mem_unfree m0 blk ofs.(Ptrofs.unsigned) (1 + ofs.(Ptrofs.unsigned) + (size_arguments sg)) = Some m1)
    :
      after_external (mkstate init_rs (State rs0 m0))
                     retv
                     (mkstate init_rs (State rs1 m1))
  .

  Inductive step (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_intro
      (STEP: Asm.step ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs))
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
    |}
  .
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify. rewrite RSP in *. clarify.
    determ_tac extcall_arguments_determ.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    rewrite INITRSP in *. clarify.
    f_equal. rewrite RETV in *. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    rewrite RSP in *. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    admit "".
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify.
    admit "".
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify.
    admit "".
  Qed.

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    eapply SkEnv.revive_no_external; eauto.
  Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge ge) st)
    :
      forall init_rs, receptive_at modsem (mkstate init_rs st)
  .
  Proof.
    inv RECEP. i. econs; eauto; ii; ss.
    - inv H. ss. exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i; des.
      eexists (mkstate _ s2). ss.
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
        (DTM: determinate_at (semantics_with_ge ge) st0)
    :
      forall init_rs, determinate_at modsem (mkstate init_rs st0)
  .
  Proof.
    inv DTM. i. econs; eauto; ii; ss.
    - inv H. inv H0. ss.
      determ_tac sd_determ_at. esplits; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i. clarify. destruct s1, s2; ss. f_equal; ss. eauto.
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
  Next Obligation.
    rewrite Sk.of_program_defs.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

End MODULE.

