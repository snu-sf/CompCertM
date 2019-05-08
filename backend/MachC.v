Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Globalenvs.
Require Import EventsC.
Require Import Smallstep.
Require Import Op.
Require Import LocationsC.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Export Mach.
Require Import StoreArguments.
Require Import Skeleton Mod ModSem.
Require Import Simulation Integers.
Require Import JunkBlock.

Set Implicit Arguments.

Section NEWSTEP.

Variable return_address_offset: function -> code -> ptrofs -> Prop.
Variable se: Senv.t.
Variable ge: genv.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Definition step: state -> trace -> state -> Prop := fun st0 tr st1 =>
  <<STEP: Mach.step return_address_offset se ge st0 tr st1>> /\ <<NOTDUMMY: st1.(get_stack) <> []>>
.

(* Inductive step: state -> trace -> state -> Prop := *)
(* | step_intro *)
(*     st0 tr st1 *)
(*     (STEP: Mach.step return_address_offset se ge st0 tr st1) *)
(*     (NOTDUMMY: st1.(get_stack) <> []) *)
(*   : *)
(*     step st0 tr st1 *)
(* . *)

(* Inductive step: state -> trace -> state -> Prop := *)
(*   | exec_Mlabel: *)
(*       forall s f sp lbl c rs m, *)
(*       step (State s f sp (Mlabel lbl :: c) rs m) *)
(*         E0 (State s f sp c rs m) *)
(*   | exec_Mgetstack: *)
(*       forall s f sp ofs ty dst c rs m v, *)
(*       load_stack m sp ty ofs = Some v -> *)
(*       step (State s f sp (Mgetstack ofs ty dst :: c) rs m) *)
(*         E0 (State s f sp c (rs#dst <- v) m) *)
(*   | exec_Msetstack: *)
(*       forall s f sp src ofs ty c rs m m' rs', *)
(*       store_stack m sp ty ofs (rs src) = Some m' -> *)
(*       rs' = undef_regs (destroyed_by_setstack ty) rs -> *)
(*       step (State s f sp (Msetstack src ofs ty :: c) rs m) *)
(*         E0 (State s f sp c rs' m') *)
(*   | exec_Mgetparam: *)
(*       forall s fb f sp ofs ty dst c rs m v rs', *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
(*       load_stack m (parent_sp s) ty ofs = Some v -> *)
(*       rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) -> *)
(*       step (State s fb sp (Mgetparam ofs ty dst :: c) rs m) *)
(*         E0 (State s fb sp c rs' m) *)
(*   | exec_Mop: *)
(*       forall s f sp op args res c rs m v rs', *)
(*       eval_operation ge sp op rs##args m = Some v -> *)
(*       rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) -> *)
(*       step (State s f sp (Mop op args res :: c) rs m) *)
(*         E0 (State s f sp c rs' m) *)
(*   | exec_Mload: *)
(*       forall s f sp chunk addr args dst c rs m a v rs', *)
(*       eval_addressing ge sp addr rs##args = Some a -> *)
(*       Mem.loadv chunk m a = Some v -> *)
(*       rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) -> *)
(*       step (State s f sp (Mload chunk addr args dst :: c) rs m) *)
(*         E0 (State s f sp c rs' m) *)
(*   | exec_Mstore: *)
(*       forall s f sp chunk addr args src c rs m m' a rs', *)
(*       eval_addressing ge sp addr rs##args = Some a -> *)
(*       Mem.storev chunk m a (rs src) = Some m' -> *)
(*       rs' = undef_regs (destroyed_by_store chunk addr) rs -> *)
(*       step (State s f sp (Mstore chunk addr args src :: c) rs m) *)
(*         E0 (State s f sp c rs' m') *)
(*   | exec_Mcall: *)
(*       forall s fb sp sig ros c rs m f f' ra, *)
(*       find_function_ptr ge ros rs m= f' -> *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       return_address_offset f c ra -> *)
(*       step (State s fb sp (Mcall sig ros :: c) rs m) *)
(*         E0 (Callstate (Stackframe fb sp (Vptr fb ra true) c :: s) *)
(*                        f' rs m) *)
(*   | exec_Mtailcall: *)
(*       forall s fb stk soff sig ros c rs m f f' m', *)
(*       find_function_ptr ge ros rs m= f' -> *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       load_stack m (Vptr stk soff true) Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
(*       load_stack m (Vptr stk soff true) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) -> *)
(*       Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
(*       step (State s fb (Vptr stk soff true) (Mtailcall sig ros :: c) rs m) *)
(*         E0 (Callstate s f' rs m') *)
(*   | exec_Mbuiltin: *)
(*       forall s f sp rs m ef args res b vargs t vres rs' m', *)
(*       eval_builtin_args ge rs sp m args vargs -> *)
(*       external_call ef ge vargs m t vres m' -> *)
(*       rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) -> *)
(*       step (State s f sp (Mbuiltin ef args res :: b) rs m) *)
(*          t (State s f sp b rs' m') *)
(*   | exec_Mgoto: *)
(*       forall s fb f sp lbl c rs m c', *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       find_label lbl f.(fn_code) = Some c' -> *)
(*       step (State s fb sp (Mgoto lbl :: c) rs m) *)
(*         E0 (State s fb sp c' rs m) *)
(*   | exec_Mcond_true: *)
(*       forall s fb f sp cond args lbl c rs m c' rs', *)
(*       eval_condition cond rs##args m = Some true -> *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       find_label lbl f.(fn_code) = Some c' -> *)
(*       rs' = undef_regs (destroyed_by_cond cond) rs -> *)
(*       step (State s fb sp (Mcond cond args lbl :: c) rs m) *)
(*         E0 (State s fb sp c' rs' m) *)
(*   | exec_Mcond_false: *)
(*       forall s f sp cond args lbl c rs m rs', *)
(*       eval_condition cond rs##args m = Some false -> *)
(*       rs' = undef_regs (destroyed_by_cond cond) rs -> *)
(*       step (State s f sp (Mcond cond args lbl :: c) rs m) *)
(*         E0 (State s f sp c rs' m) *)
(*   | exec_Mjumptable: *)
(*       forall s fb f sp arg tbl c rs m n lbl c' rs', *)
(*       rs arg = Vint n -> *)
(*       list_nth_z tbl (Int.unsigned n) = Some lbl -> *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       find_label lbl f.(fn_code) = Some c' -> *)
(*       rs' = undef_regs destroyed_by_jumptable rs -> *)
(*       step (State s fb sp (Mjumptable arg tbl :: c) rs m) *)
(*         E0 (State s fb sp c' rs' m) *)
(*   | exec_Mreturn: *)
(*       forall s fb stk soff c rs m f m', *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       load_stack m (Vptr stk soff true) Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
(*       load_stack m (Vptr stk soff true) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) -> *)
(*       Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
(*       step (State s fb (Vptr stk soff true) (Mreturn :: c) rs m) *)
(*         E0 (Returnstate s rs m') *)
(*   | exec_function_internal: *)
(*       forall s fptr fb rs m f m1 m2 m3 stk rs' *)
(*       (FPTR: fptr = Vptr fb Ptrofs.zero), *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) -> *)
(*       let sp := Vptr stk Ptrofs.zero in *)
(*       store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 -> *)
(*       store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 -> *)
(*       rs' = undef_regs destroyed_at_function_entry rs -> *)
(*       step (Callstate s fptr rs m) *)
(*         E0 (State s fb sp f.(fn_code) rs' m3) *)
(*   | exec_function_external: *)
(*       forall s fb rs m t rs' ef args res m', *)
(*       Genv.find_funct ge fb = Some (External ef) -> *)
(*       extcall_arguments rs m (parent_sp s) (ef_sig ef) args -> *)
(*       external_call ef ge args m t res m' -> *)
(*       rs' = set_pair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs) -> *)
(*       step (Callstate s fb rs m) *)
(*          t (Returnstate s rs' m') *)
(*   | exec_return: *)
(*       forall s f sp ra c rs m (NOTDUMMY: s <> []), *)
(*       step (Returnstate (Stackframe f sp ra c :: s) rs m) *)
(*         E0 (State s f sp c rs m). *)

End NEWSTEP.

Hint Unfold step.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.


Section MODSEM.

  Variable rao: function -> code -> ptrofs -> Prop.
  Hypothesis rao_dtm:
    forall f c ofs ofs',
      rao f c ofs ->
      rao f c ofs' ->
      ofs = ofs'.


  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(Sk.of_program fn_sig).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Record state := mkstate {
    init_rs: Mach.regset;
    init_sg: signature;
    st: Mach.state;
  }.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack rs m0 m1 fptr sg vs blk ofs
      (EXTERNAL: Genv.find_funct ge fptr = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd /\ SkEnv.get_sig skd = sg)
      (VALS: Mach.extcall_arguments rs m0 (parent_sp stack) sg vs)
      (ARGSRANGE: Ptrofs.unsigned ofs + 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (RSP: (parent_sp stack) = Vptr blk ofs)
      (ALIGN: forall chunk (CHUNK: size_chunk chunk <= 4 * (size_arguments sg)),
          (align_chunk chunk | ofs.(Ptrofs.unsigned)))
      (FREE: Mem.free m0 blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
      init_rs init_sg
    :
      at_external (mkstate init_rs init_sg (Callstate stack fptr rs m0)) (Args.mk fptr vs m1)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd m0 rs sg ra
      (RAPTR: Val.has_type ra Tptr)
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      targs
      (TYP: typecheck args.(Args.vs) sg targs)
      (STORE: store_arguments args.(Args.m) rs targs sg m0)
      n m1
      (JUNK: assign_junk_blocks m0 n = m1)
      (PTRFREE: forall
          mr
          (* (NOTIN: Loc.notin (R mr) (regs_of_rpairs (loc_arguments sg))) *)
          (NOTIN: ~In (R mr) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: is_junk_value m0 m1 (rs mr)>>)
    :
      initial_frame args (mkstate rs sg
                                  (Callstate [dummy_stack
                                                (Vptr args.(Args.m).(Mem.nextblock) Ptrofs.zero) ra]
                                             args.(Args.fptr) rs m1))
  (* TODO: change (Vptr args.(Args.m).(Mem.nextblock) Ptrofs.zero) into sp *)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      (init_rs rs: regset) init_sp m0 m1 blk init_sg mr ra
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr -> Val.lessdef (init_rs mr) (rs mr))
      (INITRSP: init_sp = Vptr blk Ptrofs.zero)
      (FREE: Mem.free m0 blk 0 (4 * size_arguments init_sg) = Some m1)
      (RETV: loc_result init_sg = One mr)
    :
      final_frame (mkstate init_rs init_sg (Returnstate [dummy_stack init_sp ra] rs m0))
                  (Retv.mk (rs mr) m1)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      init_rs init_sg stack fptr ls0 m0 ls1 m1 retv
      sg blk ofs
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr = Some skd /\ SkEnv.get_sig skd = sg)
      (REGSET: ls1 = (set_pair (loc_result sg) retv.(Retv.v) (regset_after_external ls0)))
      (RSP: (parent_sp stack) = Vptr blk ofs)
      (MEMWF: Ple (Senv.nextblock skenv_link) retv.(Retv.m).(Mem.nextblock))
      (UNFREE: Mem_unfree retv.(Retv.m) blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
    :
      after_external (mkstate init_rs init_sg (Callstate stack fptr ls0 m0))
                     retv
                     (mkstate init_rs init_sg (Returnstate stack ls1 m1))
  .

  Inductive step' (se: Senv.t) (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step'_intro
      (STEP: Mach.step rao se ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs))
      (INITFPTR: st0.(init_sg) = st1.(init_sg))
      (NOTDUMMY: st1.(st).(get_stack) <> [])
  .

  Lemma extcall_arguments_dtm
        rs m rsp sg vs0 vs1
        (ARGS0: Mach.extcall_arguments rs m rsp sg vs0)
        (ARGS1: Mach.extcall_arguments rs m rsp sg vs1)
    :
      vs0 = vs1
  .
  Proof.
    generalize dependent vs1. generalize dependent vs0. generalize dependent sg.
    assert (A: forall l v1 v2,
               Mach.extcall_arg rs m rsp l v1 -> Mach.extcall_arg rs m rsp l v2 -> v1 = v2).
    { intros. inv H; inv H0; congruence. }
    assert (B: forall p v1 v2,
               Mach.extcall_arg_pair rs m rsp p v1 -> Mach.extcall_arg_pair rs m rsp p v2 -> v1 = v2).
    { intros. inv H; inv H0.
      eapply A; eauto.
      f_equal; eapply A; eauto. }
    assert (C: forall ll vl1, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl1 ->
                         forall vl2, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl2 -> vl1 = vl2).
    {
      induction 1; intros vl2 EA; inv EA.
      auto.
      f_equal; eauto. }
    intros. eapply C; eauto.
  Qed.

  Lemma extcall_arguments_length
        rs m rsp sg vs
        (ARGS: extcall_arguments rs m rsp sg vs)
    :
      length (loc_arguments sg) = length vs
  .
  Proof.
    unfold extcall_arguments in *.
    abstr (loc_arguments sg) locs.
    ginduction vs; ii; inv ARGS; ss.
    f_equal. erewrite IHvs; eauto.
  Qed.
  
  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step';
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
    ii; ss; des. inv_all_once; des; ss; clarify. rewrite RSP in *. clarify. determ_tac extcall_arguments_dtm.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    eauto with congruence.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; des; ss; clarify.
    rewrite RSP in *. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify. des. clarify.
    inv STEP; clarify.
    unfold Genv.find_funct in *. des_ifs_safe ss. clarify.
  Qed.
  Next Obligation.
    ii; ss; des. inv_all_once; ss; clarify.
    inv STEP; clarify. destruct st1; ss. destruct st0; ss. clarify.
  Qed.
  Next Obligation.
    ii; ss; des.
    inv_all_once; ss; clarify.
  Qed.
    
  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof.
    econs; eauto.
    - ii; ss. inv H. destruct st; ss. destruct s1; ss. clarify.
      inv STEP; try (exploit external_call_receptive; eauto; check_safe; intro T; des); try by (inv_match_traces; (eexists (mkstate _ _ _); econs; [econs| | |]; eauto)).
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof.
    econs; eauto.
    - ii; ss. inv H; inv H0. destruct st; ss. destruct s1; ss. destruct s2; ss. clarify.
      inv STEP; inv STEP0; clarify_meq; try (determ_tac rao_dtm; check_safe); try (determ_tac extcall_arguments_dtm; check_safe); try (determ_tac eval_builtin_args_determ; check_safe); try (determ_tac external_call_determ; check_safe); esplits; eauto; try (econs; eauto); try (by rewrite Genv.find_funct_find_funct_ptr in *; congruence); ii; eq_closure_tac; clarify_meq.
    - ii. inv H. inv STEP; try (exploit external_call_trace_length; eauto; check_safe; intro T; des); ss; try xomega.
  Qed.

End MODSEM.


Section PROPS.

Variable rao: function -> code -> ptrofs -> Prop.

Lemma lift_star
      se ge st0 tr st1
      init_sg init_rs
      (STAR: star (step rao) se ge st0 tr st1)
  :
    star (step' rao) se ge (mkstate init_rs init_sg st0) tr
         (mkstate init_rs init_sg st1)
.
Proof.
  ginduction STAR; ii; ss.
  { econs; et. }
  inv H.
  econs; et.
  - econs; et.
Qed.

Lemma lift_plus
      se ge st0 tr st1
      init_sg init_rs
      (PLUS: plus (step rao) se ge st0 tr st1)
  :
    plus (step' rao) se ge (mkstate init_rs init_sg st0) tr
         (mkstate init_rs init_sg st1)
.
Proof.
  inv PLUS. inv H.
  econs; et.
  { instantiate (1:= mkstate init_rs init_sg s2).
    econs; ss; et.
  }
  eapply lift_star; et.
Qed.

End PROPS.


Section MODULE.

  Variable p: program.

  Variable rao: function -> code -> ptrofs -> Prop.

  Program Definition module: Mod.t :=
    {|
      Mod.data := p;
      Mod.get_sk := Sk.of_program fn_sig;
      Mod.get_modsem := modsem rao;
    |}
  .

End MODULE.
