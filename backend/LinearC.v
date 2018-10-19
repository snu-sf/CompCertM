Require Import CoqlibC.
Require Import ASTC Integers ValuesC MemoryC Events GlobalenvsC Smallstep.
Require Import Op LocationsC LTL Conventions.
(** newly added **)
Require Export Linear.
Require Import Skeleton Mod ModSem.
Require Import Simulation AsmregsC.

Set Implicit Arguments.



Section LINEAREXTRA.

  Definition is_external (ge: genv) (st: state): Prop :=
    match st with
    | Callstate stack fptr sg ls m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => is_external_ef ef
      | _ => False
      end
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

End LINEAREXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)



Section NEWSTEP.

Variable ge: genv.
Let find_function_ptr := find_function_ptr ge.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Inductive step: state -> trace -> state -> Prop :=
| step_intro
    st0 tr st1
    (STEP: Linear.step ge st0 tr st1)
    (NOTDUMMY: st1.(get_stack) <> [])
  :
    step st0 tr st1
.

(* Inductive step: state -> trace -> state -> Prop := *)
(*   | exec_Lgetstack: *)
(*       forall s f sp sl ofs ty dst b rs m rs', *)
(*       rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (LTL.undef_regs (destroyed_by_getstack sl) rs) -> *)
(*       step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m) *)
(*         E0 (State s f sp b rs' m) *)
(*   | exec_Lsetstack: *)
(*       forall s f sp src sl ofs ty b rs m rs', *)
(*       rs' = Locmap.set (S sl ofs ty) (rs (R src)) (LTL.undef_regs (destroyed_by_setstack ty) rs) -> *)
(*       step (State s f sp (Lsetstack src sl ofs ty :: b) rs m) *)
(*         E0 (State s f sp b rs' m) *)
(*   | exec_Lop: *)
(*       forall s f sp op args res b rs m v rs', *)
(*       eval_operation ge sp op (reglist rs args) m = Some v -> *)
(*       rs' = Locmap.set (R res) v (LTL.undef_regs (destroyed_by_op op) rs) -> *)
(*       step (State s f sp (Lop op args res :: b) rs m) *)
(*         E0 (State s f sp b rs' m) *)
(*   | exec_Lload: *)
(*       forall s f sp chunk addr args dst b rs m a v rs', *)
(*       eval_addressing ge sp addr (reglist rs args) = Some a -> *)
(*       Mem.loadv chunk m a = Some v -> *)
(*       rs' = Locmap.set (R dst) v (LTL.undef_regs (destroyed_by_load chunk addr) rs) -> *)
(*       step (State s f sp (Lload chunk addr args dst :: b) rs m) *)
(*         E0 (State s f sp b rs' m) *)
(*   | exec_Lstore: *)
(*       forall s f sp chunk addr args src b rs m m' a rs', *)
(*       eval_addressing ge sp addr (reglist rs args) = Some a -> *)
(*       Mem.storev chunk m a (rs (R src)) = Some m' -> *)
(*       rs' = LTL.undef_regs (destroyed_by_store chunk addr) rs -> *)
(*       step (State s f sp (Lstore chunk addr args src :: b) rs m) *)
(*         E0 (State s f sp b rs' m') *)
(*   | exec_Lcall: *)
(*       forall s f sp sig ros b rs m fptr *)
(*       (FPTR: find_function_ptr ros rs m= fptr) *)
(*       , *)
(*       DUMMY_PROP -> *)
(*       DUMMY_PROP -> *)
(*       step (State s f sp (Lcall sig ros :: b) rs m) *)
(*         E0 (Callstate (Stackframe f sp rs b:: s) fptr sig rs m) *)
(*   | exec_Ltailcall: *)
(*       forall s f stk sig ros b rs m rs' fptr m' *)
(*       (FPTR: find_function_ptr ros rs' m= fptr) *)
(*       , *)
(*       rs' = return_regs (parent_locset s) rs -> *)
(*       DUMMY_PROP -> *)
(*       DUMMY_PROP -> *)
(*       Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
(*       step (State s f (Vptr stk Ptrofs.zero true) (Ltailcall sig ros :: b) rs m) *)
(*         E0 (Callstate s fptr sig rs' m') *)
(*   | exec_Lbuiltin: *)
(*       forall s f sp rs m ef args res b vargs t vres rs' m', *)
(*       eval_builtin_args ge rs sp m args vargs -> *)
(*       external_call ef ge vargs m t vres m' -> *)
(*       rs' = Locmap.setres res vres (LTL.undef_regs (destroyed_by_builtin ef) rs) -> *)
(*       step (State s f sp (Lbuiltin ef args res :: b) rs m) *)
(*          t (State s f sp b rs' m') *)
(*   | exec_Llabel: *)
(*       forall s f sp lbl b rs m, *)
(*       step (State s f sp (Llabel lbl :: b) rs m) *)
(*         E0 (State s f sp b rs m) *)
(*   | exec_Lgoto: *)
(*       forall s f sp lbl b rs m b', *)
(*       find_label lbl f.(fn_code) = Some b' -> *)
(*       step (State s f sp (Lgoto lbl :: b) rs m) *)
(*         E0 (State s f sp b' rs m) *)
(*   | exec_Lcond_true: *)
(*       forall s f sp cond args lbl b rs m rs' b', *)
(*       eval_condition cond (reglist rs args) m = Some true -> *)
(*       rs' = LTL.undef_regs (destroyed_by_cond cond) rs -> *)
(*       find_label lbl f.(fn_code) = Some b' -> *)
(*       step (State s f sp (Lcond cond args lbl :: b) rs m) *)
(*         E0 (State s f sp b' rs' m) *)
(*   | exec_Lcond_false: *)
(*       forall s f sp cond args lbl b rs m rs', *)
(*       eval_condition cond (reglist rs args) m = Some false -> *)
(*       rs' = LTL.undef_regs (destroyed_by_cond cond) rs -> *)
(*       step (State s f sp (Lcond cond args lbl :: b) rs m) *)
(*         E0 (State s f sp b rs' m) *)
(*   | exec_Ljumptable: *)
(*       forall s f sp arg tbl b rs m n lbl b' rs', *)
(*       rs (R arg) = Vint n -> *)
(*       list_nth_z tbl (Int.unsigned n) = Some lbl -> *)
(*       find_label lbl f.(fn_code) = Some b' -> *)
(*       rs' = LTL.undef_regs (destroyed_by_jumptable) rs -> *)
(*       step (State s f sp (Ljumptable arg tbl :: b) rs m) *)
(*         E0 (State s f sp b' rs' m) *)
(*   | exec_Lreturn: *)
(*       forall s f stk b rs m m', *)
(*       Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
(*       step (State s f (Vptr stk Ptrofs.zero true) (Lreturn :: b) rs m) *)
(*         E0 (Returnstate s (return_regs (parent_locset s) rs) m') *)
(*   | exec_function_internal: *)
(*       forall s fptr sg f rs m rs' m' stk *)
(*       (FPTR: Genv.find_funct ge fptr = Some (Internal f)) *)
(*       (SIG: sg = funsig (Internal f)) *)
(*       , *)
(*       Mem.alloc m 0 f.(fn_stacksize) = (m', stk) -> *)
(*       rs' = LTL.undef_regs destroyed_at_function_entry (call_regs rs) -> *)
(*       step (Callstate s fptr sg rs m) *)
(*         E0 (State s f (Vptr stk Ptrofs.zero true) f.(fn_code) rs' m') *)
(*   | exec_function_external: *)
(*       forall s fptr sg ef args res rs1 rs2 m t m' *)
(*       (FPTR: Genv.find_funct ge fptr = Some (External ef)) *)
(*       (SIG: sg = funsig (External ef)) *)
(*       , *)
(*       args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) -> *)
(*       external_call ef ge args m t res m' -> *)
(*       rs2 = Locmap.setpair (loc_result (ef_sig ef)) res (LTL.undef_regs destroyed_at_call rs1) -> *)
(*       step (Callstate s fptr sg rs1 m) *)
(*          t (Returnstate s rs2 m') *)
(*   | exec_return: *)
(*       forall s f sp rs0 c rs m (NOTDUMMY: s <> []), *)
(*       step (Returnstate (Stackframe f sp rs0 c :: s) rs m) *)
(*         E0 (State s f sp c rs m). *)

End NEWSTEP.


Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

(* Definition get_stackframe (st: state): list stackframe := *)
(*   match st with *)
(*   | State stks _ _ _ _ _ => stks *)
(*   | Callstate stks _ _ _ _ => stks *)
(*   | Returnstate stks _ _ => stks *)
(*   end *)
(* . *)

Definition get_locset (st: state): locset :=
  match st with
  | State _ _ _ _ ls _ => ls
  | Callstate _ _ _ ls _ => ls
  | Returnstate _ ls _ => ls
  end
.

Definition current_locset (stk: stackframe): locset :=
  match stk with
  | Stackframe _ _ ls _ => ls
  end
.

(* Definition dummy_stacksize: Z := (admit "dummy_stacksize"). *)
(* Definition dummy_code (sig: signature): code := [Lcall sig (admit "dummy_reg")]. *)
Definition dummy_function (sig: signature) := (mkfunction sig 0 []).

Definition dummy_stack (sig: signature) (ls: locset) :=
  Stackframe (dummy_function sig)
              (* (Vptr (admit "dummy_fptr") Ptrofs.zero true) *)
             Vundef
             ls
             [] (* one may replace it with another another_dummy_code,
but then corresponding MachM's part should be transl_code another_dummy_code ... *)
.
Hint Unfold dummy_stack.

Section MODSEM.

  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(defs).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> Args.t -> Prop :=
  | at_external_intro
      stack fptr_arg sg ls vs_arg m0
      (EXTERNAL: ge.(Genv.find_funct) fptr_arg = None)
      (SIG: exists skd, skenv_link.(Genv.find_funct) fptr_arg = Some skd /\ SkEnv.get_sig skd = sg)
      (VALS: vs_arg = map (fun p => Locmap.getpair p ls) (loc_arguments sg))
    :
      at_external (Callstate stack fptr_arg sg ls m0)
                  (Args.mk fptr_arg vs_arg m0)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd ls_init sg
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      (LOCSET: typify_list args.(Args.vs) sg.(sig_args) = map (fun p => Locmap.getpair p ls_init) (loc_arguments sg))
      (PTRFREE: forall
          loc
          (* (NOTIN: Loc.notin loc (regs_of_rpairs (loc_arguments sg))) *)
          (NOTIN: ~In loc (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr (ls_init loc)>>)
      (SLOT: forall
          sl ty ofs
          (NOTIN: ~In (S sl ty ofs) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<UNDEF: ls_init (S sl ty ofs) = Vundef>>)
      (SZ: 4 * size_arguments sg <= Ptrofs.modulus)
      (LEN: args.(Args.vs).(length) = sg.(sig_args).(length))
    :
      initial_frame args
                    (Callstate [dummy_stack sg ls_init] args.(Args.fptr) sg ls_init args.(Args.m))
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      ls0 m0
      sg_init ls_init v0
      (VAL: Locmap.getpair (map_rpair R (loc_result sg_init)) ls0 = v0)
    :
      final_frame (Returnstate [dummy_stack sg_init ls_init] ls0 m0) (Retv.mk v0 m0)
  .

  Inductive after_external: state -> Retv.t -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg ls_arg m_arg retv
      ls_after
      (LSAFTER: ls_after = Locmap.setpair (loc_result sg_arg)
                                          (typify retv.(Retv.v) sg_arg.(proj_sig_res))
                                          (undef_caller_save_regs ls_arg))
    :
      after_external (Callstate stack fptr_arg sg_arg ls_arg m_arg)
                     retv
                     (Returnstate stack ls_after retv.(Retv.m))
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
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.
  Next Obligation. ii; ss; des. do 2 inv_all_once; ss; clarify. Qed.


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



  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge ge) st0)
    :
      determinate_at modsem st0
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    - inv H. inv H0. determ_tac sd_determ_at. esplits; eauto.
      eapply match_traces_preserved; try eassumption. ii; ss.
    - inv H. exploit sd_traces_at; eauto.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. eapply lift_determinate_at. eapply semantics_determinate. ii. eapply not_external; eauto. Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge ge) st)
    :
      receptive_at modsem st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss.
    - inv H. exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i; des. esplits; eauto. econs; eauto. admit "See Mach.v for same admit".
    - inv H. exploit sr_traces_at; eauto.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive. ii. eapply not_external; eauto. Qed.


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

