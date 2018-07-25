Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Export Mach.
Require Import Skeleton Mod ModSem.
Require Import Simulation Integers.

Set Implicit Arguments.

Local Open Scope asm.


Section MACHEXTRA.

  Variable rao: function -> code -> ptrofs -> Prop.

  Hypothesis rao_dtm:
    forall f c ofs ofs',
      rao f c ofs ->
      rao f c ofs' ->
      ofs = ofs'. 

  Definition is_external (ge: genv) (st: state): Prop :=
    match st with
    | Callstate stack fptr rs m =>
      match Genv.find_funct ge fptr with
      | Some (AST.External ef) => is_external_ef ef
      | _ => False
      end
    | _ => False
    end
  .

  Variable ge: genv.
  Definition semantics_with_ge := Semantics (step rao) bot1 final_state ge.
  (* *************** ge is parameterized *******************)

  Lemma semantics_receptive
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      receptive_at semantics_with_ge st
  .
  Proof.
    revert rao_dtm. (* dummy *)
    admit "this should hold".
  Qed.

  Lemma semantics_determinate
        st
        (INTERNAL: ~is_external semantics_with_ge.(globalenv) st)
    :
      determinate_at semantics_with_ge st
  .
  Proof.
    revert rao_dtm. (* dummy *)
    admit "this should hold".
  Qed.

End MACHEXTRA.
(*** !!!!!!!!!!!!!!! REMOVE ABOVE AFTER MERGING WITH MIXED SIM BRANCH !!!!!!!!!!!!!!!!!! ***)



Section NEWSTEP.

Variable return_address_offset: function -> code -> ptrofs -> Prop.
Variable ge: genv.

Definition get_stack (st: state): list stackframe :=
  match st with
  | State stk _ _ _ _ _ => stk
  | Callstate stk _ _ _ => stk
  | Returnstate stk _ _ => stk
  end.

Inductive step: state -> trace -> state -> Prop :=
| step_intro
    st0 tr st1
    (STEP: Mach.step return_address_offset ge st0 tr st1)
    (NOTDUMMY: st1.(get_stack) <> [])
  :
    step st0 tr st1
.

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
(*       (FPTR: fptr = Vptr fb Ptrofs.zero true), *)
(*       Genv.find_funct_ptr ge fb = Some (Internal f) -> *)
(*       Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) -> *)
(*       let sp := Vptr stk Ptrofs.zero true in *)
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

(* Definition dummy_stack (parent_sp parent_ra: val): stackframe := *)
(*   match parent_sp with *)
(*   | Vptr sp _ true => Stackframe 1%positive (Vptr sp Ptrofs.zero true) parent_ra [] *)
(*   | _ => Stackframe 1%positive Vundef parent_ra [] (* This should not occur. *) *)
(*   end *)
(* . *)
(* See "stack_contents" of the stackingproof. It ignores sp's offset. *)
(* "stack_contents" is used in match_states, and we want to use it... *)
Definition dummy_stack (parent_sp parent_ra: val): stackframe :=
  Stackframe 1%positive parent_sp parent_ra []
.

Hint Unfold dummy_stack.
(* Global Opaque dummy_stack. *)

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Require Import AsmregsC.
(* Coercion pregset_of: Mach.regset >-> regset. *)
(* Coercion mregset_of: regset >-> Mach.regset. *)

Section MODSEM.

  Variable rao: function -> code -> ptrofs -> Prop.
  Hypothesis rao_dtm:
    forall f c ofs ofs',
      rao f c ofs ->
      rao f c ofs' ->
      ofs = ofs'. 


  Variable skenv_link: SkEnv.t.
  Variable p: program.
  Let skenv: SkEnv.t := skenv_link.(SkEnv.project) p.(defs).
  Let ge: genv := skenv.(SkEnv.revive) p.

  Inductive at_external: state -> regset -> mem -> Prop :=
  | at_external_intro
      fptr_arg stack (rs_arg: Mach.regset) m_arg
      (EXTERNAL: Genv.find_funct ge fptr_arg = None)
      prs_arg
      (CD: Call.C2D rs_arg fptr_arg (parent_sp stack) (parent_ra stack) prs_arg)
    :
      at_external (Callstate stack fptr_arg rs_arg m_arg)
                  prs_arg m_arg
  .

  Inductive initial_frame (rs_arg: regset) (m_arg: mem)
    : state -> Prop :=
  | initial_frame_intro
      fptr_arg
      (FPTR: fptr_arg = rs_arg PC)
      fd
      (FIND: Genv.find_funct ge fptr_arg = Some (Internal fd))
      (* sp delta *)
      (* (RSPPTR: rs_arg RSP = Vptr sp (Ptrofs.repr delta) true) *)
      (* (ARGSPERM: Mem.range_perm m_arg sp delta (size_arguments fd.(fn_sig)) Cur Writable) *)

      (* sp *)
      (* (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true) *)
      (* (ARGSPERM: Mem.range_perm m_arg sp 0 (size_arguments fd.(fn_sig)) Cur Writable) *)
    :
      initial_frame rs_arg m_arg
                    (Callstate [(dummy_stack (rs_arg SP) (rs_arg RA))] fptr_arg rs_arg.(to_mregset) m_arg)
  .

  Inductive final_frame (rs_init: regset): state -> regset -> Prop :=
  | final_frame_intro
      rs_ret m_ret
      dummy_stack
    :
      final_frame rs_init (Returnstate [dummy_stack] rs_ret m_ret) rs_ret.(to_pregset)
  .

  Inductive after_external: state -> regset -> regset -> mem -> state -> Prop :=
  | after_external_intro
      stack fptr_arg _rs_arg (* TODO: We can just ignore _rs_arg. Can we unify this with rs_arg? *) rs_arg m_arg
      rs_ret m_ret
    :
      after_external (Callstate stack fptr_arg _rs_arg m_arg) rs_arg rs_ret m_ret
                     (Returnstate stack rs_ret.(to_mregset) m_ret)
  .


  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step rao;
      ModSem.get_mem := get_mem;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge; 
      ModSem.skenv := skenv;
    |}
  .
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. inv INIT0; inv INIT1; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    ii. des. inv PR. inv PR0; inv STEP; ss; all_rewrite; ss; des_ifs.
  Qed.
  Next Obligation. ii. des. all_prop_inv; ss. Qed.
  Next Obligation. ii. des. all_prop_inv; ss. Qed.

  Lemma not_external
    :
      is_external ge <1= bot1
  .
  Proof.
    ii. hnf in PR. des_ifs.
    subst_locals.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    repeat all_once_fast ltac:(fun H => try apply Genv_map_defs_spec in H; des).
    Local Opaque Genv.invert_symbol.
    unfold o_bind, o_join, o_map in *. cbn in *. des_ifs_safe.
    unfold ASTC.is_external, is_external_fd in *. simpl_bool. des_ifs.
  Qed.

  Lemma lift_receptive_at
        st
        (RECEP: receptive_at (semantics_with_ge rao ge) st)
    :
      receptive_at modsem st
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss.
    - inv H.
      exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i; des. esplits; eauto. econs; eauto.
      { admit "1) prove get_stack dtm 2) at first place, prove full determinacy instead of determinate". }
    - inv H.
      exploit sr_traces_at; eauto.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. eapply lift_receptive_at. eapply semantics_receptive; eauto. ii. eapply not_external; eauto. Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge rao ge) st0)
    :
      determinate_at modsem st0
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    - inv H. inv H0.
      determ_tac sd_determ_at. esplits; eauto.
      eapply match_traces_preserved; try eassumption. ii; ss.
    - inv H.
      exploit sd_traces_at; eauto.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. eapply lift_determinate_at. eapply semantics_determinate; eauto. ii. eapply not_external; eauto. Qed.


End MODSEM.



