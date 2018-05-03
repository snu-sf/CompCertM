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
Require Import ModSem.

Set Implicit Arguments.



Section NEWSTEP.

Variable return_address_offset: function -> code -> ptrofs -> Prop.
Variable ge: genv.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs m= f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s fb sp (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra true) c :: s)
                       f' rs m)
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f' m',
      find_function_ptr ge ros rs m= f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff true) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff true) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s fb (Vptr stk soff true) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m')
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff true) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff true) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s fb (Vptr stk soff true) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m')
  | exec_function_internal:
      forall s fptr fb rs m f m1 m2 m3 stk rs'
      (FPTR: fptr = Vptr fb Ptrofs.zero true),
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero true in
      store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fptr rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs) ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m (NOTDUMMY: s <> []),
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f sp c rs m).

End NEWSTEP.

Definition dummy_stack (parent_sp parent_ra: val): stackframe := Stackframe 1%positive parent_sp parent_ra [].
Global Opaque dummy_stack.
Require Import Asmregs.

Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Definition mreg_of (r: preg): option mreg := admit "inverse of 'pref_of'".

Lemma mreg_of_preg_of
      pr0 mr0
      (SOME: (mreg_of pr0) = Some mr0)
  :
    preg_of mr0 = pr0
.
Proof.
  admit "".
Qed.

Lemma preg_of_injective
      mr0 mr1
      (EQ: preg_of mr0 = preg_of mr1)
  :
    <<EQ: mr0 = mr1>>
.
Proof. destruct mr0, mr1; ss. Qed.

Lemma preg_of_mreg_of
      mr0 mr1
      (INV: mreg_of (preg_of mr0) = Some mr1)
  :
    mr0 = mr1
.
Proof.
  exploit mreg_of_preg_of; eauto. i.
  ss.
  apply preg_of_injective; eauto.
Qed.

Print Conventions1.
(* Note: callee_save registers all reside in mregs. So we can just put undef on preg\mreg. *)

Definition pregset_of (mrs: Mach.regset): regset :=
  fun pr =>
    match mreg_of pr with
    | Some mr => mrs mr
    | None => Vundef
    end
.

Definition mregset_of (prs: regset): Mach.regset :=
  fun mr => prs (preg_of mr)
.

Coercion pregset_of: Mach.regset >-> regset.
Coercion mregset_of: regset >-> Mach.regset.

Section MODSEM.

  Variable rao: function -> code -> ptrofs -> Prop.
  Variable p: program.
  Let ge := p.(Genv.globalenv).

  Inductive at_external: state -> val -> option signature -> regset -> mem -> Prop :=
  | at_external_intro
      fptr_arg stack rs_arg m_arg
      (EXTERNAL: Genv.find_funct ge fptr_arg = None)

    :
      at_external (Callstate stack fptr_arg rs_arg m_arg)
                  fptr_arg None rs_arg m_arg
  .

  Inductive initial_frame (fptr_arg: val) (sg_arg: option signature) (rs_arg: regset) (m_arg: mem)
    : state -> Prop :=
  | initial_frame_intro
    :
      initial_frame fptr_arg sg_arg rs_arg m_arg
                    (Callstate [(dummy_stack (rs_arg SP) (rs_arg RA))] fptr_arg rs_arg m_arg)
  .

  Inductive final_frame (sg_init: option signature) (rs_init: regset): state -> regset -> mem -> Prop :=
  | final_frame_intro
      rs_ret m_ret
      dummy_stack
    :
      final_frame sg_init rs_init (Returnstate [dummy_stack] rs_ret m_ret) rs_ret m_ret
  .

  Inductive after_external: state -> option signature -> regset -> regset -> mem -> state -> Prop :=
  | after_external_intro
      stack fptr_arg rs_arg m_arg
      rs_ret m_ret
    :
      after_external (Callstate stack fptr_arg rs_arg m_arg) None rs_arg rs_ret m_ret
                     (Returnstate stack rs_ret m_ret)
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step rao;
      ModSem.get_mem := get_mem;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.globalenv := ge; (* TODO: Change this properly *)
      ModSem.skenv := (admit "TODO")
    |}
  .
  Next Obligation. inv INIT; ss. Qed.
  Next Obligation. inv STEP; inv ATEXT; ss; try rewrite FPTR in *; des_ifs. Qed.
  Next Obligation. inv ATEXT; inv FINAL; ss; try rewrite FPTR in *; clarify. Qed.
  Next Obligation. inv STEP; inv FINAL; ss; try rewrite FPTR in *; clarify. Qed.

End MODSEM.



