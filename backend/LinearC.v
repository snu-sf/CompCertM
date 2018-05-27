Require Import CoqlibC.
Require Import ASTC Integers Values Memory Events GlobalenvsC Smallstep.
Require Import Op Locations LTL Conventions.
(** newly added **)
Require Export Linear.
Require Import ModSem.
Require Import Asmregs.

Set Implicit Arguments.



Section NEWSTEP.

Variable ge: genv.
Let find_function_ptr := find_function_ptr ge.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (LTL.undef_regs (destroyed_by_getstack sl) rs) ->
      step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (LTL.undef_regs (destroyed_by_setstack ty) rs) ->
      step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lop:
      forall s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (LTL.undef_regs (destroyed_by_op op) rs) ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (LTL.undef_regs (destroyed_by_load chunk addr) rs) ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = LTL.undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m')
  | exec_Lcall:
      forall s f sp sig ros b rs m fptr
      (FPTR: find_function_ptr ros rs m= fptr)
      ,
      DUMMY_PROP ->
      DUMMY_PROP ->
      step (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) fptr sig rs m)
  | exec_Ltailcall:
      forall s f stk sig ros b rs m rs' fptr m'
      (FPTR: find_function_ptr ros rs' m= fptr)
      ,
      rs' = return_regs (parent_locset s) rs ->
      DUMMY_PROP ->
      DUMMY_PROP ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero true) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s fptr sig rs' m')
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (LTL.undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Lbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = LTL.undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = LTL.undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = LTL.undef_regs (destroyed_by_jumptable) rs ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lreturn:
      forall s f stk b rs m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero true) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m')
  | exec_function_internal:
      forall s fptr sg f rs m rs' m' stk
      (FPTR: Genv.find_funct ge fptr = Some (Internal f))
      (SIG: sg = funsig (Internal f))
      ,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = LTL.undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s fptr sg rs m)
        E0 (State s f (Vptr stk Ptrofs.zero true) f.(fn_code) rs' m')
  | exec_function_external:
      forall s fptr sg ef args res rs1 rs2 m t m'
      (FPTR: Genv.find_funct ge fptr = Some (External ef))
      (SIG: sg = funsig (External ef))
      ,
      args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs2 = Locmap.setpair (loc_result (ef_sig ef)) res (LTL.undef_regs destroyed_at_call rs1) ->
      step (Callstate s fptr sg rs1 m)
         t (Returnstate s rs2 m')
  | exec_return:
      forall s f sp rs0 c rs m (NOTDUMMY: s <> []),
      step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m).

End NEWSTEP.


Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end.

Definition get_stackframe (st: state): list stackframe :=
  match st with
  | State stks _ _ _ _ _ => stks
  | Callstate stks _ _ _ _ => stks
  | Returnstate stks _ _ => stks
  end
.

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
Definition dummy_code (sig: signature): code := [Lcall sig (admit "dummy_reg")].
Definition dummy_function (sig: signature) := (mkfunction (admit "dummy_sig") 0 (dummy_code sig)).

Definition dummy_stack (sig: signature) (ls: locset) :=
  Stackframe (dummy_function sig)
              (Vptr (admit "dummy_fptr") Ptrofs.zero true)
              ls
              [] (* one may replace it with another another_dummy_code,
but then corresponding MachM's part should be transl_code another_dummy_code ... *)
.
Hint Unfold dummy_stack.

Definition update_locset (ls: locset) (prs: regset): locset :=
  fun loc =>
    match loc with
    | R mr => prs (preg_of mr)
    | S _ _ _ => ls loc
    end
.

Definition to_locset (prs: regset): locset :=
  update_locset (Locmap.init Vundef) prs
.

(* TODO: remove redundancy with MachC. *)
Definition mreg_of (r: preg): option mreg := admit "inverse of 'pref_of'".

Definition to_regset (ls: locset): regset :=
  fun pr =>
    match mreg_of pr with
    | Some mr => ls (R mr)
    | None => Vundef
    end
.

Inductive callee_saved (sg: signature) (rs0 rs1: regset): Prop :=
| callee_saved_intro
    (TODO: True)
    (* In Compcert' sg is not needed (see is_callee_save). Is it true in real-world too? *)
.

Section MODSEM.

  Variable p: program.
  Let ge := p.(Genv.globalenv).

  Inductive at_external: state -> regset -> mem -> Prop :=
  | at_external_intro
      stack fptr_arg sg_arg ls_arg rs_arg m_arg
      (FPTR: fptr_arg = rs_arg PC)
      (EXTERNAL: Genv.find_funct ge fptr_arg = None)
      (REGSET: rs_arg = ls_arg.(to_regset))
    :
      at_external (Callstate stack fptr_arg sg_arg ls_arg m_arg)
                  rs_arg m_arg
  .

  Print extcall_arguments.
  Print extcall_arg_pair.
  Print extcall_arg.

  Inductive fill_slots (ls0: locset) (locs: list (rpair loc)) (rs: regset) (m: mem) (ls1: locset): Prop :=
  | update_slots_intro
      (SLOTIN: forall
          sl pos ty
          (IN: In (S sl pos ty) locs.(regs_of_rpairs))
        ,
          <<SLOT: exists v, extcall_arg rs m (S sl pos ty) v /\ ls1 (S sl pos ty) = v>>)
      (SLOTNOTIN: forall
          sl pos ty
          (IN: ~ In (S sl pos ty) locs.(regs_of_rpairs))
        ,
          (* <<SLOT: ls1 (S sl pos ty) = Vundef>>) *)
          <<SLOT: ls0 (S sl pos ty) = ls1 (S sl pos ty)>>)
      (REGS: forall
          r
        ,
          <<EQ: ls0 r = ls1 r>>)
  .

  (* Definition fill_slots (ls0: locset) (locs: list (rpair loc)) (rs: regset) (m: mem): locset := *)
  (*   fun loc => *)
  (*     match loc with *)
  (*     | R _ => ls0 loc *)
  (*     | S sl pos ty => *)
  (*       if in_dec Loc.eq loc locs.(regs_of_rpairs) *)
  (*       then *)
  (*         if Mem.loadv  *)
  (*       else Vundef *)
  (* . *)

  Inductive initial_frame (rs_arg: regset) (m_arg: mem)
    : state -> Prop :=
  | initial_frame_intro
      fptr_arg fd sg_init ls_init
      (FPTR: fptr_arg = rs_arg PC)
      (FINDFUNC: Genv.find_funct ge fptr_arg = Some (Internal fd))
      (SIG: sg_init = fd.(fn_sig))
      (LOCSET: fill_slots rs_arg.(to_locset) (loc_arguments sg_init) rs_arg m_arg ls_init)
      (* sp delta *)
      (* (RSPPTR: rs_arg RSP = Vptr sp (Ptrofs.repr delta) true) *)
      (* (ARGSPERM: Mem.range_perm m_arg sp delta (size_arguments fd.(fn_sig)) Cur Writable) *)
      sp
      (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true)
      (ARGSPERM: Mem.range_perm m_arg sp 0 (size_arguments fd.(fn_sig)) Cur Writable)
    :
      initial_frame rs_arg m_arg
                    (Callstate [(dummy_stack sg_init ls_init)] fptr_arg sg_init ls_init m_arg)
  .

  Inductive final_frame (rs_init: regset): state -> regset -> mem -> Prop :=
  | final_frame_intro
      ls_ret rs_ret m_ret
      dummy_stack
      (REGSET: rs_ret = ls_ret.(to_regset))
    :
      final_frame rs_init (Returnstate [dummy_stack] ls_ret m_ret) rs_ret m_ret
  .

  Inductive after_external: state -> regset -> regset -> mem -> state -> Prop :=
  | after_external_intro
      stack fptr_arg sg_arg ls_arg m_arg
      rs_arg rs_ret m_ret
      ls_ret
      (CALLEESAVE: callee_saved sg_arg rs_arg rs_ret)
      (LOCSET: ls_ret = update_locset ls_arg rs_ret)
    :
      after_external (Callstate stack fptr_arg sg_arg ls_arg m_arg) rs_arg rs_ret m_ret
                     (Returnstate stack ls_ret m_ret)
  .

  Lemma fill_slots_dtm
        ls0 locs rs m ls1 ls2
        (FILL0: fill_slots ls0 locs rs m ls1)
        (FILL1: fill_slots ls0 locs rs m ls2)
    :
      ls1 = ls2
  .
  Proof.
    inv FILL0. inv FILL1.
    eapply Axioms.functional_extensionality.
    i. destruct x; ss.
    - erewrite <- REGS. erewrite <- REGS0. ss.
    - destruct (classic (In (S sl pos ty) (regs_of_rpairs locs))).
      + exploit SLOTIN; eauto. i; des.
        exploit SLOTIN0; eauto. i; des.
        clarify.
        inv H0; inv H2; ss. des_ifs.
        (* TODO: Move determinacy lemma for extcall_arg into Asmregs, and use it *)
      + exploit SLOTNOTIN; eauto. i; des.
        exploit SLOTNOTIN0; eauto. i; des.
        congruence.
  Qed.

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step;
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
  Next Obligation.
    inv INIT0; inv INIT1; ss. clarify.
    assert(ls_init = ls_init0).
    { eapply fill_slots_dtm; eauto. }
    clarify.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    hnf. inv H4; inv H2; subst_locals; all_rewrite; ss; des_ifs.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.

End MODSEM.



