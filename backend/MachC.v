Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import LocationsC.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Export Mach.
Require Import Skeleton Mod ModSem.
Require Import Simulation Integers.

Set Implicit Arguments.


Ltac extcall_simpl :=
  repeat match goal with
         | [ H: extcall_arg_pair _ _ _ (One _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (S _ _ _) _ |- _ ] => inv H
         | [ H: extcall_arg _ _ _ (R _) _ |- _ ] => inv H
         end
.

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


Inductive store_arguments (m0: mem) (rs: regset) (vs: list val) (sg: signature) (m2: mem): Prop :=
| store_arguments_intro
    m1 blk
    (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, blk))
    (VALS: extcall_arguments rs m2 (Vptr blk Ptrofs.zero true) sg vs)
    (UNCH: Mem.unchanged_on (fun b ofs => if eq_block b blk
                                          then (* ~ (0 <= ofs < 4 * size_arguments sg) *) False
                                          else True) m1 m2)
    (NB: m1.(Mem.nextblock) = m2.(Mem.nextblock))
    (PERM: Mem.range_perm m2 blk 0 (4 * size_arguments sg) Cur Freeable)
.

Local Opaque Z.mul Z.sub Z.div.
Local Transparent size_arguments.
Local Transparent loc_arguments.

Fixpoint fill_arguments (sp: block) (rs0: regset) (m0: mem) (args: list val) (locs: list (rpair loc)):
    option (regset * mem) :=
  match args, locs with
  | [], [] => Some (rs0, m0)
  | arg :: args, loc :: locs =>
    do (rs1, m1) <- fill_arguments sp rs0 m0 args locs ;
      match loc with
      | One (R r) => Some (rs1 # r <- arg, m1)
      (* | One (S Outgonitgttttttt ofs ty) => *)
      | One (S Outgoing ofs ty) =>
        (* do m2 <- Mach.store_stack m0 sp ty (4 * ofs).(Ptrofs.repr) arg ; *)
        do m2 <- Mem.store (chunk_of_type ty) m1 sp (4 * ofs) arg ;
          Some (rs1, m2)
      | _ => None
      end
  | _, _ => None
  end
.


Hint Unfold curry2.
Local Opaque list_nth_z.
Ltac divtac_ :=
  try apply Z.divide_0_r;
  try apply Z.divide_refl;
  try (apply Z.mul_divide_cancel_l; ss; try xomega; check_safe);
  try eapply Z.divide_add_r; eauto;
  try (by (eapply Z.divide_factor_l; eauto));
  try (by (eapply Z.divide_refl; eauto));
  try xomega.
Ltac divtac := repeat divtac_.

Let fill_arguments_progress_aux
    sig_args m0 rs0 m1 sp args
    x y z
    (LEN: Datatypes.length args = Datatypes.length sig_args)
    (ALC: Mem.alloc m0 0 (4 * size_arguments_64 sig_args x y z) = (m1, sp))
    (* (ZWF: 0 <= 4 * z <= Ptrofs.max_unsigned) *)
    (ZWF: 0 <= z /\ (2 | z))
  :
    exists rs1 m2,
      <<FILL:
        fill_arguments (* (Vptr sp Ptrofs.zero true) *) sp rs0 m1 args
                       (loc_arguments_64 sig_args x y z) = Some (rs1, m2)>>
      /\
      (* <<VALID: forall chunk ofs (LO: lo <= ofs) (HI: ofs + size_chunk chunk <= hi) (ALIGN: align_chunkMem.valid_access m2 *)
      <<PERM: Mem.range_perm m2 sp 0 (4 * size_arguments_64 sig_args x y z) Cur Freeable>>
.
Proof.
  ginduction sig_args; ii; ss; destruct args; ss.
  { esplits; eauto. eapply Mem_alloc_range_perm; eauto. }
  des.
  des_ifs; try (exploit IHsig_args; eauto; try (by esplits; divtac); i; des; check_safe);
    try (rewrite FILL; u); try by (esplits; eauto).
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. change 8 with (4 * 2). divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
  - match goal with
    | [ |- context[?chnk: memory_chunk] ] => destruct (Mem.valid_access_store m2 chnk sp (4 * pos) v)
    end.
    { eapply Mem.valid_access_implies with Freeable; eauto with mem.
      split.
      + ii. eapply PERM; eauto. split; try xomega. ss.
        generalize (size_arguments_64_above sig_args x y (pos + 2)). i. xomega.
      + ss. divtac.
    }
    des_ifs. esplits; eauto.
    ii. eapply Mem.perm_store_1; eauto.
Qed.

Lemma fill_arguments_progress
      sg m0 rs0 m1 sp args
      (LEN: length args = length sg.(sig_args))
      (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, sp))
  :
      exists rs1 m2, <<STORE: fill_arguments (* (Vptr sp Ptrofs.zero true) *) sp rs0 m1 args (loc_arguments sg)
                              = Some (rs1, m2)>>
.
Proof.
  (* set (SG:= sg). *)
  destruct sg; ss.
  unfold loc_arguments, size_arguments in *. ss. des_ifs. clear_tac.
  exploit fill_arguments_progress_aux; eauto.
  { split; try xomega. divtac. }
  i; des. eauto.
Qed.

(* Local Transparent loc_arguments size_arguments. *)
(* Let fill_arguments_spec_aux: forall *)
(*     sig_args sig_res sig_cc *)
(*     m0 rs0 m1 sp args *)
(*     (LEN: Datatypes.length args = Datatypes.length sig_args) *)
(*     x y z *)
(*     (ALC: Mem.alloc m0 0 (4 * size_arguments_64 sig_args x y z) = (m1, sp)) *)
(*     rs1 m2 *)
(*     (FILL: fill_arguments sp rs0 m1 args (loc_arguments_64 sig_args x y z) = Some (rs1, m2)) *)
(*   , *)
(*     <<STORE: store_arguments m0 rs1 args {| sig_args := sig_args; sig_res := sig_res; sig_cc := sig_cc |} m1>> *)
(* . *)
(* Proof. *)
(*   ii. *)
(*   ginduction args; ii; ss; des_ifs_safe. *)
(*   { econs; eauto. *)
(*     - unfold size_arguments. des_ifs. ss. *)
(*     - rr. unfold loc_arguments. ss. des_ifs. rewrite Heq0. econs; eauto. *)
(*     - refl. *)
(*     - eapply Mem_alloc_range_perm; eauto. *)
(*   } *)
(* Qed. *)

Hint Unfold o_bind2.

(* Lemma list_forall2_sep *)
(*       X Y *)
(*       (P Q: X -> Y -> Prop) *)
(*       xs ys *)
(*       (ALL: list_forall2 P xs ys) *)
(*       (SEP: forall x y, P x y -> Q x y) *)
(*   : *)
(*     <<ALL: list_forall2 Q xs ys>> *)
(* . *)
(* Proof. *)
(* Qed. *)

Lemma fill_arguments_unchanged_on
      sp rs0 m0 args x y z rs1 m1 tys
      (LEN: length args = length tys)
      (FILL: fill_arguments sp rs0 m0 args (loc_arguments_64 tys x y z) = Some (rs1, m1))
  :
    (* <<UNCH: Mem.unchanged_on (brange sp 0 (4 * z)) m0 m1>> *)
    <<UNCH: Mem.unchanged_on (fun b ofs => if eq_block b sp
                                           then (0 <= ofs < 4 * z)
                                           else True) m0 m1>>
.
Proof.
  ginduction args; ii; ss; des_ifs_safe; destruct tys; ss.
  { r. refl. }
  u in FILL.
  des_ifs_safe. destruct r0; ss.
  { unfold Regmap.set in *. clarify. destruct p; ss.
    des_ifs; eapply IHargs; eauto.
  }
  { des_ifs_safe. destruct p; ss.
    des_ifs.
    - r. etrans; cycle 1.
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
      exploit IHargs; eauto. i.
      eapply Mem.unchanged_on_implies; eauto.
      u. ii; ss. des. des_ifs. esplits; eauto; try xomega.
    - exploit IHargs; eauto. i; des.
      r. etrans; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
    - exploit IHargs; eauto. i; des.
      r. etrans; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
    - exploit IHargs; eauto. i; des.
      r. etrans; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
    - exploit IHargs; eauto. i; des.
      r. etrans; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
    - exploit IHargs; eauto. i; des.
      r. etrans; eauto.
      { eapply Mem.unchanged_on_implies; eauto.
        u. ii; ss. des. des_ifs. esplits; eauto; xomega. }
      { eapply Mem.store_unchanged_on; eauto. u. ii; ss. des. des_ifs. xomega. }
  }
Qed.

(* TODO: remove same lemma in AsmregsC *)
Lemma typesize_chunk
      ty
  :
    size_chunk (chunk_of_type ty) =
    4 * ty.(typesize)
.
Proof. destruct ty; ss. Qed.

Let fill_arguments_spec_aux: forall
    sg m0 rs0 m1 sp args
    x y z
    (ALC: Mem.alloc m0 0 (4 * size_arguments_64 (sig_args sg) x y z) = (m1, sp))
    rs1 m2
    (FILL: fill_arguments sp rs0 m1 args (loc_arguments_64 (sig_args sg) x y z) = Some (rs1, m2))
    (LEN: length args = length sg.(sig_args))
    (DISJ: Loc.norepet (regs_of_rpairs (loc_arguments_64 (sig_args sg) x y z)))
    (ONE: forall lp, In lp (loc_arguments_64 (sig_args sg) x y z) -> <<ONE: is_one lp >>)
    (MAX: 4 * (size_arguments_64 (sig_args sg) x y z) <= Ptrofs.max_unsigned)
    (TYPED: Val.has_type_list args sg.(sig_args))
    (ACC: forall lp, In lp (loc_arguments_64 (sig_args sg) x y z) ->
                     <<ACC: forall_rpair loc_argument_acceptable lp>>)
    (BDD: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments_64 (sig_args sg) x y z)))
          ,
            <<BDD: ofs + typesize ty <= size_arguments_64 (sig_args sg) x y z>>)
  ,
    <<ALL: list_forall2 (extcall_arg_pair rs1 m2 (Vptr sp Ptrofs.zero true)) (loc_arguments_64 (sig_args sg) x y z) args>>
.
Proof.
  i.
  exploit fill_arguments_unchanged_on; eauto.
  intro UNCH; des.
  (* abstr (4 * (size_arguments_64 (sig_args sg) x y z)) sz. *)
  (* abstr (loc_arguments_64 (sig_args sg) x y z) locs. *)
  abstr (sig_args sg) tys.
  (* generalize (loc_arguments_64_charact tys x y z). intro CHAR. *)
  set (TYS:= tys) in *.
  ginduction args; ii; destruct tys; ss; des_ifs_safe.
  { econs; eauto. }
  u in FILL. des_ifs_safe; ss. destruct p; ss.
  unfold Regmap.set in *.
  destruct t; ss.
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          change Mint32 with (chunk_of_type Tint).
          rewrite Val.load_result_same; ss.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mint32));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          change Mfloat64 with (chunk_of_type Tfloat).
          rewrite Val.load_result_same; ss.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat64));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          change Mint64 with (chunk_of_type Tlong).
          rewrite Val.load_result_same; ss.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat64));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          change Mfloat32 with (chunk_of_type Tsingle).
          rewrite Val.load_result_same; ss.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Mfloat32));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
          change Many32 with (chunk_of_type Tany32).
          rewrite Val.load_result_same; ss.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many32));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
  - des_safe. des_ifs.
    + exploit IHargs; eauto.
      { locmap_tac. }
      i; des.
      econs; eauto.
      * econs; eauto. rp; [econs|..]; try refl; eauto. ss. des_ifs.
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. ss. des_ifs. admit "ez - rpairs". }
        econs; eauto.
    + rename m2 into m3. rename m into m2.
      exploit IHargs; eauto.
      { locmap_tac. }
      { eapply fill_arguments_unchanged_on; eauto. }
      i; des.
      econs; eauto.
      * econs; eauto. econs; eauto. cbn. ss.
        rewrite Ptrofs.add_zero_l.
        rewrite Ptrofs.unsigned_repr; ss.
        { erewrite Mem.load_store_same; eauto. rp; try rewrite Val.load_result_same; eauto.
        }
        {
          hexploit BDD; eauto. i; des. ss.
          exploit ACC; eauto. i; ss; des.
          split; try xomega.
        }
      * eapply list_forall2_imply; eauto.
        ii. specialize (ONE v1). hexploit1 ONE; eauto. destruct v1; ss. clear_tac.
        extcall_simpl.
        econs; eauto.
        match goal with | [ H: extcall_arg _ _ _ _ _ |- _ ] => inv H end; ss.
        { rp; [econs|..]; try refl; eauto. }
        econs; eauto.
        ss. cbn in *.
        rewrite Ptrofs.add_zero_l in *.
        rewrite ! Ptrofs.unsigned_repr in *; ss; cycle 1.
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        {
          hexploit BDD; try right; eauto.
          { eapply in_regs_of_rpairs; ss; eauto; ss; eauto. }
          i; des.
          exploit ACC; try right; eauto. i; ss; des.
          generalize (typesize_pos ty); i.
          split; try xomega.
        }
        eapply Mem.load_unchanged_on with (P:= ~2 brange sp (4 * pos) (4 * pos + size_chunk Many64));
          try apply H3; eauto.
        { eapply Mem.store_unchanged_on; eauto. }
        { locmap_tac.
          exploit Loc.in_notin_diff; eauto.
          { eapply in_regs_of_rpairs; eauto. ss. eauto. }
          intro DIFF. ss. des_safe; ss. rewrite typesize_chunk.
          u; ii. des; try xomega.
        }
Qed.

Let fill_arguments_perm: forall
    sp rs0 m0 args locs rs1 m1
    (FILL: fill_arguments sp rs0 m0 args locs = Some (rs1, m1))
  ,
    <<PERM: forall ofs k p, Mem.perm m0 sp ofs k p -> Mem.perm m1 sp ofs k p>>
.
Proof.
  i.
  ginduction args; ii; ss; des_ifs_safe.
  { des_ifs. }
  u in FILL. des_ifs_safe. des_ifs.
  - destruct p0; ss. eapply IHargs; eauto.
  - destruct p0; ss. eapply Mem.perm_store_1; eauto. eapply IHargs; eauto.
Qed.

Theorem fill_arguments_spec
      sg m0 rs0 m1 sp args targs
      (* (LEN: length args = length sg.(sig_args)) *)
      (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, sp))
      rs1 m2
      (LEN: length args = length sg.(sig_args))
      (TYPIFY: typify_list args sg.(sig_args) = targs)
      (MAX: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (FILL: fill_arguments sp rs0 m1 targs (loc_arguments sg) = Some (rs1, m2))
  :
    store_arguments m0 rs1 targs sg m2
.
Proof.
  generalize (loc_arguments_norepet sg). intro DISJ.
  generalize (loc_arguments_one sg). intro ONE.
  (* destruct sg; ss. unfold size_arguments, loc_arguments in *. *)
  ss. des_ifs. clear_tac.
  unfold loc_arguments in *. des_ifs.
  assert(LEN2: length (typify_list args (sig_args sg)) = length (sig_args sg)).
  { u. rewrite zip_length. lia. }
  econs; eauto.
  - rr.
    eapply fill_arguments_spec_aux; ss; eauto.
    + eapply typify_has_type_list; eauto.
    + ii. eapply loc_arguments_acceptable; eauto. unfold loc_arguments. des_ifs. eauto.
    + i. eapply loc_arguments_bounded; eauto.
  - eapply Mem.unchanged_on_implies.
    { eapply fill_arguments_unchanged_on; try apply FILL; eauto. }
    i. des_ifs.
  - admit "ez - nextblock".
  - ii. eapply fill_arguments_perm; eauto. eauto with mem.
Qed.

Lemma store_arguments_progress
      m0 vs sg
  :
    exists rs m2, <<STR: store_arguments m0 rs vs sg m2>>
.
Proof.
  admit "".
Qed.

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
      (VALS: extcall_arguments rs m0 (parent_sp stack) sg vs)
      (RSP: (parent_sp stack) = Vptr blk ofs true)
      (OFSZERO: ofs = Ptrofs.zero)
      (FREE: Mem.free m0 blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
      init_rs init_sg
    :
      at_external (mkstate init_rs init_sg (Callstate stack fptr rs m0)) (Args.mk fptr vs m1)
  .

  Inductive initial_frame (args: Args.t)
    : state -> Prop :=
  | initial_frame_intro
      fd m0 sp m1 rs0 rs1 sg ra
      (RAPTR: Val.has_type ra Tptr)
      (SIG: sg = fd.(fn_sig))
      (FINDF: Genv.find_funct ge args.(Args.fptr) = Some (Internal fd))
      targs
      (TYP: typecheck args.(Args.vs) sg targs)
      (ALC: Mem.alloc args.(Args.m) 0 (4 * size_arguments sg) = (m0, sp))
      (FILL: fill_arguments sp rs0 m0 (typify_list args.(Args.vs) sg.(sig_args)) (loc_arguments sg) = Some (rs1, m1))
      (PTRFREE: forall
          mr
          (* (NOTIN: Loc.notin (R mr) (regs_of_rpairs (loc_arguments sg))) *)
          (NOTIN: ~In (R mr) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr (rs1 mr)>>)
      (MEMWF: Ple (Senv.nextblock skenv_link) args.(Args.m).(Mem.nextblock))
    :
      initial_frame args (mkstate rs1 sg
                                  (Callstate [dummy_stack
                                                (Vptr args.(Args.m).(Mem.nextblock) Ptrofs.zero true) ra]
                                             args.(Args.fptr) rs1 m1))
  (* TODO: change (Vptr args.(Args.m).(Mem.nextblock) Ptrofs.zero true) into sp *)
  .

  Inductive final_frame: state -> Retv.t -> Prop :=
  | final_frame_intro
      (init_rs rs: regset) init_sp m0 m1 blk init_sg mr ra
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr -> Val.lessdef (init_rs mr) (rs mr))
      (INITRSP: init_sp = Vptr blk Ptrofs.zero true)
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
      (RSP: (parent_sp stack) = Vptr blk ofs true)
      (MEMWF: Ple (Senv.nextblock skenv_link) retv.(Retv.m).(Mem.nextblock))
      (UNFREE: Mem_unfree retv.(Retv.m) blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some m1)
    :
      after_external (mkstate init_rs init_sg (Callstate stack fptr ls0 m0))
                     retv
                     (mkstate init_rs init_sg (Returnstate stack ls1 m1))
  .

  Inductive step' (ge: genv) (st0: state) (tr: trace) (st1: state): Prop :=
  | step'_intro
      (STEP: Mach.step rao ge st0.(st) tr st1.(st))
      (INITRS: st0.(init_rs) = st1.(init_rs))
      (INITFPTR: st0.(init_sg) = st1.(init_sg))
      (NOTDUMMY: st1.(st).(get_stack) <> [])
  .

  Program Definition modsem: ModSem.t :=
    {|
      ModSem.step := step';
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
    assert(vs = vs0).
    { admit "this should be prove in mixed sim. merge with it". }
    clarify.
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
        (RECEP: receptive_at (semantics_with_ge rao ge) st)
    :
      forall init_rs init_sg, receptive_at modsem (mkstate init_rs init_sg st)
  .
  Proof.
    inv RECEP. econs; eauto; ii; ss.
    - inv H. ss.
      exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i; des. destruct s1; ss.
      exists (mkstate init_rs1 init_sg1 s2).
      econs; eauto. ss.
      { admit "1) prove get_stack dtm 2) at first place, prove full determinacy instead of determinate". }
    - inv H.
      exploit sr_traces_at; eauto.
  Qed.

  Lemma modsem_receptive
        st
    :
      receptive_at modsem st
  .
  Proof. destruct st. eapply lift_receptive_at. eapply semantics_receptive; eauto. ii. eapply not_external; eauto. Qed.

  Lemma lift_determinate_at
        st0
        (DTM: determinate_at (semantics_with_ge rao ge) st0)
    :
      forall init_rs init_sg, determinate_at modsem (mkstate init_rs init_sg st0)
  .
  Proof.
    inv DTM. econs; eauto; ii; ss.
    - inv H. inv H0.
      determ_tac sd_determ_at. esplits; eauto.
      { eapply match_traces_preserved; try eassumption. ii; ss. }
      i. destruct s1, s2; ss. rewrite H0; ss. eauto with congruence.
    - inv H.
      exploit sd_traces_at; eauto.
  Qed.

  Lemma modsem_determinate
        st
    :
      determinate_at modsem st
  .
  Proof. destruct st. eapply lift_determinate_at. eapply semantics_determinate; eauto. ii. eapply not_external; eauto. Qed.


End MODSEM.




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
  Next Obligation.
    rewrite Sk.of_program_defs.
    eapply SkEnv.project_impl_spec; eauto.
  Qed.

End MODULE.
