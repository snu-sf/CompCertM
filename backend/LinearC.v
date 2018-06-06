Ltac check_safe := let n := numgoals in guard n < 2.

Require Import CoqlibC.
Require Import ASTC Integers Values MemoryC Events GlobalenvsC Smallstep.
Require Import Op Locations LTL Conventions.
(** newly added **)
Require Export Linear.
Require Import ModSem.
Require Import AsmregsC.

Set Implicit Arguments.



Fixpoint fill_arguments (ls0: locset) (args: list val) (locs: list (rpair loc)): option locset :=
  match args, locs with
  | [], [] => Some ls0
  | arg :: args, loc :: locs =>
    match fill_arguments ls0 args locs with
    | Some ls1 =>
      match loc with
      | One loc => Some (Locmap.set loc arg ls1)
      | Twolong hi lo => Some (Locmap.set lo arg.(Val.loword) (Locmap.set hi arg.(Val.hiword) ls1))
      end
    | None => None
    end
  | _, _ => None
  end
.

Local Opaque Z.mul Z.add.
Local Opaque list_nth_z.

Lemma chunk_type_chunk
      ty
  :
    (type_of_chunk (chunk_of_type ty)) = ty
.
Proof.
  destruct ty; ss.
Qed.

Print Loc.notin.
Print Loc.norepet.
Print Loc.no_overlap.

Lemma Loc_cons_right_disjoint
      xs0 xs1
      (DISJ: Loc.disjoint xs0 xs1)
      x
      (NOTIN: Loc.notin x xs0)
  :
    <<DISJ: Loc.disjoint xs0 (x :: xs1)>>
.
Proof.
  ii; ss.
  des; ss; clarify; eauto.
  apply Loc.diff_sym.
  eapply Loc.in_notin_diff; eauto.
Qed.

Lemma loc_arguments_norepet_aux
      tys (ir fr ofs: Z)
      locs
      (LOCS: (regs_of_rpairs (loc_arguments_64 tys ir fr ofs)) = locs)
  :
    (<<NOREP: Loc.norepet locs>>)
    /\
    (<<NOTINIR: Loc.disjoint (map R (List.firstn ir.(Z.to_nat) int_param_regs)) locs>>)
    /\
    (<<NOTINFR: Loc.disjoint (map R (List.firstn fr.(Z.to_nat) float_param_regs)) locs>>)
.
Proof.
  ginduction tys; ii; ss; clarify.
  { esplits; eauto.
    - econs; eauto.
    - ii; ss.
    - ii; ss.
  }
  des_ifs; ss.
  -
    (* rewrite Z.add_comm in *; ss. *)
    (* specialize (IHtys (1 + ir)%nat fr ofs _ eq_refl); des; ss. *)
    specialize (IHtys (ir + 1) fr ofs _ eq_refl); des; ss.
    esplits; eauto.
    + econs; eauto.
      eapply Loc.disjoint_notin; try apply NOTINIR.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      { admit "easy". }
      { admit "easy". }
    + eapply Loc_cons_right_disjoint; eauto.
      { admit "easy". }
  - specialize (IHtys ir fr (ofs + 2) _ eq_refl); des; ss.
    esplits; eauto.
    + econs; eauto.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      admit "easy".
    + eapply Loc_cons_right_disjoint; eauto.
      admit "easy".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
  - admit "ditto".
Qed.

Lemma loc_arguments_norepet
      sg
  :
    Loc.norepet (regs_of_rpairs (loc_arguments sg))
.
Proof.
  unfold loc_arguments. des_ifs.
  generalize (loc_arguments_norepet_aux (sig_args sg) 0 0 0). i. specialize (H _ eq_refl). des.
  ss.
Qed.

Lemma Val_hiword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.hiword (Val.longofwords vhi vlo)) = vhi>>
.
Proof.
  u.
  unfold Val.longofwords, Val.hiword. des_ifs; ss; eauto.
  rewrite Int64.hi_ofwords. ss.
Qed.

Lemma Val_loword_spec
      vhi vlo
      (DEFINED: (Val.longofwords vhi vlo) <> Vundef)
  :
    <<EQ: (Val.loword (Val.longofwords vhi vlo)) = vlo>>
.
Proof.
  u.
  unfold Val.longofwords, Val.loword. des_ifs; ss; eauto.
  rewrite Int64.lo_ofwords. ss.
Qed.

Ltac _locmap_tac :=
  try (first[rewrite Locmap.gss; ss; check_safe|rewrite Locmap.gso; ss]);
  try match goal with
      | [H: Loc.notin _ (_ :: _) |- _] => inv H
      | [H: Loc.norepet (_ :: _) |- _] => inv H
      | [ |- Loc.diff _ _] => by (eapply Loc.in_notin_diff; eauto)
      | [H: Loc.diff ?A ?B |- Loc.diff ?B ?A] => apply Loc.diff_sym; assumption
      | [H: R ?x <> R ?y |- _] =>
        tryif exists_prop (x <> y)
        then idtac
        else assert(x <> y) by (ii; clarify; ss)
      end;
  des_safe;
  idtac
.
Local Opaque Loc.diff.
Ltac locmap_tac := repeat _locmap_tac.

Lemma fill_arguments_spec_slot
      (rs: regset) m sg vs ls
      sp
      (RSP: (rs RSP) = Vptr sp Ptrofs.zero true)
      (EXT: extcall_arguments rs m sg vs)
      (FILL: fill_arguments (Locmap.init Vundef) vs (loc_arguments sg) = Some ls)
      (SZBOUND: size_arguments sg <= Ptrofs.max_unsigned / 4)
  :
    (<<SLOT: forall
        ofs ty
      ,
        (<<INSIDE: forall (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
          (<<LOAD: Mem.load (chunk_of_type ty) m sp (4 * ofs) = Some (ls (S Outgoing ofs ty))>>)
            \/ (<<UNDEF: ls (S Outgoing ofs ty) = Vundef>>)>>)
        /\
        (<<OUTSIDE: forall (OUT: (* Loc.notin *) ~ In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg))),
            (<<UNDEF: (ls (S Outgoing ofs ty)) = Vundef>>)>>)>>)
.
Proof.
  unfold extcall_arguments in *.
  assert(BDD: forall ofs ty,
        In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
        0 <= ofs /\ (typealign ty | ofs) /\
        ofs + typesize ty <= Ptrofs.max_unsigned/4).
  { i.
    generalize (loc_arguments_acceptable_2 sg (S Outgoing ofs ty)); eauto. intro ACCP. special ACCP; ss. des.
    esplits; ss; try xomega.
    etransitivity; eauto.
    generalize (loc_arguments_bounded sg); eauto.
  }
  assert(NOREPT: Loc.norepet (regs_of_rpairs (loc_arguments sg))).
  { apply loc_arguments_norepet. }
  abstr (loc_arguments sg) locs. clears sg. clear sg.
  ginduction locs; ii; ss.
  { split; ii; ss. destruct vs; ss. clarify. }
  split; ii; ss.
  {
    assert(OFS: 0 <= 4 * ofs <= Ptrofs.max_unsigned).
    { specialize (BDD ofs ty).
      special BDD.
      { ss. }
      des_safe.
      generalize (typesize_pos ty). i.
      split; try xomega.
      assert((4 * (Ptrofs.max_unsigned/4)) <= Ptrofs.max_unsigned).
      { eapply Z_mult_div_ge. xomega. }
      etransitivity; eauto.
      eapply Z.mul_le_mono_pos_l with (p:=4) (n:=ofs); try xomega.
    }
    apply in_app_or in IN.
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { ii. eapply BDD. apply in_app_iff. right. ss. }
    { admit "easy". }
    i; des_safe. specialize (H ofs ty). des_safe.
    des; cycle 1.
    - special INSIDE; ss.
      des; ss; cycle 1.
      + right.
        des_ifs; ss; locmap_tac.
      + left.
        des_ifs; ss; locmap_tac.
    - inv H1; ss.
      + des; ss; clarify; locmap_tac.
        inv H. left.
        unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
        rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
        rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
      + destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
        * rewrite e in *. right.
          des; ss; clarify; locmap_tac.
          admit "easy".
          admit "easy".
        * rewrite Val_hiword_spec in *; ss.
          rewrite Val_loword_spec in *; ss.
          clarify.
          des; ss; clarify; locmap_tac.
          { left.
            inv H. ss.
            unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
            rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
            rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
          }
          { left.
            inv H0. ss.
            unfold Mem.loadv, Val.offset_ptr in *. des_ifs.
            rewrite Ptrofs.add_zero_l in *. rewrite Z.add_0_l in *. rewrite Ptrofs.unsigned_repr in *; ss.
            rewrite Val.load_result_same; ss. rewrite <- chunk_type_chunk. eapply Mem.load_type; eauto.
          }
  }
  {
    destruct vs; ss. inv EXT.
    des_ifs_safe; ss.
    hexploit IHlocs; eauto.
    { ii. eapply BDD. apply in_app_iff. right. ss. }
    { admit "easy". }
    i; des. specialize (H ofs ty). des.
    des_ifs; ss.
    - rename r into rrr.
      apply not_or_and in OUT. des.
      destruct (classic (Loc.diff rrr (S Outgoing ofs ty))).
      + locmap_tac. erewrite OUTSIDE; eauto.
      + unfold Locmap.set. des_ifs.
    - apply not_or_and in OUT. des.
      apply not_or_and in OUT0. des.
      destruct (classic (Loc.diff rlo (S Outgoing ofs ty))).
      {
        destruct (classic (Loc.diff rhi (S Outgoing ofs ty))).
        { locmap_tac. erewrite OUTSIDE; eauto. }
        unfold Locmap.set. des_ifs.
      }
      unfold Locmap.set. des_ifs.
  }
Qed.

Lemma fill_arguments_spec_reg
      (rs: regset) m sg vs ls
      sp
      (RSP: (rs RSP) = Vptr sp Ptrofs.zero true)
      (EXT: extcall_arguments rs m sg vs)
      (FILL: fill_arguments (Locmap.init Vundef) vs (loc_arguments sg) = Some ls)
  :
    (<<REG: forall
        r
      ,
        (<<INSIDE: forall (IN: In (R r) (regs_of_rpairs (loc_arguments sg))),
            <<EQ: ls (R r) = rs (preg_of r)>> \/ <<UNDEF: ls (R r) = Vundef>>>>)
        /\
        (<<OUTSIDE: forall (OUT: ~ In (R r) (regs_of_rpairs (loc_arguments sg))),
            <<UNDEF: ls (R r) = Vundef>>>>)>>)
.
Proof.
  unfold extcall_arguments in *.
  assert(NOREPT: Loc.norepet (regs_of_rpairs (loc_arguments sg))).
  { apply loc_arguments_norepet. }
  abstr (loc_arguments sg) locs. clears sg. clear sg.
  ginduction locs; ii; ss.
  { split; ii; ss. destruct vs; ss. clarify. }
  split; ii; ss.
  {
    apply in_app_or in IN.
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { admit "easy". }
    i; des_safe. specialize (H r). des_safe.
    inv H1; ss; clarify.
    - inv H; des; ss; clarify.
      + locmap_tac; eauto.
      + destruct (mreg_eq r0 r); ss; clarify; locmap_tac; eauto.
      + locmap_tac; eauto.
    - destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
      + rewrite e in *. ss.
        des; ss; clarify; inv H; ss; locmap_tac; eauto.
      + rewrite Val_loword_spec in *; ss.
        rewrite Val_hiword_spec in *; ss.
        des; ss; clarify; inv H; inv H0; ss; locmap_tac; eauto.
  }
  {
    inv EXT. ss. des_ifs_safe.
    rename l into ls0.
    hexploit IHlocs; eauto.
    { admit "easy". }
    i; des_safe. specialize (H r). des_safe.
    inv H1; ss; clarify.
    - apply not_or_and in OUT. des.
      inv H; des; ss; clarify; locmap_tac; eauto.
    - apply not_or_and in OUT. des.
      apply not_or_and in OUT0. des.
      destruct (classic ((Val.longofwords vhi vlo) = Vundef)) eqn:T; clear T.
      + rewrite e in *. ss.
        rewrite <- OUTSIDE; ss.
        des; ss; clarify; inv H; ss; locmap_tac; eauto.
        * destruct lo; locmap_tac.
        * destruct lo; locmap_tac.
      + rewrite Val_loword_spec in *; ss.
        rewrite Val_hiword_spec in *; ss.
        rewrite <- OUTSIDE; ss.
        des; ss; clarify; inv H; inv H0; ss; try (by locmap_tac; eauto).
        destruct (classic (r0 = r)); ss; clarify; locmap_tac.
  }
Qed.

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

  Inductive fill_slots_old (ls0: locset) (locs: list (rpair loc)) (rs: regset) (m: mem) (ls1: locset): Prop :=
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

  (* Definition fill_slots_old (ls0: locset) (locs: list (rpair loc)) (rs: regset) (m: mem): locset := *)
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
      fptr_arg fd sg_init
      (FPTR: fptr_arg = rs_arg PC)
      (FINDFUNC: Genv.find_funct ge fptr_arg = Some (Internal fd))
      (SIG: sg_init = fd.(fn_sig))

      vs_init m_init
      (LOADARG: load_arguments rs_arg m_arg sg_init vs_init m_init)

      (* (LOCSET: fill_slots rs_arg.(to_locset) (loc_arguments sg_init) rs_arg m_arg ls_init) *)
      ls_init
      (LOCSET: fill_arguments (Locmap.init Vundef) vs_init (loc_arguments sg_init) = Some ls_init)

      (* sp delta *)
      (* (RSPPTR: rs_arg RSP = Vptr sp (Ptrofs.repr delta) true) *)
      (* (ARGSPERM: Mem.range_perm m_arg sp delta (size_arguments fd.(fn_sig)) Cur Writable) *)

      sp
      (RSPPTR: rs_arg RSP = Vptr sp Ptrofs.zero true)
      (* (ARGSPERM: Mem.range_perm m_arg sp 0 (size_arguments fd.(fn_sig)) Cur Writable) *)
      (* (RSPSTK: m_arg.(is_stack_block) sp) *)
    :
      initial_frame rs_arg m_arg
                    (Callstate [(dummy_stack sg_init ls_init)] fptr_arg sg_init ls_init m_init)
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

  (* Lemma fill_slots_old_dtm *)
  (*       ls0 locs rs m ls1 ls2 *)
  (*       (FILL0: fill_slots_old ls0 locs rs m ls1) *)
  (*       (FILL1: fill_slots_old ls0 locs rs m ls2) *)
  (*   : *)
  (*     ls1 = ls2 *)
  (* . *)
  (* Proof. *)
  (*   inv FILL0. inv FILL1. *)
  (*   eapply Axioms.functional_extensionality. *)
  (*   i. destruct x; ss. *)
  (*   - erewrite <- REGS. erewrite <- REGS0. ss. *)
  (*   - destruct (classic (In (S sl pos ty) (regs_of_rpairs locs))). *)
  (*     + exploit SLOTIN; eauto. i; des. *)
  (*       exploit SLOTIN0; eauto. i; des. *)
  (*       clarify. *)
  (*       inv H0; inv H2; ss. des_ifs. *)
  (*       (* TODO: Move determinacy lemma for extcall_arg into Asmregs, and use it *) *)
  (*     + exploit SLOTNOTIN; eauto. i; des. *)
  (*       exploit SLOTNOTIN0; eauto. i; des. *)
  (*       congruence. *)
  (* Qed. *)

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
  Next Obligation.
    inv INIT0; inv INIT1; ss. clarify.
    inv LOADARG. inv LOADARG0.
    determ_tac extcall_arguments_determ.
    rewrite RSPPTR in *. clarify.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation.
    hnf. inv H4; inv H2; subst_locals; all_rewrite; ss; des_ifs.
  Qed.
  Next Obligation. all_prop_inv; ss. Qed.
  Next Obligation. all_prop_inv; ss. Qed.

End MODSEM.



