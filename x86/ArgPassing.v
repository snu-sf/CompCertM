Require Import CoqlibC Maps.
Require Import ValuesC.
Require Import MemoryC Integers AST.
Require Import LocationsC Stacklayout Conventions.
(** newly added **)
Require Import AsmregsC.
Require Mach.

Set Implicit Arguments.

Local Open Scope asm.



Local Opaque Z.mul Z.add Z.div Z.sub.
Local Opaque list_nth_z.

(* A: RTL: list val *)
(* B: Linear/LTL: Mach.regset + slot (locset) *)
(* C: Mach: Mach.regset + mem *)
(* D: Asm: Asm.regset + mem *)

Section STYLES.

  Variable sg: signature.
  About Mach.extcall_arguments.
  Print Mach.extcall_arg.
  About extcall_arguments.

  Inductive A2B (vs_arg: list val)
            (ls_arg: locset): Prop :=
  | A2B_intro
      (ARGS: vs_arg = (map (fun p => Locmap.getpair p ls_arg) (loc_arguments sg)))
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (PTRFREE: forall
          r
          (NOTIN: Loc.notin (R r) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr (ls_arg (R r))>>)
  .

  Inductive B2A (ls_arg: locset)
            (vs_arg: list val): Prop :=
  | B2A_intro
      (ARGS: vs_arg = (map (fun p => Locmap.getpair p ls_arg) (loc_arguments sg)))
  .

  (* Q: Why * 4? See Stackig.v "Definition offset_arg (x: Z) := fe_ofs_arg + 4 * x." *)
  Fixpoint B2C_mem (m0: mem) (rsp: val) (ls: locset) (locs: list loc): option mem :=
    match locs with
    | [] =>  Some m0
    | loc :: locs =>
      do m1 <- B2C_mem m0 rsp ls locs ;
        match loc with
        | S Outgoing ofs ty => Mach.store_stack m1 rsp ty (4 * ofs).(Ptrofs.repr) (ls loc)
        | _ => Some m1
        end
    end
  .

  Lemma B2C_mem_spec
        m0 rsp ls
        (PERM: Mem.range_perm m0 rsp fe_ofs_arg (4 * (size_arguments sg)) Cur Freeable)
    :
      exists m1,
        (<<BCM: B2C_mem m0 (Vptr rsp Ptrofs.zero true) ls (regs_of_rpairs (loc_arguments sg)) = Some m1>>)
        /\ (<<NB: m0.(Mem.nextblock) = m1.(Mem.nextblock)>>)
        /\ (<<PERM: all4 (Mem.perm m0 <4> Mem.perm m1)>>)
        /\ (<<UNCH: Mem.unchanged_on (fun blk _ => blk <> rsp) m0 m1>>)
        /\ (<<STORED: forall
               l0
               (IN: In l0 (regs_of_rpairs (loc_arguments sg)))
             ,
               match l0 with
               | S Outgoing ofs ty =>
                 Mach.load_stack m1 (Vptr rsp Ptrofs.zero true) ty
                                 (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some (ls l0)
               | _ => True
               end>>)
  .
  Proof.
    admit "ez".
  Qed.

  Inductive B2C (ls_arg: locset) (m_arg0: mem)
            (mrs_arg: Mach.regset) (rsp_arg: val) (m_arg1: mem): Prop :=
  | B2C_intro
      (REGS: mrs_arg = fun mr => ls_arg (R mr))
      m_alloc blk
      (ALLOC: Mem.alloc m_arg0 fe_ofs_arg (4 * (size_arguments sg)) = (m_alloc, blk))
      (MEM: B2C_mem m_alloc rsp_arg ls_arg (regs_of_rpairs (loc_arguments sg)) = Some m_arg1)
      (RSPPTR: rsp_arg = (Vptr blk Ptrofs.zero true))
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
  .
  (* Inductive B2C (m0: mem) (ls: locset) (m1: mem) (mrs: Mach.regset) (rsp: val): Prop := *)
  (* | B2C_intro *)
  (*     (REGS: forall *)
  (*         mr *)
  (*       , *)
  (*         ls (R mr) = mrs mr) *)
  (*     (NB: Pos.succ m0.(Mem.nextblock) = m1.(Mem.nextblock)) *)
  (*     (RSPPTR: rsp = (Vptr m0.(Mem.nextblock) Ptrofs.zero true)) *)
  (*     (PERM: Mem.range_perm m1 m0.(Mem.nextblock) 0 (4 * (size_arguments sg)) Cur Freeable) *)
  (*     (SLOTS: forall *)
  (*         l0 *)
  (*         (IN: In l0 (regs_of_rpairs (loc_arguments sg))) *)
  (*       , *)
  (*         match l0 with *)
  (*         | S Outgoing ofs ty => *)
  (*           Mach.load_stack m1 rsp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some (ls l0) *)
  (*         | _ => True *)
  (*         end) *)
  (*     (UNCH: Mem.unchanged_on top2 m0 m1) *)
  (*     (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
  (* . *)

  Definition C2B_locset (mrs_arg: Mach.regset) (rsp_arg: val) (m_arg: mem): locset :=
    fun l0 =>
      match l0 with
      | R mr => mrs_arg mr
      | S sl ofs ty =>
        if Loc.notin_dec l0 (regs_of_rpairs (loc_arguments sg))
        then Vundef
        else
          match Mach.load_stack m_arg rsp_arg ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) with
          | Some v => v
          | None => Vundef
          end
      end
  .

  Inductive C2B (mrs_arg: Mach.regset) (rsp_arg: val) (m_arg: mem)
            (ls_arg: locset) (m_init: mem): Prop :=
  | C2B_intro
      (LOCSET: ls_arg = C2B_locset mrs_arg rsp_arg m_arg)
      blk
      (RSPPTR: rsp_arg = (Vptr blk Ptrofs.zero true))
      (PERM: Mem.range_perm m_arg blk 0 (4 * (size_arguments sg)) Cur Writable)
      (DROP: Mem_drop_perm_none m_arg blk 0 (4 * (size_arguments sg)) = m_init)
  .

  Compute (to_mreg RSP).
  Compute (to_mreg PC).
  Compute (to_mreg RA).

  Definition C2D_pregset (mrs_arg: Mach.regset) (ra: val) (fptr_arg: val) (rsp_arg: val): Asmregs.regset :=
    (mrs_arg.(to_pregset)
               # PC <- fptr_arg
               # RA <- ra
               # RSP <- rsp_arg)
  .
  Inductive C2D (mrs_arg: Mach.regset) (fptr_arg: val) (rsp_arg: val)
            (prs_arg: Asmregs.regset): Prop :=
  | C2D_intro
      ra
      (REGSET: prs_arg = fun pr =>
                           match to_mreg pr with
                           | Some mr => mrs_arg mr
                           | None =>
                             match pr with
                             | RSP => rsp_arg
                             | PC => fptr_arg
                             | RA => ra
                             | _ => Vundef
                             end
                           end)
      (RAPTR: is_fake_ptr ra)
  .

  Inductive B2D (fptr_arg: val) (ls_arg: locset) (m_arg_pre: mem)
            (prs_arg: Asmregs.regset) (m_arg: mem): Prop :=
  | B2D_intro
      mrs rsp_arg
      (BC: B2C ls_arg m_arg_pre mrs rsp_arg m_arg)
      (CD: C2D mrs fptr_arg rsp_arg prs_arg)
  .

  Inductive A2D (fptr_arg: val) (vs_arg: list val) (m_arg_pre: mem)
             (prs_arg: Asmregs.regset) (m_arg: mem): Prop :=
  | A2D_intro
      ls
      (AB: A2B vs_arg ls)
      mrs rsp_arg
      (BC: B2C ls m_arg_pre mrs rsp_arg m_arg)
      (CD: C2D mrs fptr_arg rsp_arg prs_arg)
  .

  Inductive D2C (prs_arg: Asmregs.regset)
            (mrs: Mach.regset) (fptr: val) (rsp: val): Prop :=
  | D2C_intro
      (FPTR: prs_arg PC = fptr)
      (RSPPTR: prs_arg RSP = rsp)
      (REGSET: mrs = prs_arg.(to_mregset))
      (RAPTR: is_fake_ptr (prs_arg RA))
  .

  Inductive D2A (prs_arg: regset) (m_arg: mem)
            (fptr_init: val) (vs_init: list val) (m_init: mem): Prop :=
  | D2A_intro
      rsp mrs_arg ls_arg
      (DC: D2C prs_arg mrs_arg fptr_init rsp)
      (CB: C2B mrs_arg rsp m_arg ls_arg m_init)
      (BA: B2A ls_arg vs_init)
  .

  Inductive D2A_old (prs_arg: regset) (m_arg: mem)
            (fptr_init: val) (vs_init: list val) (m_init: mem): Prop :=
  | D2A_old_intro
      sp
      (RSPPTR: prs_arg RSP = Vptr sp Ptrofs.zero true)
      (FPTR: prs_arg PC = fptr_init)
      (PERM: Mem.range_perm m_arg sp 0 (4 * (size_arguments sg)) Cur Writable)
      (VAL: extcall_arguments prs_arg m_arg sg vs_init)
      (DROP: Mem_drop_perm_none m_arg sp 0 (4 * (size_arguments sg)) = m_init)
      (RAPTR: is_fake_ptr (prs_arg RA))
      (BOUND: DUMMY_PROP) (* 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
  .

  Inductive D2B_old (prs_arg: Asmregs.regset) (m_arg: mem)
            (fptr_init: val) (ls_init: locset) (m_init: mem): Prop :=
  | D2B_intro_old
      vs_init
      (DA: D2A prs_arg m_arg fptr_init vs_init m_init)
      (AB: A2B vs_init ls_init)
  .

  Inductive D2B (prs_arg: Asmregs.regset) (m_arg: mem)
            (fptr_init: val) (ls_init: locset) (m_init: mem): Prop :=
  | D2B_intro
      rsp mrs
      (DC: D2C prs_arg mrs fptr_init rsp)
      (CB: C2B mrs rsp m_arg ls_init m_init)
  .

  Lemma A2B_progress
        vs
    :
      exists ls, <<AB: A2B vs ls>>
  .
  Proof.
    admit "This is needed for user to reason about their program.
(or to prove refinement of C-phys >= C-logic)
This is a complex job, and Compcert avoided it by translation validation.
We might need to revert some old code.
NOTE: Old version of Compcert should have related code.
> 6224148 - (HEAD -> master) Reorganization test directory (2010-02-17 13:44:32 +0000) <xleroy>
I checked this commit, there is a pass called Reload which deals this problem.
--------------------------------------------
just define something like 'fill_arguments' in locationsC
".
  Qed.

  Lemma A2D_progress
        fptr vs m0
        (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
    :
      exists prs m1, <<AD: A2D fptr vs m0 prs m1>>
  .
  Proof.
    destruct (Mem.alloc m0 fe_ofs_arg (4 * size_arguments sg)) eqn:ALLOC.
    rename m into m1. rename b into rsp.
    hexploit (A2B_progress vs); eauto. i; des.
    exploit (@B2C_mem_spec m1 rsp ls); eauto. { eapply Mem_alloc_range_perm; eauto. } i; des.
    esplits; eauto.
    econs; eauto.
    - econs; eauto.
      reflexivity.
    - econs; eauto.
      + reflexivity.
      + instantiate (1:= fake_ptr_one). ss.
  Qed.

  (* Lemma A2D2A_old *)
  (*       fptr vs m0 prs m1 *)
  (*       (AD: A2D fptr vs m0 prs m1) *)
  (*   : *)
  (*     exists m2, <<DA :D2A_old prs m1 fptr vs m2>> /\ <<MEM: mem_equiv m0 m2>> *)
  (* . *)
  (* Proof. *)
  (*   inv AD. *)
  (*   inv AB; inv BC; inv CD. ss. *)
  (*   esplits; eauto. *)
  (*   - econs; cbn; eauto. *)
  (*     + ii. eapply PERM. eapply Mem.perm_implies; eauto with mem. *)
  (*     + hnf. *)
  (*       generalize (loc_arguments_acceptable_2 sg). intro ACCPS. *)
  (*       generalize (loc_arguments_one sg). intro ONES. *)
  (*       abstr (loc_arguments sg) locs. *)
  (*       clears sg; clear sg. *)
  (*       clear - ACCPS ONES MEM. *)
  (*       ginduction locs; ii; ss. *)
  (*       * econs; eauto. *)
  (*       * exploit ONES; eauto. i; des. destruct a; ss. clear_tac. *)
  (*         exploit ACCPS; eauto. i; des. *)
  (*         u in *. des_ifs_safe. ss. *)
  (*         destruct r; ss; clarify. *)
  (*         { econs; eauto. *)
  (*           - econs; eauto. econs; eauto. *)
  (*         } *)
  (*         econs; eauto; cycle 1. *)
  (*         { eapply IHlocs; eauto. *)
  (*           - ii. eapply SLOTS; eauto. apply in_app_iff. eauto. *)
  (*           - ii. eapply ACCPS. eauto. apply in_app_iff. eauto. } *)
  (*         destruct r; ss; econs; eauto. *)
  (*         -- rpapply extcall_arg_reg. u. rewrite to_preg_to_mreg. ss. *)
  (*         -- exploit ACCPS; eauto. intro ACCP. ss. des_ifs. *)
  (*            econs; eauto. exploit SLOTS; eauto. *)
  (*   - hexploit (Mem_drop_perm_none_spec m1 m0.(Mem.nextblock) 0 (4 * size_arguments sg)); eauto. i; des. *)
  (*     exploit Mem.alloc_result; eauto. i; des. clarify. *)
  (*     econs; eauto. *)
  (*     + eapply Mem_unchanged_on_trans_strong; eauto. *)
  (*       eapply Mem.unchanged_on_implies; eauto. *)
  (*       ii; des. *)
  (*       left. ii. unfold Mem.valid_block in *. subst. xomega. *)
  (*     + i. rewrite <- NB0 in *. rewrite <- NB in *. *)
  (*       assert(b = Mem.nextblock m0). *)
  (*       { admit "ez". } *)
  (*       clarify. *)
  (*       eapply drop_perm_none_dead_block; eauto. ii; ss. *)
  (*       rewrite <- PERM in PERM0. *)
  (*       eapply Mem.perm_alloc_3; eauto. *)
  (* Unshelve. *)
  (*   all: ss. *)
  (* Qed. *)

  Lemma A2D2A
        fptr vs m0 prs m1
        (AD: A2D fptr vs m0 prs m1)
    :
      exists m2, <<DA :D2A prs m1 fptr vs m2>> /\ <<MEM: mem_equiv m0 m2>>
  .
  Proof.
    inv AD; ss. inv AB; inv BC; inv CD; ss.
    exploit (@B2C_mem_spec m_alloc blk ls); eauto. { eapply Mem_alloc_range_perm; eauto. } i; des. clarify.
    esplits; eauto.
    - econs; eauto.
      + econs; eauto.
      + cbn. unfold to_mregset.
        econs; eauto.
        * ii. rewrite <- PERM. eauto with mem.
      + econs; eauto.
        generalize (loc_arguments_acceptable sg). intro ACCPS.
        generalize (loc_arguments_one sg). intro ONES.
        clear - ACCPS ONES STORED.
        Local Opaque Loc.notin_dec.
        eapply map_ext_strong.
        ii; ss.
        exploit ONES; eauto. i; des. destruct x; ss.
        destruct r; ss.
        { rewrite to_preg_to_mreg. reflexivity. }
        exploit ACCPS; eauto. i; des. ss. des_ifs_safe.
        specialize (STORED (S Outgoing pos ty)). ss.
        assert(INN: In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))).
        { admit "ez". }
        exploit STORED; eauto. i; des.
        des_ifs.
        exfalso. eapply Loc.notin_not_in; eauto.
    - admit "ez".
  Qed.

  Lemma mem_future
    :
      True
  .
  Proof.
    admit "
Two possibilities.
1) all these operations can be presented with memory primitives. (alloc/store/etc)
2) put these as primitive, and show that they comply to axioms. (readonly things)
".
  Qed.

End STYLES.



Lemma D2C_dtm
      prs_arg mrs0 fptr0 rsp0 mrs1 fptr1 rsp1
      (DC0: D2C prs_arg mrs0 fptr0 rsp0)
      (DC1: D2C prs_arg mrs1 fptr1 rsp1)
  :
    mrs0 = mrs1 /\ fptr0 = fptr1 /\ rsp0 = rsp1
.
Proof.
  inv DC0; inv DC1; ss; clarify.
Qed.

Lemma C2B_dtm
      sg_arg mrs_arg rsp_arg m_arg ls_arg0 m_init0 ls_arg1 m_init1
      (CB0: C2B sg_arg mrs_arg rsp_arg m_arg ls_arg0 m_init0)
      (CB1: C2B sg_arg mrs_arg rsp_arg m_arg ls_arg1 m_init1)
  :
    ls_arg0 = ls_arg1 /\ m_init0 = m_init1
.
Proof.
  inv CB0; inv CB1; ss; clarify.
Qed.

Lemma B2A_dtm
      sg_arg ls_arg vs_arg0 vs_arg1
      (BA0: B2A sg_arg ls_arg vs_arg0)
      (BA1: B2A sg_arg ls_arg vs_arg1)
  :
    vs_arg0 = vs_arg1
.
Proof.
  inv BA0; inv BA1; ss; clarify.
Qed.

Lemma D2A_dtm0
      rs_arg m_arg sg_init0 sg_init1
      fptr_init0 fptr_init1 vs_init0 vs_init1 m_init0 m_init1
      (DA0: D2A sg_init0 rs_arg m_arg fptr_init0 vs_init0 m_init0)
      (DA1: D2A sg_init1 rs_arg m_arg fptr_init1 vs_init1 m_init1)
  :
    fptr_init0 = fptr_init1
.
Proof.
  inv DA0; inv DA1; ss; clarify.
  determ_tac D2C_dtm.
Qed.

Lemma D2A_dtm1
      rs_arg m_arg sg_init
      fptr_init vs_init0 vs_init1 m_init0 m_init1
      (DA0: D2A sg_init rs_arg m_arg fptr_init vs_init0 m_init0)
      (DA1: D2A sg_init rs_arg m_arg fptr_init vs_init1 m_init1)
  :
    vs_init0 = vs_init1 /\ m_init0 = m_init1
.
Proof.
  inv DA0; inv DA1; ss; clarify.
  determ_tac D2C_dtm.
  determ_tac C2B_dtm.
  determ_tac B2A_dtm.
Qed.

Lemma D2A_old_dtm0
      rs_arg m_arg sg_init0 sg_init1
      fptr_init0 fptr_init1 vs_init0 vs_init1 m_init0 m_init1
      (DA0: D2A_old sg_init0 rs_arg m_arg fptr_init0 vs_init0 m_init0)
      (DA1: D2A_old sg_init1 rs_arg m_arg fptr_init1 vs_init1 m_init1)
  :
    fptr_init0 = fptr_init1
.
Proof.
  inv DA0. inv DA1. clarify.
Qed.

Lemma D2A_old_dtm1
      rs_arg m_arg sg_init
      fptr_init vs_init0 vs_init1 m_init0 m_init1
      (DA0: D2A_old sg_init rs_arg m_arg fptr_init vs_init0 m_init0)
      (DA1: D2A_old sg_init rs_arg m_arg fptr_init vs_init1 m_init1)
  :
    vs_init0 = vs_init1 /\ m_init0 = m_init1
.
Proof.
  inv DA0. inv DA1.
  rewrite RSPPTR in *. clarify.
  determ_tac extcall_arguments_determ.
Qed.

Lemma D2B_dtm0
      rs_arg m_arg sg_init0 sg_init1
      fptr_init0 fptr_init1 ls_init0 ls_init1 m_init0 m_init1
      (DB0: D2B sg_init0 rs_arg m_arg fptr_init0 ls_init0 m_init0)
      (DB1: D2B sg_init1 rs_arg m_arg fptr_init1 ls_init1 m_init1)
  :
    fptr_init0 = fptr_init1
.
Proof.
  inv DB0; inv DB1; ss; clarify.
  determ_tac D2C_dtm.
Qed.

Lemma D2B_dtm1
      rs_arg m_arg sg_init
      fptr_init ls_init0 ls_init1 m_init0 m_init1
      (DB0: D2B sg_init rs_arg m_arg fptr_init ls_init0 m_init0)
      (DB1: D2B sg_init rs_arg m_arg fptr_init ls_init1 m_init1)
  :
    ls_init0 = ls_init1 /\ m_init0 = m_init1
.
Proof.
  inv DB0; inv DB1; ss; clarify.
  determ_tac D2C_dtm.
  determ_tac C2B_dtm.
Qed.

