Require Import CoqlibC Maps.
Require Import ValuesC.
Require Import MemoryC Integers AST.
Require Import LocationsC Stacklayout Conventions.
(** newly added **)
Require Import AsmregsC.
Require Mach.

Set Implicit Arguments.


(* Notation rtc := (Relation_Operators.clos_refl_trans_1n _). (* reflexive transitive closure *) *)
(* Definition stores: mem -> mem -> Prop := *)
(*   rtc (fun m0 m1 => exists chunk ptr val, Mem.storev chunk m0 ptr val = Some m1). *)

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

  Inductive A2B (vs: list val) (ls: locset): Prop :=
  | A2B_intro
      (ARGS: vs = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)))
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
  .

  Inductive B2C (m0: mem) (ls: locset) (m1: mem) (mrs: Mach.regset) (rsp: val): Prop :=
  | B2C_intro
      (REGS: forall
          mr
        ,
          ls (R mr) = mrs mr)
      m_alloc blk
      (ALLOC: Mem.alloc m0 fe_ofs_arg (4 * (size_arguments sg)) = (m_alloc, blk))
      (NB: m_alloc.(Mem.nextblock) = m1.(Mem.nextblock))
      (PERM: all4 (Mem.perm m_alloc <4> Mem.perm m1))
      (SLOTS: forall
          l0
          (IN: In l0 (regs_of_rpairs (loc_arguments sg)))
        ,
          match l0 with
          | S Outgoing ofs ty =>
            Mach.load_stack m1 rsp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some (ls l0)
          | _ => True
          end)
      (UNCH: Mem.unchanged_on top2 m0 m1)
      (RSPPTR: rsp = (Vptr blk Ptrofs.zero true))
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

  Compute (to_mreg RSP).
  Compute (to_mreg PC).
  Compute (to_mreg RA).

  Inductive C2D (mrs: Mach.regset) (fptr: val) (rsp: val) (prs: Asmregs.regset): Prop :=
  | C2D_intro
      ra
      (REGSET: prs = fun pr =>
                       match to_mreg pr with
                       | Some mr => mrs mr
                       | None =>
                         match pr with
                         | RSP => rsp
                         | PC => fptr
                         | RA => ra
                         | _ => Vundef
                         end
                       end)
      (RAPTR: is_ptr ra)
  .

  Inductive D2A (prs_arg: regset) (m_arg: mem)
            (fptr_init: val) (vs_init: list val) (m_init: mem): Prop :=
  | D2A_intro
      sp
      (RSPPTR: prs_arg RSP = Vptr sp Ptrofs.zero true)
      (FPTR: prs_arg PC = fptr_init)
      (PERM: Mem.range_perm m_arg sp 0 (4 * (size_arguments sg)) Cur Writable)
      (VAL: extcall_arguments prs_arg m_arg sg vs_init)
      (DROP: Mem_drop_perm_none m_arg sp 0 (4 * (size_arguments sg)) = m_init)
      (RAPTR: is_ptr (prs_arg RA))
      (BOUND: DUMMY_PROP) (* 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
  .

  Inductive A2D (fptr_arg: val) (vs_arg: list val) (m_arg_pre: mem)
             (prs_arg: Asmregs.regset) (m_arg: mem): Prop :=
  | A2D_intro
      ls
      (AB: A2B vs_arg ls)
      mrs rsp_arg
      (BC: B2C m_arg_pre ls m_arg mrs rsp_arg)
      (CD: C2D mrs fptr_arg rsp_arg prs_arg)
  .

  Lemma A2D_progress
        fptr vs m0
        (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
    :
      exists prs m1, <<AD: A2D fptr vs m0 prs m1>>
  .
  Proof.
    admit "This is needed for user to reason about their program. (or to prove refinement of C-phys >= C-logic)
This is a complex job, and Compcert avoided it by translation validation.
We might need to revert some old code.
NOTE: Old version of Compcert should have related code.
> 6224148 - (HEAD -> master) Reorganization test directory (2010-02-17 13:44:32 +0000) <xleroy>
I checked this commit, there is a pass called Reload which deals this problem.".
  Qed.

  Lemma A2D2A
        fptr vs m0 prs m1
        (AD: A2D fptr vs m0 prs m1)
    :
      exists m2, <<DA :D2A prs m1 fptr vs m2>> /\ <<MEM: mem_equiv m0 m2>>
  .
  Proof.
    inv AD.
    inv AB; inv BC; inv CD. ss.
    esplits; eauto.
    - econs; cbn; eauto.
      + ii. eapply PERM. eapply Mem.perm_implies; eauto with mem.
      + hnf.
        generalize (loc_arguments_acceptable_2 sg). intro ACCPS.
        generalize (loc_arguments_one sg). intro ONES.
        abstr (loc_arguments sg) locs.
        clears sg; clear sg.
        clear - ACCPS ONES SLOTS REGS.
        ginduction locs; ii; ss.
        * econs; eauto.
        * econs; eauto; cycle 1.
          { eapply IHlocs; eauto.
            - ii. eapply SLOTS; eauto. apply in_app_iff. eauto.
            - ii. eapply ACCPS. eauto. apply in_app_iff. eauto. }
          exploit ONES; eauto. i; des.
          destruct a; ss.
          destruct r; ss; econs; eauto.
          -- erewrite REGS. rpapply extcall_arg_reg. u. rewrite to_preg_to_mreg. ss.
          -- exploit ACCPS; eauto. intro ACCP. ss. des_ifs.
             econs; eauto. exploit SLOTS; eauto.
    - hexploit (Mem_drop_perm_none_spec m1 m0.(Mem.nextblock) 0 (4 * size_arguments sg)); eauto. i; des.
      exploit Mem.alloc_result; eauto. i; des. clarify.
      econs; eauto.
      + eapply Mem_unchanged_on_trans_strong; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        ii; des.
        left. ii. unfold Mem.valid_block in *. subst. xomega.
      + i. rewrite <- NB0 in *. rewrite <- NB in *.
        assert(b = Mem.nextblock m0).
        { admit "ez". }
        clarify.
        eapply drop_perm_none_dead_block; eauto. ii; ss.
        rewrite <- PERM in PERM0.
        eapply Mem.perm_alloc_3; eauto.
  Unshelve.
    all: ss.
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


