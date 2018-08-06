Require Import CoqlibC Maps.
Require Import ValuesC.
Require Import MemoryC Integers AST.
Require Import LocationsC Stacklayout Conventions.
(** newly added **)
Require Import AsmregsC.
Require Import Asm.
Require Mach.
(* Require Lineartyping. *)

Set Implicit Arguments.

Local Open Scope asm.


Inductive wt_locset (sg: signature) (ls: locset): Prop :=
| wt_locset_intro
    (SLOT: forall
        ofs ty
        (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)))
      ,
        Val.has_type (ls (S Outgoing ofs ty)) ty)
.

Theorem Val_load_result_undef
        v ty
        (UNTYPED: ~Val.has_type v ty)
  :
    <<UNDEF: Val.load_result (chunk_of_type ty) v = Vundef>>
.
Proof. i. destruct v, ty; ss. Qed.

(* TODO: Move to proper place *)
Lemma typealign
      ty
  :
    align_chunk (chunk_of_type ty) = 4 * typealign ty
.
Proof.
  destruct ty; ss.
Qed.

Local Opaque Z.mul Z.add Z.div Z.sub.
Local Opaque list_nth_z.

(* A: RTL: list val *)
(* B: Linear/LTL: Mach.regset + slot (locset) *)
(* C: Mach: Mach.regset + mem *)
(* D: Asm: Asm.regset + mem *)

Module Call.
Section STYLES.

  Variable sg: signature.
  About Mach.extcall_arguments.
  Print Mach.extcall_arg.
  About extcall_arguments.

  Inductive A2B (vs_arg: list val)
            (ls_arg: locset): Prop :=
  | A2B_intro
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (ARGS: vs_arg = (map (fun p => Locmap.getpair p ls_arg) (loc_arguments sg)))
      (PTRFREE: forall
          r
          (NOTIN: Loc.notin (R r) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr (ls_arg (R r))>>)
  .

  Inductive B2A (ls_arg: locset)
            (vs_arg: list val): Prop :=
  | B2A_intro
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (ARGS: vs_arg = (map (fun p => Locmap.getpair p ls_arg) (loc_arguments sg)))
  .

  (* Q: Why * 4? See Stackig.v "Definition offset_arg (x: Z) := fe_ofs_arg + 4 * x." *)
  Definition B2C_mem (m0: mem) (rsp: val) (ls: locset) (locs: list loc): option mem :=
    fold_right (fun i s => do m1 <- s ;
                            match i with
                            | S Outgoing ofs ty => Mach.store_stack m1 rsp ty (4 * ofs).(Ptrofs.repr) (ls i)
                            | _ => Some m1
                            end)
               (Some m0) locs
  .

  Lemma B2C_mem_spec
        m0 rsp ls
        (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
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
                 (forall (TYPE: Val.has_type (ls l0) ty),
                   Mach.load_stack m1 (Vptr rsp Ptrofs.zero true) ty
                                   (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some (ls l0))
                 /\
                 (forall (NOTYPE: ~ Val.has_type (ls l0) ty),
                    Mach.load_stack m1 (Vptr rsp Ptrofs.zero true) ty
                                   (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some Vundef)
               | _ => True
               end>>)
  .
  Proof.
    generalize (loc_arguments_bounded sg); eauto. intro SZ.
    generalize (loc_arguments_acceptable_2 sg); eauto. intro ACCP.
    generalize (loc_arguments_norepet sg). intro DISJ.
    abstr (size_arguments sg) sz.
    abstr (regs_of_rpairs (loc_arguments sg)) locs.
    ginduction locs; ii; ss.
    - u. esplits; eauto.
      + eapply Mem.unchanged_on_refl.
      + ii; ss.
    - inv DISJ; ss. exploit IHlocs; eauto. i; des.
      rewrite BCM. cbn.
      exploit ACCP; eauto. i.
      destruct a; ss.
      + esplits; eauto.
        ii. des; clarify. exploit STORED; eauto.
      + des_ifs. des; ss.
        hexploit SZ; eauto. i.
        rewrite ! Ptrofs.add_zero_l.
        generalize (typesize_pos ty); intro TY.
        rewrite Ptrofs.unsigned_repr; [|xomega].
        edestruct Mem.valid_access_store with (m1 := m1) (ofs := 4 * pos) (chunk := chunk_of_type ty)
          as [m2 STORE].
        { split; ss.
          - eapply Mem.range_perm_implies with (p1 := Freeable); [|eauto with mem].
            rewrite <- PLAYGROUND.typesize_chunk.
            ii. erewrite <- PERM0. eapply PERM; eauto. unfold fe_ofs_arg. xomega.
          - rewrite typealign. eapply Z.mul_divide_mono_l; eauto.
        }
        esplits; try apply STORE; eauto.
        * exploit Mem.nextblock_store; eauto. i. congruence.
        * etransitivity; eauto. eauto with mem.
        * eapply Mem.unchanged_on_trans; eauto. eapply Mem.store_unchanged_on; eauto.
        * ii. des; clarify.
          { rewrite Ptrofs.add_zero_l. unfold fe_ofs_arg. rewrite Ptrofs.unsigned_repr; [|xomega].
            rewrite Z.add_0_l. erewrite Mem.load_store_same; eauto.
            split; i; f_equal.
            - eapply Val.load_result_same; ss.
            - eapply Val_load_result_undef; eauto.
          }
          des_ifs; ss.
          exploit STORED; eauto. i. ss. unfold Mach.load_stack in *. ss.
          erewrite Mem.load_store_other; eauto.
          right. rewrite Ptrofs.add_zero_l in *. unfold fe_ofs_arg. rewrite Z.add_0_l.
          rewrite <- ! PLAYGROUND.typesize_chunk.
          exploit Loc.in_notin_diff; eauto. i. ss.
          hexploit SZ. { right. eauto. }  i.
          generalize (typesize_pos ty0); intro TY0.
          exploit ACCP. { right. eauto. } i. ss. des_safe.
          rewrite Ptrofs.unsigned_repr; [|xomega].
          des; ss; try xomega.
  Qed.

  Inductive B2C (ls_arg: locset) (m_arg0: mem)
            (mrs_arg: Mach.regset) (rsp_arg: val) (ra_arg: val) (m_arg1: mem): Prop :=
  | B2C_intro
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (REGS: mrs_arg = fun mr => ls_arg (R mr))
      m_alloc blk
      (ALLOC: Mem.alloc m_arg0 fe_ofs_arg (4 * (size_arguments sg)) = (m_alloc, blk))
      (MEM: B2C_mem m_alloc rsp_arg ls_arg (regs_of_rpairs (loc_arguments sg)) = Some m_arg1)
      (RSPPTR: rsp_arg = (Vptr blk Ptrofs.zero true))
      (RAPTR: is_fake_ptr ra_arg)
  .

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
      (BOUND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (LOCSET: ls_arg = C2B_locset mrs_arg rsp_arg m_arg)
      blk
      (RSPPTR: rsp_arg = (Vptr blk Ptrofs.zero true))
      (* (PERM: Mem.range_perm m_arg blk 0 (4 * (size_arguments sg)) Cur Freeable) *)
      (* (DROP: Mem_drop_perm_none m_arg blk 0 (4 * (size_arguments sg)) = m_init) *)
      (FREE: Mem.free m_arg blk 0 (4 * (size_arguments sg)) = Some m_init)
  .

  Compute (to_mreg RSP).
  Compute (to_mreg PC).
  Compute (to_mreg RA).

  Definition C2D_pregset (mrs_arg: Mach.regset) (ra: val) (fptr_arg: val) (rsp_arg: val): regset :=
    (mrs_arg.(to_pregset)
               # PC <- fptr_arg
               # RA <- ra
               # RSP <- rsp_arg)
  .
  Inductive C2D (mrs_arg: Mach.regset) (fptr_arg: val) (rsp_arg: val) (ra_arg: val)
            (prs_arg: regset): Prop :=
  | C2D_intro
      (REGSET: prs_arg = fun pr =>
                           match to_mreg pr with
                           | Some mr => mrs_arg mr
                           | None =>
                             match pr with
                             | RSP => rsp_arg
                             | PC => fptr_arg
                             | RA => ra_arg
                             | _ => Vundef
                             end
                           end)
  .

  Inductive B2D (fptr_arg: val) (ls_arg: locset) (m_arg_pre: mem)
            (prs_arg: regset) (m_arg: mem): Prop :=
  | B2D_intro
      mrs rsp_arg ra_arg
      (BC: B2C ls_arg m_arg_pre mrs rsp_arg ra_arg m_arg)
      (CD: C2D mrs fptr_arg rsp_arg ra_arg prs_arg)
  .

  Inductive A2D (fptr_arg: val) (vs_arg: list val) (m_arg_pre: mem)
             (prs_arg: regset) (m_arg: mem): Prop :=
  | A2D_intro
      ls
      (AB: A2B vs_arg ls)
      mrs rsp_arg ra_arg
      (BC: B2C ls m_arg_pre mrs rsp_arg ra_arg m_arg)
      (CD: C2D mrs fptr_arg rsp_arg ra_arg prs_arg)
  .

  Inductive D2C (prs_arg: regset)
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
      (DROP: Mem.free m_arg sp 0 (4 * (size_arguments sg)) = Some m_init)
      (RAPTR: is_fake_ptr (prs_arg RA))
      (BOUND: DUMMY_PROP) (* 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
  .

  Inductive D2B_old (prs_arg: regset) (m_arg: mem)
            (fptr_init: val) (ls_init: locset) (m_init: mem): Prop :=
  | D2B_intro_old
      vs_init
      (DA: D2A prs_arg m_arg fptr_init vs_init m_init)
      (AB: A2B vs_init ls_init)
  .

  Inductive D2B (prs_arg: regset) (m_arg: mem)
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

  Lemma A2B_preservation
        vs
        (WTA: Val.has_type_list vs sg.(sig_args))
        (* (WT: Forall2 Val.has_type vs sg.(sig_args)) *)
        ls
        (AB: A2B vs ls)
    :
      <<WTB: wt_locset sg ls>>
  .
  Proof.
    inv AB; ss.
    econs; eauto. clear BOUND PTRFREE.
    destruct sg; ss. unfold loc_arguments in *. ss. des_ifs. clear_tac.
    revert WTA.
    generalize 0 at 1 4 as ir. generalize 0 at 1 3 as fr. generalize 0 at 1 2 as ofs.
    ginduction sig_args; ii; ss.
    destruct a; ss; des_ifs; ss; des; ss; clarify; eapply IHsig_args; eauto.
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
      + reflexivity.
      + instantiate (1:= fake_ptr_one). ss.
    - econs; eauto.
      + reflexivity.
  Qed.

  Lemma A2D2A
        fptr vs m0 prs m1
        (WTA: Val.has_type_list vs sg.(sig_args))
        (AD: A2D fptr vs m0 prs m1)
    :
      exists m2, <<DA: D2A prs m1 fptr vs m2>> /\ <<MEM: mem_equiv m0 m2>>
  .
  Proof.
    inv AD; ss.
    exploit A2B_preservation; eauto. intro WTB; des.
    inv AB; inv BC; inv CD; ss.
    exploit (@B2C_mem_spec m_alloc blk ls); eauto. { eapply Mem_alloc_range_perm; eauto. } i; des. clarify.
    hexploit Mem.range_perm_free; eauto.
    { ii. rewrite <- PERM. eapply Mem.perm_alloc_2; eauto. }
    i; des. inv X.
    esplits; eauto.
    - econs; eauto.
      + econs; eauto.
      + cbn. unfold to_mregset.
        econs; eauto.
      + econs; eauto.
        generalize (loc_arguments_acceptable sg). intro ACCPS.
        generalize (loc_arguments_one sg). intro ONES.
        clear - ACCPS ONES STORED WTB.
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
        exploit STORED; eauto. i; des_safe.
        destruct (Loc.notin_dec (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) eqn:T.
        { exfalso. eapply Loc.notin_not_in; eauto. }
        inv WTB. exploit SLOT; eauto. i. rewrite H1; ss.
    - admit "ez".
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

End Call.



Module Ret.

  (* TODO: Fill this please! *)
  (* NOTE: Important spec: D2A should fill callee-save registers properly. *)
  (* If not, compilation from physical-C into logical-C will be broken. all C program will have UB! *)

End Ret.

