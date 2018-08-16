Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.

Set Implicit Arguments.

Local Opaque Z.mul.

Section PRESERVATION.

  Existing Instance Val.mi_final.

(** PLAN A*)

(*
c0 * c1 * ... * cn
>=
c0 + c1 + ... + cn
*)
  
(** ********************* linking *********************************)
  

(** ********************* genv *********************************)
  
  Variable sk_src : Sk.t.
  Hypothesis LINK_SK_src : link_sk prog = Some sk_src.
  (* TODO: consider linking fail case *)
  Let skenv_link := Sk.load_skenv sk.

  Let ge := load_genv prog skenv_link.
  Let tge := globalenv tprog.

  Definition local_genv (p : Csyntax.program) :=
    (skenv_link.(SkEnv.project) p.(defs)).(revive) p.

  Inductive genv_le (j: meminj) (src_ge tgt_ge: Genv.t fundef unit): Prop :=
  | genv_le_intro 
      (SYMB: forall id b (FIND: Genv.find_symbol src_ge id = Some b),
          Genv.find_symbol tgt_ge id = Some b
          /\ j b = Some (b, 0)) (* is it needed? *)
      (DEFS: forall b0 d (FIND: Genv.find_def src_ge b0 = Some d),
          exists b1, j b0 = Some (b1, 0)
                     /\ Genv.find_def tgt_ge b1 = Some d).

  Lemma genv_le_incr j0 j1 src_ge tgt_ge
        (INCR: inject_incr j0 j1)
        (GENVLE: genv_le j0 src_ge tgt_ge)
    :      
       genv_le j1 src_ge tgt_ge.
  Proof.
    inv GENVLE. econs; ii; ss.
    - specialize (SYMB _ _ FIND). des. eauto.
    - specialize (DEFS _ _ FIND). des. esplits; eauto.
  Qed.
  
(** ********************* initial memory *********************************)
  
  Variable m_init : mem.
  Hypothesis INIT_MEM: sk.(Sk.load_mem) = Some m_init.
  (* TODO: m_init exist *)

  Definition m_tgt_init := m_init.
  (* Variable m_tgt_init : mem. *)
  (* Hypothesis INIT_TGT_MEM: Genv.init_mem tprog = Some m_tgt_init. *)
  Lemma TGT_INIT_MEM: Genv.init_mem tprog = Some m_tgt_init.
  Proof.
    unfold Sk.load_mem in *.
    eapply Genv.init_mem_match
      with (ctx := tt) (match_fundef := top3) (match_varinfo := top2);
      [| eapply INIT_MEM]. econs.
    - admit "list_forall2 (match_ident_globdef top3 top2 ()) (prog_defs sk) (prog_defs tprog)".
    - admit "prog_main tprog = prog_main sk /\ prog_public tprog = prog_public sk".
  Qed.

  Definition init_inject := Mem.flat_inj (Mem.nextblock m_init).

  Lemma initmem_inject: Mem.inject init_inject m_init m_tgt_init.
  Proof.
    eapply Genv.initmem_inject. unfold Sk.load_mem in INIT_MEM. eauto.
  Qed.

  Lemma init_inject_genv_le p: genv_le init_inject (local_genv p) tge.
  Admitted.

  Lemma local_genv_le j p
        (INCR: inject_incr init_inject j)
    : genv_le j (local_genv p) tge.
  Proof.
    eapply genv_le_incr; eauto. apply init_inject_genv_le.
  Qed.  

  Lemma ALLOC_NEXT_INCR F V (gen: Genv.t F V) x m0 m1
        (ALLOC: Genv.alloc_global gen m0 x = Some m1)
    :
      Plt (Mem.nextblock m0) (Mem.nextblock m1).
  Proof.
    destruct x. ss. destruct g; des_ifs.
    - apply Mem.nextblock_alloc in Heq.
      eapply Mem.nextblock_drop in ALLOC.
      rewrite ALLOC. rewrite Heq. apply Plt_succ.
    - apply Mem.nextblock_alloc in Heq.
      apply Genv.store_zeros_nextblock in Heq0.
      apply Genv.store_init_data_list_nextblock in Heq1.
      eapply Mem.nextblock_drop in ALLOC.
      rewrite ALLOC. rewrite Heq1. rewrite Heq0. rewrite Heq.
      apply Plt_succ.
  Qed.

  Lemma ALLOCS_NEXT_INCR F V (gen: Genv.t F V) l m0 m1
        (ALLOC: Genv.alloc_globals gen m0 l = Some m1)
    :
      Ple (Mem.nextblock m0) (Mem.nextblock m1).
  Proof.
    revert l gen m0 m1 ALLOC. induction l; i; ss; clarify.
    - reflexivity.
    - des_ifs. etrans.
      + apply Plt_Ple. eapply ALLOC_NEXT_INCR; eauto.
      + eapply IHl; eauto.
  Qed.

  Lemma init_mem_nextblock F V (p: AST.program F V) m
        (INIT: Genv.init_mem p = Some m)
    :
      Plt 1 (Mem.nextblock m).
  Proof.
    unfold Genv.init_mem in *.
    eapply ALLOCS_NEXT_INCR in INIT.
    ss. apply Pos.le_succ_l. ss.
  Qed.
  
(** ********************* regset *********************************)

  Definition initial_regset : regset := 
    (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
      # RA <- Vnullptr
      # RSP <- (Vptr 1%positive Ptrofs.zero true).

  Definition initial_tgt_regset := initial_regset.

  Definition agree (j: meminj) (rs_src rs_tgt: regset) : Prop :=
    forall pr, Val.inject j (rs_src pr) (rs_tgt pr).

  Lemma update_agree j rs_src rs_tgt pr v
        (AGREE: agree j rs_src rs_tgt)
        (UPDATE: Val.inject j v (rs_tgt # pr))
    :
      agree j (rs_src # pr <- v) rs_tgt.
  Proof.
    destruct pr; intros pr0; specialize (AGREE pr0); destruct pr0; eauto.
    - destruct i, i0; eauto.
    - destruct f, f0; eauto.
    - destruct c, c0; eauto.
  Qed.

  Lemma update_agree2 j rs_src rs_tgt pr v_src v_tgt
        (AGREE: agree j rs_src rs_tgt)
        (UPDATE: Val.inject j v_src v_tgt)
    :
      agree j (rs_src # pr <- v_src) (rs_tgt # pr <- v_tgt).
  Proof.
    destruct pr; intros pr0; specialize (AGREE pr0); destruct pr0; eauto.
    - destruct i, i0; eauto.
    - destruct f, f0; eauto.
    - destruct c, c0; eauto.
  Qed.

  Lemma initial_regset_agree: agree init_inject initial_regset initial_tgt_regset.
  Proof.
    unfold initial_tgt_regset, initial_regset.
    repeat eapply update_agree2; ss; eauto.
    - unfold Genv.symbol_address; des_ifs. econs; eauto.
      unfold init_inject, Mem.flat_inj. des_ifs.
      exfalso. eapply Genv.genv_symb_range in Heq. 
      unfold tge in *. erewrite Genv.init_mem_genv_next in Heq. eauto.
      apply TGT_INIT_MEM. symmetry. apply Ptrofs.add_zero.
    - econs.
    - econs.
      + unfold init_inject, Mem.flat_inj; des_ifs.
        exfalso. apply n. eapply init_mem_nextblock.
        unfold Sk.load_mem in INIT_MEM. apply INIT_MEM.
      + symmetry. apply Ptrofs.add_zero.
  Qed.      

  Inductive inj_same (j: meminj) v_caller v_callee : Prop :=
  | inj_same_intro
      blk_caller blk_callee blk delta delta' ofs
      (CALLERRSP: v_caller = Vptr blk_caller ofs true)
      (CALLEERSP: v_callee = Vptr blk_callee Ptrofs.zero true)
      (EQ: Ptrofs.repr delta' = ofs)
      (CALLER: j blk_caller = Some (blk, delta))
      (CALLEE: j blk_callee = Some (blk, delta + delta')).

  Lemma inj_same_inj j v_caller v_callee v_tgt
        (SAME: inj_same j v_caller v_callee)
        (INJ: Val.inject j v_caller v_tgt)
    :
      Val.inject j v_callee v_tgt.
  Proof.
    inv SAME. inv INJ. clarify. econs; eauto. 
    rewrite Ptrofs.add_zero_l.
    rewrite IntegersC.Ptrofs_add_repr.
    f_equal. apply Z.add_comm.
  Qed.

  Lemma inj_same_inj2 j v_caller v_callee v_tgt
        (SAME: inj_same j v_caller v_callee)
        (INJ: Val.inject j v_callee v_tgt)
    :
      Val.inject j v_caller v_tgt.
  Proof.
    inv SAME. inv INJ. clarify. econs; eauto. 
    rewrite Ptrofs.add_zero_l.
    rewrite IntegersC.Ptrofs_add_repr.
    f_equal. apply Z.add_comm.
  Qed.

  Definition to_fake (v: val) : val :=
    match v with
    | Vptr blk ofs true => Vptr blk ofs false
    | _ => v
    end.

  Lemma to_fake_inj j v_src v_tgt
        (INJ: Val.inject j v_src v_tgt)
    :
        Val.inject j (to_fake v_src) v_tgt.
  Proof. unfold to_fake. inv INJ; econs; eauto. Qed.

  Definition extcall_args_reg (mr: mreg) (sg: signature):
    {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
    {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
  Proof.
    generalize (regs_of_rpairs (loc_arguments sg)). induction l.
    - ss. tauto.
    - ss. inv IHl; [tauto|].
      destruct a.
      + destruct (mreg_eq r mr); [clarify; eauto|].
        right. intros []; clarify.
      + right. intros []; clarify.
  Qed.

  Lemma extcall_args_callee_save_disjoint sg mr
        (EXT: In (R mr) (regs_of_rpairs (loc_arguments sg)))
    :
      ~ Conventions1.is_callee_save mr.
  Proof.
    destruct sg. ss.
    unfold loc_arguments in *.
    ss. replace Archi.ptr64 with true in *; eauto.
    assert (forall l mr p q r,
                In (R mr) (regs_of_rpairs (loc_arguments_64 l p q r)) ->
                ~ is_callee_save mr); eauto.
    induction l; ss; i; destruct a; des_ifs; ss; des; eauto; inv H; ss.
  Qed.

  Definition src_init_rs sg (rs_src: regset) (rsp: val) : regset :=
    fun (pr : PregEq.t) =>
      match Asm.to_mreg pr with
      | Some mr =>
        if (extcall_args_reg mr sg)
        then (rs_src pr)
        else (to_fake (rs_src pr))
      | None =>
        match pr with
        | IR RSP => rsp
        | PC => rs_src PC
        | RA => rs_src RA
        | _ => to_fake (rs_src pr)
        end
      end.

  Definition callee_injection (j: meminj) old_blk new_blk old_delta : meminj :=
    fun blk => if (eq_block blk new_blk)
               then
                 (match (j old_blk) with
                  | None => None
                  | Some (blk', delta) => Some (blk', old_delta + delta)
                  end)
               else (j blk).

  Lemma src_init_rs_agree' j sg rsp (rs_src rs_tgt: regset)
        (AGREE: agree j rs_src rs_tgt)
        (RSPINJ: Val.inject j rsp (rs_tgt # RSP))
    :
      agree j (src_init_rs sg rs_src rsp) rs_tgt.
  Proof.
    intros pr. specialize (AGREE pr). unfold src_init_rs.
    destruct pr; ss; try (destruct (extcall_args_reg _ sg); ss; eapply to_fake_inj; eauto).
    - destruct i; try (destruct (extcall_args_reg _ sg); ss; eapply to_fake_inj; eauto); ss.
    - destruct f; try (destruct (extcall_args_reg _ sg); ss; eapply to_fake_inj; eauto); ss.
    - eapply to_fake_inj; eauto.
  Qed.

  Lemma src_init_rs_agree j sg blk delta ofs new_blk (rs_src rs_tgt: regset)
        (RSPPTR: rs_src # RSP = Vptr blk ofs true)
        (DELTA: Ptrofs.repr delta = ofs)
        (INJNONE: j new_blk = None)
        (AGREE: agree j rs_src rs_tgt)
    :
      agree (callee_injection j blk new_blk delta)
            (src_init_rs sg rs_src (Vptr new_blk Ptrofs.zero true)) rs_tgt.
  Proof.
    set (RSPAGREE := AGREE RSP).
    rewrite RSPPTR in *. inv RSPAGREE. eapply src_init_rs_agree'.
    - intros pr. specialize (AGREE pr).
      inv AGREE; econs; clarify; eauto; unfold callee_injection; des_ifs.
    - unfold callee_injection. rewrite <- H1. econs. des_ifs.
      rewrite IntegersC.Ptrofs_add_repr. rewrite Ptrofs.add_zero_l. auto.
  Qed.

  Inductive almost_eq : val -> val -> Prop :=
  | almost_eq_refl v : almost_eq v v
  | almost_eq_ptr blk ofs b1 b2 : almost_eq (Vptr blk ofs b1) (Vptr blk ofs b2)
  .

  Lemma to_fake_almost_eq v
    :
      almost_eq v (to_fake v).
  Proof.
    destruct v; try econs. destruct b0; econs.
  Qed.

  Lemma almost_eq_commute j v_src0 v_src1 v_tgt
        (INJ: Val.inject j v_src1 v_tgt)
        (EQ: almost_eq v_src0 v_src1)
    :
      Val.inject j v_src0 v_tgt.
  Proof.
    inv EQ; eauto.
    destruct b1, b2; inv INJ; try econs; eauto. clarify.
  Qed.

  Lemma lessdef_commute j v_src0 v_src1 v_tgt
        (INJ: Val.inject j v_src1 v_tgt)
        (LESS: Val.lessdef v_src0 v_src1)
    :
      Val.inject j v_src0 v_tgt.
  Proof.
    inv LESS; inv INJ; eauto.
  Qed.

  Inductive wf_init_rs (j: meminj) (rs_caller rs_callee: regset) : Prop :=
  | wf_init_rs_intro
      (PCSAME: rs_caller # PC = rs_callee # PC)
      (RASAME: rs_caller # RA = rs_callee # RA)
      (RSPSAME: inj_same j (rs_caller # RSP) (rs_callee # RSP))
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              almost_eq (rs_caller (to_preg mr))
                                        (rs_callee (to_preg mr)))
  .    

  Lemma src_init_rs_wf j old_blk new_blk ofs (rs: regset) sg b' delta
        (INJ_NONE: j new_blk = None)
        (INJ_SOME: j old_blk = Some (b', delta))
        (RSRSP: rs # RSP = Vptr old_blk ofs true)
    :
      wf_init_rs
      (callee_injection j old_blk new_blk (Ptrofs.unsigned ofs))
      rs
      (src_init_rs sg rs (Vptr new_blk Ptrofs.zero true)).
  Proof.
    econs; ss.
    - econs; eauto; ss.
      + apply Ptrofs.repr_unsigned.
      + unfold callee_injection. des_ifs. apply INJ_SOME.
      + unfold callee_injection. des_ifs.
        rewrite Z.add_comm. auto.
    - intros. unfold src_init_rs. Opaque to_fake.
      destruct mr; ss; clarify; des_ifs; try econs; try apply to_fake_almost_eq.
  Qed.          

(** ********************* match stack *********************************)
  
  Inductive match_stack (j: meminj) : regset -> list Frame.t -> Prop :=
  | match_stack_init
      init_rs
      (RSRA: init_rs # RA = Vnullptr)
      (RSPC: init_rs # PC = Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
      (SIG: skenv_link.(Genv.find_funct) (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero) = Some (Internal signature_main))
    :
      match_stack j init_rs nil
  | match_stack_cons
      fr frs p st b init_rs0 init_rs1
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate init_rs1 st b))
      (STACK: match_stack j init_rs1 frs)
      (WF: wf_init_rs j st.(st_rs) init_rs0)
    :
      match_stack j init_rs0 (fr::frs)
  .

  Inductive match_stack_call (j: meminj) : mem -> regset -> list Frame.t -> Prop :=
  | match_stack_call_init
      init_rs m
      (MEM: m = m_init)
      (INITRS: init_rs = initial_regset)
    :
      match_stack_call j m init_rs nil
  | match_stack_call_cons
      fr frs p st b init_rs0 init_rs1 m
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs1 st b))
      (INITRS: init_rs0 = st.(st_rs))
      (STACK: match_stack j init_rs1 frs)
      (MEM: m = st.(st_m))      
    :
      match_stack_call j m init_rs0 (fr::frs)
  .

  Lemma match_stack_incr j1 j2 init_rs l
        (INCR: inject_incr j1 j2)
        (MATCH: match_stack j1 init_rs l)
    :
      match_stack j2 init_rs l.
  Proof.
    revert init_rs INCR MATCH. induction l; ss; ii; inv MATCH; econs; ss; eauto.
    inv WF. econs; eauto.
    inv RSPSAME. econs; eauto.
  Qed.

  Lemma frame_inj a0 b0 a1 b1
        (EQ: Frame.mk a0 b0 = Frame.mk a1 b1)
    : b0 ~= b1.
  Proof. inv EQ. eauto. Qed.

  Lemma asm_frame_inj se1 se2 p1 p2 st1 st2
        (EQ : Frame.mk (modsem se1 p1) st1 = Frame.mk (modsem se2 p2) st2)
    :
      st1 = st2.
  Proof. apply frame_inj in EQ. apply JMeq_eq. eauto. Qed.

  Definition memcpy (m: mem) (blk: Values.block) (lo size: Z) : mem. Admitted.
  
  Lemma memcpy_spec1 m blk lo size
    :
      Mem.nextblock (memcpy m blk lo size) = Pos.succ m.(Mem.nextblock).
  Admitted.

  (* Lemma memcpy_spec2_1 m chunk blk lo size ofs *)
  (*       (BOUND: 0 <= ofs < size) *)
  (*   : *)
  (*     Mem.load chunk (memcpy m blk lo size) (Mem.nextblock m) ofs = *)
  (*     Mem.load chunk m blk (lo + ofs). *)
  (* Admitted. *)

  Lemma memcpy_spec2_2 m blk lo size blk0 ofs
        (NEQ0: blk0 <> blk)
        (NEQ1: blk0 <> m.(Mem.nextblock))
    :
      ZMap.get ofs (Mem.mem_contents (memcpy m blk lo size)) !! blk0 =
      ZMap.get ofs (Mem.mem_contents m) !! blk0.
  Admitted.

  Lemma memcpy_load m chunk blk lo size ofs
        (BOUND: 0 <= ofs < size)
    :
      Mem.load chunk (memcpy m blk lo size) (Mem.nextblock m) ofs =
      Mem.load chunk m blk (lo + ofs).
  Admitted.

  Lemma memcpy_spec3_1 m blk lo size ofs k p
        (BOUND: 0 <= ofs < size)
    :
      Mem.perm (memcpy m blk lo size) m.(Mem.nextblock) ofs k p <->
      Mem.perm m blk (lo + ofs) k p.
  Admitted.

  Lemma memcpy_spec3_2 m blk lo size ofs k p
        (BOUND: ~ 0 <= ofs < size)
    :
      ~ Mem.perm (memcpy m blk lo size) m.(Mem.nextblock) ofs k p.
  Admitted.

  Lemma memcpy_spec3_3 m blk lo size blk0 ofs k p
        (NEQ0: blk0 <> blk)
        (NEQ1: blk0 <> m.(Mem.nextblock))
    :
      Mem.perm (memcpy m blk lo size) blk0 ofs k p <->
      Mem.perm m blk0 ofs k p.
  Admitted.
    
  Lemma memcpy_spec3_4 m blk lo size ofs k p
        (BOUND: 0 <= ofs < size)
    :
      ~ Mem.perm (memcpy m blk lo size) blk (lo + ofs) k p.
  Admitted.

  Lemma memcpy_spec3_5 m blk lo size ofs k p
        (BOUND: ~ 0 <= ofs < size)
    :
      Mem.perm (memcpy m blk lo size) blk (lo + ofs) k p <->
      Mem.perm m blk (lo + ofs) k p.
  Admitted.

  Lemma unfree_free_inj j (m_src0 m_src1 m_src2 m_tgt: mem) blk0 blk1 delta1 delta2 ofs1 ofs2 size
        (DELTA1: Ptrofs.repr delta1 = ofs1)
        (DELTA2: Ptrofs.repr delta2 = ofs2)
        (FREE: Mem.free m_src0 blk0 delta1 (delta1 + size) = Some m_src1)
        (UNFREE: Mem_unfree m_src1 blk1 delta2 (delta2 + 4 * size) = Some m_src2)
        (SAME: inj_same j (Vptr blk1 ofs2 true) (Vptr blk0 ofs1 true))
        (INJ: Mem.inject j m_src0 m_tgt)
    :
      Mem.inject j m_src2 m_tgt.
  Admitted.

  Lemma preg_case pr :
    (exists mr, pr = to_preg mr) \/
    (pr = PC) \/ (exists c, pr = CR c) \/ (pr = RSP) \/ (pr = RA)
  .
  Proof.
    destruct (to_mreg pr) eqn:EQ.
    - left. exists m. unfold to_mreg in *.
      destruct pr; clarify.
      destruct i; clarify; auto.
      destruct f; clarify; auto.
    - right. unfold to_mreg in *.
      destruct pr; clarify; eauto.
      destruct i; clarify; auto.
      destruct f; clarify; auto.
  Qed.

  Lemma callee_save_agree j rs_caller init_rs rs_callee rs_tgt sg mr rs
        (WF: wf_init_rs j rs_caller init_rs)
        (AGREE: agree j rs_callee rs_tgt)
        (INITSIG: exists skd, skenv_link.(Genv.find_funct) (init_rs # PC) = Some skd /\ SkEnv.get_sig skd = sg)
        (RETV: loc_result sg = One mr)
        (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                                Val.lessdef (init_rs mr.(to_preg)) (rs_callee mr.(to_preg)))
        (RSRA: rs_callee # PC = init_rs # RA)
        (RSRSP: rs_callee # RSP = init_rs # RSP)
        (RS: rs = (set_pair (loc_external_result sg) (rs_callee mr.(to_preg)) (Asm.regset_after_external rs_caller)))
    :
        agree j rs rs_tgt.
  Proof.
    inv WF. clarify.
    - unfold loc_external_result. rewrite RETV. ss.
      eapply update_agree; eauto.
      unfold Asm.regset_after_external in *. intros pr. specialize (AGREE pr).
      destruct (preg_case pr); des; clarify; ss.
      + rewrite to_preg_to_mreg. des_ifs.
        specialize (CALLEESAVE mr0). specialize (CALLEESAVE0 mr0).
        rewrite Heq in *.
        eapply almost_eq_commute with (v_src1 := init_rs (to_preg mr0)); eauto.
        eapply lessdef_commute with (v_src1 := rs_callee (to_preg mr0)); eauto.
      + rewrite RSRSP in *.
        eapply inj_same_inj2; eauto.
  Qed.

  Inductive match_states : Sem.state -> Asm.state -> nat -> Prop :=
  | match_states_intro
      j fr frs p init_rs b rs_src rs_tgt m_src m_tgt n
      (AGREE: agree j rs_src rs_tgt)
      (INJ: Mem.inject j m_src m_tgt)
      (INITINCR: inject_incr init_inject j)
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs (Asm.State rs_src m_src) b))
      (STACK: match_stack j init_rs frs)
      (ORD: n = if (external_state skenv_link p (rs_src # PC))
                then (length frs + 2)%nat else 0%nat)
    :
      match_states (State (fr::frs)) (Asm.State rs_tgt m_tgt) n
  | match_states_call
      j init_rs frs args m_src rs_tgt m_tgt ofs blk sg n
      (STACK: match_stack_call j m_src init_rs frs)
      (AGREE: agree j init_rs rs_tgt)
      (INJECT: Mem.inject j m_src m_tgt)
      (INITINCR: inject_incr init_inject j)
      (FPTR: args.(Args.fptr) = init_rs # PC)
      (SIG: exists skd, skenv_link.(Genv.find_funct) args.(Args.fptr)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (ARGS: extcall_arguments init_rs m_src sg args.(Args.vs))
      (RSPPTR: init_rs # RSP = Vptr blk ofs true)
      (FREE: Mem.free m_src blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)) = Some args.(Args.m))
      (ORD: n = 1%nat)
    :
      match_states (Callstate args frs) (Asm.State rs_tgt m_tgt) n.

  Lemma mem_free_none m blk lo hi
        (EQ: lo = hi)
    :
      Mem.free m blk lo hi = Some m.
  Proof. admit "mem_free_none". Qed.

  Lemma symb_main :
    Genv.find_symbol skenv_link (prog_main sk) =
    Genv.find_symbol tge (prog_main tprog).
  Proof. admit "". Qed.

  Lemma transf_initial_states:
    forall st1, Sem.initial_state prog st1 ->
                exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2 1.
  Proof.
    generalize TGT_INIT_MEM.
    generalize initial_regset_agree.
    generalize initmem_inject.
    intros initmem_inject initial_regset_agree TGT_INT_MEM.
    intros st1 INIT. inv INIT; clarify. esplits.
    - econs; eauto.
    - econs; ss; eauto; ss.
      + econs; ss; eauto.
      + unfold initial_regset.
        rewrite Pregmap.gso; clarify.
        rewrite Pregmap.gso; clarify. ss.
        rewrite Pregmap.gss. unfold tge.
        set (MAIN:= symb_main).
        unfold Genv.symbol_address. unfold skenv_link, tge in *. rewrite MAIN. auto.
      + econs.
      + apply mem_free_none. ss.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r n,
      match_states st1 st2 n -> Sem.final_state st1 r -> Asm.final_state st2 r.
  Proof.
    intros st_src st_tgt r n MTCHST FINAL. inv FINAL. inv MTCHST. ss.
    inv FINAL0. clarify. inv STACK. econs.
    - specialize (AGREE PC). rewrite RSRA in *. rewrite RSRA0 in *.
      inv AGREE; ss.
    - des. rewrite RSPC in *. rewrite SIG in *. clarify.
      ss. unfold signature_main, loc_arguments, loc_result in *.
      Transparent Archi.ptr64. ss. unfold loc_result_64 in *. ss. clarify.
      ss. specialize (AGREE RAX). rewrite INT in *. inv AGREE; auto.
  Qed.  

  Lemma step_return_simulation
        fr0 fr1 frs retv st0 st_tgt n0
        (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
        (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) retv st0)
        (MTCHST: match_states (State (fr0 :: fr1 :: frs)) st_tgt n0)
    :
      exists n1, match_states (State ((fr1.(Frame.update_st) st0) :: frs)) st_tgt n1
                 /\ (n1 < n0)%nat.
  Proof.
    inv MTCHST. inv STACK. ss. inv FINAL. inv AFTER. set WF as WF2. inv WF2. ss.
    rewrite PCSAME in *. des. ss. clarify. esplits.
    econs; simpl in *.
    - eapply callee_save_agree; eauto.
    - set unfree_free_inj.
      specialize (i j m_src m1 m2 m_tgt blk blk0 0 (Ptrofs.unsigned ofs)).
      eapply i; eauto. clear i.
      rewrite INITRSP in RSPSAME. rewrite RSRSP0 in RSPSAME.
      rewrite Ptrofs.repr_unsigned. auto.
    - ss.
    - ss. 
    - ss.
    - ss.
    - des_ifs. omega.
  Qed.

  Lemma asm_step_preserve_injection
        rs_src0 rs_src1 m_src0 m_src1 tr j0
        rs_tgt0 m_tgt0
        ge_src ge_tgt
        (GENVLE: genv_le j0 ge_src ge_tgt)
        (GE: genv_le j0 ge_src ge_tgt)
        (AGREE: agree j0 rs_src0 rs_tgt0)
        (INJ: Mem.inject j0 m_src0 m_tgt0)
        (STEP: Asm.step ge_src (Asm.State rs_src0 m_src0) tr (Asm.State rs_src1 m_src1))
    :
      exists rs_tgt1 m_tgt1 j1,
        (Asm.step ge_tgt (Asm.State rs_tgt0 m_tgt0) tr (Asm.State rs_tgt1 m_tgt1)) /\
        (agree j1 rs_src1 rs_tgt1) /\
        (Mem.inject j1 m_src1 m_tgt1) /\
        (inject_incr j0 j1).
  Admitted.

  Lemma asm_step_internal_simulation
        st_src0 st_src1 st_tgt0 tr frs p b0 b1 init_rs n0
        (STEP: Asm.step (local_genv p) st_src0 tr st_src1)
        (STEPRET: AsmC.step_ret skenv_link p st_src0 b1)
        (MTCHST: match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                                (AsmC.mkstate init_rs st_src0 b0))::frs))
                              st_tgt0 n0)
    :
      exists st_tgt1 n1,
        Asm.step tge st_tgt0 tr st_tgt1 /\
        match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                       (AsmC.mkstate init_rs st_src1 b1))::frs))
                     st_tgt1 n1.
  Proof.
    inv MTCHST. apply asm_frame_inj in FRAME. inv FRAME. destruct st_src1.
    exploit asm_step_preserve_injection; ss; eauto.
    - apply local_genv_le. ss.
    - apply local_genv_le; auto.
    - ii. des. esplits; eauto; econs; eauto.
      + etrans. apply INITINCR. auto.
      + eapply match_stack_incr; eauto.
  Qed.

  Lemma step_internal_simulation
        fr0 frs tr st0 st_tgt0 n0
        (STEP: fr0.(Frame.ms).(ModSem.step) fr0.(Frame.ms).(ModSem.globalenv) fr0.(Frame.st) tr st0)
        (MTCHST: match_states (State (fr0 :: frs)) st_tgt0 n0) 
    :
      exists st_tgt1 n1,
        Asm.step tge st_tgt0 tr st_tgt1 /\
        match_states (State ((fr0.(Frame.update_st) st0) :: frs)) st_tgt1 n1.
  Proof.
    inv MTCHST. inv STEP.
    exploit asm_step_internal_simulation; ss; eauto.
    - econs; eauto.
    - ii. des. esplits; ss; eauto.
      destruct st0; ss; clarify. eassumption.
    Unshelve. auto.
  Qed.

  Lemma step_call_simulation
        fr0 frs args st_tgt n
        (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) args)
        (MTCHST: match_states (State (fr0 :: frs)) st_tgt n)
    :
        match_states (Callstate args (fr0 :: frs)) st_tgt 1%nat.
  Proof.
    inv MTCHST. ss. inv AT.
    econs; ss; eauto.
    econs; eauto.
  Qed.

  Lemma to_fake_fake_ptr v : ~ is_real_ptr (to_fake v).
  Proof.
    intros i. inv i. destruct v; ss. destruct b0; ss.
  Qed.

  Lemma nextblock_unvalid j m1 m2
        (INJ: Mem.inject j m1 m2)
    :
      j (Mem.nextblock m1) = None.
  Proof.
    inv INJ. eapply mi_freeblocks.
    unfold Mem.valid_block. apply Plt_strict.
  Qed.

  Lemma callee_injection_incr j old_blk new_blk delta
        (INJ_NONE: j new_blk = None)
    :
      inject_incr j (callee_injection j old_blk new_blk delta).
  Proof.
    unfold callee_injection. ii. des_ifs.
  Qed.

  Lemma memcpy_inject j m_src m_tgt blk ofs size 
        (INJ: Mem.inject j m_src m_tgt)
    :
      Mem.inject (callee_injection j blk (Mem.nextblock m_src) ofs)
                 (memcpy m_src blk ofs size) m_tgt.
  Admitted.

  Lemma local_genv_skenv_signature p fptr fd
        (FIND: Genv.find_funct (local_genv p) fptr = Some (Internal fd))
    :
      Genv.find_funct skenv_link fptr = Some (Internal (fn_sig fd)).
  Admitted.

  Lemma src_init_rs_PTRFREE sg rs v
    :
      forall
          pr mr
          (MR: to_mreg pr = Some mr)
          (NOTIN: ~In (R mr) (regs_of_rpairs (loc_arguments sg)))
        ,
          <<PTRFREE: ~ is_real_ptr ((src_init_rs sg rs v) pr)>>.
  Proof.
    i. intros PTR. unfold src_init_rs in PTR.
    des_ifs; eapply to_fake_fake_ptr; eauto.
  Qed.

  Lemma skenv_link_main
    :
      Genv.find_funct
        skenv_link (Genv.symbol_address tge (prog_main tprog) Ptrofs.zero)
      = Some (Internal signature_main).
  Admitted.

  Lemma src_init_rs_arguments (rs: regset) m0 m1 sg rsp mr v
        (ARG: extcall_arg rs m0 (R mr) v)
        (IN: In (R mr) (regs_of_rpairs (loc_arguments sg)))
    :
      extcall_arg (src_init_rs sg rs rsp) m1 (R mr) v.
  Proof.
    inv ARG.
    replace (rs (preg_of mr)) with (src_init_rs sg rs rsp (preg_of mr)); [econs|].
    unfold src_init_rs.
    destruct mr; ss; des_ifs.
  Qed.

  Lemma memcpy_property m0 m1 m2 blk lo size
        (FREE: m0.(Mem.free) blk lo (lo + size) =
               Some m1)
        (ALLOC: Mem.alloc m1 0 size = (m2, m0.(Mem.nextblock)))
    :
      Mem.unchanged_on
        (fun blk0 ofs0 => if eq_block blk0 (m0.(Mem.nextblock)) then ~ (0 <= ofs0 < size) else True)
        m2 (memcpy m0 blk lo size).
  Proof.
    econs.
    - rewrite memcpy_spec1.
      erewrite Mem.nextblock_alloc; eauto.
      erewrite Mem.nextblock_free; eauto.
      reflexivity.
    - intros blk0 ofs0 k p EQ VALID.
      des_ifs.
      + split; intro PERM.
        * eapply Mem.perm_alloc_3 in PERM; eauto. clarify.
        * eapply memcpy_spec3_2 in PERM; clarify.
      + split; intro PERM; destruct (eq_block blk0 blk); clarify.
        * admit "".
        * eapply memcpy_spec3_3; auto.
          eapply Mem.perm_alloc_4 in PERM; [| apply ALLOC| eauto].
          eapply Mem.perm_free_3; eauto.
        * admit "".
        * erewrite memcpy_spec3_3 in PERM; eauto.
          eapply Mem.perm_alloc_1; eauto.
          eapply Mem.perm_free_1; eauto.
    - intros blk0 ofs0 EQ PERM. des_ifs.
  Admitted.

  Lemma memcpy_arguments (rs0 rs1: regset) m sg blk ofs delta ty v
        (RSRSP0: rs0 # RSP = Vptr blk ofs true)
        (REPRESENT:
           Ptrofs.unsigned ofs + (4 * size_arguments sg) <= Ptrofs.modulus)
        (RSRSP1: rs1 # RSP = Vptr (Mem.nextblock m) Ptrofs.zero true)
        (ARG: extcall_arg rs0 m (S Outgoing delta ty) v)
        (DELTA: 0 <= delta < size_arguments sg)
    :
      extcall_arg
        rs1
        (memcpy m blk (Ptrofs.unsigned ofs)
                (4 * size_arguments sg)) (S Outgoing delta ty) v.
  Proof.
    econs. reflexivity. inv ARG. rewrite RSRSP0 in *. rewrite RSRSP1 in *. ss.
    rewrite Ptrofs.add_zero_l. rewrite memcpy_load.
    - replace (Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr (4 * delta)))
        with (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (4 * delta)))); auto.
      admit "ez".
    - rewrite Ptrofs.unsigned_repr; [omega|].
      split; try omega.
      admit "ez".
  Qed.

  Lemma free_success m0 blk lo hi m1
        (FREE: Mem.free m0 blk lo hi = Some m1)
    :
      Mem.range_perm m0 blk lo hi Cur Freeable.
  Proof.
    Local Transparent Mem.free. unfold Mem.free in FREE. des_ifs; eauto.
  Qed.

  Lemma memcpy_store_arguments rs m0 m1 sg args blk ofs true
        (ARGS: extcall_arguments rs m0 sg args)
        (RSRSP: rs # RSP = Vptr blk ofs true)
        (FREE: Mem.free m0 blk (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 4 * size_arguments sg) = Some m1)
    :
      store_arguments
        m1
        (src_init_rs sg rs (Vptr (Mem.nextblock m0) Ptrofs.zero true))
        args sg (memcpy m0 blk (Ptrofs.unsigned ofs) (4 * size_arguments sg)).
  Proof.
    destruct (Mem.alloc m1 0 (4 * size_arguments sg)) eqn:MEQ.
    destruct (eq_sym (Mem.alloc_result _ _ _ _ _ MEQ)).
    erewrite Mem.nextblock_free in MEQ; eauto.
    econs; eauto.
    - admit "".
    - eapply memcpy_property; eauto.
    - rewrite memcpy_spec1.
      erewrite Mem.nextblock_alloc; [|eauto].
      erewrite Mem.nextblock_free; eauto.
    - intros ofs0 BOUND.
      apply memcpy_spec3_1; auto.
      eapply free_success; eauto. omega.
  Qed.    
  
  Lemma step_init_simulation
        args frs st_tgt p fd n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
        (MSFIND: ge.(Ge.find_fptr_owner) args.(Args.fptr) (AsmC.modsem skenv_link p))
        (FINDF: Genv.find_funct (local_genv p) args.(Args.fptr) = Some (Internal fd))
        (SIZEWF: 4 * size_arguments (fn_sig fd) <= Ptrofs.modulus)
    :
      exists rs m,
        (AsmC.initial_frame skenv_link p args (AsmC.mkstate rs (Asm.State rs m) false)) /\
        (match_states (State ((Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate rs (Asm.State rs m) false)) :: frs)) st_tgt 0).
  Proof.
    inv MTCHST. des. ss. set (nextblock_unvalid := nextblock_unvalid INJECT).
    set (SKDSG:= local_genv_skenv_signature _ _ FINDF). clarify.
    exists (src_init_rs (fn_sig fd) init_rs (Vptr m_src.(Mem.nextblock) Ptrofs.zero true)).
    exists (memcpy m_src blk (Ptrofs.unsigned ofs) (4 * size_arguments (fn_sig fd))).
    esplits; eauto.
    - econs.
      + apply (eq_refl (fn_sig fd)).
      + apply FINDF.
      + ss.
      + unfold src_init_rs. ss. f_equal.
        symmetry. eapply Mem.nextblock_free. eauto.
      + ss.
      + eapply memcpy_store_arguments; eauto.
      + apply src_init_rs_PTRFREE.
    - econs.
      + instantiate (2 := callee_injection j blk (Mem.nextblock m_src) (Ptrofs.unsigned ofs)).
        eapply src_init_rs_agree; eauto.
        apply Ptrofs.repr_unsigned.
      + instantiate (1 := memcpy m_src blk (Ptrofs.unsigned ofs)
                                 (4 * size_arguments (fn_sig fd))).
        eapply memcpy_inject; auto.
      + eapply inject_incr_trans with (f2 := j); auto.
        apply callee_injection_incr; auto.
      + reflexivity.
      + inv STACK; econs; ss; [apply skenv_link_main| |].
        * eapply match_stack_incr; [|eauto].
          apply callee_injection_incr; auto.
        * set (AGREERSP := AGREE RSP).
          rewrite RSPPTR in AGREERSP. inv AGREERSP.
          eapply src_init_rs_wf; eauto.
      + unfold external_state.
        des_ifs. exfalso. unfold src_init_rs, local_genv in *. ss.
        rewrite <- FPTR in *. rewrite Heq0 in *. ss. des_ifs.
        clear - FINDF Heq1. remember (SkEnv.revive (SkEnv.project skenv_link (defs p)) p).
        unfold fundef in *. clarify.
  Qed.

  Definition index := nat.

  Definition order := le.

  Lemma symb_preserved id
    :
      Senv.public_symbol (symbolenv (semantics tprog)) id =
      Senv.public_symbol (symbolenv (sem prog)) id.
  Admitted.

  Lemma at_external_external p st frs st_tgt n args
        (MTCHST: match_states
                   (State
                      ((Frame.mk (AsmC.modsem skenv_link p) st)::frs))
                   st_tgt n)
        (ATEXTERNAL: at_external skenv_link p st args)
    :
      (1 < n)%nat.
  Proof.
    inv MTCHST.
    replace (at_external skenv_link p) with (at_external skenv_link p0) in *.
    - inv ATEXTERNAL. apply asm_frame_inj in FRAME. clarify.
      unfold external_state. des_ifs. omega.
    - apply f_equal with (f := Frame.ms) in FRAME. ss.
      inv FRAME. apply Eqdep.EqdepTheory.inj_pair2 in H1. auto.
  Qed.  

  Lemma normal_state_fsim_step frs st_src1 st_tgt0 t n0
        (MTCHST: match_states (State frs) st_tgt0 n0)
        (STEP: step ge (State frs) t st_src1)
    :
      (exists st_tgt1 n1,
          Asm.step tge st_tgt0 t st_tgt1 /\ match_states st_src1 st_tgt1 n1) \/
      (exists n1,
          match_states st_src1 st_tgt0 n1 /\ n1 < n0)%nat /\ (t = E0).
  Proof.
    inv STEP.
    - right. exploit step_call_simulation; eauto.
      i. esplits; eauto.
      inv MTCHST; ss.
      exploit at_external_external; eauto.
      econs; try eassumption; ss.
    - left. exploit step_internal_simulation; eauto.
    - right. exploit step_return_simulation; eauto.
  Qed.

  Lemma match_state_xsim
    :
      forall st_src st_tgt n (MTCHST: match_states st_src st_tgt n),
        xsim (sem prog) (semantics tprog) lt n st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold. destruct st_src.
    - admit "init".
    - left. econs.
      + i. econs.
        * exploit transf_final_states; eauto.
        * { (** D return **)
            i. inv FINAL0. inv FINAL1. eq_closure_tac.
          }
        * ii. inv FINAL. inv H; eq_closure_tac.
      + econs.
        * i. ss. rewrite LINK_SK in *.
          exploit normal_state_fsim_step; eauto.
          i. des; esplits; eauto.
          -- left. econs; ss.
             ++ econs; eauto. admit "determinate at".
             ++ econs 1.
             ++ rewrite E0_right. auto.
          -- right. econs; ss. clarify. econs.
        * admit "receptive at".
  Qed.
  
  Lemma transf_xsim_properties
    :
        xsim_properties (sem prog) (semantics tprog) nat lt.
  Proof.
    econs; [apply lt_wf| |apply symb_preserved].
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - { (** D init **)
        i. inv INIT0. inv INIT1. clarify.
      }
    - apply match_state_xsim; eauto.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Sem.sem prog) (Asm.semantics tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.    

End PRESERVATION.
