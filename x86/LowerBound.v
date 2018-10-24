Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC MemoryC2 Lia.

Set Implicit Arguments.

Local Opaque Z.mul.


Section LINKABILITY.

  Variable asms: list Asm.program.
  Let p_src: Syntax.program := List.map AsmC.module asms.

  Theorem link_sim
          link_src
          (SRC: link_sk p_src = Some link_src)
    :
      exists link_tgt, <<TGT: link_list asms = Some link_tgt>>
  .
  Proof.
    ginduction asms; ii; ss.
    subst p_src. u in SRC.
    destruct l; ss.
    { esplits; eauto. ss. }
    eapply link_list_cons_inv in SRC; cycle 1.
    { ss. }
    des.
    exploit IHl; eauto. i; des.
    rename link_tgt into link_tgt_middle.
    assert(exists link_tgt, <<LINK: link a link_tgt_middle = Some link_tgt>>).
    { admit "this should hold". }
    des.
    exploit (@link_list_cons Asm.program); eauto. i; des.
    esplits; eauto.
  Qed.

End LINKABILITY.


Section PRESERVATION.

  Existing Instance Val.mi_final.

(** ********************* linking *********************************)
  
  Variable progs : list Asm.program.
  Let prog : Syntax.program := List.map AsmC.module progs.

  Variable tprog : Asm.program.
  Hypothesis LINK : link_list progs = Some tprog.

(** ********************* genv *********************************)
  
  Variable sk : Sk.t.
  Hypothesis LINK_SK : link_sk prog = Some sk.
  Let skenv_link := Sk.load_skenv sk.
  Let ge := load_genv prog skenv_link.
  Let tge := Genv.globalenv tprog.

  Definition local_genv (p : Asm.program) :=
    (skenv_link.(SkEnv.project) p.(defs)).(SkEnv.revive) p.

  Record sub_match_genvs A B V W (R: globdef A V -> globdef B W -> Prop)
         (ge1: Genv.t A V) (ge2: Genv.t B W): Prop :=
    {
      sub_mge_next : Ple (Genv.genv_next ge1) (Genv.genv_next ge2);
      sub_mge_symb id b (FIND: Genv.find_symbol ge1 id = Some b):
        Genv.find_symbol ge2 id = Some b;
      sub_mge_defs b d0 (FIND: Genv.find_def ge1 b = Some d0):
        exists d1, <<FIND: Genv.find_def ge2 b = Some d1>> /\ <<MATCHDEF: R d0 d1>>;
    }.
  
  Lemma match_genvs_sub A B V W R (ge1: Genv.t A V) (ge2: Genv.t B W)
        (MATCHGE: Genv.match_genvs R ge1 ge2)
    :
      sub_match_genvs R ge1 ge2.
  Proof.
    inv MATCHGE. econs; i; ss; eauto.
    - rewrite mge_next. refl.
    - etrans; eauto.
    - unfold Genv.find_def in *. specialize (mge_defs b).
      inv mge_defs; eq_closure_tac. eauto.
  Qed.

  Lemma match_skenv_link_tge :
    Genv.match_genvs (fun skdef fdef => skdef_of_gdef fn_sig fdef = skdef) skenv_link tge.
  Proof.
    admit "ez".
  Qed.

  Definition genv_le (ge_src ge_tgt: Genv.t fundef unit): Prop :=
    sub_match_genvs eq ge_src ge_tgt.

  Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj): Prop :=
  | sken_inject_intro
      (DOMAIN: forall b, Plt b ge.(Genv.genv_next) -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta (INJ: j b1 = Some(b2, delta)),
          Senv.block_is_volatile ge b2 = Senv.block_is_volatile ge b1)
  .

  (* Lemma sub_match_inj A B V W R (ge0: Genv.t A V) (ge1: Genv.t B W) j *)
  (*       (MATCHGE: sub_match_genvs R ge0 ge1) *)
  (*       (RESPECT: forall g_src g_tgt (REL: R g_src g_tgt), *)
  (*           match g_src, g_tgt with *)
  (*           | Gfun _, Gfun _ => True *)
  (*           | Gfun _, Gvar _ => False *)
  (*           | Gvar _, Gfun _ => False *)
  (*           | Gvar g_src', Gvar g_tgt' => *)
  (*             gvar_volatile g_src' = gvar_volatile g_tgt' *)
  (*           end) *)
  (*       (SKINJ: skenv_inject ge1 j) *)
  (*   : *)
  (*     skenv_inject ge0 j. *)
  (* Proof. *)
  (*   inv SKINJ. inv MATCHGE. econs. *)
  (*   - i. eapply DOMAIN. eapply Plt_Ple_trans; eauto. *)
  (*   - i. ss. admit "". *)
  (* Qed. *)

  Lemma sub_match_local_genv ge_local
        (MATCHGE: genv_le ge_local tge)
    :
      sub_match_genvs (fun fdef skdef => skdef_of_gdef fn_sig fdef = skdef) ge_local skenv_link.
  Proof.
    destruct match_skenv_link_tge. inv MATCHGE.
    unfold Genv.find_symbol, Genv.find_def in *. econs.
    - rewrite <- mge_next. eauto.
    - i. eapply sub_mge_symb0 in FIND.
      rewrite mge_symb in FIND. eauto.
    - i. eapply sub_mge_defs0 in FIND. des.
      specialize (mge_defs b). inv mge_defs.
      + eq_closure_tac.
      + eq_closure_tac. esplits; eauto.
  Qed.

  Inductive valid_owner fptr (p: Asm.program) : Prop :=
  | valid_owner_intro
      fd
      (MSFIND: ge.(Ge.find_fptr_owner) fptr (AsmC.modsem skenv_link p))
      (FINDF: Genv.find_funct (local_genv p) fptr = Some (Internal fd))
      (SIZEWF: 4 * size_arguments (fn_sig fd) <= Ptrofs.modulus).   
  
  Lemma valid_owner_genv_le fptr p
        (OWNER: valid_owner fptr p) 
    :
      genv_le (local_genv p) tge.
  Proof.
    admit "this should hold".
  Qed.
  
  Lemma symb_preserved id
    :
      Senv.public_symbol (symbolenv (semantics tprog)) id =
      Senv.public_symbol (symbolenv (sem prog)) id.
  Proof.
    ss.
    admit "this should hold. fill in `symbolenv` of `Sem.v`".
  Qed.

  Lemma symb_main :
    Genv.find_symbol skenv_link (prog_main sk) =
    Genv.find_symbol tge (prog_main tprog).
  Proof.
    unfold Genv.find_symbol in *.
    admit "ez".
  Qed.

  Lemma local_global_consistent
        ge_local
        (IN: genv_le ge_local tge)
        fptr fd
        (LOCAL: Genv.find_funct ge_local fptr = Some (Internal fd))
        skd
        (GLOBAL: Genv.find_funct skenv_link fptr = Some skd)
    :
      SkEnv.get_sig skd = fd.(fn_sig)
  .
  Proof.
    admit "ez".
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
    Local Transparent Linker_prog.
    unfold Sk.load_mem in *.
    eapply Genv.init_mem_match
      with (ctx := tt) (match_fundef := top3) (match_varinfo := top2);
      [| eapply INIT_MEM]. econs.
    - admit "list_forall2 (match_ident_globdef top3 top2 ()) (prog_defs sk) (prog_defs tprog)".
    - split.
      + subst prog. generalize tprog sk LINK LINK_SK. induction progs; ss.
        i. unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs.
      + subst prog. generalize tprog sk LINK LINK_SK.
        clear LINK LINK_SK. induction progs; ss.
        i. unfold link_sk, link_list in *; ss; unfold link_prog in *. des_ifs; ss.
        * exfalso. admit "use Heq0 & Heq1".
        * exfalso. admit "use Heq0 & Heq2".
        * f_equal. eauto.
  Qed.

  Definition init_inject := Mem.flat_inj (Mem.nextblock m_init).

  Lemma initmem_inject: Mem.inject init_inject m_init m_tgt_init.
  Proof.
    eapply Genv.initmem_inject. unfold Sk.load_mem in INIT_MEM. eauto.
  Qed.

  Lemma init_inject_ge :        
    skenv_inject skenv_link init_inject.
  Proof.
    admit "ez".
  Qed.

  Definition agree (j: meminj) (rs_src rs_tgt: regset) : Prop :=
    forall pr, Val.inject j (rs_src pr) (rs_tgt pr).

  Lemma system_symbols_inject j
        (SKINJ: skenv_inject skenv_link j)
    :
      symbols_inject j (System.globalenv skenv_link) tge.
  Proof.
    destruct match_skenv_link_tge. inv SKINJ.
    unfold System.globalenv. econs; ss; i.
    - unfold Genv.public_symbol, Genv.find_symbol.
      rewrite mge_symb. admit "should hold".
    - splits; ss; i.
      + exploit (DOMAIN b1).
        * eapply Genv.genv_symb_range. eauto.
        * i. clarify. split; auto.
          unfold Genv.find_symbol in *. rewrite mge_symb. auto.
      + exists b1. split.
        * eapply DOMAIN. eapply Genv.genv_symb_range. eauto.
        * unfold Genv.find_symbol in *. rewrite mge_symb. auto.
      + auto. rewrite <- (IMAGE _ _ _ H).
        unfold Genv.block_is_volatile, Genv.find_var_info, Genv.find_def in *.
        specialize (mge_defs b2). unfold fundef in *. inv mge_defs; ss.
        des_ifs; ss; clarify. des_ifs.
  Qed.

  Lemma external_function_sig
        v skd ef
        (FIND0: Genv.find_funct (System.globalenv skenv_link) v = Some (External ef))
        (FIND1: Genv.find_funct skenv_link v = Some skd)
    :
      SkEnv.get_sig skd = ef_sig ef
  .
  Proof.
    unfold System.globalenv in *. clarify.
  Qed.

  Section SYSTEM.
    
    Lemma system_function_ofs j b_src b_tgt delta fd
          (SKINJ: skenv_inject skenv_link j)
          (FIND: Genv.find_funct_ptr (System.globalenv skenv_link) b_src = Some fd)
          (INJ: j b_src = Some (b_tgt, delta))
    :
      delta = 0.
    Admitted.

    Lemma system_sig j b_src b_tgt delta ef
          (SKINJ: skenv_inject skenv_link j)
          (FIND: Genv.find_funct_ptr (System.globalenv skenv_link) b_src = Some (External ef))
          (INJ: j b_src = Some (b_tgt, delta))
      :
        Genv.find_funct_ptr tge b_tgt = Some (External ef).
    Admitted.

    Lemma system_receptive_at st frs
      :
        receptive_at (sem prog)
                     (State ((Frame.mk (System.modsem skenv_link) st) :: frs)).
    Admitted.
    
  End SYSTEM.
    
  Lemma asm_determinate_at p st
    :
      determinate_at (semantics p) st.
  Proof.
  Admitted.  

  Definition no_extern_fun (ge: Genv.t fundef unit): Prop :=
    forall b ef, ~ Genv.find_funct_ptr ge b = Some (External ef).

  Lemma local_genv_no_extern_fun p :
    no_extern_fun (local_genv p).
  Proof.
    admit "ez".
  Qed.

  Lemma asm_step_preserve_injection
        rs_src0 rs_src1 m_src0 m_src1 tr j0
        rs_tgt0 m_tgt0
        ge_src ge_tgt
        (GENVLE: genv_le ge_src ge_tgt)
        (DOMAIN: forall b (LT: Plt b ge_src.(Genv.genv_next)),
            j0 b = Some(b, 0))
        (NOEXTFUN: no_extern_fun ge_src)
        (AGREE: agree j0 rs_src0 rs_tgt0)
        (INJ: Mem.inject j0 m_src0 m_tgt0)
        (STEP: Asm.step ge_src (Asm.State rs_src0 m_src0) tr (Asm.State rs_src1 m_src1))
    :
      exists rs_tgt1 m_tgt1 j1,
        (Asm.step ge_tgt (Asm.State rs_tgt0 m_tgt0) tr (Asm.State rs_tgt1 m_tgt1)) /\
        (agree j1 rs_src1 rs_tgt1) /\
        (Mem.inject j1 m_src1 m_tgt1) /\
        (inject_incr j0 j1) /\
        (inject_separated j0 j1 m_src0 m_tgt0) 
  .
  Proof.
  Admitted.

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

(** ********************* calee initial *********************************)

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
        | RA => to_fake (rs_src RA)
        | _ => to_fake (rs_src pr)
        end
      end.

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
    - eapply to_fake_inj; eauto.
  Qed.

  Lemma src_init_rs_agree j sg blk ofs new_blk (rs_src rs_tgt: regset)
        (RSPPTR: rs_src # RSP = Vptr blk ofs true)
        (INJNONE: j new_blk = None)
        (AGREE: agree j rs_src rs_tgt)
    :
      agree (callee_injection j blk new_blk)
            (src_init_rs sg rs_src (Vptr new_blk ofs true)) rs_tgt.
  Proof.
    set (RSPAGREE := AGREE RSP).
    rewrite RSPPTR in *. inv RSPAGREE. eapply src_init_rs_agree'.
    - intros pr. specialize (AGREE pr).
      inv AGREE; econs; clarify; eauto; unfold callee_injection; des_ifs.
    - unfold callee_injection. rewrite <- H1. econs; auto. des_ifs; eauto.
  Qed.

  Inductive wf_init_rs (j: meminj) (rs_caller rs_callee: regset) : Prop :=
  | wf_init_rs_intro
      (PCSAME: rs_caller # PC = rs_callee # PC)
      (RAPTR: wf_RA (rs_callee # RA))
      (RASAME: to_fake (rs_caller # RA) = rs_callee # RA)
      (RSPSAME: inj_same j (rs_caller # RSP) (rs_callee # RSP))
      (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                              almost_eq (rs_caller (to_preg mr))
                                        (rs_callee (to_preg mr)))
  .    

  Lemma src_init_rs_wf j old_blk new_blk ofs (rs: regset) sg b' delta
        (INJ_NONE: j new_blk = None)
        (INJ_SOME: j old_blk = Some (b', delta))
        (TPTR: Val.has_type (rs RA) Tptr)
        (RADEF: rs RA <> Vundef)
        (RSRSP: rs # RSP = Vptr old_blk ofs true)
        (OFSZERO: ofs = Ptrofs.zero)
    :
      wf_init_rs
      (callee_injection j old_blk new_blk)
      rs
      (src_init_rs sg rs (Vptr new_blk ofs true)).
  Proof.
    econs; ss.
    - unfold src_init_rs. ss. destruct (rs RA); des_ifs; ss. des_ifs.
    - econs; eauto; ss.
      + unfold callee_injection. des_ifs. apply INJ_SOME.
      + unfold callee_injection. des_ifs.
    - intros. unfold src_init_rs. Opaque to_fake.
      destruct mr; ss; clarify; des_ifs; try econs; try apply to_fake_almost_eq.
  Qed.          

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
        (RETV: loc_result sg = One mr)
        (CALLEESAVE: forall mr, Conventions1.is_callee_save mr ->
                                Val.lessdef (init_rs mr.(to_preg)) (rs_callee mr.(to_preg)))
        (RSRA: rs_callee # PC = init_rs # RA)
        (RSRSP: rs_callee # RSP = init_rs # RSP)
        (RS: rs = (set_pair (loc_external_result sg) (rs_callee mr.(to_preg)) (Asm.regset_after_external rs_caller)) #PC <- (rs_caller RA))
    :
        agree j rs rs_tgt.
  Proof.
    inv WF. clarify.
    - unfold loc_external_result. rewrite RETV. ss.
      eapply update_agree; eauto; cycle 1.
      { eapply to_fake_inj2. rewrite RASAME. rewrite <- RSRA. auto. }
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
      fr frs p st init_rs0 init_rs1
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate init_rs1 st))
      (STACK: match_stack j init_rs1 frs)
      (WF: wf_init_rs j st.(st_rs) init_rs0)
      (IN: genv_le (local_genv p) tge)
    :
      match_stack j init_rs0 (fr::frs)
  .

  Inductive match_stack_call (j: meminj) : mem -> regset -> list Frame.t -> Prop :=
  | match_stack_call_init
      init_rs m
      (MEM: m = m_init)
      (INITRS: init_rs = initial_regset)
      (SIG: skenv_link.(Genv.find_funct) (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero) = Some (Internal signature_main))
    :
      match_stack_call j m init_rs nil
  | match_stack_call_cons
      fr frs p st init_rs0 init_rs1 m
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs1 st))
      (INITRS: init_rs0 = st.(st_rs))
      (STACK: match_stack j init_rs1 frs)
      (MEM: m = st.(st_m))
      (IN: genv_le (local_genv p) tge)
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

  Lemma f_hequal A (B : A -> Type) (f : forall a, B a)
        a1 a2 (EQ : a1 = a2)
    :
      f a1 ~= f a2.
  Proof.
    destruct EQ. econs.
  Qed.

  Lemma asm_frame_inj2 p1 p2 st1 st2
        (EQ : Frame.mk (modsem skenv_link p1) st1
              = Frame.mk (modsem skenv_link p2) st2)
    :
      local_genv p1 = local_genv p2.
  Proof.
    apply f_equal with (f := Frame.ms) in EQ. ss.
    apply f_hequal with (f := ModSem.globalenv) in EQ.
    apply JMeq_eq in EQ. ss.
  Qed.

(** ********************* arguments *********************************)

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

  Lemma src_init_rs_argument (rs: regset) m0 m1 sg rsp mr v
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

  Lemma arguments_loc sg sl delta ty
        (IN: In (S sl delta ty) (regs_of_rpairs (loc_arguments sg)))
    :
      sl = Outgoing /\
      0 <= delta /\
      4 * delta + size_chunk (chunk_of_type ty) <= 4 * size_arguments sg.
  Proof.
    generalize (loc_arguments_acceptable_2 _ _ IN). i. ss. des_ifs.
    set (loc_arguments_bounded _ _ _ IN).
    splits; eauto; [omega|].
    unfold typesize in *. des_ifs; ss; lia.
  Qed.

  Lemma tail_In A l0 l1 (a: A)
        (IN: In a l0)
        (TAIL: is_tail l0 l1)
    :
      In a l1.
  Proof.
    induction TAIL; auto.
    econs 2; eauto.
  Qed.        

  Lemma memcpy_argument
        (rs0 rs1: regset) m_src0 m_src1 m_src2 sg blk_old blk_new ofs delta ty v
        (RSRSP0: rs0 # RSP = Vptr blk_old ofs true)
        (RSRSP1: rs1 # RSP = Vptr blk_new ofs true)
        (OFS: ofs = Ptrofs.zero)
        (NEQ: blk_old <> blk_new)
        (FREE: freed_from m_src0 m_src1 blk_old 0 (4*size_arguments sg))
        (ALLOC: Mem.alloc m_src1 0 (4*size_arguments sg)
                = (m_src2, blk_new))
        (ARG: extcall_arg rs0 m_src0 (S Outgoing delta ty) v)
        (DELTA0: 0 <= delta)
        (SZ: 4 * size_arguments sg <= Ptrofs.modulus)
        (DELTA1: 4 * delta + size_chunk (chunk_of_type ty) <= 4 * size_arguments sg)
    :
      extcall_arg
        rs1
        (memcpy m_src2 blk_old blk_new) (S Outgoing delta ty) v.
  Proof.
    clarify. econs. refl. inv ARG.
    rewrite RSRSP0 in *. rewrite RSRSP1 in *. ss.
    assert (CHUNK: 0 < size_chunk (chunk_of_type ty)).
    { unfold size_chunk. destruct (chunk_of_type ty); lia. }
    eapply memcpy_load; eauto.
    - apply Ptrofs.unsigned_range.
    - rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr; [lia|].
      unfold Ptrofs.max_unsigned. lia.
  Qed.

  Lemma init_argument (rs: regset) ofs blk_old blk_new m_src0 m_src1 m_src2 sg l v
        (RSRSP: rs # RSP = Vptr blk_old ofs true)
        (OFSZERO: ofs = Ptrofs.zero)
        (NEQ: blk_old <> blk_new)
        (FREE: freed_from m_src0 m_src1 blk_old 0 (4*size_arguments sg))
        (ALLOC: Mem.alloc m_src1 0 (4*size_arguments sg)
                = (m_src2, blk_new))
        (ARG: extcall_arg rs m_src0 l v)
        (SZ: 4 * size_arguments sg <= Ptrofs.modulus)
        (IN: In l (regs_of_rpairs (loc_arguments sg)))
    :
      extcall_arg (src_init_rs sg rs (Vptr blk_new ofs true))
                  (memcpy m_src2 blk_old blk_new) l v.
  Proof.
    destruct l.
    - eapply src_init_rs_argument; eauto.
    - apply arguments_loc in IN. des. clarify.
      eapply memcpy_argument; eauto.
  Qed.      

  Lemma regs_of_rpair_In A (l: list (rpair A))
    :
      (forall r (IN: In (One r) l), In r (regs_of_rpairs l))
      /\ (forall r0 r1 (IN: In (Twolong r0 r1) l),
             In r0 (regs_of_rpairs l) /\ In r1 (regs_of_rpairs l)).
  Proof.
    induction l; i; ss; split; i; des; clarify; ss; eauto.
    - eapply in_or_app. eauto.
    - split; eapply in_or_app; right; eapply (IHl0 _ _ IN).
  Qed.

  Lemma memcpy_store_arguments
        rs m_src0 m_src1 m_src2 sg args blk_old blk_new ofs
        (ARGS: extcall_arguments rs m_src0 sg args)
        (RSRSP: rs # RSP = Vptr blk_old ofs true)
        (OFSZERO: ofs = Ptrofs.zero)
        (NEQ: blk_old <> blk_new)
        (SZ: 4 * size_arguments sg <= Ptrofs.modulus)
        (FREE: freed_from m_src0 m_src1
                          blk_old ofs.(Ptrofs.unsigned)
                                        (ofs.(Ptrofs.unsigned)+4*size_arguments sg))
        (ALLOC: Mem.alloc m_src1 ofs.(Ptrofs.unsigned)
                                       (ofs.(Ptrofs.unsigned)+4*size_arguments sg)
                = (m_src2, blk_new))
    :
      store_arguments
        m_src1
        (src_init_rs sg rs (Vptr blk_new ofs true))
        args sg (memcpy m_src2 blk_old blk_new).
  Proof.
    clarify; econs; eauto.
    - unfold extcall_arguments in *.
      revert args ARGS. generalize (is_tail_refl (loc_arguments sg)).
      assert (forall
                 l args
                 (TAIL: is_tail l (loc_arguments sg))
                 (ARGS: list_forall2 (extcall_arg_pair rs m_src0) l args)
               ,
                 list_forall2
                   (extcall_arg_pair (src_init_rs sg rs (Vptr blk_new Ptrofs.zero true))
                                     (memcpy m_src2 blk_old blk_new)) l args); auto.
      induction l; i; inv ARGS; econs; eauto.
      + inv H1; econs.
        * eapply init_argument; eauto.
          apply tail_In with (a := One l0) in TAIL; [|econs; eauto].
          eapply regs_of_rpair_In in TAIL. auto.
        * eapply init_argument; eauto.
          apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto].
          eapply regs_of_rpair_In in TAIL. tauto.
        * eapply init_argument; eauto.
          apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto].
          eapply regs_of_rpair_In in TAIL. tauto.
      + eapply IHl; auto.
        eapply is_tail_trans; eauto. econs 2. econs 1.
    - econs; ss; eauto.
      + refl.
      + intros b ofs0 IN PERM. des_ifs.
        * exfalso. apply IN. eapply Mem.perm_alloc_3; eauto.
        * f_equal. eapply PMap.gso; auto.
    - ss. ii. unfold Mem.perm. ss.
      eapply Mem.perm_alloc_2; eauto.
  Qed.    

  Local Opaque Mem.alloc.

(** ********************* match states *********************************)

  Definition different_owner (v0 v1 : val): Prop :=
    forall mod0 mod1
      (OWNER0: ge.(Ge.find_fptr_owner) v0 mod0)
      (OWNER1: ge.(Ge.find_fptr_owner) v1 mod1),
      mod0 <> mod1.

  Inductive match_states : Sem.state -> Asm.state -> nat -> Prop :=
  | match_states_intro
      j fr frs p init_rs rs_src rs_tgt m_src m_tgt n
      (AGREE: agree j rs_src rs_tgt)
      (INJ: Mem.inject j m_src m_tgt)
      (GELE: genv_le (local_genv p) tge) 
      (GEINJECT: skenv_inject skenv_link j)      
      (FRAME: fr = Frame.mk (AsmC.modsem skenv_link p)
                            (AsmC.mkstate init_rs (Asm.State rs_src m_src)))
      (STACK: match_stack j init_rs frs)
      (* (RAPTR: wf_RA (init_rs RA)) *)
      (ORD: n = if (external_state (local_genv p) (rs_src # PC))
                then (length frs + 2)%nat else 0%nat)
    :
      match_states (State (fr::frs)) (Asm.State rs_tgt m_tgt) n
  | match_states_call
      j init_rs frs args m_src rs_tgt m_tgt ofs blk sg n
      (STACK: match_stack_call j m_src init_rs frs)
      (AGREE: agree j init_rs rs_tgt)
      (INJECT: Mem.inject j m_src m_tgt)
      (GEINJECT: skenv_inject skenv_link j)
      (FPTR: args.(Args.fptr) = init_rs # PC)
      (SIG: exists skd, skenv_link.(Genv.find_funct) args.(Args.fptr)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (ARGS: extcall_arguments init_rs m_src sg args.(Args.vs))
      (RSPPTR: init_rs # RSP = Vptr blk ofs true)
      (NOTVOL: Senv.block_is_volatile skenv_link blk = false) 
      (OFSZERO: ofs = Ptrofs.zero)
      (* (RAPTR: wf_RA (init_rs RA)) *)
      (RAPTR: <<TPTR: Val.has_type (init_rs RA) Tptr>> /\ <<RADEF: init_rs RA <> Vundef>>)
      (FREE: freed_from m_src args.(Args.m) blk ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg)))
      (ORD: n = 1%nat)
    :
      match_states (Callstate args frs) (Asm.State rs_tgt m_tgt) n.


(** ********************* transf initial final  *********************************)

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
        admit "This should hold..".
      + eapply init_inject_ge.
      + unfold initial_regset.
        rewrite Pregmap.gso; clarify.
        rewrite Pregmap.gso; clarify. ss.
        rewrite Pregmap.gss. unfold tge.
        set (MAIN:= symb_main).
        unfold Genv.symbol_address. unfold skenv_link, tge in *. rewrite MAIN. auto.
      + econs.
      + admit "should hold".
      + apply init_mem_freed_from.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r n,
      match_states st1 st2 n -> Sem.final_state st1 r -> Asm.final_state st2 r.
  Proof.
    intros st_src st_tgt r n MTCHST FINAL. inv FINAL. inv MTCHST. ss.
    inv FINAL0. clarify. inv STACK. econs.
    - specialize (AGREE PC). rewrite RSRA in *. rewrite RSRA0 in *.
      inv AGREE; ss.
    - des. rewrite RSPC in *. exploit local_global_consistent; eauto. intro SGEQ. rewrite <- SGEQ in *. clarify.
      ss. unfold signature_main, loc_arguments, loc_result in *.
      Transparent Archi.ptr64. ss. unfold loc_result_64 in *. ss. clarify.
      ss. specialize (AGREE RAX). rewrite INT in *. inv AGREE; auto.
  Qed.  

(** ********************* transf step  *********************************)

  Lemma asm_step_internal_simulation
        st_src0 st_src1 st_tgt0 tr frs p init_rs n0
        (STEP: Asm.step (local_genv p) st_src0 tr st_src1)
        (MTCHST: match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                                (AsmC.mkstate init_rs st_src0))::frs))
                              st_tgt0 n0)
    :
      exists st_tgt1 n1,
        Asm.step tge st_tgt0 tr st_tgt1 /\
        match_states (State ((Frame.mk (AsmC.modsem skenv_link p)
                                       (AsmC.mkstate init_rs st_src1))::frs))
                     st_tgt1 n1.
  Proof. 
    inv MTCHST. dup FRAME. apply asm_frame_inj in FRAME0.
    apply asm_frame_inj2 in FRAME. inv FRAME0. destruct st_src1.
    rewrite <- FRAME in GELE.
    exploit asm_step_preserve_injection; eauto.
    - inv GEINJECT. i. eapply DOMAIN.
      eapply sub_mge_next in GELE. destruct match_skenv_link_tge. 
      rewrite <- mge_next. eapply Plt_Ple_trans; eauto.
    - eapply local_genv_no_extern_fun.
    - ii. des. esplits; eauto; econs; eauto.
      + 
        {
          clear - INJ H2 H3 GEINJECT.
          inv GEINJECT. econs.
          - i. unfold inject_incr in *. 
            eapply H2. eapply DOMAIN. eauto.
          - i. ss.
            destruct (Genv.block_is_volatile skenv_link b2) eqn:EQ1;
            destruct (Genv.block_is_volatile skenv_link b1) eqn:EQ2;
            auto; rewrite <- EQ1; rewrite <- EQ2; eapply IMAGE.

            + set (Genv.block_is_volatile_below _ _ EQ1).
              destruct (j b1) eqn : EQ.
              * destruct p0. apply H2 in EQ. clarify.
              * exfalso. eapply H3 in EQ. specialize (EQ INJ0). des.
                inv INJ. unfold Mem.valid_block in *. eauto.
            + eapply Genv.block_is_volatile_below in EQ2.
              set (DOMAIN _ EQ2).
              set (H2 _ _ _ e). clarify. auto.
        }
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
    inv RSPSAME. rewrite RSRSP0 in *. rewrite INITRSP in *. clarify.
    rewrite PCSAME in *. des. ss. clarify. esplits.
    econs; simpl in *.
    - eapply callee_save_agree; eauto.
      etrans; eauto. 
    - eapply unfree_free_inj; eauto. 
      + instantiate (1 := Ptrofs.zero).
        rewrite Ptrofs.unsigned_zero. rewrite Z.add_0_l.
        rp; eauto. repeat f_equal.
        eapply local_global_consistent; try apply GELE; eauto.
      + econs; eauto.
    - eapply IN.
    - ss.
    - unfold Frame.update_st. s. repeat f_equal. eapply local_global_consistent; try apply GELE; eauto.
    - ss.
    - ss.
    - des_ifs. omega.
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
    - econs; eauto.
    - eapply free_freed_from; eauto.
  Qed.

  Lemma below_block_is_volatile F V (ge': Genv.t F V) b
        (LE: ~ Plt b (Genv.genv_next ge'))
    :
      Genv.block_is_volatile ge' b = false.
  Proof.
    destruct (Genv.block_is_volatile ge' b) eqn: EQ; auto.
    apply Genv.block_is_volatile_below in EQ.
    exfalso. auto.
  Qed.    

  Lemma asm_step_init_simulation
        args frs st_tgt p n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
        (OWNER: valid_owner args.(Args.fptr) p)
    :
      exists rs m,
        (AsmC.initial_frame skenv_link p args (AsmC.mkstate rs (Asm.State rs m))) /\
        (match_states (State ((Frame.mk (AsmC.modsem skenv_link p) (AsmC.mkstate rs (Asm.State rs m))) :: frs)) st_tgt 0).
  Proof.
    inv MTCHST. dup OWNER. apply valid_owner_genv_le in OWNER0.
    inv OWNER. des. ss.
    set (nextblock_unvalid := nextblock_unvalid INJECT).
    destruct (Mem.alloc args.(Args.m) 0 (4 * size_arguments (fn_sig fd))) eqn:MEQ.
    assert (Genv.find_funct skenv_link (Args.fptr args) =
            Some (Internal (fn_sig fd))).
    { clear - FINDF OWNER0. dup OWNER0.
      unfold Genv.find_funct, Genv.find_funct_ptr in *.
      exploit sub_match_local_genv; eauto. intros MATCHGE.
      set (sub_mge_defs MATCHGE).
      des_ifs; specialize (e b _ Heq1); des; clarify. }
    clarify. ss.
    exists (src_init_rs (fn_sig fd) init_rs (Vptr b Ptrofs.zero true)).
    exists (memcpy m blk b).
    assert (BNEQ: blk <> b).
    { intros BEQ. rewrite (Mem.alloc_result _ _ _ _ _ MEQ) in BEQ.
      clarify. specialize (AGREE RSP). rewrite RSPPTR in *.
      inv AGREE. rewrite (freed_from_nextblock FREE) in *. clarify.
    }    esplits; eauto.
    - econs.
      + apply (eq_refl (fn_sig fd)).
      + apply FINDF.
      + ss.
      + ss.
      + clear - GEINJECT INJECT FREE.
        erewrite freed_from_nextblock; eauto.
        set (LE:=Registers.Regset.MSet.Raw.MX.OrderTac.TO.lt_total
                 (Senv.nextblock skenv_link) (Mem.nextblock m_src)). des.
        * apply Plt_Ple. auto.
        * rewrite LE. refl.
        * inv GEINJECT. apply DOMAIN in LE.
          inv INJECT. unfold Mem.valid_block in *.
          specialize (mi_freeblocks _ (Plt_strict (Mem.nextblock m_src))).
          clarify.
      + eapply memcpy_store_arguments; ss; eauto.
      + unfold src_init_rs. ss.
        destruct (init_rs RA); ss; eauto. destruct b1; ss; eauto.
      + apply src_init_rs_PTRFREE.
    - rewrite <- (freed_from_nextblock FREE) in *.
      rewrite <- (Mem.alloc_result _ _ _ _ _ MEQ) in *.
      econs.
      + instantiate (2 := callee_injection j blk b).
        eapply src_init_rs_agree; eauto.
      + eapply memcpy_inject; eauto.
      + eapply valid_owner_genv_le. econs; eauto.
      + unfold callee_injection. inv GEINJECT. econs; i.
        { des_ifs; eauto. exploit (DOMAIN b); auto. i. clarify. }
        des_ifs; [| eauto].
        rewrite (IMAGE _ _ _ INJ). ss. rewrite NOTVOL.
        symmetry. eapply below_block_is_volatile. intros EQ.
        eapply DOMAIN in EQ. clarify.
      + reflexivity.
      + inv STACK.
        { econs; ss. }
        econs; ss.
        * eapply match_stack_incr; [|eauto].
          apply callee_injection_incr; auto.
        * set (AGREERSP := AGREE RSP).
          rewrite RSPPTR in AGREERSP. inv AGREERSP.
          eapply src_init_rs_wf; eauto.
      + unfold external_state.
        des_ifs; exfalso; unfold src_init_rs, local_genv in *; ss;
        rewrite <- FPTR in *; rewrite Heq0 in *; ss; des_ifs.
  Qed.

  Lemma step_init_simulation
        args frs st_tgt p n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
        (OWNER: valid_owner args.(Args.fptr) p)
    :
      exists st_src,
        step ge (Callstate args frs) E0 st_src /\ match_states st_src st_tgt 0.
  Proof.
    exploit asm_step_init_simulation; eauto. inv OWNER.
    i. des. esplits; try eassumption.
    econs; eauto.
  Qed.

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
      unfold local_genv, fundef in *. clarify.
    - apply f_equal with (f := Frame.ms) in FRAME. ss.
      inv FRAME. apply Eqdep.EqdepTheory.inj_pair2 in H0. auto.
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

  Lemma owner_asm_or_system fptr ms
        (OWNER: Ge.find_fptr_owner ge fptr ms)
    :
      (<<ASMMOD: exists p, ms= AsmC.modsem skenv_link p >>)\/
      (<<SYSMOD: ms = System.modsem skenv_link>>).
  Proof.
    inv OWNER. clear - MODSEM. unfold ge in *.
    unfold load_genv, load_modsems, prog, flip in *.
    ss. des; auto.
    left. generalize progs ms MODSEM.
    intros l. induction l; ss; i. des; eauto. 
  Qed.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner ge fptr ms0)
        (FIND1: Ge.find_fptr_owner ge fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    eapply SemProps.find_fptr_owner_determ; ss;
      rewrite LINK_SK; eauto.
  Qed.

  Lemma init_case st args frs fptr
        (STATE: st = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
    :
      (<<ASMMOD: exists p, valid_owner fptr p>>) \/
      (<<SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link)>>) \/
      (<<UNSAFE: ~ safe (sem prog) st>>).
  Proof.
    destruct (classic (exists ms, Ge.find_fptr_owner ge args.(Args.fptr) ms)) as [[ms OWNER] | NOOWNER].   
    - destruct (owner_asm_or_system OWNER); des; clarify.
      + destruct (classic (valid_owner args.(Args.fptr) p)); eauto.
        right. right. intros SAFE. exploit SAFE; [econs|].
        i. des.
        * inv H0.
        * inv H0. apply H.
          revert MSFIND st_init INIT. intros MSFIND.
          ss. rewrite LINK_SK in *.
          rewrite <- (find_fptr_owner_determ OWNER MSFIND) in *. i.
          inv INIT. econs; eauto.
      + right. left. clarify.
    - right. right. intros SAFE. clarify. exploit SAFE; [econs|].
      i. des.
      + inv H.
      + inv H. ss. rewrite LINK_SK in *. eauto.
  Qed.

  Lemma call_step_noevent ge' args frs st1 tr
        (STEP: step ge' (Callstate args frs) tr st1)
    :
      E0 = tr.
  Proof. inv STEP. auto. Qed.

  Lemma extcall_arg_inject j rs_src rs_tgt m_src m_tgt l v_src  
        (AGREE: agree j rs_src rs_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
        (ARG: extcall_arg rs_src m_src l v_src)
    :
      exists v_tgt,
        extcall_arg rs_tgt m_tgt l v_tgt /\
        Val.inject j v_src v_tgt.
  Proof.
    inv ARG.
    - exists (rs_tgt (preg_of r)). split; eauto. econs.
    - eapply Mem.loadv_inject in H0; des; eauto.
      + esplits; eauto. econs; eauto.
      + ss. specialize (AGREE RSP).
        destruct (rs_src RSP); clarify.
        inv AGREE; ss. econs; eauto.
        rewrite Ptrofs.add_assoc. 
        rewrite Ptrofs.add_assoc. f_equal.
        apply Ptrofs.add_commut.
  Qed.

  Lemma extcall_arguments_inject sg j rs_src rs_tgt m_src m_tgt args_src 
        (AGREE: agree j rs_src rs_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
        (ARGS: extcall_arguments rs_src m_src sg args_src)
    :
      exists args_tgt,
        extcall_arguments rs_tgt m_tgt sg args_tgt /\
        Val.inject_list j args_src args_tgt.
  Proof.
    unfold extcall_arguments in *.
    revert args_src ARGS. induction (loc_arguments sg); i; ss.
    - inv ARGS. exists []. split; econs.
    - inv ARGS. inv H1.
      + eapply extcall_arg_inject in H; eauto. apply IHl in H3. des.
        exists (v_tgt :: args_tgt). split.
        * econs; eauto. econs; eauto.
        * econs; eauto.
      + eapply extcall_arg_inject in H; eauto.
        eapply extcall_arg_inject in H0; eauto. apply IHl in H3. des.
        exists (Val.longofwords v_tgt0 v_tgt :: args_tgt). split.
        * econs; eauto. econs; eauto.
        * econs; eauto. eapply Val.longofwords_inject; eauto.
  Qed.

  Lemma syscall_receptive
        st_src0 st_src1 st_tgt0 args frs fptr tr0 n0
        (STATE: st_src0 = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
        (SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link))
        (MTCHST: match_states st_src0 st_tgt0 n0)
        (STEP0: Sem.step ge st_src0 tr0 st_src1)
    :
      receptive_at (sem prog) st_src1.
  Proof.
    clarify. inv STEP0.
    destruct (find_fptr_owner_determ SYSMOD MSFIND).
    eapply system_receptive_at.
  Qed.  


  Lemma syscall_simulation
        st_src0 st_src1 st_src2 st_tgt0 args frs fptr tr0 tr1 n0
        (STATE: st_src0 = Callstate args frs)
        (FPTR: fptr = args.(Args.fptr))
        (SYSMOD: ge.(Ge.find_fptr_owner)
                      fptr (System.modsem skenv_link))
        (MTCHST: match_states st_src0 st_tgt0 n0)
        (STEP0: Sem.step ge st_src0 tr0 st_src1)
        (STEP1: Sem.step ge st_src1 tr1 st_src2)
    :
      receptive_at (sem prog) st_src2 /\
      exists st_tgt1 n1,
        (<< STEPTGT: Asm.step tge st_tgt0 tr1 st_tgt1 >>) /\
        (<< MTCHST: forall st_src3 tr2
                           (STEP2: Sem.step ge st_src2 tr2 st_src3),
            match_states st_src3 st_tgt1 n1 /\ tr2 = E0>>) /\
        (n1 < length frs + 3)%nat.
  Proof.
    clarify; inv MTCHST; inv STEP0; ss.
    destruct (find_fptr_owner_determ SYSMOD MSFIND). ss. inv INIT.
    inv STEP1; ss; [|inv FINAL]. inv STEP.    
    exploit extcall_arguments_inject; eauto.
    i. des.
    exploit external_call_mem_inject_gen.
    - eapply system_symbols_inject; eauto.
    - eapply EXTCALL.
    - eapply freed_from_inject; eauto.
    - eauto.
    - i. des.
      unfold Frame.update_st. ss.
      split.
      { eapply system_receptive_at. }
      exists (Asm.State
                ((set_pair (loc_external_result (ef_sig ef)) vres'
                           (regset_after_external rs_tgt)) #PC <- (rs_tgt RA))
                m2').
      inv STACK.
      { exfalso. clarify.
        rewrite FPTR in *.
        unfold System.globalenv, initial_regset in *. unfold Pregmap.set in *. ss. clarify.
      }
      assert (SIGEQ: SkEnv.get_sig skd = ef_sig ef).
      { eapply external_function_sig; eauto. }
      exists (
        if
          external_state (local_genv p)
                         ((set_pair (loc_external_result (ef_sig ef)) (Retv.v retv)
                                    (regset_after_external st.(st_rs))) # PC <- (st.(st_rs) RA) PC)
        then (length frs0 + 2)%nat
        else 0%nat).
      splits.
      + set (AGREEPC:= AGREE PC). rewrite <- FPTR in *.
        destruct (Args.fptr args) eqn:EQ; ss; des_ifs; clarify. inv AGREEPC.       
        econs 3.
        * instantiate (1 := b2).
          assert (delta = 0); clarify.
          eapply system_function_ofs; eauto.
        * instantiate (1 := ef).
          eapply system_sig; eauto.
        * instantiate (1 := args_tgt).
          rewrite <- SIGEQ. auto.
        * eapply H1.
        * auto.
      + i. inv STEP2; [inv AT|inv STEP|]. inv FINAL. split; auto.
        ss. unfold Frame.update_st. ss. inv AFTER. ss. clarify.
        assert (SGEQ: sg = ef_sig ef).
        { des. rewrite FPTR in *. clarify. } clarify.
        econs; cycle 3.
        * instantiate (1 := f').
          { inv GEINJECT. econs.
            - i. unfold inject_incr in *. 
              eapply H6. eapply DOMAIN. eauto.
            - i. unfold inject_incr,inject_separated in *.
              destruct (j b1) eqn : EQ.
              + destruct p0. dup EQ.
                apply H6 in EQ. clarify.
                eapply IMAGE in EQ0. auto.

              + ss. specialize (H7 _ _ _ EQ INJ). des.
                unfold Mem.valid_block in *.
                erewrite below_block_is_volatile; cycle 1.
                { intros LE. specialize (DOMAIN _ LE).
                  clear - INJECT H8 DOMAIN.
                  inv INJECT.
                  eapply mi_mappedblocks in DOMAIN. auto. }
                erewrite below_block_is_volatile. auto.
                { intros LE. specialize (DOMAIN _ LE). clarify. }                
          }
        * ss.
        * eapply match_stack_incr; eauto.
        * ss.
        * unfold set_pair. des_ifs; repeat (eapply update_agree2; eauto).
          -- unfold regset_after_external.
             intros []; des_ifs; try econs; eauto.
          -- unfold regset_after_external.
             intros []; des_ifs; try econs; eauto.
          -- eapply Val.hiword_inject; eauto.
          -- eapply Val.loword_inject; eauto.
        * set (AGREE RSP). rewrite RSPPTR in *. clarify.
          inv i.
          eapply private_unfree_inj; eauto.          
          { ii. rewrite Ptrofs.unsigned_zero in *.
            exploit Mem.unchanged_on_perm; eauto.
            - eapply freed_from_out_of_reach; eauto. rewrite SIGEQ. eauto.
            - eapply Mem.mi_mappedblocks; eauto.
            - intros PERM. eapply PERM.
              exploit Mem.perm_inject; eauto.
              eapply freed_from_perm; eauto. instantiate (1:=ofs-delta).
              rewrite SIGEQ. omega.
              i. replace ofs with (ofs - delta + delta); [auto|omega].
          }
          i. eapply separated_out_of_reach; cycle 2; eauto.          
          -- eapply Mem.mi_mappedblocks; eauto.
          -- eapply freed_from_out_of_reach; eauto.
             rewrite Ptrofs.unsigned_zero in *. rewrite SIGEQ. omega.
          -- i. eapply ec_max_perm; eauto. eapply external_call_spec.
          -- eapply freed_from_inject; eauto.
        * ss.
      + ss. des_ifs; omega.
  Qed.
  
  Lemma match_states_call_ord_1 args frs st_tgt n
        (MTCHST: match_states (Callstate args frs) st_tgt n)
    :
      1%nat = n.
  Proof. inv MTCHST. auto. Qed.

  Lemma src_receptive_at st_src st_tgt n
        (MTCHST: match_states st_src st_tgt n)
    :
      receptive_at (sem prog) st_src.
  Proof.    
    inv MTCHST; ss.
    - eapply SemProps.lift_receptive_at. ss.
      eapply AsmC.lift_receptive_at.
      eapply semantics_receptive.
      intros EXTERN. eapply not_external in EXTERN. auto.
    - econs; i.
      + set (STEP := H). inv STEP. inv H0. eexists. eauto.
      + ii. inv H. ss. omega.
  Qed.
  
  Lemma match_state_xsim
    :
      forall st_src st_tgt n (MTCHST: match_states st_src st_tgt n),
        xsim (sem prog) (semantics tprog) lt n st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold. destruct st_src.
    - exploit init_case; ss.
      instantiate (1:=frs). instantiate (2:=args). i. des.
      + destruct (match_states_call_ord_1 MTCHST).
        right. econs; i.
        * exfalso. inv MTCHST. inv FINALTGT. inv ASMMOD.
          inv MSFIND. unfold Genv.find_funct in *. des_ifs.
          specialize (AGREE PC). rewrite <- FPTR in *.
          inv AGREE. unfold Vnullptr in *. des_ifs. congruence.
        * exploit step_init_simulation; try eassumption.
          i. des. econs 2; ss; eauto. rewrite LINK_SK.
          split; auto. apply star_one. eauto.
      + left. econs.
        { i. exfalso. inv FINALSRC. }
        econs; [|eapply src_receptive_at; eauto].
        i.
        destruct (call_step_noevent STEPSRC).
        destruct (match_states_call_ord_1 MTCHST).
        exists 0%nat. exists st_tgt. split.
        { right. split; [apply star_refl|omega]. }
        left. pfold. left.
        econs.
        { i. exfalso. inv STEPSRC. ss. rewrite LINK_SK in *.
          destruct (find_fptr_owner_determ SYSMOD MSFIND).
          inv INIT. inv FINALSRC. inv FINAL.
        }
        econs; cycle 1.
        { inv STEPSRC. ss. rewrite LINK_SK in *.
          destruct (find_fptr_owner_determ SYSMOD MSFIND). ss.
          eapply system_receptive_at.
        }
        i. exists (length frs + 3)%nat. ss. rewrite LINK_SK in *.
        exploit syscall_simulation; eauto.
        i. des. exists st_tgt1. split.
        { left. apply plus_one. econs; [apply asm_determinate_at|]. auto. }
        left. pfold. left.
        econs.
        {
          i. exfalso. inv STEPSRC. ss.
          destruct (find_fptr_owner_determ SYSMOD MSFIND).
          inv INIT. inv STEPSRC0; ss; [|inv FINAL].
          inv STEP. inv FINALSRC. ss. inv MTCHST.
          inv STACK. inv SYSMOD. ss.
          unfold System.globalenv in *.
          clear - FPTR SIG0 FPTR0.
          unfold initial_regset, Pregmap.set in *. des_ifs.
          rewrite FPTR0 in *. clarify.
        }
        econs; auto.
        i.
        ss. rewrite LINK_SK in *. apply MTCHST0 in STEPSRC1. des. clarify.
        exists n1, st_tgt1. split.
        { right. split; auto. apply star_refl. }
        right. eauto.
      + right. econs; i; try (exfalso; eauto).          
    - left. econs.
      + i. econs.
        * exploit transf_final_states; eauto.
        * i. inv FINAL0. inv FINAL1. eq_closure_tac.
        * ii. inv FINAL. inv H; eq_closure_tac.
      + econs.
        * i. ss. rewrite LINK_SK in *.
          exploit normal_state_fsim_step; eauto.
          i. des; esplits; eauto.
          -- left. econs; ss.
             ++ econs; eauto.
                apply asm_determinate_at.
             ++ econs 1.
             ++ rewrite E0_right. auto.
          -- right. econs; ss. clarify. econs.
        * eapply src_receptive_at; eauto.
  Qed.

  Lemma transf_xsim_properties
    :
        xsim_properties (sem prog) (semantics tprog) nat lt.
  Proof.
    econs; [apply lt_wf| |apply symb_preserved].
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - i. inv INIT0. inv INIT1. clarify.
    - apply match_state_xsim; eauto.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Sem.sem prog) (Asm.semantics tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.    

End PRESERVATION.


Require Import BehaviorsC.

Theorem lower_bound_correct
        (asms: list Asm.program)
  :
    (<<INITUB: program_behaves (sem (map AsmC.module asms)) (Goes_wrong E0)>>) \/
    exists link_tgt,
      (<<TGT: link_list asms = Some link_tgt>>)
      /\ (<<REFINE: improves (sem (map AsmC.module asms)) (Asm.semantics link_tgt)>>)
.
Proof.
  destruct (link_sk (map module asms)) eqn:T; cycle 1.
  { left. econs 2. ii. ss. inv H. clarify. }
  destruct (Sk.load_mem t) eqn:T2; cycle 1.
  { left. econs 2. ii. ss. inv H. clarify. }
  right.
  exploit link_sim; eauto. i; des.
  rewrite TGT. esplits; eauto.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  eapply transf_program_correct; eauto.
Qed.

