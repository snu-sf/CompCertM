Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Simulation Ctypes Cop Ctyping Csyntax ClightC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import MatchSimModSem.
Require Import mktac.
Require Import IntegersC.
Require Import IdSimExtra ClightStepInj.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

Inductive match_states_ext_clight
  : unit -> state -> state -> SimMemExt.t' -> Prop :=
| match_ext_State
    fn stmt K_src K_tgt env_src env_tgt tenv_src tenv_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (ENV: match_env inject_id env_src env_tgt)
    (TENV: match_temp_env inject_id tenv_src tenv_tgt)
    (CONT: match_cont inject_id K_src K_tgt):
    match_states_ext_clight
      tt
      (State fn stmt K_src env_src tenv_src m_src)
      (State fn stmt K_tgt env_tgt tenv_tgt m_tgt)
      sm0
| match_ext_Callstate
    fptr_src fptr_tgt ty args_src args_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (INJ: Val.lessdef fptr_src fptr_tgt)
    (VALS: Val.lessdef_list args_src args_tgt)
    (CONT: match_cont inject_id K_src K_tgt):
    match_states_ext_clight
      tt
      (Callstate fptr_src ty args_src K_src m_src)
      (Callstate fptr_tgt ty args_tgt K_tgt m_tgt)
      sm0
| match_ext_Returnstate
    retv_src retv_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (INJ: Val.lessdef retv_src retv_tgt)
    (CONT: match_cont inject_id K_src K_tgt):
    match_states_ext_clight
      tt
      (Returnstate retv_src K_src m_src)
      (Returnstate retv_tgt K_tgt m_tgt)
      sm0.

Section CLIGHTEXT.

  Variable se: Senv.t.
  Variable ge: genv.

  Definition function_entry_extends
             (function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) :=
      forall fn vs_src vs_tgt m_src0 m_tgt0 en tenv_src m_src1
        (MWF: Mem.extends m_src0 m_tgt0)
        (VALS: Val.lessdef_list vs_src vs_tgt)
        (ENTRY: function_entry ge fn vs_src m_src0 en tenv_src m_src1),
      exists tenv_tgt m_tgt1,
        (<<MWF: Mem.extends m_src1 m_tgt1>>) /\
        (<<TENV: match_temp_env inject_id tenv_src tenv_tgt>>) /\
        (<<ENTRY: function_entry ge fn vs_tgt m_tgt0 en tenv_tgt m_tgt1>>).

  Variable function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
  Hypothesis FUNCTIONENTRY: function_entry_extends function_entry.

  Lemma alloc_variables_extends idl en_src0 en_tgt0 en_src1 m_src0 m_tgt0 m_src1
        (ALLOC: alloc_variables ge en_src0 m_src0 idl en_src1 m_src1)
        (ENV: match_env inject_id en_src0 en_tgt0)
        (MWF: Mem.extends m_src0 m_tgt0):
      exists m_tgt1 en_tgt1,
        (<<MWF: Mem.extends m_src1 m_tgt1>>) /\
        (<<ENV: match_env inject_id en_src1 en_tgt1>>) /\
        (<<ALLOC: alloc_variables ge en_src0 m_tgt0 idl en_src1 m_tgt1>>).
  Proof.
    revert m_src0 m_src1 m_tgt0 en_src0 en_tgt0 en_src1 ALLOC ENV MWF. induction idl.
    - i. inv ALLOC. esplits; eauto. econs; eauto.
    - i. inv ALLOC.
      exploit Mem.alloc_extends; eauto; try refl. i. des.
      exploit IHidl; eauto.
      { instantiate (1:=PTree.set id (b1, ty) en_tgt0). ii.
        repeat rewrite PTree.gsspec. des_ifs. left. esplits; ss. } i. des.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma assign_loc_extends ce ty m_src0 m_tgt0 v_src v_tgt m_src1 blk ofs
        (ASSIGN: assign_loc ce ty m_src0 blk ofs v_src m_src1)
        (VAL: Val.lessdef v_src v_tgt)
        (MWF: Mem.extends m_src0 m_tgt0):
      exists m_tgt1,
        (<<ASSIGN: assign_loc ce ty m_tgt0 blk ofs v_tgt m_tgt1>>) /\
        (<<MWF: Mem.extends m_src1 m_tgt1>>).
  Proof.
    inv ASSIGN.
    - exploit Mem.storev_extends; eauto. i. des. esplits; eauto. econs 1; eauto.
    - cinv VAL.
      exploit Mem.loadbytes_extends; eauto. i. des_safe.
      exploit Mem.storebytes_within_extends; eauto. i. des_safe.
      esplits; eauto. econs 2; eauto.
  Qed.

  Lemma match_env_inject_id en:
      match_env inject_id en en.
  Proof.
    ii. destruct (en ! id) eqn:ENV; eauto. destruct p. left. esplits; ss.
  Qed.

  Lemma bind_parameters_extends e_src e_tgt m_src0 m_tgt0 idl vargs_src vargs_tgt m_src1
        (BIND: bind_parameters ge e_src m_src0 idl vargs_src m_src1)
        (ENV: match_env inject_id e_src e_tgt)
        (MWF: Mem.extends m_src0 m_tgt0)
        (VALS: Val.lessdef_list vargs_src vargs_tgt):
      exists m_tgt1,
        (<<MWF: Mem.extends m_src1 m_tgt1>>) /\
        (<<BIND: bind_parameters ge e_tgt m_tgt0 idl vargs_tgt m_tgt1>>).
  Proof.
    revert m_src0 m_tgt0 ENV vargs_src vargs_tgt m_src1 MWF VALS BIND. induction idl.
    - i. inv BIND. inv VALS. esplits; eauto. econs.
    - i. inv BIND. inv VALS. destruct (ENV id); des; clarify. unfold inject_id in *. clarify.
      exploit assign_loc_extends; eauto. i. des. clarify.
      exploit IHidl; try apply H6; eauto. i. des.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma function_entry2_extends: function_entry_extends function_entry2.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_extends; eauto.
    { eapply match_env_inject_id. } i. des.
    exploit bind_parameter_temps_inject; eauto.
    { eapply create_undef_temps_match. }
    { eapply val_inject_list_lessdef. eauto. } i. des.
    esplits; eauto. econs; eauto.
  Qed.

  Lemma function_entry1_extends:
      function_entry_extends function_entry1.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_extends; eauto.
    { eapply match_env_inject_id. } i. des.
    clear ENV.
    exploit bind_parameters_extends; eauto.
    { eapply match_env_inject_id. } i. des.
    esplits; eauto; try econs; eauto. eapply create_undef_temps_match.
  Qed.

  Lemma bool_val_extends m_src m_tgt ty v_src v_tgt b
        (VAL: Val.lessdef v_src v_tgt)
        (MWF: Mem.extends m_src m_tgt)
        (BVAL: bool_val v_src ty m_src = Some b):
      bool_val v_tgt ty m_tgt = Some b.
  Proof.
    unfold bool_val in *. cinv VAL; des_ifs; ss; clarify.
    exploit Mem.weak_valid_pointer_extends; eauto. i. clarify.
  Qed.

  Lemma sem_unary_operation_extends m_src m_tgt op v_src0 v_tgt0 v_src1 ty
        (EXT: Mem.extends m_src m_tgt)
        (VAL: Val.lessdef v_src0 v_tgt0)
        (SEM: sem_unary_operation op v_src0 ty m_src = Some v_src1)
    :
      exists v_tgt1,
        (<<SEM: sem_unary_operation op v_tgt0 ty m_tgt = Some v_tgt1>>) /\
        (<<VAL: Val.lessdef v_src1 v_tgt1>>).
  Proof.
    destruct op; ss.
    - unfold sem_notbool, option_map in *. des_ifs_safe. erewrite bool_val_extends; eauto.
    - unfold sem_notint in *. cinv VAL; des_ifs; esplits; eauto.
    - unfold sem_neg in *. cinv VAL; des_ifs; esplits; eauto.
    - unfold sem_absfloat in *. cinv VAL; des_ifs; esplits; eauto.
  Qed.

  Lemma sem_binary_operation_extends ce m_src m_tgt op
        v_src0 v_tgt0 v_src1 v_tgt1 v_src2 ty0 ty1
        (SEM: sem_binary_operation ce op v_src0 ty0 v_src1 ty1 m_src = Some v_src2)
        (EXT: Mem.extends m_src m_tgt)
        (VAL0: Val.lessdef v_src0 v_tgt0)
        (VAL1: Val.lessdef v_src1 v_tgt1):
      exists v_tgt2,
        (<<SEM: sem_binary_operation ce op v_tgt0 ty0 v_tgt1 ty1 m_tgt = Some v_tgt2>>) /\
        (<<VAL: Val.lessdef v_src2 v_tgt2>>).
  Proof.
    exploit sem_binary_operation_inj; try eassumption.
    - instantiate (1:=m_tgt). instantiate (1:=fun b => Some (b, 0)).
      i. ss. clarify. psimpl. eapply Mem.valid_pointer_extends; eauto.
    - i. ss. clarify. psimpl. eapply Mem.weak_valid_pointer_extends; eauto.
    - i. ss. clarify. psimpl. zsimpl. eapply Ptrofs.unsigned_range_2; eauto.
    - i. ss. clarify. eauto.
    - eapply val_inject_id; eauto.
    - eapply val_inject_id; eauto.
    - i. des. esplits; eauto. eapply val_inject_id; eauto.
  Qed.

  Lemma sem_cast_extends m_src m_tgt v_src0 v_tgt0 v_src1 ty0 ty1
        (EXT: Mem.extends m_src m_tgt)
        (VAL: Val.lessdef v_src0 v_tgt0)
        (SEM: sem_cast v_src0 ty0 ty1 m_src = Some v_src1):
      exists v_tgt1,
        (<<SEM: sem_cast v_tgt0 ty0 ty1 m_tgt = Some v_tgt1>>) /\
        (<<VAL: Val.lessdef v_src1 v_tgt1>>).
  Proof.
    exploit sem_cast_inj; try eassumption.
    - instantiate (1:=m_tgt). instantiate (1:=fun b => Some (b, 0)).
      i. ss. clarify. psimpl. eapply Mem.weak_valid_pointer_extends; eauto.
    - eapply val_inject_id; eauto.
    - i. des. esplits; eauto. eapply val_inject_id; eauto.
  Qed.

  Lemma deref_loc_extends ty m_src m_tgt blk ofs v_src
        (DEREF: deref_loc ty m_src blk ofs v_src)
        (EXT: Mem.extends m_src m_tgt):
      exists v_tgt,
        (<<DEREF: deref_loc ty m_tgt blk ofs v_tgt>>) /\
        (<<VAL: Val.lessdef v_src v_tgt>>).
  Proof.
    inv DEREF.
    - exploit Mem.loadv_extends; eauto. i. des. esplits; eauto. econs 1; eauto.
    - esplits; eauto. econs 2; eauto.
    - esplits; eauto. econs 3; eauto.
  Qed.

  Lemma eval_expr_lvalue_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt
        (ENV: match_env inject_id en_src en_tgt)
        (TENV: match_temp_env inject_id tenv_src tenv_tgt)
        (EXT: Mem.extends m_src m_tgt):
      (forall exp v_src
          (EVAL: eval_expr ge en_src tenv_src m_src exp v_src),
          exists v_tgt,
            (<<EVAL: eval_expr ge en_tgt tenv_tgt m_tgt exp v_tgt>>) /\
            (<<LESS: Val.lessdef v_src v_tgt>>)) /\
      (forall exp blk ofs
          (EVAL: eval_lvalue ge en_src tenv_src m_src exp blk ofs),
          eval_lvalue ge en_tgt tenv_tgt m_tgt exp blk ofs).
  Proof.
    apply eval_expr_lvalue_ind; i; try by (esplits; eauto; econs; eauto).
    - cinv (TENV id); rewrite H in *; clarify.
      erewrite val_inject_id in *. esplits; eauto. econs 5; eauto.
    - des. exploit sem_unary_operation_extends; eauto. i. des. esplits; eauto. econs; eauto.
    - des. exploit sem_binary_operation_extends; eauto. i. des. esplits; eauto. econs; eauto.
    - des. exploit sem_cast_extends; eauto. i. des. esplits; eauto. econs; eauto.
    - des. exploit deref_loc_extends; eauto. i. des. esplits; eauto. econs 12; eauto.
    - cinv (ENV id); des; clarify. unfold inject_id in *. clarify. econs; eauto.
    - cinv (ENV id); des; clarify. econs 2; eauto.
    - des. cinv LESS. econs; eauto.
    - des. cinv LESS. econs; eauto.
    - des. cinv LESS. econs; eauto.
  Qed.

  Lemma eval_expr_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt
        (ENV: match_env inject_id en_src en_tgt)
        (TENV: match_temp_env inject_id tenv_src tenv_tgt)
        (EXT: Mem.extends m_src m_tgt)
        exp v_src
        (EVAL: eval_expr ge en_src tenv_src m_src exp v_src):
      exists v_tgt,
        (<<EVAL: eval_expr ge en_tgt tenv_tgt m_tgt exp v_tgt>>) /\
        (<<LESS: Val.lessdef v_src v_tgt>>).
  Proof.
    eapply eval_expr_lvalue_extends; eauto.
  Qed.

  Lemma eval_exprlist_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt tys
        (ENV: match_env inject_id en_src en_tgt)
        (TENV: match_temp_env inject_id tenv_src tenv_tgt)
        (EXT: Mem.extends m_src m_tgt)
        exps vs_src
        (EVALS: eval_exprlist ge en_src tenv_src m_src exps tys vs_src):
      exists vs_tgt,
        (<<EVALS: eval_exprlist ge en_tgt tenv_tgt m_tgt exps tys vs_tgt>>) /\
        (<<LESS: Val.lessdef_list vs_src vs_tgt>>).
  Proof.
    revert tys vs_src EVALS TENV EXT. induction exps; i.
    - inv EVALS. exists []. esplits; eauto. econs; eauto.
    - inv EVALS. exploit IHexps; eauto. i. des.
      exploit eval_expr_extends; eauto. i. des.
      exploit sem_cast_extends; eauto. i. des.
      exists (v_tgt1 :: vs_tgt). esplits; eauto. econs; eauto.
  Qed.

  Lemma eval_lvalue_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt
        (ENV: match_env inject_id en_src en_tgt)
        (TENV: match_temp_env inject_id tenv_src tenv_tgt)
        (EXT: Mem.extends m_src m_tgt)
        exp blk ofs
        (EVAL: eval_lvalue ge en_src tenv_src m_src exp blk ofs):
      eval_lvalue ge en_tgt tenv_tgt m_tgt exp blk ofs.
  Proof.
    eapply eval_expr_lvalue_extends; eauto.
  Qed.

  Lemma free_list_extends_parallel
        m_src0 m_tgt0 locs m_src1
        (MWF: Mem.extends m_src0 m_tgt0)
        (FREE: Mem.free_list m_src0 locs = Some m_src1):
      exists m_tgt1,
        (<<MWF: Mem.extends m_src1 m_tgt1>>) /\
        (<<FREE: Mem.free_list m_tgt0 locs = Some m_tgt1>>).
  Proof.
    revert m_src0 m_tgt0 m_src1 FREE MWF. induction locs; ss.
    - i. clarify. esplits; eauto.
    - i. des_ifs_safe.
      exploit Mem.free_parallel_extends; eauto. i. des.
      exploit IHlocs; eauto. i. des.
      esplits; eauto. rewrite H. rewrite FREE0. eauto.
  Qed.

  Lemma blocks_of_env_ext_match e_src e_tgt
        (ENV: match_env inject_id e_src e_tgt):
      (blocks_of_env ge e_src) = (blocks_of_env ge e_tgt).
  Proof.
    exploit PTree.elements_canonical_order.
    - instantiate (1:= @eq (block * type)). instantiate (1:= e_tgt). instantiate (1:= e_src).
      i. unfold inject_id in *. destruct (ENV i); des; clarify. esplits; eauto; ss.
    - i. unfold inject_id in *. destruct (ENV i); des; clarify. esplits; eauto.
    - intros ALL. unfold blocks_of_env. revert ALL.
      generalize (PTree.elements e_tgt). generalize (PTree.elements e_src). induction l; ss; i.
      + inv ALL. econs.
      + inv ALL. ss. destruct a, b1. ss. des. clarify.
        des_ifs; ss. f_equal. exploit IHl; eauto.
  Qed.

  Lemma clight_step_preserve_extension
        u st_src0 st_tgt0 st_src1 sm0 tr
        (MATCH: match_states_ext_clight u st_src0 st_tgt0 sm0)
        (STEP: step se ge (function_entry ge) st_src0 tr st_src1):
    exists st_tgt1 sm1,
      (<<STEP: step se ge (function_entry ge) st_tgt0 tr st_tgt1>>) /\
      (<<MATCH: match_states_ext_clight u st_src1 st_tgt1 sm1>>).
  Proof.
    inv STEP; inv MATCH; try (by inv CONT; esplits; do 3 (econs; eauto)).
    - exploit eval_expr_extends; eauto. i. des.
      exploit eval_lvalue_extends; eauto. i. des.
      exploit sem_cast_extends; eauto. i. des.
      exploit assign_loc_extends; eauto. i. des.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto.

    - exploit eval_expr_extends; eauto. i. des.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto.
      eapply set_match_temp_env; eauto. eapply val_inject_id; eauto.

    - exploit eval_exprlist_extends; eauto. i. des.
      exploit eval_expr_extends; eauto. i. des. esplits; econs; eauto. econs; eauto.

    - exploit eval_exprlist_extends; eauto. i. des.
      exploit external_call_mem_extends; eauto. i. des.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto.
      destruct optid; ss. eapply set_match_temp_env; eauto. eapply val_inject_id; eauto.

    - exploit eval_expr_extends; eauto. i. des.
      exploit bool_val_extends; eauto. i. esplits; econs; eauto.

    - exploit free_list_extends_parallel; eauto. i. des.
      erewrite blocks_of_env_ext_match in *; eauto.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto. eapply call_cont_match; eauto.

    - exploit eval_expr_extends; eauto. i. des.
      exploit sem_cast_extends; eauto. i. des.
      erewrite blocks_of_env_ext_match in *; eauto.
      exploit free_list_extends_parallel; eauto. i. des.
      eexists. eexists (SimMemExt.mk _ _). esplits; try econs 16; eauto.
      econs; ss; eauto. eapply call_cont_match; eauto.

    - exploit free_list_extends_parallel; eauto. i. des.
      erewrite blocks_of_env_ext_match in *; eauto.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto.
      unfold is_call_cont in *. destruct CONT; clarify.

    - exploit eval_expr_extends; eauto. i. des.
      assert (SWITCH: sem_switch_arg v_tgt (typeof a) = Some n).
      { unfold sem_switch_arg in *. inv LESS; ss; clarify; des_ifs. }
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto. econs; eauto.

    - exploit find_label_match; eauto.
      { eapply call_cont_match; eauto. } i. des. esplits; econs; eauto.

    - cinv INJ; clarify.
      exploit FUNCTIONENTRY; eauto. i. des. clarify.
      eexists. eexists (SimMemExt.mk _ _). esplits; econs; ss; eauto. eapply match_env_inject_id; eauto.

    - cinv INJ; clarify.
      exploit external_call_mem_extends; eauto. i. des.
      eexists. eexists (SimMemExt.mk _ _). esplits; try econs 24; eauto. econs; ss; eauto.

    - inv CONT. esplits; try econs 25; eauto. econs; eauto. destruct optid; ss.
      eapply set_match_temp_env; eauto. eapply val_inject_id. eauto.
  Qed.

End CLIGHTEXT.

Lemma match_states_clight_get_mem st_src st_tgt j m_src m_tgt
      (MATCH: match_states_clight_internal st_src st_tgt j m_src m_tgt):
    (<<MSRC: (get_mem st_src) = m_src>>) /\ (<<MTGT: (get_mem st_tgt) = m_tgt>>).
Proof. inv MATCH; ss. Qed.

Definition flattize_inj (j: meminj): meminj :=
  fun blk => match j blk with
             | Some _ => Some (blk, 0)
             | _ => None
             end.

Lemma flattize_inj_val j v v_tgt
      (VAL: Val.inject j v v_tgt):
    Val.inject (flattize_inj j) v v.
Proof.
  destruct v; ss. inv VAL. unfold flattize_inj. econs; eauto.
  - rewrite H1. eauto.
  - psimpl. auto.
Qed.

Lemma flattize_inj_env j env_src env_tgt
      (ENV: match_env j env_src env_tgt):
    match_env (flattize_inj j) env_src env_src.
Proof.
  ii. specialize (ENV id). des.
  - left. esplits; eauto. unfold flattize_inj. des_ifs.
  - right. eauto.
Qed.

Lemma flattize_inj_temp_env j tenv_src tenv_tgt
      (TENV: match_temp_env j tenv_src tenv_tgt):
    match_temp_env (flattize_inj j) tenv_src tenv_src.
Proof.
  ii. specialize (TENV id). inv TENV; econs. eapply flattize_inj_val; eauto.
Qed.

Lemma flattize_inj_cont j K_src K_tgt
      (TENV: match_cont j K_src K_tgt):
    match_cont (flattize_inj j) K_src K_src.
Proof.
  revert K_tgt TENV. induction K_src; eauto; i; inv TENV; econs; eauto.
  - eapply flattize_inj_env; eauto.
  - eapply flattize_inj_temp_env; eauto.
Qed.

Lemma flattiize_inj_states j st_src st_tgt m_src m_tgt
      (MATCH: match_states_clight_internal st_src st_tgt j m_src m_tgt):
    match_states_clight_internal st_src st_src (flattize_inj j) m_src m_src.
Proof.
  inv MATCH; econs.
  - eapply flattize_inj_env; eauto.
  - eapply flattize_inj_temp_env; eauto.
  - eapply flattize_inj_cont; eauto.
  - eapply flattize_inj_val; eauto.
  - revert args_tgt VALS. induction args_src; ss.
    i. inv VALS. econs; eauto. eapply flattize_inj_val; eauto.
  - eapply flattize_inj_cont; eauto.
  - eapply flattize_inj_val; eauto.
  - eapply flattize_inj_cont; eauto.
Qed.

Section CLIGHTSOUNDSTATE.

  Variable skenv_link: SkEnv.t.
  Variable su: Sound.t.

  Inductive sound_state_clight: state -> Prop :=
  | match_states_clight_intro
      st j m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (INJ: j = UnreachC.to_inj su su.(Unreach.nb))
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
      (SKLE: Ple skenv_link.(Genv.genv_next) su.(Unreach.nb))
      (MATCHST: match_states_clight_internal st st j m m):
      sound_state_clight st.

End CLIGHTSOUNDSTATE.

Require Import Program.

Section CLIGHTSOUND.

  Variable skenv_link: SkEnv.t.

  Lemma clight_unreach_local_preservation clight:
      exists sound_state, <<PRSV: local_preservation (modsem2 skenv_link clight) sound_state>>.
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_spec with (lift := UnreachC.le') (sound_state := sound_state_clight skenv_link); eauto.
    instantiate (1:= get_mem). econs; ss; i.
    { eapply UnreachC.liftspec; et. }
    - inv INIT. ss. destruct args; ss. des. esplits; ss.
      + refl.
      + inv SKENV. cinv MEM. econs; ss; eauto.
        { rewrite NB0. eauto. }
        econs; eauto; try econs.
        * eapply UnreachC.unreach_to_inj_val; eauto.
        * inv TYP. unfold typify_list. revert VALS.
          generalize (sig_args (signature_of_function fd)). clear.
          induction vs; ss. i. inv VALS. des_ifs. econs; eauto.
          unfold typify. des_ifs. eapply UnreachC.unreach_to_inj_val; eauto.
      + refl.

    - inv SUST. ss.
      exploit clight_step_preserve_injection2; eauto.
      { eapply function_entry2_inject; eauto. }
      { instantiate (1:=skenv_link). unfold UnreachC.to_inj.
        unfold symbols_inject. esplits; ss; eauto; ii; try by des_ifs.
        - ii. exists b1; esplit; eauto. inv WF. des_ifs.
          + exfalso. erewrite SKE in WFLO. eapply WFLO in Heq. eapply Genv.genv_symb_range in H0. extlia.
          + eapply Genv.genv_symb_range in H0. ss. exfalso. apply n.
            inv MEM. rewrite SKE in *. rewrite NB in *. eapply Plt_Ple_trans; eauto.
      }
      { unfold UnreachC.to_inj, Mem.flat_inj in *. econs; ss; i.
        - unfold UnreachC.to_inj, Mem.flat_inj in *. des_ifs. esplits; eauto.
        - esplits; eauto. eapply Genv.genv_symb_range in FINDSRC. ss. des_ifs.
          + exfalso. inv WF. eapply WFLO in Heq. rewrite SKE in *. extlia.
          + exfalso. apply n. inv MEM. rewrite SKE in *. rewrite NB in *.
            eapply Plt_Ple_trans; eauto. }
      { cinv MEM. rewrite NB. eapply UnreachC.to_inj_mem; eauto. }
      i. des.
      exists (UnreachC.to_su j1 (Genv.genv_next skenv_link) (Mem.nextblock m_src1)). esplits; eauto.
      + unfold Unreach.hle. splits; ss.
        * i. des_ifs.
          { destruct p0. destruct (Unreach.unreach su0 blk) eqn:U; auto.
            exploit SEP; eauto.
            - unfold UnreachC.to_inj. des_ifs.
            - i. des. exfalso. eapply H. inv MEM. eapply BOUND; eauto. }
          { destruct (Unreach.unreach su0 blk) eqn:U;auto. exfalso. exploit INCR.
            - unfold UnreachC.to_inj. des_ifs.
            - i. clarify. }
          { exfalso. eapply n. eapply Plt_Ple_trans; eauto.
            inv MEM. rewrite NB. eapply Mem.unchanged_on_nextblock; eauto. }
        * inv MEM. rewrite NB. eapply Mem.unchanged_on_nextblock; eauto.
      + eapply flattiize_inj_states in MATCH. econs; ss; eauto.
        * econs; ss; eauto.
          { i. des_ifs. inv WF. rewrite <- SKE.
            destruct ((UnreachC.to_inj su0 (Unreach.nb su0)) x0) eqn:BLK.
            - destruct p0. eapply INCR in BLK. clarify.
            - unfold UnreachC.to_inj in BLK. des_ifs.
              + eapply WFLO; eauto.
              + rewrite SKE. etrans; eauto. clear - n. extlia. }
          { i. des_ifs. }
        * eapply UnreachC.mem_to_su; eauto. etrans; eauto. inv MEM. rewrite NB. eapply Mem.unchanged_on_nextblock; eauto.
        * etrans; eauto. inv MEM. rewrite NB. eapply Mem.unchanged_on_nextblock; eauto.
        * rpapply MATCH. unfold UnreachC.to_inj, flattize_inj.
          extensionality blk. ss. des_ifs.
          exfalso. apply n. destruct p. eapply Mem.valid_block_inject_1; eauto.
      + eapply match_states_clight_get_mem in MATCH.
        eapply match_states_clight_get_mem in MATCHST. des. clarify. econs; ss; eauto.
        * eapply clight_step_readonly; eauto.
        * eapply Mem.unchanged_on_implies; eauto.
          unfold flip, loc_unmapped, UnreachC.to_inj. i. des_ifs.

    - inv AT. inv SUST. inv MATCHST. esplits; eauto.
      + refl.
      + unfold Sound.args; ss. instantiate (1:=su0). esplits; eauto.
        * ii. subst. clear EXTERNAL. des. ss.
          unfold Genv.find_funct_ptr in *. des_ifs.
          eapply Genv.genv_defs_range in Heq. inv WF. split.
          { ii. rewrite SKE in *. eapply Plt_strict. eapply Plt_Ple_trans; eauto. }
          { rewrite SKE in *. eapply Plt_Ple_trans; eauto. }
        * eapply UnreachC.unreach_to_inj_vals; eauto.
      + refl.
      + i. inv AFTER. unfold Sound.retv in *. des. ss. esplits; eauto.
        * des_ifs; ss. des; ss. unfold Unreach.hle in *. des. econs; eauto.
          { rewrite <- GENB. auto. }
          { etrans; eauto. }
          { econs; eauto.
            - eapply UnreachC.unreach_to_inj_val. unfold typify. des_ifs.
            - eapply match_cont_incr; cycle 1; eauto. unfold UnreachC.to_inj. ii. des_ifs.
              + ss. erewrite OLD in *; eauto. clarify.
              + exfalso. eapply n. eapply Plt_Ple_trans; eauto. }
        * unfold Retv.get_m. des_ifs. ss. refl.

    - inv FINAL. inv SUST. inv MATCHST. esplits; ss; eauto; try refl.
      + unfold Sound.retv. ss. esplits; eauto. eapply UnreachC.unreach_to_inj_val; eauto.
  Qed.

End CLIGHTSOUND.
