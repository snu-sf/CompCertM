Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Simulation Ctypes Cop Ctyping Csyntax ClightC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import StaticMutrecA StaticMutrecAspec StaticMutrecAproof.
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

Inductive match_states_ext_a (sm_arg: SimMemExt.t')
  : unit -> state -> state -> SimMemExt.t' -> Prop :=
| match_ext_Callstate
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_a
      sm_arg tt
      (Callstate i m_src)
      (Callstate i m_tgt)
      sm0
| match_inter_Callstate
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_a
      sm_arg tt
      (Interstate i m_src)
      (Interstate i m_tgt)
      sm0
| match_return_Callstate
    i m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
  :
    match_states_ext_a
      sm_arg tt
      (Returnstate i m_src)
      (Returnstate i m_tgt)
      sm0.

Section AEXT.

  Variable se: Senv.t.
  Variable ge: SkEnv.t.

  (* Definition function_entry_extends *)
  (*            (function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) *)
  (*   := *)
  (*     forall *)
  (*       fn vs_src vs_tgt m_src0 m_tgt0 en tenv_src m_src1 *)
  (*       (MWF: Mem.extends m_src0 m_tgt0) *)
  (*       (VALS: Val.lessdef_list vs_src vs_tgt) *)
  (*       (ENTRY: function_entry ge fn vs_src m_src0 en tenv_src m_src1), *)
  (*     exists tenv_tgt m_tgt1, *)
  (*       (<<MWF: Mem.extends m_src1 m_tgt1>>) /\ *)
  (*       (<<TENV: match_temp_env inject_id tenv_src tenv_tgt>>) /\ *)
  (*       (<<ENTRY: function_entry ge fn vs_tgt m_tgt0 en tenv_tgt m_tgt1>>). *)

  (* Variable function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop. *)
  (* Hypothesis FUNCTIONENTRY: function_entry_extends function_entry. *)

  (* Lemma alloc_variables_extends idl en_src0 en_tgt0 en_src1 m_src0 m_tgt0 m_src1 *)
  (*       (ALLOC: alloc_variables ge en_src0 m_src0 idl en_src1 m_src1) *)
  (*       (ENV: match_env inject_id en_src0 en_tgt0) *)
  (*       (MWF: Mem.extends m_src0 m_tgt0) *)
  (*   : *)
  (*     exists m_tgt1 en_tgt1, *)
  (*       (<<MWF: Mem.extends m_src1 m_tgt1>>) /\ *)
  (*       (<<ENV: match_env inject_id en_src1 en_tgt1>>) /\ *)
  (*       (<<ALLOC: alloc_variables ge en_src0 m_tgt0 idl en_src1 m_tgt1>>). *)
  (* Proof. *)
  (*   revert m_src0 m_src1 m_tgt0 en_src0 en_tgt0 en_src1 ALLOC ENV MWF. induction idl. *)
  (*   - i. inv ALLOC. esplits; eauto. *)
  (*     econs; eauto. *)
  (*   - i. inv ALLOC. *)
  (*     exploit Mem.alloc_extends; eauto; try refl. i. des. *)
  (*     exploit IHidl; eauto. *)
  (*     { instantiate (1:=PTree.set id (b1, ty) en_tgt0). *)
  (*       ii. repeat rewrite PTree.gsspec. des_ifs. *)
  (*       left. esplits; ss. } i. des. *)
  (*     esplits; eauto. *)
  (*     econs; eauto. *)
  (* Qed. *)

  (* Lemma assign_loc_extends ce ty m_src0 m_tgt0 v_src v_tgt m_src1 blk ofs *)
  (*       (ASSIGN: assign_loc ce ty m_src0 blk ofs v_src m_src1) *)
  (*       (VAL: Val.lessdef v_src v_tgt) *)
  (*       (MWF: Mem.extends m_src0 m_tgt0) *)
  (*   : *)
  (*     exists m_tgt1, *)
  (*       (<<ASSIGN: assign_loc ce ty m_tgt0 blk ofs v_tgt m_tgt1>>) /\ *)
  (*       (<<MWF: Mem.extends m_src1 m_tgt1>>). *)
  (* Proof. *)
  (*   inv ASSIGN. *)
  (*   - exploit Mem.storev_extends; eauto. i. des. *)
  (*     esplits; eauto. econs 1; eauto. *)
  (*   - cinv VAL. *)
  (*     exploit Mem.loadbytes_extends; eauto. i. des_safe. *)
  (*     exploit Mem.storebytes_within_extends; eauto. i. des_safe. *)
  (*     esplits; eauto. econs 2; eauto. *)
  (* Qed. *)

  (* Lemma match_env_inject_id en *)
  (*   : *)
  (*     match_env inject_id en en. *)
  (* Proof. *)
  (*   ii. destruct (en ! id) eqn:ENV; eauto. *)
  (*   destruct p. left. esplits; ss. *)
  (* Qed. *)

  (* Lemma bind_parameters_extends e_src e_tgt m_src0 m_tgt0 idl *)
  (*       vargs_src vargs_tgt m_src1 *)
  (*       (BIND: bind_parameters ge e_src m_src0 idl vargs_src m_src1) *)
  (*       (ENV: match_env inject_id e_src e_tgt) *)
  (*       (MWF: Mem.extends m_src0 m_tgt0) *)
  (*       (VALS: Val.lessdef_list vargs_src vargs_tgt) *)
  (*   : *)
  (*     exists m_tgt1, *)
  (*       (<<MWF: Mem.extends m_src1 m_tgt1>>) /\ *)
  (*       (<<BIND: bind_parameters ge e_tgt m_tgt0 idl vargs_tgt m_tgt1>>). *)
  (* Proof. *)
  (*   revert m_src0 m_tgt0 ENV vargs_src vargs_tgt m_src1 MWF VALS BIND. induction idl. *)
  (*   - i. inv BIND. inv VALS. esplits; eauto. econs. *)
  (*   - i. inv BIND. inv VALS. *)
  (*     destruct (ENV id); des; clarify. *)
  (*     unfold inject_id in *. clarify. *)
  (*     exploit assign_loc_extends; eauto. i. des. clarify. *)
  (*     exploit IHidl; try apply H6; eauto. i. des. *)
  (*     esplits; eauto. econs; eauto. *)
  (* Qed. *)

  (* Lemma function_entry2_extends *)
  (*   : *)
  (*     function_entry_extends function_entry2. *)
  (* Proof. *)
  (*   ii. inv ENTRY. *)
  (*   exploit alloc_variables_extends; eauto. *)
  (*   { eapply match_env_inject_id. } i. des. *)
  (*   exploit bind_parameter_temps_inject; eauto. *)
  (*   { eapply create_undef_temps_match. } *)
  (*   { eapply val_inject_list_lessdef. eauto. } i. des. *)
  (*   esplits; eauto. econs; eauto. *)
  (* Qed. *)

  (* Lemma function_entry1_extends *)
  (*   : *)
  (*     function_entry_extends function_entry1. *)
  (* Proof. *)
  (*   ii. inv ENTRY. *)
  (*   exploit alloc_variables_extends; eauto. *)
  (*   { eapply match_env_inject_id. } i. des. *)
  (*   clear ENV. *)
  (*   exploit bind_parameters_extends; eauto. *)
  (*   { eapply match_env_inject_id. } i. des. *)
  (*   esplits; eauto. *)
  (*   - eapply create_undef_temps_match. *)
  (*   - econs; eauto. *)
  (* Qed. *)

  (* Lemma bool_val_extends m_src m_tgt ty v_src v_tgt b *)
  (*       (VAL: Val.lessdef v_src v_tgt) *)
  (*       (MWF: Mem.extends m_src m_tgt) *)
  (*       (BVAL: bool_val v_src ty m_src = Some b) *)
  (*   : *)
  (*     bool_val v_tgt ty m_tgt = Some b. *)
  (* Proof. *)
  (*   unfold bool_val in *. cinv VAL; des_ifs; ss; clarify. *)
  (*   exploit Mem.weak_valid_pointer_extends; eauto. i. clarify. *)
  (* Qed. *)

  (* Lemma sem_unary_operation_extends m_src m_tgt op v_src0 v_tgt0 v_src1 ty *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       (VAL: Val.lessdef v_src0 v_tgt0) *)
  (*       (SEM: sem_unary_operation op v_src0 ty m_src = Some v_src1) *)
  (*   : *)
  (*     exists v_tgt1, *)
  (*       (<<SEM: sem_unary_operation op v_tgt0 ty m_tgt = Some v_tgt1>>) /\ *)
  (*       (<<VAL: Val.lessdef v_src1 v_tgt1>>). *)
  (* Proof. *)
  (*   destruct op; ss. *)
  (*   - unfold sem_notbool, option_map in *. des_ifs_safe. *)
  (*     exploit bool_val_extends; eauto. *)
  (*     intros BVAL. rewrite BVAL. esplits; eauto. *)
  (*   - unfold sem_notint in *. cinv VAL; des_ifs; esplits; eauto. *)
  (*   - unfold sem_neg in *. cinv VAL; des_ifs; esplits; eauto. *)
  (*   - unfold sem_absfloat in *. cinv VAL; des_ifs; esplits; eauto. *)
  (* Qed. *)

  (* Lemma sem_binary_operation_extends ce m_src m_tgt op *)
  (*       v_src0 v_tgt0 v_src1 v_tgt1 v_src2 ty0 ty1 *)
  (*       (SEM: sem_binary_operation ce op v_src0 ty0 v_src1 ty1 m_src = Some v_src2) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       (VAL0: Val.lessdef v_src0 v_tgt0) *)
  (*       (VAL1: Val.lessdef v_src1 v_tgt1) *)
  (*   : *)
  (*     exists v_tgt2, *)
  (*       (<<SEM: sem_binary_operation ce op v_tgt0 ty0 v_tgt1 ty1 m_tgt = Some v_tgt2>>) /\ *)
  (*       (<<VAL: Val.lessdef v_src2 v_tgt2>>). *)
  (* Proof. *)
  (*   exploit sem_binary_operation_inj; try eassumption. *)
  (*   - instantiate (1:=m_tgt). instantiate (1:=fun b => Some (b, 0)). *)
  (*     i. ss. clarify. psimpl. *)
  (*     eapply Mem.valid_pointer_extends; eauto. *)
  (*   - i. ss. clarify. psimpl. eapply Mem.weak_valid_pointer_extends; eauto. *)
  (*   - i. ss. clarify. psimpl. zsimpl. *)
  (*     eapply Ptrofs.unsigned_range_2; eauto. *)
  (*   - i. ss. clarify. eauto. *)
  (*   - eapply val_inject_id; eauto. *)
  (*   - eapply val_inject_id; eauto. *)
  (*   - i. des. esplits; eauto. *)
  (*     eapply val_inject_id; eauto. *)
  (* Qed. *)

  (* Lemma sem_cast_extends m_src m_tgt v_src0 v_tgt0 v_src1 ty0 ty1 *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       (VAL: Val.lessdef v_src0 v_tgt0) *)
  (*       (SEM: sem_cast v_src0 ty0 ty1 m_src = Some v_src1) *)
  (*   : *)
  (*     exists v_tgt1, *)
  (*       (<<SEM: sem_cast v_tgt0 ty0 ty1 m_tgt = Some v_tgt1>>) /\ *)
  (*       (<<VAL: Val.lessdef v_src1 v_tgt1>>). *)
  (* Proof. *)
  (*   exploit sem_cast_inj; try eassumption. *)
  (*   - instantiate (1:=m_tgt). instantiate (1:=fun b => Some (b, 0)). *)
  (*     i. ss. clarify. psimpl. eapply Mem.weak_valid_pointer_extends; eauto. *)
  (*   - eapply val_inject_id; eauto. *)
  (*   - i. des. esplits; eauto. *)
  (*     eapply val_inject_id; eauto. *)
  (* Qed. *)

  (* Lemma deref_loc_extends ty m_src m_tgt blk ofs v_src *)
  (*       (DEREF: deref_loc ty m_src blk ofs v_src) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*   : *)
  (*     exists v_tgt, *)
  (*       (<<DEREF: deref_loc ty m_tgt blk ofs v_tgt>>) /\ *)
  (*       (<<VAL: Val.lessdef v_src v_tgt>>). *)
  (* Proof. *)
  (*   inv DEREF. *)
  (*   - exploit Mem.loadv_extends; eauto. i. des. *)
  (*     esplits; eauto. econs 1; eauto. *)
  (*   - esplits; eauto. econs 2; eauto. *)
  (*   - esplits; eauto. econs 3; eauto. *)
  (* Qed. *)

  (* Lemma eval_expr_lvalue_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt *)
  (*       (ENV: match_env inject_id en_src en_tgt) *)
  (*       (TENV: match_temp_env inject_id tenv_src tenv_tgt) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*   : *)
  (*     (forall *)
  (*         exp v_src *)
  (*         (EVAL: eval_expr ge en_src tenv_src m_src exp v_src), *)
  (*         exists v_tgt, *)
  (*           (<<EVAL: eval_expr ge en_tgt tenv_tgt m_tgt exp v_tgt>>) /\ *)
  (*           (<<LESS: Val.lessdef v_src v_tgt>>)) /\ *)
  (*     (forall *)
  (*         exp blk ofs *)
  (*         (EVAL: eval_lvalue ge en_src tenv_src m_src exp blk ofs), *)
  (*         eval_lvalue ge en_tgt tenv_tgt m_tgt exp blk ofs). *)
  (* Proof. *)
  (*   apply eval_expr_lvalue_ind; i; try by (esplits; eauto; econs; eauto). *)
  (*   - cinv (TENV id); rewrite H in *; clarify. *)
  (*     erewrite val_inject_id in *. *)
  (*     esplits; eauto. econs 5; eauto. *)
  (*   - des. exploit sem_unary_operation_extends; eauto. i. des. *)
  (*     esplits; eauto. econs; eauto. *)
  (*   - des. exploit sem_binary_operation_extends; eauto. i. des. *)
  (*     esplits; eauto. econs; eauto. *)
  (*   - des. exploit sem_cast_extends; eauto. i. des. *)
  (*     esplits; eauto. econs; eauto. *)
  (*   - des. exploit deref_loc_extends; eauto. i. des. *)
  (*     esplits; eauto. econs 12; eauto. *)
  (*   - cinv (ENV id); des; clarify. unfold inject_id in *. *)
  (*     clarify. econs; eauto. *)
  (*   - cinv (ENV id); des; clarify. *)
  (*     econs 2; eauto. *)
  (*   - des. cinv LESS. econs; eauto. *)
  (*   - des. cinv LESS. econs; eauto. *)
  (*   - des. cinv LESS. econs; eauto. *)
  (* Qed. *)

  (* Lemma eval_expr_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt *)
  (*       (ENV: match_env inject_id en_src en_tgt) *)
  (*       (TENV: match_temp_env inject_id tenv_src tenv_tgt) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       exp v_src *)
  (*       (EVAL: eval_expr ge en_src tenv_src m_src exp v_src) *)
  (*   : *)
  (*     exists v_tgt, *)
  (*       (<<EVAL: eval_expr ge en_tgt tenv_tgt m_tgt exp v_tgt>>) /\ *)
  (*       (<<LESS: Val.lessdef v_src v_tgt>>). *)
  (* Proof. *)
  (*   eapply eval_expr_lvalue_extends; eauto. *)
  (* Qed. *)

  (* Lemma eval_exprlist_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt tys *)
  (*       (ENV: match_env inject_id en_src en_tgt) *)
  (*       (TENV: match_temp_env inject_id tenv_src tenv_tgt) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       exps vs_src *)
  (*       (EVALS: eval_exprlist ge en_src tenv_src m_src exps tys vs_src) *)
  (*   : *)
  (*     exists vs_tgt, *)
  (*       (<<EVALS: eval_exprlist ge en_tgt tenv_tgt m_tgt exps tys vs_tgt>>) /\ *)
  (*       (<<LESS: Val.lessdef_list vs_src vs_tgt>>). *)
  (* Proof. *)
  (*   revert tys vs_src EVALS TENV EXT. induction exps; i. *)
  (*   - inv EVALS. exists []. esplits; eauto. econs; eauto. *)
  (*   - inv EVALS. exploit IHexps; eauto. i. des. *)
  (*     exploit eval_expr_extends; eauto. i. des. *)
  (*     exploit sem_cast_extends; eauto. i. des. *)
  (*     exists (v_tgt1 :: vs_tgt). esplits; eauto. *)
  (*     econs; eauto. *)
  (* Qed. *)

  (* Lemma eval_lvalue_extends en_src en_tgt tenv_src tenv_tgt m_src m_tgt *)
  (*       (ENV: match_env inject_id en_src en_tgt) *)
  (*       (TENV: match_temp_env inject_id tenv_src tenv_tgt) *)
  (*       (EXT: Mem.extends m_src m_tgt) *)
  (*       exp blk ofs *)
  (*       (EVAL: eval_lvalue ge en_src tenv_src m_src exp blk ofs) *)
  (*   : *)
  (*     eval_lvalue ge en_tgt tenv_tgt m_tgt exp blk ofs. *)
  (* Proof. *)
  (*   exploit eval_expr_lvalue_extends; eauto. i. des. eauto. *)
  (* Qed. *)

  (* Lemma free_list_extends_parallel *)
  (*       m_src0 m_tgt0 locs m_src1 *)
  (*       (MWF: Mem.extends m_src0 m_tgt0) *)
  (*       (FREE: Mem.free_list m_src0 locs = Some m_src1) *)
  (*   : *)
  (*     exists m_tgt1, *)
  (*       (<<MWF: Mem.extends m_src1 m_tgt1>>) /\ *)
  (*       (<<FREE: Mem.free_list m_tgt0 locs = Some m_tgt1>>). *)
  (* Proof. *)
  (*   revert m_src0 m_tgt0 m_src1 FREE MWF. induction locs; ss. *)
  (*   - i. clarify. esplits; eauto. *)
  (*   - i. des_ifs_safe. *)
  (*     exploit Mem.free_parallel_extends; eauto. i. des. *)
  (*     exploit IHlocs; eauto. i. des. *)
  (*     esplits; eauto. *)
  (*     rewrite H. rewrite FREE0. eauto. *)
  (* Qed. *)

  (* Lemma blocks_of_env_ext_match e_src e_tgt *)
  (*       (ENV: match_env inject_id e_src e_tgt) *)
  (*   : *)
  (*     (blocks_of_env ge e_src) = (blocks_of_env ge e_tgt). *)
  (* Proof. *)
  (*   exploit PTree.elements_canonical_order. *)
  (*   - instantiate (1:= @eq (block * type)). *)
  (*     instantiate (1:= e_tgt). *)
  (*     instantiate (1:= e_src). *)
  (*     i. unfold inject_id in *. destruct (ENV i); des; clarify. *)
  (*     esplits; eauto; ss. *)
  (*   - i. unfold inject_id in *. destruct (ENV i); des; clarify. *)
  (*     esplits; eauto. *)
  (*   - intros ALL. *)
  (*     unfold blocks_of_env. revert ALL. *)
  (*     generalize (PTree.elements e_tgt). *)
  (*     generalize (PTree.elements e_src). *)
  (*     induction l; ss; i. *)
  (*     + inv ALL. econs. *)
  (*     + inv ALL. ss. destruct a, b1. ss. des. clarify. *)
  (*       des_ifs; ss. f_equal. *)
  (*       exploit IHl; eauto. *)
  (* Qed. *)

  Lemma a_step_preserve_extension
        sm_arg u st_src0 st_tgt0 st_src1 sm0 tr
        (MATCH: match_states_ext_a sm_arg u st_src0 st_tgt0 sm0)
        (STEP: step se ge st_src0 tr st_src1)
  :
    exists st_tgt1 sm1,
      (<<STEP: step se ge st_tgt0 tr st_tgt1>>) /\
      (<<MATCH: match_states_ext_a sm_arg u st_src1 st_tgt1 sm1>>).
  Proof.
    inv STEP; inv MATCH.
    - esplits. econs. econs; eauto.
    - esplits. econs 2; eauto. econs; eauto.
  Qed.

End AEXT.

Section ASOUNDSTATE.

  Variable skenv_link: SkEnv.t.
  Variable su: Sound.t.

  (* Definition sound_external := *)
  (*            forall g_fptr, Genv.find_symbol (SkEnv.project skenv_link (CtypesC.CSk.of_program signature_of_function prog)) *)
  (*                                        MutrecHeader.g_id = Some g_fptr -> *)
  (*                       Sound.val su (Vptr g_fptr Ptrofs.zero). *)

  Inductive sound_state_a
    : state -> Prop :=
  | sound_Callstate
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state_a (Callstate i m)
  | sound_Interstate
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
      (NZERO: Int.intval i <> 0)
      (* (EXT: sound_external) *)
    :
      sound_state_a (Interstate i m)
  | sound_Returnstate
      i m
      (WF: Sound.wf su)
      (MEM: UnreachC.mem' su m)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
    :
      sound_state_a (Returnstate i m)
  .

End ASOUNDSTATE.


Section ASOUND.

  Variable skenv_link: SkEnv.t.

  Lemma a_unreach_local_preservation
    :
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link tt) sound_state>>
  .
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_spec with (sound_state := sound_state_a skenv_link); eauto.
    econs; ss; i.
    - inv INIT. ss. inv SUARG. des. esplits.
      + refl.
      + econs; eauto.
        * inv SKENV. eauto.
      + instantiate (1:=get_mem). ss. refl.
    - exists su0. esplits; eauto.
      + refl.
      + inv STEP; eauto.
        { inv SUST. econs; eauto. }
        { inv SUST. econs; eauto. }
          (* ss. des_ifs. *)
      + inv STEP; eauto.
        { ss. refl. }
        { ss. refl. }
    - inv AT; inv SUST; ss.
      split.
      + rr. refl.
      + cinv WF.
        exists su0.
        esplits.
        * econs; ss; eauto.
          { ss. ii. split.
            - ii. clarify. eapply WFLO in H.
              rewrite SKE in H.
              unfold Genv.find_symbol in FINDG.
              exploit Genv.genv_symb_range; eauto. i. ss.
              admit "true".
            - clarify.
              inv MEM. ss. rewrite NB.
              exploit Genv.genv_symb_range; eauto. i. ss.
              rewrite SKE in GENB.
              eapply Plt_Ple_trans; eauto. }
          esplits; eauto.
          econs; ss.
        * refl.
        * i.
          destruct retv. ss.
          rr in RETV. des; ss. inv MEM0.
          exists su_ret.
          inv AFTER.
          esplits; eauto.
          { econs; ss; eauto.
            inv LE. ss. des. rewrite <- GENB0. eauto. }
          { ss. refl. }
    - exists su0. inv SUST; inv FINAL; ss.
      esplits.
      + refl.
      + ss.
      + refl.
  Qed.

End ASOUND.
