Require Import CoqlibC Errors.
Require Import IntegersC ASTC Linking.
Require Import ValuesC MemoryC SeparationC Events GlobalenvsC Smallstep.
Require Import LTL Op LocationsC LinearC MachC.
Require Import Bounds ConventionsC StacklayoutC LineartypingC.
Require Import Stacking.

Local Open Scope string_scope.
Local Open Scope sep_scope.

(* newly added *)
Require Export StackingproofC0 StoreArguments.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC ArgPassing MatchSimModSem.
Require Import Conventions1C.
Require SimMemInjC.
Require Import AxiomsC.
Require SoundTop.

Set Implicit Arguments.








(*** put this into MachC. ***)
Section MACHEXTRA.

  Lemma extcall_arguments_dtm
        rs m rsp sg vs0 vs1
        (ARGS0: extcall_arguments rs m rsp sg vs0)
        (ARGS1: extcall_arguments rs m rsp sg vs1)
  :
    vs0 = vs1
  .
  Proof.
    admit "merge with mixed sim".
  Qed.

  Lemma extcall_arguments_length
        rs m rsp sg vs
        (ARGS: extcall_arguments rs m rsp sg vs)
    :
      length (loc_arguments sg) = length vs
  .
  Proof.
    unfold extcall_arguments in *.
    abstr (loc_arguments sg) locs.
    ginduction vs; ii; inv ARGS; ss.
    f_equal. erewrite IHvs; eauto.
  Qed.

End MACHEXTRA.

















Local Opaque Z.add Z.mul Z.div.
Local Opaque sepconj.
Local Opaque function_bounds.
Local Opaque make_env.









Local Existing Instance Val.mi_normal.

Section STACKINGEXTRA.

Lemma match_stacks_sp_ofs:
  forall j ge cs cs' sg sm,
  match_stacks ge j cs cs' sg sm ->
  exists sp, (parent_sp cs') = Vptr sp Ptrofs.zero true.
Proof.
  induction 1; ii; ss; esplits; eauto.
Qed.

Ltac sep_simpl_tac :=
  unfold NW in *;
  repeat (try rewrite sep_assoc in *;
          try rewrite sep_pure in *;
          try rewrite stack_contents_nil_left_false in *;
          try rewrite stack_contents_nil_right_false in *;
          try match goal with
              | [H: _ |= pure False |- _] => simpl in H; inv H
              | [H: _ |= _ ** pure False |- _] => apply sep_proj2 in H
              | [H: _ |= _ ** pure False ** _ |- _] => apply sep_pick2 in H
              end;
          idtac
         )
.
Local Opaque Z.add Z.mul make_env function_bounds.
Lemma arguments_private
      sp_tgt spdelta
      m_src m_tgt
      stk_src stk_tgt
      F
      sg
      ge sm
      (MATCH: m_tgt |= stack_contents F stk_src stk_tgt ** minjection F m_src)
      (STACKS: match_stacks ge F stk_src stk_tgt sg sm)
      (SP: parent_sp stk_tgt = Vptr sp_tgt spdelta true)
  :
    <<_ : forall ofs (OFS: 0 <= ofs < 4 * size_arguments sg),
    (<<PRIV: loc_out_of_reach F m_src sp_tgt (spdelta.(Ptrofs.unsigned) + ofs)>>)>>
.
Proof.
  ii.
  eapply separation_private; eauto.
  destruct stk_tgt; ss. inv STACKS. des_ifs. destruct stk_src; ss.
  { sep_simpl_tac. des; ss. }
  des_ifs_safe.
  des_ifs; sep_simpl_tac.
  - unfold dummy_frame_contents in *. inv MATCH. ss.
    inv STACKS; ss; cycle 1.
    { inv STK; ss. }
    des; cycle 1.
    { apply tailcall_size in LE. xomega. }
    clarify.
  - Local Transparent sepconj. cbn.
    left. left. right. left.
    split; [ss|].
    Local Opaque sepconj.
    apply sep_pick1 in MATCH. unfold frame_contents in *.
    unfold fe_ofs_arg. rewrite ! Z.add_0_l in *.
    inv STACKS; ss. des_ifs_safe. des.
    rewrite Ptrofs.unsigned_zero in *.
    esplits; eauto; try xomega.
Qed.

Lemma arguments_perm
      ge sm
      sp_tgt spdelta
      m_src m_tgt
      stk_src stk_tgt
      F
      sg
      (MATCH: m_tgt |= stack_contents F stk_src stk_tgt ** minjection F m_src)
      (STACKS: match_stacks ge F stk_src stk_tgt sg sm)
      (SP: parent_sp stk_tgt = Vptr sp_tgt spdelta true)
  :
    <<_ : forall ofs (OFS: 0 <= ofs < 4 *size_arguments sg),
    (<<PERM: Mem.perm m_tgt sp_tgt (spdelta.(Ptrofs.unsigned) + ofs) Cur Freeable>>)>>
.
Proof.
  ii.
  destruct stk_tgt; ss. inv STACKS. des_ifs. destruct stk_src; ss.
  { sep_simpl_tac. des; ss. }
  des_ifs_safe.
  des_ifs; ss; sep_simpl_tac.
  - unfold dummy_frame_contents in *. inv MATCH. ss.
    inv STACKS; ss; cycle 1.
    { inv STK; ss. }
    des; cycle 1.
    { apply tailcall_size in LE. xomega. }
    clarify. eapply H4; eauto.
  - apply sep_pick1 in MATCH. unfold frame_contents in *.
    ss. des_ifs. des.
    apply sep_pick2 in MATCH.
    unfold fe_ofs_arg in *. inv MATCH. des; ss. eapply H2; eauto.
    inv STACKS; ss.
    rewrite ! Z.add_0_l in *. xomega.
Qed.

End STACKINGEXTRA.

Lemma external_call_parallel_rule:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
  external_call ef ge vargs1 m1 t vres1 m1' ->
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  exists j' vres2 m2',
     external_call ef ge vargs2 m2 t vres2 m2'
  /\ Val.inject j' vres1 vres2
  /\ m2' |= minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m2.
Proof.
  intros until vargs2; intros CALL SEP ARGS.
  destruct SEP as (A & B & C). simpl in A.
  exploit external_call_mem_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  intros (j' & vres2 & m2' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP).
  assert (MAXPERMS: forall b ofs p,
            Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists j', vres2, m2'; intuition auto.
  split; [|split].
- exact INJ'.
- apply m_invar with (m0 := m2).
+ apply globalenv_inject_incr with j m1; auto.
+ eapply Mem.unchanged_on_implies; eauto.
  intros; red; intros; red; intros.
  eelim C; eauto. simpl. exists b0, delta; auto.
- red; intros. destruct H as (b0 & delta & J' & E).
  destruct (j b0) as [[b' delta'] | ] eqn:J.
+ erewrite INCR in J' by eauto. inv J'.
  eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto.
  eapply Mem.valid_block_inject_1; eauto.
+ exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto.
Qed.

Lemma minjection_disjoint_footprint_private
      sm0 P
      (SEP: (SimMemInj.tgt sm0) |= P)
      (DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P)
  :
    P.(m_footprint) <2= sm0.(SimMemInj.tgt_private)
.
Proof.
  u.
  - ii. esplits; eauto.
    + ii. eapply DISJ; eauto. ss. esplits; eauto.
    + destruct P; ss. eapply m_valid; eauto.
Qed.

Lemma minjection_private_disjoint_footprint
      sm0 P
      (PRIV: P.(m_footprint) <2= sm0.(SimMemInj.tgt_private))
  :
    <<DISJ: disjoint_footprint (minjection (SimMemInj.inj sm0) (SimMemInj.src sm0)) P>>
.
Proof.
  - ii. ss. des. eapply PRIV; eauto.
Qed.

Lemma external_call_parallel_rule_simmem
      (F V: Type) (ge0: Genv.t F V)
      sm_at sm_after P
      (SEP: sm_at.(SimMem.tgt) |= (minjection sm_at.(SimMemInj.inj) sm_at.(SimMem.src))
                             ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P)
      sm_arg sm_ret
      (MWF: SimMem.wf sm_at)
      (MWF0: SimMem.wf sm_arg)
      (MWF1: SimMem.wf sm_ret)
      (MWF2: SimMem.wf sm_after)
      (MWFAFTR : SimMem.wf (SimMemInj.unlift' sm_arg sm_ret))
      (MLE: SimMem.le sm_at sm_arg)
      (MLE0: SimMem.le (SimMem.lift sm_arg) sm_ret)
      (MLE1: SimMem.le (SimMem.unlift sm_at sm_ret) sm_after)
      (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret))
      (PRIV0: sm_at.(SimMemInj.tgt_private) = sm_arg.(SimMemInj.tgt_private))
      (PRIV1: sm_ret.(SimMemInj.tgt_private) = sm_after.(SimMemInj.tgt_private))
      (UNCH0: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_at) (SimMemInj.tgt sm_arg))
      (UNCH1: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_ret) (SimMemInj.tgt sm_after))
  :
    <<SEP: sm_after.(SimMem.tgt) |= (minjection sm_after.(SimMemInj.inj) sm_after.(SimMem.src))
                            ** globalenv_inject ge0 sm_at.(SimMemInj.inj) ** P>>
.
Proof.
  (* See external_call_parallel_rule *)
  destruct SEP as (A & B & C). simpl in A.
  apply disjoint_footprint_sepconj in C. des. ss.
  eapply minjection_disjoint_footprint_private in DISJ1; cycle 1.
  { apply sep_drop in B. ss. }
  sep_split.
  { ss. eapply MWF2. }
  { apply disjoint_footprint_sepconj. ss.
    split; ss.
    apply minjection_private_disjoint_footprint.
    etrans; eauto.
    rewrite PRIV0. rewrite <- PRIV1.
    inv MLEAFTR. inv MLE0. inv MWF0. inv MWF1. ss.
    etrans; try apply TGTEXT0; eauto. rewrite TGTPARENTEQ0. reflexivity. }
  sep_split.
  { eapply globalenv_inject_incr in B; eauto.
    - apply sep_pick1 in B. ss. des. esplits; eauto.
      etrans; eauto. inv MLE. inv MLE0. inv MLE1. inv MLEAFTR.
      etrans; eauto with mem. etrans; eauto with mem.
    - apply SimMemInj.inject_separated_frozen; eauto.
      eapply SimMemInj.frozen_refl; eauto.
  }
  { ss. }
  destruct B as (X & Y & Z); ss.
  eapply m_invar; eauto.
  eapply Mem.unchanged_on_implies; cycle 1.
  { ii. exploit DISJ1; eauto. }
  rewrite PRIV0.
  etrans.
  { instantiate (1:= (SimMemInj.tgt sm_arg)). eauto. }
  etrans; cycle 1.
  { instantiate (1:= (SimMemInj.tgt sm_ret)). eauto. }
  clears sm_after. clear sm_after. clears sm_at. clear sm_at.
  inv MLE0. ss.
Unshelve.
  all: try apply Mem.empty.
Qed.

(* Lemma after_external_parallel_rule *)
(*       (F V: Type) *)
(*       P sm_at sm_arg sm_ret sm_after *)
(*       (SEP: sm_at.(SimMem.tgt) |= (minjection sm_at.(SimMemInj.inj) sm_at.(SimMem.src)) ** P) *)
(*       (MWF0: SimMem.wf sm_at) *)
(*       (MWF1: SimMem.wf sm_arg) *)
(*       (MWF2: SimMem.wf sm_ret) *)
(*       (MWF3: SimMem.wf sm_after) *)
(*       (MWFAFTR : SimMem.wf (SimMemInj.unlift' sm_arg sm_ret)) *)
(*       (MLE0: SimMem.le sm_at sm_arg) *)
(*       (MLE1: SimMem.le (SimMem.lift sm_arg) sm_ret) *)
(*       (MLE2: SimMem.le (SimMem.unlift sm_at sm_ret) sm_after) *)
(*       (MLEAFTR: SimMem.le sm_arg (SimMem.unlift sm_arg sm_ret)) *)
(*       (PRIV0: sm_at.(SimMemInj.tgt_private) = sm_arg.(SimMemInj.tgt_private)) *)
(*       (PRIV1: sm_ret.(SimMemInj.tgt_private) = sm_after.(SimMemInj.tgt_private)) *)
(*       (UNCH0: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_at) (SimMemInj.tgt sm_arg)) *)
(*       (UNCH1: Mem.unchanged_on (SimMemInj.tgt_private sm_arg) (SimMemInj.tgt sm_ret) (SimMemInj.tgt sm_after)) *)
(*   : *)
(*     <<SEP: sm_after.(SimMem.tgt) |= (minjection sm_after.(SimMemInj.inj) sm_after.(SimMem.src)) ** P>> *)
(* . *)
(* Proof. *)
(* Qed. *)

Local Transparent make_env sepconj.
Lemma contains_callee_saves_footprint
      j sp b rs0 ofs
      (FOOT: m_footprint
            (contains_callee_saves j sp (fe_ofs_callee_save (make_env b)) (used_callee_save b) rs0)
            sp ofs)
  :
    <<BOUND: fe_ofs_callee_save (make_env b) <=
             ofs < size_callee_save_area b (fe_ofs_callee_save (make_env b))>>
.
Proof.
  destruct b; ss. des_ifs.
  unfold size_callee_save_area. ss.
  clear_tac.
  assert(4 | 8).
  { admit "so ez". }
  assert(0 < align (4 * bound_outgoing) 8 + 8 /\ (4 | align (4 * bound_outgoing) 8 + 8)).
  { hexploit (align_le (4 * bound_outgoing) 8); try lia. i. split; try lia.
    eapply Z.divide_add_r; try lia; ss.
    - etrans; cycle 1. eapply align_divides; try lia. eauto.
  (* TODO: strengthen zsimpl. *)
  }
  (* assert(0 < align (4 * bound_outgoing) 8 + 8 /\ (8 | align (4 * bound_outgoing) 8 + 8)). *)
  (* { hexploit (align_le (4 * bound_outgoing) 8); try lia. i. split; try lia. *)
  (*   eapply Z.divide_add_r; try lia. *)
  (*   - eapply align_divides; try lia. *)
  (*   - refl. *)
  (* (* TODO: strengthen zsimpl. *) *)
  (* } *)
  abstr (align (4 * bound_outgoing) 8 + 8) initofs.
  clear bound_outgoing_pos bound_stack_data_pos bound_local_pos. clear_tac.
  ginduction used_callee_save; ii; ss.
  (* assert((AST.typesize (mreg_type a)) = 4 \/ (AST.typesize (mreg_type a)) = 8). *)
  assert((4 | (AST.typesize (mreg_type a))) /\
         ((AST.typesize (mreg_type a)) | 8) /\ 0 < (AST.typesize (mreg_type a))).
  { destruct a; ss; des_ifs; cbn; splits; try refl; try lia; ss. }
  destruct FOOT.
  - des.
    split.
    + etrans; eauto.
      eapply align_le; try lia.
    + eapply Z.lt_le_trans; eauto.
      etrans; cycle 1.
      { eapply size_callee_save_area_rec_incr; eauto. }
      rewrite ! size_type_chunk.
      refl.
  - exploit IHused_callee_save; revgoals; cycle 1; swap 1 3.
    { eauto. }
    { ss. }
    { esplits; eauto.
      - admit "so ez".
      - admit "so ez".
    }
    { ii. eapply used_callee_save_prop; eauto. }
    { inv used_callee_save_norepet. ss. }
    { ss.
      split.
      - admit "so ze".
      - admit "so ez".
    }
Qed.
Local Opaque make_env sepconj.







Section SIMMODSEM.

Local Existing Instance Val.mi_normal.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Variable rao: Mach.function -> Mach.code -> ptrofs -> Prop.
Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).

Print Instances SimMem.class.
Print Instances SimSymb.class.

Definition msp: ModSemPair.t :=
  ModSemPair.mk (LinearC.modsem skenv_link_src prog) (MachC.modsem rao skenv_link_tgt tprog) tt sm_link
.

Fixpoint last_option X (xs: list X): option X :=
  match xs with
  | [] => None
  | hd :: nil => Some hd
  | hd :: tl => last_option tl
  end
.

Compute last_option (@nil Z).
Compute last_option [1].
Compute last_option [1 ; 2].

Lemma functions_translated_inject
      j
      (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge)
      (SIMGE0: DUMMY_PROP) (* globalenv_inject match_globalenvs *)
      fptr_src fd_tgt fptr_tgt
      (FUNCSRC: Genv.find_funct tge fptr_tgt = Some fd_tgt)
      (INJ: Val.inject j fptr_src fptr_tgt)
  :
    exists fd_src,
      <<FUNCTGT: Genv.find_funct ge fptr_src = Some fd_src>>
      /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>>
.
Proof.
  admit "ez".
Qed.

Hypothesis TRANSL: match_prog prog tprog.

Definition locset_copy (rs: Mach.regset): locset :=
  fun loc =>
    match loc with
    | S _ _ _ => Vundef
    | R r => rs r
    end
.
Hint Unfold locset_copy.

Lemma transf_function_sig
      f tf
      (TRANSFF: transf_function f = OK tf)
  :
    f.(Linear.fn_sig) = tf.(fn_sig)
.
Proof. unfold transf_function in *. des_ifs. Qed.

Lemma init_match_frame_contents_depr
      sm_arg sg
      m_tgt0 rs vs_src vs_tgt ls
      (STORE: StoreArguments.store_arguments sm_arg.(SimMemInj.tgt) rs vs_tgt sg m_tgt0)
      (SG: 4 * size_arguments sg <= Ptrofs.modulus)
      (LS: LocationsC.fill_arguments (locset_copy rs) vs_src (loc_arguments sg) = Some ls)
      (SIMVS: Val.inject_list (SimMemInj.inj sm_arg) vs_src vs_tgt)
      sm_init
      (SM: sm_init = sm_arg.(SimMemInjC.update) sm_arg.(SimMemInj.src) m_tgt0 sm_arg.(SimMemInj.inj))
      (PRIV: forall ofs (BDD: 0 <= ofs < 4 * size_arguments sg),
          SimMemInj.tgt_private sm_init (Mem.nextblock sm_arg.(SimMemInj.tgt)) ofs)
      (MWF: SimMem.wf sm_init)
  :
    m_tgt0
      |= dummy_frame_contents sm_arg.(SimMemInj.inj) ls sg (Mem.nextblock sm_arg.(SimMemInj.tgt)) 0
      ** minjection sm_arg.(SimMemInj.inj) sm_arg.(SimMemInj.src)
      ** globalenv_inject ge sm_arg.(SimMemInj.inj)
.
Proof.
  sep_split.
  { ss. zsimpl. esplits; eauto with lia.
    - zsimpl. apply Z.divide_0_r.
    - inv STORE. hexpl Mem.alloc_result NB. clarify.
    - clear - SG SIMVS STORE LS. inv STORE.
      hexpl LocationsC.fill_arguments_spec. clear LS. clarify.
      hexpl Mem.alloc_result. clarify.
      intros ? ? OFS0 OFS1 ALIGN. zsimpl.
      destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)))).
      + hnf in VALS. generalize (loc_arguments_one sg); intro ONES. abstr (loc_arguments sg) locs.
        clear - OFS0 OFS1 SG H SIMVS VALS locs ONES.
        ginduction locs; ii; ss.
        exploit ONES; eauto. i.
        destruct a; ss.
        des; ss; clarify.
        * inv VALS. inv H2. inv H1. cbn in H5. psimpl. zsimpl. inv SIMVS.
          rewrite Ptrofs.unsigned_repr in *; cycle 1.
          { split; try lia. unfold Ptrofs.max_unsigned.
            generalize (typesize_pos ty); i. xomega.
          }
          esplits; eauto.
        * inv SIMVS. inv VALS. eapply IHlocs; eauto.
      + exploit OUT; eauto. i; des. ss. rewrite H0.
        exploit (Mem.valid_access_load m_tgt0 (chunk_of_type ty)); cycle 1.
        { i; des. esplits; eauto. }
        red. esplits; eauto.
        * erewrite Stackingproof.size_type_chunk in *. rewrite Stackingproof.typesize_typesize in *.
          ii. eapply Mem.perm_implies.
          { eapply PERM. xomega. }
          eauto with mem.
        * rewrite Stackingproof.align_type_chunk. eapply Z.mul_divide_mono_l; eauto.
  }
  { apply disjoint_footprint_sepconj. split.
    - ii; ss. des. clarify. zsimpl. specialize (PRIV ofs). exploit PRIV; eauto with lia.
      intro TPRIV. hnf in TPRIV. ss. des. eapply TPRIV; eauto.
    - ii; ss.
  }
  sep_split.
  { ss. subst sm_init. eapply MWF. }
  { ss. }
  ss.
  admit "ge relax - sim_skenv_inj - ez".
Qed.

Lemma init_match_frame_contents
      sm_arg sg
      m_tgt0 rs vs_src vs_tgt ls
      (STORE: StoreArguments.store_arguments sm_arg.(SimMemInj.tgt) rs (typify_list vs_tgt sg.(sig_args)) sg m_tgt0)
      (SG: 4 * size_arguments sg <= Ptrofs.modulus)
      (LS: LocationsC.fill_arguments (locset_copy rs) (typify_list vs_src sg.(sig_args)) (loc_arguments sg) = Some ls)
      (SIMVS: Val.inject_list (SimMemInj.inj sm_arg) vs_src vs_tgt)
      sm_init
      (SM: sm_init = sm_arg.(SimMemInjC.update) sm_arg.(SimMemInj.src) m_tgt0 sm_arg.(SimMemInj.inj))
      (PRIV: forall ofs (BDD: 0 <= ofs < 4 * size_arguments sg),
          SimMemInj.tgt_private sm_init (Mem.nextblock sm_arg.(SimMemInj.tgt)) ofs)
      (MWF: SimMem.wf sm_init)
  :
    m_tgt0
      |= dummy_frame_contents sm_arg.(SimMemInj.inj) ls sg (Mem.nextblock sm_arg.(SimMemInj.tgt)) 0
      ** minjection sm_arg.(SimMemInj.inj) sm_arg.(SimMemInj.src)
      ** globalenv_inject ge sm_arg.(SimMemInj.inj)
.
Proof.
  sep_split.
  { ss. zsimpl. esplits; eauto with lia.
    - apply Z.divide_0_r.
    - inv STORE. hexpl Mem.alloc_result NB. clarify.
    - clear - SG SIMVS STORE LS. inv STORE.
      hexpl LocationsC.fill_arguments_spec. clear LS. clarify.
      hexpl Mem.alloc_result. clarify.
      intros ? ? OFS0 OFS1 ALIGN. zsimpl.
      destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)))).
      + hnf in VALS. generalize (loc_arguments_one sg); intro ONES. abstr (loc_arguments sg) locs.
        clear - OFS0 OFS1 SG H SIMVS VALS locs ONES FILL.
        abstr (sig_args sg) tys.
        ginduction locs; ii; ss.
        exploit ONES; eauto. i.
        destruct a; ss.
        des; ss; clarify.
        { unfold typify_list in *.
          inv VALS. inv SIMVS; ss; des_ifs.
          inv H3. inv H7.
          exists (typify v' t). esplits; eauto.
          - unfold Mem.loadv in *. ss. psimpl.
            unfold fe_ofs_arg, Ptrofs.max_unsigned in *.
            set (typesize_pos ty). lia.
          - rewrite <- H6.
            eapply inject_typify; eauto. }
        { unfold typify_list in *.
          inv VALS. inv SIMVS; ss; des_ifs.
          eapply IHlocs; eauto. }
      + exploit OUT; eauto. i; des. ss. rewrite H0.
        exploit (Mem.valid_access_load m_tgt0 (chunk_of_type ty)); cycle 1.
        { i; des. esplits; eauto. }
        red. esplits; eauto.
        * erewrite Stackingproof.size_type_chunk in *. rewrite Stackingproof.typesize_typesize in *.
          ii. eapply Mem.perm_implies.
          { eapply PERM. xomega. }
          eauto with mem.
        * rewrite Stackingproof.align_type_chunk. eapply Z.mul_divide_mono_l; eauto.
  }
  { apply disjoint_footprint_sepconj. split.
    - ii; ss. des. clarify. zsimpl. specialize (PRIV ofs). exploit PRIV; eauto with lia.
      intro TPRIV. hnf in TPRIV. ss. des. eapply TPRIV; eauto.
    - ii; ss.
  }
  sep_split.
  { ss. subst sm_init. eapply MWF. }
  { ss. }
  ss.
  admit "ge relax - sim_skenv_inj - ez".
Unshelve. all: eauto.
Qed.

Lemma after_external_parallel_rule
      sm_at sm_after P
      (SEP: SimMemInj.tgt sm_at |= P ** minjection (SimMemInj.inj sm_at) (SimMemInj.src sm_at))
  :
  <<SEP: SimMemInj.tgt sm_after |= P ** minjection (SimMemInj.inj sm_after) (SimMemInj.src sm_after)>>
.
Proof.
  admit "".
Abort.

(* Lemma after_external_match_contents *)
(*       sm_at sm_arg sm_ret sm_after *)
(*       stack cs' *)
(*       (SEP: SimMemInj.tgt sm_at |= stack_contents tprog rao (SimMemInj.inj sm_at) stack cs' ** *)
(*                           minjection (SimMemInj.inj sm_at) (SimMemInj.src sm_at) ** *)
(*                           globalenv_inject (Genv.globalenv prog) (SimMemInj.inj sm_at)) *)
(*       sp sg_arg *)
(*       (UNFR : Mem_unfree (SimMemInj.tgt sm_ret) sp 0 (4 * size_arguments sg_arg) = Some sm_after.(SimMem.tgt)) *)
(*       (MSRC: SimMemInj.src sm_after = SimMemInj.src sm_ret) *)
(*       (MWF1: SimMemInj.wf' sm_after) *)
(*       (MLE: SimMemInj.le' sm_at sm_arg) *)
(*       (MLE0: SimMemInj.le' (SimMemInj.lift' sm_arg) sm_ret) *)
(*       (MLE1: SimMemInj.le' (SimMemInj.unlift' sm_at sm_ret) sm_after) *)
(*       (MLEAFTR: SimMemInj.le' sm_arg (SimMemInj.unlift' sm_arg sm_ret)) *)
(*       (SRCAFTR: (SimMem.src sm_ret) = (SimMem.src sm_after)) *)
(*       (INJAFTR: (SimMemInj.inj sm_ret) = (SimMemInj.inj sm_after)) *)
(*   : *)
(*     sm_after.(SimMem.tgt) *)
(*       |= stack_contents tprog rao (SimMemInj.inj sm_ret) stack cs' ** *)
(*       minjection (SimMemInj.inj sm_ret) (SimMemInj.src sm_ret) ** *)
(*       globalenv_inject (Genv.globalenv prog) (SimMemInj.inj sm_ret) *)
(* . *)
(* Proof. *)
(*   rewrite <- ! MSRC. *)
(*   rewrite ! INJAFTR. *)

(*   rewrite <- sep_assoc in SEP. rewrite <- sep_assoc. *)
(*   destruct SEP as (A & B & DISJ0). (* destruct B as (C & D & DISJ1). *) *)
(*   apply_all_once disjoint_footprint_sepconj. des. *)
(*   Local Opaque globalenv_inject. *)
(*   sep_split; ss. *)
(*   { eapply stack_contents_change_meminj with (j:= (SimMemInj.inj sm_at)). *)
(*     { eapply inject_incr_trans; try apply MLE; eauto. rewrite <- INJAFTR. *)
(*       eapply inject_incr_trans; try apply MLEAFTR; eauto. } *)
(*     eapply after_external_parallel_rule; eauto. *)
(*   } *)
(*   admit "". *)
(* Qed. *)



(* Lemma agree_callee_save_after_external *)
(*       ls0 stk *)
(*       (AGLOCS: agree_callee_save ls0 (parent_locset stk)) *)
(*   : *)
(*     Stackingproof.agree_callee_save_after (locset_after_external ls0) *)
(*                                           (parent_locset (stackframes_after_external stk)) *)
(* . *)
(* Proof. *)
(*   intro. unfold agree_callee_save, stackframes_after_external, locset_after_external in *. *)
(*   destruct stk; simpl in *; eauto. *)
(*   - destruct l; eauto. *)
(*     + intros. rewrite H; eauto. *)
(*     + intros. destruct sl; eauto. *)
(*   - destruct s; simpl. destruct l; intro; auto. *)
(*     + rewrite H. rewrite <- AGLOCS; auto. *)
(*     + destruct sl; auto. *)
(* Qed. *)



(* Lemma match_stacks_after_external *)
(*       j s ts sg *)
(*       (MATCH: match_stacks tprog j s ts sg) *)
(*   : *)
(*     match_stacks tprog j s.(stackframes_after_external) ts sg *)
(* . *)
(* Proof. *)
(*   inv MATCH; econstructor; eauto. inv AGL. econstructor; eauto. intros. erewrite <- agree_unused_reg; eauto. *)
(*   unfold mreg_within_bounds in *. unfold LTL.undef_caller_save_regs. *)
(*   destruct (Conventions1.is_callee_save r) eqn:T; simpl; eauto; try tauto. exfalso. apply H. intros. inv H0. *)
(* Qed. *)



Definition frame_contents_1_at_external f (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
  let b := function_bounds f in
  let fe := make_env b in
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** pure True
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents_at_external f (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) sg :=
  let b := function_bounds f in
  let fe := make_env b in
  mconj (frame_contents_1_at_external f j sp ls ls0 parent retaddr)
        ((* range sp fe_ofs_arg fe.(fe_stack_data) ** *)
         (freed_range sp fe_ofs_arg (4 * (size_arguments sg)) **
         range sp (4 * (size_arguments sg)) fe.(fe_stack_data)) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

Fixpoint stack_contents_at_external (j: meminj) (cs: list Linear.stackframe) (cs': list Mach.stackframe) sg : massert :=
  match cs, cs' with
  | [Linear.Stackframe f _ ls _], [Mach.Stackframe fb (Vptr sp' spofs true) ra _] =>
    (freed_range sp' spofs.(Ptrofs.unsigned) (4 * (size_arguments sg)))
      ** range sp' (4 * (size_arguments sg)) (4 * (size_arguments f.(Linear.fn_sig)))
    (* pure True *)
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' spofs true) ra c' :: cs' =>
      frame_contents_at_external f j sp' ls (parent_locset cs) (parent_sp cs') (parent_ra cs') sg
      ** stack_contents j cs cs'
  | _, _ => pure False
  end.

Ltac sep_simpl_tac :=
  unfold NW in *;
  repeat (try rewrite sep_assoc in *;
          try rewrite sep_pure in *;
          try rewrite stack_contents_nil_left_false in *;
          try rewrite stack_contents_nil_right_false in *;
          try match goal with
              | [H: _ |= pure False |- _] => simpl in H; inv H
              | [H: _ |= _ ** pure False |- _] => apply sep_proj2 in H
              | [H: _ |= _ ** pure False ** _ |- _] => apply sep_pick2 in H
              end;
          idtac
         )
.

Lemma contains_locations_range
      m j sp pos bound slot ls
      (SEP: m |= contains_locations j sp pos bound slot ls)
  :
    <<RANEG: m |= range sp pos (pos + 4 * bound)>>
.
Proof. ss. des. esplits; eauto. ii. eauto with mem. Qed.

Lemma stack_contents_at_external_footprint_split
      j cs cs'
      f sp ls c fb sp' spofs ra c' sg
      (NONNIL: cs <> [])
  :
    m_footprint (stack_contents_at_external j
                                            ((Linear.Stackframe f sp ls c) :: cs)
                                            ((Mach.Stackframe fb (Vptr sp' spofs true) ra c') :: cs') sg)
    =
    (m_footprint (frame_contents_at_external f j sp' ls (parent_locset cs) (parent_sp cs') (parent_ra cs') sg)
                 \2/
                 m_footprint (stack_contents j cs cs'))
.
Proof.
  ii; ss. des_ifs.
Qed.

Lemma frame_contents_1_at_external_impl
      f j sp rs rs0 sp2 retaddr0 sg
      (SZ: 0 <= 4 * size_arguments sg <= fe_stack_data (make_env (function_bounds f)))
  :
    massert_imp
      (frame_contents_1 f j sp rs rs0 sp2 retaddr0)
      (frame_contents_1_at_external f j sp rs rs0 sp2 retaddr0)
.
Proof.
  (* - ii. ss. des. esplits; eauto. *)
  - econs; eauto; ii; ss; des.
    + unfold frame_contents_1, frame_contents_1_at_external in *.
      rewrite sep_comm. rewrite sep_assoc.
      rewrite sep_comm in H. rewrite sep_assoc in H.
      repeat rewrite sep_assoc in *.
      eapply sep_imp; eauto. ss.
    + unfold frame_contents_1, frame_contents_1_at_external in *.
      Local Transparent sepconj.
      ss.
      Local Opaque sepconj.
      des; ss; clarify; eauto.
      * right. right. left. esplits; eauto.
      * right. right. right. left. esplits; eauto.
Qed.

Lemma frame_contents_at_external_impl
      f j sp rs rs0 sp2 retaddr0 sg
      (SZ: 0 <= 4 * size_arguments sg <= fe_stack_data (make_env (function_bounds f)))
  :
    massert_imp
      (frame_contents f j sp rs rs0 sp2 retaddr0 )
      (frame_contents_at_external f j sp rs rs0 sp2 retaddr0 sg)
.
Proof.
  unfold frame_contents, frame_contents_at_external in *.
  unfold fe_ofs_arg.
  eapply mconj_morph_1_Proper; eauto.
  - eapply frame_contents_1_at_external_impl; eauto.
  - eapply sepconj_morph_1_Proper.
    + etrans.
      { eapply range_split0; eauto. }
      eapply sepconj_morph_1_Proper; eauto.
      eapply range_freed_range; eauto.
    + refl.
Qed.

Lemma sepconj_isolated_mutation_strongest
      m0 m1 P P0 P1 CTX CHNG
      (SEP: m0 |= P ** CTX)
      (UNCH: Mem.unchanged_on (~2 CHNG) m0 m1)
      (IMP: massert_imp P P1)
      (PRED: m1 |= P0)
      (ISOL: CHNG <2= P.(m_footprint))
      (ISOL0: P0.(m_footprint) <2= CHNG)
      (ISOL1: P1.(m_footprint) <2= ~2 CHNG)
      (DISJ: disjoint_footprint P0 P1)
  :
    <<SEP: m1 |= P0 ** P1 ** CTX>>
.
Proof.
  destruct SEP as (A & B & C).
  hnf in IMP. des.
  sep_split; eauto.
  { apply disjoint_footprint_sepconj. split; ss. ii. eapply C; eauto. }
  sep_split.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. eapply ISOL1; eauto.
  - ii. eapply C; eauto.
  - eapply m_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    ii. apply ISOL in H1. eauto.
Qed.





Lemma stack_contents_at_external_spec
      sm0 stack cs' sg sp sm1
      (STACKS: match_stacks tge (SimMemInj.inj sm0) stack cs' sg sm0)
      (RSP: parent_sp cs' = Vptr sp Ptrofs.zero true)
      (FREETGT: Mem.free (SimMemInj.tgt sm0) sp 0 (4 * size_arguments sg) = Some (SimMemInj.tgt sm1))
      (SEP: SimMemInj.tgt sm0 |= stack_contents (SimMemInj.inj sm0) stack cs')
  :
  <<SEP: SimMemInj.tgt sm1 |= stack_contents_at_external (SimMemInj.inj sm0) stack cs' sg>>
.
Proof.
  hexploit Mem.nextblock_free; eauto. intro NB.
  destruct stack; ss. destruct cs'; ss. inv STACKS.
  des_ifs_safe.
  destruct stack.
  { des_ifs; sep_simpl_tac. psimpl. unfold dummy_frame_contents in *.
    apply contains_locations_range in SEP. zsimpl.
    eapply range_split0 with (mid := (4 * size_arguments sg)) in SEP; cycle 1.
    { generalize (size_arguments_above sg); i. inv STACKS; des; clarify; ss; split; try lia.
      - erewrite ConventionsC.tailcall_size; eauto. generalize (size_arguments_above sg_init); i. lia.
      - inv STK.
    }
    destruct SEP as (A & B & C).
    sep_split; eauto.
    - ss. esplits; eauto; try lia. i.
      eapply Mem.valid_block_free_1; eauto.
      des. hexploit A1; eauto. i. eapply Mem.perm_valid_block; eauto.
    - eapply m_invar; eauto. hexpl Mem.free_unchanged_on UNCH. ii. ss. des; clarify. lia.
      (* TODO: Fix hexpl tactic *)
  }
  Local Opaque stack_contents.
  destruct cs'; ss.
  { inv STACKS. inv STK. }
  des_ifs_safe.

  exploit Mem.free_unchanged_on; eauto.
  { instantiate (1:= fun blk ofs => blk <> sp \/ ~(0 <= ofs < 4 * size_arguments sg)). ss. ii; des; eauto. }
  intro UNCH.

  unfold frame_contents in SEP.
  exploit frame_env_separated; eauto.
  { apply mconj_proj2 in SEP. rewrite sep_assoc in *. eauto. }
  intro RANGE; des.

  hexploit (bound_outgoing_stack_data (function_bounds f)); eauto. intro OUTGOING.

  generalize (size_arguments_above sg); intro SZ.

  unfold frame_contents_at_external. apply mconj_distr in SEP. des.
  apply mconj_distr. esplits; eauto.
  { clear SEP1.





    eapply sep_imp with (P' := (frame_contents_1_at_external f (SimMemInj.inj sm0) sp rs rs0 sp2 retaddr0))
      in SEP0; eauto; cycle 1.
    { eapply frame_contents_1_at_external_impl with (sg := sg); eauto.
      inv STACKS. split; try lia. }
    eapply m_invar; eauto.
    { eapply Mem.unchanged_on_implies; eauto. bar.
      Local Transparent sepconj.
      s.
      Local Opaque sepconj.
      clear - SZ STACKS RANGE.
      ii; ss. apply not_and_or. ii. des_safe; clarify.
      repeat match goal with
               | [ H: _ |= _ ** _ |- _] =>
                 let name0 := fresh "SEP" in
                 let name1 := fresh "SEP" in
                 let name2 := fresh "SEP" in
                 destruct H as (name0 & name1 & name2)
               | [ H: disjoint_footprint _ (_ ** _) |- _ ] =>
                 apply disjoint_footprint_sepconj in H; desH H
             end.
      (* revert H. *)
      (* repeat match goal with *)
      (*        | [ H: context[stack_contents] |- _ ] => clear H *)
      (*        end *)
      (* . *)
      (* i. *)
      unfold disjoint_footprint in *. ss.
      inv STACKS.
      des; clarify.
      - eapply DISJ0; eauto. esplits; eauto. lia.
      - eapply DISJ4; eauto. esplits; eauto. lia.
      - eapply DISJ7; eauto. esplits; eauto. lia.
      - exploit contains_callee_saves_footprint; eauto. i.
        eapply DISJ6; eauto. esplits; eauto. lia.
      - eapply DISJ9; eauto. esplits; eauto. lia.
    }
  }
  { clear SEP0.


    (* rewrite ! sep_assoc in SEP1. *)
    (* eapply sep_imp with *)
    (*     (P' := (freed_range sp fe_ofs_arg (4 * size_arguments sg) ** *)
    (*                         range sp (4 * size_arguments sg) (fe_stack_data (make_env (function_bounds f))))) *)
    (*   in SEP1; eauto; cycle 1. *)
    (* { etrans. *)
    (*   { eapply range_split0 with (mid := (4 * size_arguments sg)); eauto. inv STACKS. *)
    (*     split; try lia. unfold fe_ofs_arg. generalize (size_arguments_above sg); i; lia. } *)
    (*   eapply sepconj_morph_1_Proper; eauto. *)
    (*   eapply range_freed_range; eauto. *)
    (* } *)


    rewrite ! sep_assoc in *.
    eapply sepconj_isolated_mutation_strongest with
        (CHNG:= (fun b ofs => Mem.valid_block (SimMemInj.tgt sm0) b /\ b = sp
                              /\ 0 <= ofs < 4 * size_arguments sg)); try eassumption.
    - eapply Mem.unchanged_on_implies; eauto. ii; ss. apply not_and_or. ii. des. eauto.
    - etrans.
      { eapply range_split0 with (mid := (4 * size_arguments sg)); eauto.
        unfold fe_ofs_arg. inv STACKS. split; lia. }
      rewrite sepconj_sym. rewrite add_pure_r_eq.
      eapply sepconj_morph_1_Proper; eauto. ss.
    - ss. unfold fe_ofs_arg. esplits; eauto with lia.
      + apply sep_pick1 in SEP1. ss. des. inv STACKS. lia.
      + i. eapply Mem.valid_block_free_1; eauto.
        apply sep_pick1 in SEP1. eapply range_nonnil_valid_block; eauto.  unfold fe_ofs_arg. inv STACKS. lia.
    - u. ii; ss. des. esplits; eauto. inv STACKS. lia.
    - u. ii; ss. des; clarify.
      esplits; eauto.
      apply sep_pick1 in SEP1. eapply range_nonnil_valid_block; eauto. unfold fe_ofs_arg in *. inv STACKS. lia.
    - u. ii. des; clarify. lia.
    - unfold disjoint_footprint. u. ii; des; clarify. lia.
  }
Unshelve.
  all: econs.
Qed.


Local Transparent stack_contents.


Local Transparent sepconj.
Lemma m_footprint_sepconj_le
      P0 Q0 P1 Q1
      (LEP: P0.(m_footprint) <2= P1.(m_footprint))
      (LEQ: Q0.(m_footprint) <2= Q1.(m_footprint))
  :
    <<LE: (P0 ** Q0).(m_footprint) <2= (P1 ** Q1).(m_footprint)>>
.
Proof. ii; ss. des; ss; eauto. Qed.
Local Opaque sepconj.

(* Lemma stack_contents_footprint_irr *)
(*       j0 j1 cs cs' *)
(*   : *)
(*     m_footprint (stack_contents tprog rao j0 cs cs') = m_footprint (stack_contents tprog rao j1 cs cs') *)
(* . *)
(* Proof. *)
(*   clear ge tge. clear_tac. *)
(*   repeat (apply functional_extensionality; i). *)
(*   apply prop_ext. *)
(*   split; i. *)
(*   - ginduction cs; ii; ss; des_ifs. *)
(*     + ss. des_ifs. *)
(* Qed. *)

(* Lemma stack_contents_at_external_after_footprint *)
(*       j0 j1 cs cs' sg *)
(*       j2 *)
(*       (STACKS: match_stacks tprog j2 cs cs' sg) *)
(*   : *)
(*     m_footprint (stack_contents tprog rao j0 (stackframes_after_external cs) cs') <2= *)
(*     m_footprint (stack_contents_at_external j1 cs cs' sg) *)
(* . *)
(* Proof. *)
(*   clear ge tge. clear_tac. *)
(*   inv STACKS; i; ss. *)
(*   { admit "". } *)
(*   des_ifs; try (by inv STK). *)
(*   eapply m_footprint_sepconj_le; cycle 1. *)
(*   { refl. } *)
(*   ss. des_ifs_safe. *)
(*   des_ifs; try (by inv STACKS; ss). *)
(*   - admit "". *)
(*   - admit "". *)
(*   ss. *)
(*   destruct cs, cs'; ss; des_ifs_safe. *)
(*   { destruct s; ss. } *)
(*   destruct cs, cs'; ss; des_ifs_safe. *)
(* Qed. *)

(* Lemma stack_contents_at_external_after_footprint *)
(*       j0 j1 j2 cs cs' sg *)
(*       (STACKS: match_stacks tprog j2 cs cs' sg) *)
(*       sp *)
(*       (RSP: parent_sp cs' = Vptr sp Ptrofs.zero true) *)
(*   : *)
(*     m_footprint (stack_contents tprog rao j0 (stackframes_after_external cs) cs') <2= *)
(*     (m_footprint (stack_contents_at_external j1 cs cs' sg) \2/ (brange sp 0 (4 * size_arguments sg))) *)
(* . *)
(* Proof. *)
(*   pose cs as X. pose cs' as Y. *)
(*   { *)
(*     clear_tac. clear ge tge. clear_tac. *)
(*     ginduction cs; i; ss; des_ifs_safe. *)
(*     inv STACKS. *)
(*     { ss. clarify. des_safe; clarify. psimpl. zsimpl. admit "". } *)
(*     exploit match_stacks_sp_ofs; eauto. i; des. *)
(*     hexploit IHcs; eauto. i; des. *)
(*     des_ifs. *)
(*     { inv STK. } *)
(*     ss. *)
(*   } *)
(*   destruct cs; ss. des_ifs_safe. *)
(*   inv STACKS; ss. *)
(*   - ii. des_safe. u. psimpl. zsimpl. des; clarify. *)
(*     + right. esplits; eauto. *)
(*     + left. *)
(*       Local Transparent sepconj. *)
(*       s. *)
(*       Local Opaque sepconj. *)
(*       u. right. esplits; eauto. rewrite ConventionsC.tailcall_size; ss. *)
(*   - des_ifs_safe. *)
(*     inv STK; ss. *)
(*     + u. admit "". *)
(* Qed. *)

Definition current_function (stk: Linear.stackframe): Linear.function :=
  match stk with
  | Linear.Stackframe f _ _ _ => f
  end
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Linear.state) (st_tgt0: MachC.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: StackingproofC0.match_states ge tge st_src0 st_tgt0.(st) sm0)
    (MCOMPATSRC: st_src0.(LinearC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(st).(get_mem) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (INITRS: exists dummy_stack_src,
        <<DUMMY: st_src0.(LinearC.get_stack).(last_option) = Some dummy_stack_src>> /\
        <<AGREE: agree_regs sm0.(SimMemInj.inj) dummy_stack_src.(current_locset) st_tgt0.(init_rs)>> /\
        <<GOOD: forall
                   mr
                   (CALLEESAVE: Conventions1.is_callee_save mr)
                 ,
                   <<EQ: dummy_stack_src.(current_locset) (R mr) = st_tgt0.(init_rs) mr>>
                   /\ <<PTRFREE: ~ is_real_ptr (st_tgt0.(init_rs) mr)>>>> /\
        <<SIG: dummy_stack_src.(current_function).(Linear.fn_sig) = st_tgt0.(init_sg)>>)
.

Inductive match_states_at
          (st_src0: Linear.state) (st_tgt0: MachC.state) (sm_at sm_arg: SimMem.t): Prop :=
| match_states_at_intro
    (INJ: sm_at.(SimMemInj.inj) = sm_arg.(SimMemInj.inj))
    (INJ: sm_at.(SimMem.src) = sm_arg.(SimMem.src))
    init_rs init_sg cs' tfptr rs sp skd fptr cs ls
    (SRCST: st_src0 = Linear.Callstate cs fptr (SkEnv.get_sig skd) ls (SimMemInj.src sm_arg))
    (TGTST: st_tgt0 = mkstate init_rs init_sg (Callstate cs' tfptr rs (SimMemInj.tgt sm_at)))
    (RSP: parent_sp cs' = Vptr sp Ptrofs.zero true)
    (PRIV: brange sp 0 (4 * size_arguments (SkEnv.get_sig skd)) <2= sm_arg.(SimMemInj.tgt_private))
    (SIG: Genv.find_funct skenv_link_src fptr = Some skd)
    (VALID: Mem.valid_block (SimMemInj.tgt sm_arg) sp)
    (NB: sm_at.(SimMem.tgt).(Mem.nextblock) = sm_arg.(SimMem.tgt).(Mem.nextblock))
    (SEP: SimMemInj.tgt sm_arg |= stack_contents_at_external (SimMemInj.inj sm_arg) cs cs' (SkEnv.get_sig skd)
                        ** minjection (SimMemInj.inj sm_arg) (SimMemInj.src sm_arg) **
                        globalenv_inject ge (SimMemInj.inj sm_arg))
.

(* TODO: Move to LocationsC *)
Lemma loc_result_one
      sg
  :
    exists mr_res, <<ONE: loc_result sg = One mr_res>>
.
Proof. compute. des_ifs; eauto. Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  eapply match_states_sim with (match_states := match_states) (match_states_at := match_states_at)
                               (sound_state := fun _ _ => wt_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply wt_state_local_preservation; eauto.
    eapply wt_prog; eauto.
  - (* init bsim *)
    {
      inv INITTGT. inv STORE. folder.
      inv SIMARGS. ss.
      exploit functions_translated_inject; eauto.
      { admit "match genvs ez". }
      i; des.
      destruct fd_src; ss. unfold bind in *. des_ifs.
      hexpl transf_function_sig SG.
      assert(LEN0: length (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f))) =
                   length (loc_arguments (Linear.fn_sig f))).
      {
        etransitivity.
        - unfold typify_list. rewrite zip_length. erewrite SimMem.sim_val_list_length; try apply VALS0. ss.
        - symmetry. rewrite SG.
          (* eapply extcall_arguments_imply in VALS. *)
          erewrite extcall_arguments_length; eauto with congruence.
          assert((length targs) = (length (sig_args (fn_sig fd)))).
          { erewrite <- extcall_arguments_length; eauto. erewrite loc_arguments_length; eauto. }
          inv TYP. xomega.
      }
      exploit (LocationsC.fill_arguments_progress (locset_copy rs)
                                       (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f)))
                                       (* args_src.(Args.vs) *)
                                       (loc_arguments f.(Linear.fn_sig))); eauto. i; des.
      exploit (LocationsC.fill_arguments_spec
                 (typify_list (Args.vs args_src) (sig_args (Linear.fn_sig f)))
                 (* args_src.(Args.vs) *)
                 f.(Linear.fn_sig)); eauto. i; des.
      exploit SimMemInjC.mach_store_arguments_simmem; eauto.
      { econs; eauto with congruence. rp; eauto. }
      i; des.

      esplits.
      { (* initial frame *)
        econs; eauto with congruence; cycle 2.
        - ii. hexpl OUT.
        - inv TYP.
          econs; eauto with congruence.
          erewrite SimMem.sim_val_list_length; try apply VALS0. ss.
          etrans; eauto with congruence.
        - ii. hexpl OUT.
          destruct loc; ss.
          + hexploit PTRFREE; eauto.
            { rewrite <- SG. eauto. }
            ii; eauto with congruence.
          + rewrite OUT0 in *. ss.
      }
      { eauto. }
      { (* match states *)
        assert(INITRS: agree_regs (SimMemInj.inj sm_arg) ls1 rs).
        {
          ii. destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (Linear.fn_sig f))))).
          * red in VALS. inv TYP. rewrite <- SG in *. clear - FILL VALS VALS0 H.
            generalize (loc_arguments_one (Linear.fn_sig f)). i.
            abstr (loc_arguments (Linear.fn_sig f)) locs. clear_tac.
            abstr (Args.vs args_src) vals_src. abstr (Args.vs args_tgt) vals_tgt. clear_tac.
            abstr (sig_args (Linear.fn_sig f)) tys. clear_tac.

            unfold typify_list in *.
            ginduction locs; ii; ss.
            exploit H0; eauto. i. destruct a; ss. des; clarify.
            { inv VALS. destruct vals_tgt; ss. des_ifs. inv VALS0.
              rename H4 into EARGP. inv EARGP. rename H2 into EARG. inv EARG; ss.
              clarify. rewrite <- H4. rewrite H.
              eapply inject_typify; eauto.
            }
            inv VALS. destruct vals_tgt; ss. des_ifs. inv VALS0.
            unfold typify_list in *. ss. des_ifs.
            eapply IHlocs; eauto.
          * (* eapply Loc_not_in_notin_R in H; eauto. *)
            hexploit PTRFREE; eauto.
            { rewrite <- SG. eauto. }
            i. rewrite OUT; ss.
            eapply fakeptr_inject_id; eauto.
        }
        rename targs into targs_tgt. rename TYP into TYPTGT.
        (* assert(TYPSRC: exists targs_src, typecheck (Args.vs args_src) (fn_sig fd) targs_src). *)
        (* { esplits; eauto. econs; eauto. inv TYPTGT. rewrite <- LEN. clear - VALS0. admit "ez". } *)
        (* des. *)
        econs; ss; eauto.
        - econs; ss; eauto.
          + clarify.
          + econs; ss; eauto. eapply loc_arguments_bounded.
          + psimpl. zsimpl. rewrite SG.
            rewrite MEMSRC. rewrite MEMTGT.
            eapply init_match_frame_contents with (vs_src := (Args.vs args_src))
                                                  (vs_tgt := (Args.vs args_tgt)(* targs_tgt *)); eauto.
            * inv TYPTGT. econs; eauto. rewrite <- MEMTGT. ss.
            * inv TYPTGT. unfold Ptrofs.max_unsigned in *. xomega.
            * rewrite <- SG. eauto with congruence.
          (* + i; des. admit "ge relax, ez". *)
        - clarify.
        - clarify.
        - esplits; ss.
          + ss. clarify; ss.
          + i. ss. split.
            * erewrite OUT; ss. ii. hexpl loc_arguments_acceptable_2 ACCP. ss. clarify.
            * eapply PTRFREE. ii. hexpl loc_arguments_acceptable_2 ACCP. ss. clarify.
      }
    }
  - (* init progress *)
    admit "Use MachC.store_arguments_progress".
  - (* callstate wf *)
    inv MATCH; ss.

  - (* call fsim *)
    inv CALLSRC. inv MATCH; ss. clarify.
    inv MATCHST; ss. destruct st_tgt0; ss. clarify. ss. clarify.
    des. exploit wt_callstate_agree; eauto. intros [AGCS AGARGS].
    assert(MCOMPAT0: sm0.(SimMemInj.inj) = j). { inv MCOMPAT. ss. } clarify.

    hexpl match_stacks_sp_ofs RSP.
    hexploit arguments_perm; eauto. { eapply sep_drop_tail3 in SEP. eauto. } i; des. psimpl.
    hexploit arguments_private; eauto. { eapply sep_drop_tail3 in SEP. eauto. } i; des. psimpl.
    hexploit Mem.range_perm_free. { ii. spc H. zsimpl. eapply H; eauto. } intros [m_tgt0 FREETGT].
    exploit transl_external_arguments; eauto. { apply sep_pick1 in SEP. eauto. } intro ARGS; des.

    assert(VALID: Mem.valid_block (SimMemInj.tgt sm0) sp).
    { admit "Strengthen match_states - this might be done while strengthening Stackingproof.v". }

    exploit SimMemInj.free_right; eauto.
    { u. ii. esplits; eauto.
      do 2 spc H0. zsimpl. eauto.
    }
    i; des. clarify.

    hexpl Mem.nextblock_free NB.
    esplits; eauto.
    + econs; eauto.
      * folder. admit "ge relax - ez".
      * admit "SIMSKENVLINK - ez".
    + econs; ss; eauto with congruence.
    + econs; eauto with congruence.
      * rp; eauto.
      * u. ii. des; clarify. specialize (H0 x1). zsimpl. esplits; eauto.
        { rp; [eapply H0; eauto|..]; eauto. }
        { unfold Mem.valid_block in *. eauto with congruence. }
      * rewrite <- sep_assoc. rewrite sep_comm.
        eapply globalenv_inject_incr with (j:= sm0.(SimMemInj.inj)); eauto.
        { rewrite <- MINJ. eapply inject_incr_refl. }
        { eapply SimMemInj.inject_separated_frozen. rewrite <- MINJ. eapply SimMemInj.frozen_refl. }
        rewrite <- sep_assoc in SEP. rewrite sep_comm in SEP. bar. move SEP at bottom.
        destruct SEP as (A & B & C).
        sep_split.
        { eapply m_invar; eauto. ss. eapply Mem_unchanged_on_bot; eauto.
          rewrite NB. refl. }
        { ss. }
        destruct B as (D & E & F).
        sep_split; revgoals.
        { ss. eapply MWF1. }
        { admit "Compared to C, left footprint: <=. right footprint: =.". }
        rewrite MINJ.
        eapply stack_contents_at_external_spec; eauto.

  - (* after fsim *)
    des.
    (* assert(WTST1: wt_state st_src1). *)
    (* { hexploit (@wt_state_local_preservation prog (wt_prog _ _ TRANSL) skenv_link_src); eauto. *)
    (*   intro PRSV. inv PRSV. *)
    (*   inv HISTORY. ss. *)
    (*   hexploit CALL; eauto. *)
    (*   { eapply sm_init.(SimMemInj.src). } *)
    (*   { apply tt. } *)
    (*   i; des. *)
    (*   eapply K; eauto. *)
    (* } *)
    inv AFTERSRC. inv MATCH; ss. clarify.
    inv MATCHST; ss. destruct st_tgt0; ss. clarify. ss. clarify.
    assert(MCOMPAT0: sm0.(SimMemInj.inj) = j). { inv MCOMPAT; ss. } clarify.

    hexpl match_stacks_sp_ofs RSP.
    inv SIMRET.

    assert(VALID: Mem.valid_block (SimMemInj.tgt sm0) sp).
    { inv HISTORY. inv MATCHARG. ss. clarify. eauto with congruence. }
    assert(exists m_tgt0, <<UNFR: Mem_unfree sm_ret.(SimMemInj.tgt) sp 0 (4 * size_arguments sg_arg)
                                  = Some m_tgt0>>).
    { eapply Mem_unfree_suceeds; eauto.
      - unfold Mem.valid_block in *. eapply Plt_Ple_trans; eauto. etransitivity; try eapply MLE. eapply MLEAFTR.
      - inv HISTORY. inv CALLSRC. inv CALLTGT. rewrite RSP in *. clarify. psimpl. zsimpl. inv SIMARGS. ss. clarify.
        assert(sg = sg_arg).
        { des. clarify. clear - SIG SIG0 FPTR0 SIMSKENV. admit "ez". }
        clarify.
        assert(NP: Mem_range_noperm (SimMemInj.tgt sm_arg) blk 0 (4 * size_arguments sg_arg)).
        { eapply Mem_free_noperm; eauto. }
        eapply Mem_unchanged_noperm; try apply NP; eauto.
        + eapply Mem.unchanged_on_implies; try apply MLE0. ii. ss.
          u. esplits; eauto.
          hexploit arguments_private; eauto.
          { eapply sep_drop_tail3 in SEP. eauto. }
          i; des. psimpl. spc H1. zsimpl. inv MATCHARG. rewrite <- MEMSRC0. rewrite <- INJ. u in H. des; clarify.
          eapply H1. eauto.
        + eapply Mem.valid_block_free_1; eauto.
    }
    des.

    exploit (@SimMemInjC.unfree_right _ (SimMemInj.unlift' sm_arg sm_ret)); try apply UNFR; eauto.
    { admit "strengthen match_stacks". }
    i; des. ss.

    exists sm1; esplits; eauto.
    + econs; eauto.
      * admit "SIMSKENVLINK - ez".
      * rewrite MEMTGT. inv MWFAFTR. ss.
        etrans; eauto.
        inv MLE. rewrite <- TGTPARENTEQNB.
        inv SIMSKENV. inv SIMSKELINK. ss. rr in SIMSKENV. rewrite <- SIMSKENV. ss.
      * psimpl. zsimpl. rp; eauto.
    + econs; ss; eauto with congruence; cycle 1.
      { assert(MLE2: SimMemInj.le' sm0 sm1).
        { etrans; eauto. etrans; eauto. }
        clear - MLE2 GOOD DUMMY AGREE STACKS. destruct stack; ss; des_ifs; ss.
        { esplits; ss; eauto; ss. eapply agree_regs_inject_incr; eauto. apply MLE2. }
        rewrite DUMMY. esplits; eauto.
        eapply agree_regs_inject_incr; eauto. apply MLE2.
      }
      assert(WTST: wt_state (Linear.Returnstate stack
       (Locmap.setpair (loc_result sg_arg) (typify (Retv.v retv_src) (proj_sig_res sg_arg))
          (LTL.undef_caller_save_regs ls_arg)) (Retv.m retv_src))).
      { admit "somehow". }
      inv WTST.
      eapply match_states_return with (j:= sm_ret.(SimMemInj.inj)); eauto.
      * econs; ss; eauto. admit "this is not true!!!".
      * (* eapply match_stacks_after_external; eauto. *)
        eapply match_stacks_change_meminj; try apply STACKS.
        { eapply inject_incr_trans; try apply MLE0. refl. }
        admit "raw admit - use match_stacks_le?".
      * eapply agree_regs_set_pair; cycle 1.
        { unfold typify_opt, typify. des_ifs. }
        (* TODO: Remove Mach.regset_after_external *)
        change regset_after_external with undef_caller_save_regs.
        eapply agree_regs_undef_caller_save_regs; eauto.
        eapply agree_regs_inject_incr; eauto.
        eapply inject_incr_trans; try apply MLE0. ss. apply MLE.
      * unfold typify_opt. unfold proj_sig_res in *. des_ifs; ss.
        { ii. erewrite <- AGCS; eauto. rewrite ! locmap_get_set_loc_result_callee_save; ss. }
      * bar. move HISTORY at bottom. inv HISTORY. inv MATCHARG. ss. clarify.
        rename sm0 into sm_at. rename sm1 into sm_after.
        rewrite RSP0 in *. clarify.
        hexpl Mem_nextblock_unfree NB.
        rewrite <- sep_assoc. rewrite sep_comm.
        rewrite <- sep_assoc in SEP0. rewrite sep_comm in SEP0. destruct SEP0 as (A & B & C).
        sep_split.
        { eapply globalenv_inject_incr_strong with (j:= sm_arg.(SimMemInj.inj)); eauto.
          - inv MLE0. ss.
          - eapply SimMemInj.inject_separated_frozen.
            inv MLE0. ss. inv MWF2.
            eapply SimMemInj.frozen_shortened; eauto.
            + refl.
            + refl.
          - rewrite <- NB0. inv MLE0; ss. clear - TGTUNCHANGED. change Pos.le with Ple. eauto with mem.
        }
        { ss. }
        rewrite sep_comm. rewrite sep_comm in B. destruct B as (D & E & F).
        sep_split.
        { ss. rp; try eapply MWF2; eauto with congruence. }
        { hexploit minjection_disjoint_footprint_private; eauto. intro PRIV0.
          rewrite MEMSRC. eapply minjection_private_disjoint_footprint.
          assert(SimMemInj.tgt_private sm_arg <2= SimMemInj.tgt_external sm_ret).
          { clear - MLE0. inv MLE0. ss. rewrite <- TGTPARENTEQ. ss. }
          inv MWF.
          etrans; try eassumption; eauto.
          etrans; try eassumption; eauto.

          etrans; try eassumption; eauto.
          admit "footprint eq".

          (* Lemma less2_divide_r *)
          (*       X0 X1 *)
          (*       (A B0 B1 B: X0 -> X1 -> Prop) *)
          (*       (LESS0: B0 <2= B) *)
          (*       (LESS1: B1 <2= B) *)
          (*       (LESS: A <2= (B0 \2/ B1)) *)
          (*   : *)
          (*     A <2= B *)
          (* . *)
          (* Proof. ii. apply LESS in PR. des; eauto. Qed. *)
          (* eapply less2_divide_r. *)
          (* { eapply PRIV. } *)
          (* { eapply PRIV0. } *)
          (* etrans; try eassumption; eauto. *)
        }
        (*   ss. *)
        (*   - clear - MLE0. ss. u. ii. des. hexpl Mem.perm_valid_block VL. inv MLE0. ss. *)
        (*     destruct (SimMemInj.inj sm_arg b0) eqn:T. *)
        (*     exploit H; eauto. *)
        (*     esplits; eauto. *)
        (*     + ii. exploit INCR; eauto. i; clarify. *)
        (* } *)
        assert(STEP0: SimMemInj.tgt sm_ret |= stack_contents_at_external (SimMemInj.inj sm_arg)
                                    cs cs'0 (SkEnv.get_sig skd)).
        { eapply m_invar; eauto. inv MLE0. ss. eapply Mem.unchanged_on_implies; eauto.
          ii. eapply minjection_disjoint_footprint_private; eauto. }

        assert(STEP1: SimMemInj.tgt sm_ret |= stack_contents_at_external (SimMemInj.inj sm_ret)
                                    cs cs'0 (SkEnv.get_sig skd)).
        { About stack_contents_change_meminj. admit "this should hold". }

        admit "this shold hold in high level. Low level details may differ".

  - (* final fsim *)
    inv FINALSRC. inv MATCH. inv MATCHST.
    exploit match_stacks_sp_ofs; eauto; intro RSP; des_safe.

    (* note: this lemma is not useful here *)
    (* hexploit arguments_private; eauto. *)
    (* { apply sep_drop_tail3 in SEP. eauto. } *)
    (* intro PRIVTGT. *)

    ss; clarify.
    des_ifs; sep_simpl_tac; des; ss. Undo 1.
    des_ifs; sep_simpl_tac; des_safe; ss. Undo 1. (*** TODO: Fix des_safe with check_safe!! ***)
    (* assert(AGLOCS0: Stackingproof.agree_callee_save_after ls0 ls_init). *)
    (* { des; ss. ii. eapply AGLOCS. des_ifs; ss. } *)
    (* clear AGLOCS. *)
    (* sguard in AGLOCS. *)
    des.
    des_ifs; sep_simpl_tac; des; ss.
    (* unsguard AGLOCS. *)
    destruct st_tgt0; ss. clarify. ss. clarify. ss.
    inv STACKS.
    hexploit (loc_result_one init_sg); eauto. i; des_safe.
    unfold dummy_frame_contents in *. psimpl.
    hexploit (Mem.range_perm_free sm0.(SimMemInj.tgt) sp 0 (4 * (size_arguments init_sg))); eauto.
    { clear - SEP. apply sep_pick1 in SEP. rr in SEP. des. eauto with xomega. }
    intros (sm_tgt1 & FREETGT).

    assert(j = sm0.(SimMemInj.inj)).
    { admit "Strengthen stackingproof". }
    clarify.

    exploit SimMemInj.free_right; eauto.
    { clear - SEP.
      apply sep_drop_tail3 in SEP.
      destruct SEP as (A & B & DISJ). ss. des. zsimpl. clear_tac.
      ii. rr in DISJ.
      rr. esplits; eauto; cycle 1.
      { admit "sp is valid block". }
      specialize (DISJ sp ofs). ss.
      ii. exploit DISJ; eauto.
    }
    i; des_safe. rename sm1 into sm_ret.

    eexists sm_ret, (Retv.mk _ _). esplits; eauto; cycle 1.
    + econs; ss; eauto.
      * rewrite ONE. ss. specialize (AGREGS mr_res).
        eapply val_inject_incr; try apply MLE; eauto.
    + econs; eauto.
      * ii. specialize (AGLOCS (R mr)). ss. specialize (GOOD mr H). des_safe.
        rewrite <- GOOD. rewrite <- AGLOCS; ss.
        destruct (Val.eq (ls0 (R mr)) Vundef).
        { rewrite e. ss. }
        specialize (AGREGS mr). inv AGREGS; ss.
        exfalso.
        eapply GOOD0. rewrite <- GOOD. rewrite <- AGLOCS; ss. rewrite <- H0. ss.

  - (* step lemma *)
    admit "".

Unshelve.
  all: ss.
  all: try (by econs).
  all: try apply Mem.empty.
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Variable rao: function -> code -> ptrofs -> Prop.

Hypothesis TRANSF: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (LinearC.module prog) (MachC.module tprog rao) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - admit "easy".
  - ii. eapply sim_modsem; eauto.
Unshelve.
Qed.

End SIMMOD.


(* (* Section DUMMY_FUNCTION. *) *)

(* (*   Variable sg: signature. *) *)

(* (*   Lemma dummy_function_used_callee_save *) *)
(* (*     : *) *)
(* (*     (dummy_function sg).(function_bounds).(used_callee_save) = [] *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_bound_local *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_local) = 0 *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_bound_outgoing *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_outgoing) = (size_arguments sg) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     ss. unfold dummy_function. cbn. *) *)
(* (*     rewrite Z.max_l; try xomega. rewrite Z.max_r; try xomega. *) *)
(* (*     generalize (size_arguments_above sg). i. xomega. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_bound_stack_data *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_stack_data) = 0 *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_size_callee_save_area *) *)
(* (*         ofs *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(size_callee_save_area) ofs = ofs *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_local *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_local) = (align (4 * size_arguments sg) 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_link *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_link) = (align (4 * size_arguments sg) 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     ss. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_retaddr *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_retaddr) = (align (4 * size_arguments sg) 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_size *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_size) = (align (4 * size_arguments sg) 8 + 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. *) *)
(* (*     (*??????????????? simpl. -> inf loop, but cbn works!!!!!!!!!!!!! *) *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (* End DUMMY_FUNCTION. *) *)

(* (* Hint Rewrite dummy_function_used_callee_save: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_local: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_outgoing: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_stack_data: dummy. *) *)
(* (* Hint Rewrite dummy_function_size_callee_save_area: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_local: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_link: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_retaddr: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_size: dummy. *) *)

(* Print typesize. *)
(* Print loc_arguments_64. (* always + 2 *) *)
(* (* Lemma loc_arguments_64_complete *) *)
(* (*       x tys ir fr *) *)
(* (*       (SIZE0: x < 4 * size_arguments_64 tys ir fr 0) *) *)
(* (*       (SIZE1: 0 <= x) *) *)
(* (*       (IR: 0 <= ir) *) *)
(* (*       (FR: 0 <= fr) *) *)
(* (*   : *) *)
(* (*     exists sl pos ty, <<IN: In (S sl pos ty) (loc_arguments_64 tys ir fr 0).(regs_of_rpairs)>> *) *)
(* (*                             /\ <<OFS: pos <= x < pos + 4 * ty.(typesize)>> *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   ginduction tys; ii; ss. *) *)
(* (*   { xomega. } *) *)
(* (*   destruct a; ss. *) *)
(* (*   - des. *) *)
(* (*     des_ifs; try (exploit IHtys; eauto; try xomega; i; des; []; esplits; eauto; ss; right; eauto). *) *)
(* (*     assert(6 <= ir). *) *)
(* (*     { xomega. } *) *)
(* (*     ss. esplits; eauto; try xomega. ss. rewrite Z.add_0_l in *. rewrite Z.mul_1_r. *) *)
(* (*     unfold size_arguments_64 in SIZE0. ss. des_ifs. *) *)
(* (*     u in SIZE0. *) *)
(* (*     destruct ir; try xomega. *) *)
(* (*     ss. *) *)
(* (*   - *) *)
(* (* Qed. *) *)

(* (* Lemma size_arguments_loc_arguments *) *)
(* (*       ofs sg *) *)
(* (*       (SIZE: 0 <= ofs < 4 * size_arguments sg) *) *)
(* (*   : *) *)
(* (*     exists sl pos ty, In (S sl pos ty) (loc_arguments sg).(regs_of_rpairs) *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   destruct sg; ss. unfold size_arguments in *. unfold loc_arguments in *. des_ifs_safe. ss. clear_tac. *) *)
(* (*   ginduction sig_args; ii; ss. *) *)
(* (*   { xomega. } *) *)
(* (* Qed. *) *)










(* (* TODO: Move to CoqlibC *) *)
(* Ltac psimpl := *)
(*   repeat (try rewrite ! Ptrofs.unsigned_zero in *; *)
(*           try rewrite ! Ptrofs.add_zero in *; *)
(*           try rewrite ! Ptrofs.add_zero_l in *; *)
(*           try rewrite ! Ptrofs.repr_unsigned in *; *)
(*           try rewrite ! IntegersC.Ptrofs_add_repr in *; *)
(*           try (rewrite Ptrofs.unsigned_repr in *; ss; try xomega; []) *)
(*          ) *)
(* . *)






(* Section ARGPASSING. *)

(* Local Existing Instance Val.mi_final. *)

(* (* Lemma store_stored_inject *) *)
(* (*       j0 m_src0 m_src1 m_tgt *) *)
(* (*       (INJ: Mem.inject j0 m_src0 m_tgt) *) *)
(* (*       v_src v_tgt *) *)
(* (*       (INJV: Val.inject j0 v_src v_tgt)  *) *)
(* (*       ty rsp_src rsp_tgt rspdelta ofs *) *)
(* (*       (SRC: Mem.storev (chunk_of_type ty) m_src0 (Vptr rsp_src ofs true) v_src = Some m_src1) *) *)
(* (*       (TGT: Mem_stored (chunk_of_type ty) m_tgt rsp_tgt (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) v_tgt) *) *)
(* (*       (INJRSP: j0 rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned))) *) *)
(* (*   : *) *)
(* (*     <<INJ: Mem.inject j0 m_src1 m_tgt>> *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   ss. red. *) *)
(* (*   exploit Mem.store_mapped_inject; eauto. i; des. *) *)
(* (*   eapply Mem.inject_extends_compose; eauto. *) *)
(* (*   clear - TGT H. *) *)
(* (* Local Transparent Mem.store. *) *)
(* (*   hexploit MemoryC.Mem_store_perm_eq; eauto. intro PERM. des. *) *)
(* (*   replace (Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta) with *) *)
(* (*       (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) in *; cycle 1. *) *)
(* (*   { rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; ss. split; try xomega. *) *)
(* (*     hexploit (Ptrofs.unsigned_range ofs); eauto. i. *) *)
(* (*     hexploit (Ptrofs.unsigned_range rspdelta); eauto. i. *) *)
(* (*     xomega. *) *)
(* (*   } *) *)
(* (*   abstr (Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta) ofs0. *) *)
(* (*   unfold Mem.store in *. inv TGT. des_ifs. *) *)
(* (*   econs; eauto. *) *)
(* (*   unfold inject_id. *) *)
(* (*   econs; ss; eauto. *) *)
(* (*   - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss. *) *)
(* (*   - ii; clarify. unfold Mem.range_perm, Mem.perm in *. ss. rewrite Z.divide_0_r. reflexivity. *) *)
(* (*   - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss. *) *)
(* (*     rewrite Maps.PMap.gsspec. des_ifs; cycle 1. *) *)
(* (*     { apply memval_inject_refl. } *) *)
(* (*     rewrite <- STORED. *) *)
(* (*     rename rsp_tgt into b. abstr (chunk_of_type ty) chunk. clear_tac. *) *)
(* (*     destruct chunk; ss; rewrite ! Maps.ZMap.gsspec; des_ifs; try apply memval_inject_refl. *) *)
(* (* Qed. *) *)

(* Lemma B2C_mem_inject *)
(*       j m_alloc ls_arg sg m_arg m_tgt *)
(*       (INJ: Mem.inject j m_alloc m_tgt) *)
(*       (* rsp_src rsp_tgt *) *)
(*       (* (INJRSP: Val.inject j rsp_src rsp_tgt) *) *)
(*       blk_src blk_tgt (* delta *) *)
(*       (INJRSP: j blk_src = Some (blk_tgt, 0)) *)
(*       (* (DELTA: 0 <= delta <= Ptrofs.max_unsigned) *) *)
(*       (BCM: Call.B2C_mem m_alloc (Vptr blk_src Ptrofs.zero true) ls_arg *)
(*                     (regs_of_rpairs (loc_arguments sg)) = Some m_arg) *)
(*       (ARGSTGTSTRONG: forall ofs ty, *)
(*           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef >> \/ *)
(*           (exists v, *)
(*               <<STORED: Mem_storedv (chunk_of_type ty) m_tgt *)
(*                                     (Val.offset_ptr (Vptr blk_tgt Ptrofs.zero(* delta.(Ptrofs.repr) *) true) *)
(*                                                     (Ptrofs.repr (4 * ofs))) v >> /\ *)
(*               <<INJECT: Val.inject j (ls_arg (S Outgoing ofs ty)) v >>)) *)
(*       (SZARG: 4 * (size_arguments sg) <= Ptrofs.max_unsigned) *)
(*   : *)
(*     <<INJ: Mem.inject j m_arg m_tgt>> *)
(* . *)
(* Proof. *)
(*   generalize (loc_arguments_acceptable_2 sg); eauto. i. *)
(*   generalize (loc_arguments_bounded sg); eauto. i. *)
(*   abstr (regs_of_rpairs (loc_arguments sg)) locs. *)
(*   ss. *)
(*   ginduction locs; ii; ss; psimpl. *)
(*   { clarify. } *)
(*   u in *. *)
(*   des_ifs; ss; try (by eapply IHlocs; eauto). *)
(*   exploit IHlocs; try eassumption; eauto. intro INJ0. *)
(*   (* rewrite Ptrofs.add_unsigned in H0. *) *)
(*   exploit ARGSTGTSTRONG; eauto. i; des. *)
(*   { eapply Mem_store_mapped_inject_undef; eauto. rewrite H1 in *. eauto. } *)
(*   eapply store_stored_inject; eauto; cycle 1. *)
(*   { rewrite INJRSP. repeat f_equal; eauto. *)
(*     rewrite Ptrofs.unsigned_repr; ss. *)
(*   } *)
(*   { rewrite Ptrofs.unsigned_repr; ss. psimpl. *)
(*     hexploit H; eauto. i; des. *)
(*     hexploit H0; eauto. i; des. *)
(*     generalize (typesize_pos ty); i. *)
(*     rewrite Ptrofs.unsigned_repr; ss; try xomega. *)
(*   } *)
(*   psimpl. rpapply H1. *)
(* Qed. *)

(* Lemma B2C_mem_simmem *)
(*       ls_arg sg sm0 m_src1 *)
(*       (MWF: SimMem.wf sm0) *)
(*       blk_src blk_tgt (* delta *) *)
(*       (INJRSP: sm0.(inj) blk_src = Some (blk_tgt, 0)) *)
(*       (BCM: Call.B2C_mem sm0.(SimMem.src) (Vptr blk_src Ptrofs.zero true) ls_arg *)
(*                     (regs_of_rpairs (loc_arguments sg)) = Some m_src1) *)
(*       (ARGSTGTSTRONG: forall ofs ty, *)
(*           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef >> \/ *)
(*           (exists v, *)
(*               <<STORED: Mem_storedv (chunk_of_type ty) sm0.(SimMem.tgt) *)
(*                                     (Val.offset_ptr (Vptr blk_tgt Ptrofs.zero(* delta.(Ptrofs.repr) *) true) *)
(*                                                     (Ptrofs.repr (4 * ofs))) v >> /\ *)
(*               <<INJECT: Val.inject sm0.(inj) (ls_arg (S Outgoing ofs ty)) v >>)) *)
(*       (SZARG: 4 * (size_arguments sg) <= Ptrofs.max_unsigned) *)
(*   : *)
(*     let sm1 := (mk sm0.(inj) m_src1 sm0.(m_tgt) *)
(*                          sm0.(src_external) sm0.(tgt_external) *)
(*                          sm0.(src_parent_nb) sm0.(tgt_parent_nb)) in *)
(*     <<MWF: SimMem.wf sm1>> /\ <<MLE: SimMem.le sm0 sm1>> *)
(* . *)
(* Proof. *)
(*   generalize (loc_arguments_acceptable_2 sg); eauto. i. *)
(*   generalize (loc_arguments_bounded sg); eauto. i. *)
(*   abstr (regs_of_rpairs (loc_arguments sg)) locs. *)
(*   subst_locals. *)
(*   ss. *)
(*   ginduction locs; ii; ss; psimpl. *)
(*   { clarify. destruct sm0; ss. esplits; eauto. reflexivity. } *)
(*   u in *. *)
(*   des_ifs; ss; try (by eapply IHlocs; eauto). *)
(*   exploit IHlocs; try eassumption; eauto. intro INJ0. *)
(*   (* rewrite Ptrofs.add_unsigned in H0. *) *)
(*   exploit ARGSTGTSTRONG; eauto. i; des_safe. *)
(*   des. *)
(*   { rewrite H1 in *. eapply store_undef_simmem in INJ0; eauto; cycle 1. *)
(*     { u. unfold loc_unmapped. i; des. clarify. } *)
(*     ss. des. esplits; eauto. etransitivity; eauto. } *)
(*   psimpl. *)
(*   exploit store_stored_simmem; try apply INJ0; eauto; ss. *)
(*   { rpapply H1. rewrite Ptrofs.add_zero. eauto. } *)
(*   { rewrite INJRSP. repeat f_equal; eauto. } *)
(*   { psimpl. *)
(*     hexploit H; eauto. i; des. *)
(*     hexploit H0; eauto. i; des. *)
(*     generalize (typesize_pos ty); i. *)
(*     rewrite Ptrofs.unsigned_repr; ss; try xomega. *)
(*   } *)
(*   i; des. *)
(*   esplits; eauto. *)
(*   etransitivity; eauto. *)
(* Qed. *)

(* End ARGPASSING. *)


(* Section SIMMODSEM. *)

(* Local Existing Instance Val.mi_final. *)
(* Variable skenv_link_src skenv_link_tgt: SkEnv.t. *)
(* Variable prog: Linear.program. *)
(* Variable tprog: Mach.program. *)
(* Hypothesis TRANSF: match_prog prog tprog. *)
(* Variable rao: Mach.function -> Mach.code -> ptrofs -> Prop. *)
(* Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog). *)
(* Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog). *)

(* Definition msp: ModSemPair.t := *)
(*   ModSemPair.mk (LinearC.modsem skenv_link_src prog) (MachC.modsem rao skenv_link_tgt tprog) tt *)
(* . *)

(* Inductive match_states (rs_init_src rs_init_tgt: regset) *)
(*           (sm_init: SimMem.t) *)
(*           (idx: nat) (st_src0: Linear.state) (st_tgt0: Mach.state) (sm0: SimMem.t): Prop := *)
(* | match_states_intro *)
(*     (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt) *)
(*     (MATCHST: StackingproofC0.match_states prog tprog rao st_src0 st_tgt0) *)
(*     (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0) *)
(*     (* TODO: put sm intside match_states. j is actually sm0.(inj) *) *)
(*     (MWF: SimMem.wf sm0) *)
(*     (* (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge) *) *)
(* . *)

(* Lemma functions_translated_inject *)
(*       j *)
(*       (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge) *)
(*       (SIMGE0: DUMMY_PROP) (* globalenv_inject match_globalenvs *) *)
(*       fptr_src fd_src *)
(*       (FUNCSRC: Genv.find_funct ge fptr_src = Some fd_src) *)
(*       fptr_tgt *)
(*       (INJ: Val.inject j fptr_src fptr_tgt) *)
(*   : *)
(*     exists fd_tgt, *)
(*       <<FUNCTGT: Genv.find_funct tge fptr_tgt = Some fd_tgt>> *)
(*       /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>> *)
(* . *)
(* Proof. *)
(*   admit "ez". *)
(* Qed. *)

(* Local Opaque sepconj. *)
(* Local Opaque function_bounds. *)
(* Local Opaque make_env. *)
(* Ltac sep_split := econs; [|split]; swap 2 3. *)
(* Hint Unfold fe_ofs_arg. *)
(* Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *) *)
(* Hint Unfold to_mregset. *)

(* Theorem init_match_states *)
(*         sm_arg *)
(*         (SIMSKENV: SimSymb.sim_skenv sm_arg tt (SkEnv.project skenv_link_src (defs prog)) *)
(*                                      (SkEnv.project skenv_link_tgt (defs tprog))) *)
(*         (MWF: SimMem.wf sm_arg) *)
(*         rs_arg_src rs_arg_tgt *)
(*         (SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt) *)
(*         st_init_src *)
(*         (INITSRC: LinearC.initial_frame skenv_link_src prog rs_arg_src sm_arg.(SimMem.src) st_init_src) *)
(*   : *)
(*     exists st_init_tgt sm_init idx_init, *)
(*     <<INITTGT: initial_frame skenv_link_tgt tprog rs_arg_tgt sm_arg.(SimMem.tgt) st_init_tgt >> /\ *)
(*     <<MCOMPAT: mem_compat (LinearC.modsem skenv_link_src prog) (modsem rao skenv_link_tgt tprog) *)
(*                           st_init_src st_init_tgt sm_init >> /\ *)
(*     <<MLE: SimMem.le sm_arg sm_init >> /\ *)
(*     <<MATCH: match_states rs_arg_src rs_arg_tgt sm_arg idx_init st_init_src st_init_tgt sm_init>> *)
(* . *)
(* Proof. *)
(*   ss. *)
(*   inv INITSRC. *)
(*   assert(RSPINJ:= SIMRS SP). *)
(*   assert(PCINJ:= SIMRS PC). *)
(*   dup DB. inv DB. ss. inv DC. inv CB. ss. *)
(*   exploit (functions_translated_inject); eauto. *)
(*   { admit "sim ge". } *)
(*   intro FPTRTGT; des. *)
(*   destruct fd_tgt; ss; unfold bind in *; ss; des_ifs. *)
(*   rename fd into fd_src. rename f into fd_tgt. *)
(*   ss. rewrite RSPPTR in *. inv RSPINJ. *)
(*   rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ. *)
(*   rename blk into sp_src. rename b2 into sp_tgt. *)
(*   rename m_init into m_init_src. *)
(*   rewrite Ptrofs.add_zero_l in *. *)
(*   hexploit Mem.free_range_perm; eauto. intro PERMSRC. *)
(*   set (sm_init := (mk sm_arg.(inj) *)
(*                    m_init_src sm_arg.(m_tgt) *)
(*                    sm_arg.(src_external) sm_arg.(tgt_external) *)
(*                    sm_arg.(src_parent_nb) sm_arg.(tgt_parent_nb))). *)
(*   exploit Mem.free_result; eauto. i; des. clarify. *)
(*   assert(MWF0: SimMem.wf sm_init). *)
(*   { ss. econs; ss; try apply MWF; eauto. *)
(*     + eapply Mem.free_left_inject; eauto. apply MWF. *)
(*     + etransitivity; try apply MWF; eauto. admit "ez". *)
(*   } *)
(*   eexists _, sm_init, 0%nat; cbn. *)
(*   esplits; eauto. *)
(*   - econs; eauto. *)
(*   - ss. *)
(*   - ss. econs; ss; eauto. *)
(*     + admit "drop_perm ez". *)
(*     + reflexivity. *)
(*     + eapply frozen_refl. *)
(*     + admit "drop_perm ez". *)
(*     + reflexivity. *)
(*   - ss. *)
(*     econs; ss; eauto. *)
(*     assert(PTRRA: is_ptr (rs_arg_tgt RA)). *)
(*     { u in RAPTR. des_ifs. specialize (SIMRS RA). rewrite Heq0 in *. inv SIMRS; ss. } *)
(*     (* autounfold with * in PTRRA. *) *)
(*     (* u in PTRRA. des_ifs. clear_tac. *) *)
(*     (* rename b into ra. rename i into delta_ra. *) *)
(*     rename delta into delta_sp. clear_tac. *)

(*     econs; eauto. *)
(*     + econs 1; eauto; cycle 1. *)
(*       { rewrite RSPPTRTGT. ss. } *)
(*       i. *)
(*       assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)). *)
(*       { eapply loc_arguments_acceptable_2; eauto. } *)
(*       assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty). *)
(*       { destruct ACC. unfold slot_valid, proj_sumbool. *)
(*         rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. } *)
(*       { *)
(*         intros; red. *)
(*           eapply Z.le_trans with (size_arguments _); eauto. *)
(*           apply loc_arguments_bounded; eauto. *)
(*         u. *)
(*         xomega. *)
(*       } *)
(*     + ii. *)
(*       ss. u. eapply SIMRS; eauto. *)
(*     + ii. des_ifs. *)
(*     + u. des_ifs. *)
(*       rename Heq0 into RSPTGT. *)
(*       assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) -> *)
(*                     0 <= delta_sp <= Ptrofs.max_unsigned *)
(*                     /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned). *)
(*       { i; eapply delta_range; eauto. apply MWF. xomega. } *)
(*       rewrite sep_comm. rewrite sep_assoc. *)
(*       sep_split. *)
(*       { simpl. apply MWF0. } *)
(*       { apply disjoint_footprint_drop_empty. *)
(*         { ss. } *)
(*         intros ? delta INJDUP. ii. ss. des. clarify. *)
(*         rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'. *)
(*         destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*         { omega. } *)
(*         special DELTA; ss. clear_tac. *)
(*         rewrite Ptrofs.unsigned_repr in *; try omega. *)
(*         (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *) *)
(*         assert(sp_src' = sp_src). *)
(*         { apply NNPP. intro DISJ. *)
(*           hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP. *)
(*           exploit OVERLAP; eauto. *)
(*           { eapply Mem.perm_free_3; eauto. } *)
(*           { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. } *)
(*           { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. } *)
(*         } *)
(*         clarify. *)
(*         hexploit (Mem_drop_perm_none_spec (SimMem.src sm_arg) sp_src 0 *)
(*                                           (4 * size_arguments (Linear.fn_sig fd_src))); eauto. i; des. *)
(*         eapply INSIDE; eauto. omega. *)
(*       } *)
(*       sep_split. *)
(*       { ss. admit "sim_genv". } *)
(*       { ss. } *)
(* { *)
(*   ss. rewrite Ptrofs.unsigned_repr_eq. *)
(*   assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus). *)
(*   { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. } *)
(*   split; eauto. *)
(*   split; eauto. *)
(*   { eapply POSBOUND. } *)
(*   destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*   { esplits; auto. *)
(*     - specialize (POSBOUND delta_sp). xomega. *)
(*     - ii. xomega. *)
(*     - i. generalize (typesize_pos ty). i. xomega. *)
(*   } *)
(*   special DELTA; ss. *)
(*   des. *)
(*   specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *. *)
(*   erewrite Z.mod_small; try xomega. *)
(*   split; try xomega. *)
(*   Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name]. *)
(*   dsplit_r; try xomega. *)
(*   { rewrite Z.add_comm. *)
(*     change (delta_sp) with (0 + delta_sp). *)
(*     eapply Mem.range_perm_inject; try apply MWF; eauto. *)
(*   } *)
(*   ii; des. *)
(*   { *)
(*     assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (SimMem.tgt sm_arg) sp_tgt (delta_sp + 4 * ofs) = Some v). *)
(*     { eapply Mem.valid_access_load; eauto. *)
(*       hnf. *)
(*       rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*       split; try xomega. *)
(*       - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*       - apply Z.divide_add_r. *)
(*         + rewrite <- align_type_chunk. *)
(*           eapply Mem.mi_align; try apply MWF; eauto. *)
(*           instantiate (1:= Nonempty). *)
(*           instantiate (1:= 0). *)
(*           rewrite Z.add_0_l. *)
(*           ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*           rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*         + apply Z.mul_divide_mono_l. ss. *)
(*     } *)
(*     des. *)
(*     esplits; eauto. *)
(*     - des_ifs; try (by econs; eauto). *)
(*       Local Opaque Ptrofs.modulus. *)
(*       unfold load_stack in *. ss. *)
(*       rewrite ! Ptrofs.add_zero_l in *. unfold fe_ofs_arg in *. rewrite Z.add_0_l in *. *)
(*       exploit Mem.load_inject; try apply MWF; eauto. intro LOADTGT0; des. *)
(*       assert(v = v2). *)
(*       { erewrite Ptrofs.unsigned_repr in LOADTGT0; eauto. rewrite Z.add_comm in LOADTGT0. clarify. *)
(*         split; try xomega. *)
(*         unfold Ptrofs.max_unsigned. *)
(*         generalize (typesize_pos ty); i. *)
(*         xomega. *)
(*       } *)
(*       clarify. *)
(*   } *)
(* } *)
(*     + i; des; ss. clear - FINDFUNC H. admit "ge". *)
(* Qed. *)

(* Lemma match_stacks_parent_sp *)
(*       j cs stack sg *)
(*       (MATCH: match_stacks tprog j cs stack sg) *)
(*   : *)
(*     <<RSPPTR: is_real_ptr (parent_sp stack)>> *)
(* . *)
(* Proof. *)
(*   induction MATCH; ss. *)
(* Qed. *)

(* Theorem sim_modsem *)
(*   : *)
(*     ModSemPair.sim msp *)
(* . *)
(* Proof. *)
(*   eapply match_states_sim with (match_states := match_states); eauto; ii; ss. *)
(*   - instantiate (1:= Nat.lt). apply lt_wf. *)
(*   - (* INITFSIM *) *)
(*     exploit init_match_states; eauto. i; des. *)
(*     esplits; eauto. *)
(*   - (* ATPROGRESS *) *)
(*     (* NNNNNNNNNNNNNNNNNNNNNNNNOTE WE CAN DO FSIM HERE TOO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *) *)
(*     inv MATCH. *)
(*     esplits; eauto. *)
(*     u in CALLSRC. des. *)
(*     destruct sm0; ss. inv MCOMPAT; ss. des. clarify. *)
(*     inv CALLSRC; ss. inv MATCHST; ss. *)
(*     fold_all ge. *)
(*     u. *)
(*     inv BD. inv BC. *)
(*     esplits; eauto. *)
(*     econs; eauto. *)
(*     + fold_all tge. *)
(*       admit "this should hold. is_call_progress". *)
(*     + econs; eauto. *)
(*       { reflexivity. } *)
(*     (* inv STORE; ss. *) *)
(*     (* u in PCPTR. des_ifs. clear_tac. ss. *) *)
(*     (* destruct b0; ss; cycle 1. *) *)
(*     (* { inv FPTR. ss. esplits; eauto. econs; eauto. } *) *)
(*     (* destruct (Genv.find_funct tge tfptr) eqn:T; cycle 1. *) *)
(*     (* { esplits; eauto. econs; eauto. } *) *)
(*     (* unfold Genv.find_funct in *. des_ifs_safe; inv FPTR; ss. *) *)
(*     (* assert(delta = 0). *) *)
(*     (* { admit "by genv match". } *) *)
(*     (* clarify. rewrite Ptrofs.add_zero in *. clarify. *) *)
(*     (* des_ifs. *) *)
(*     (* esplits; eauto. *) *)
(*     (* econs; eauto. *) *)
(*     (* ss. fold_all tge. des_ifs. *) *)
(*     (* admit "by genv match". *) *)
(*   - (* ATBSIM *) *)
(*     revert_until MATCH. *)
(*     assert(ATFSIM: forall *)
(*               rs_arg_src m_arg_src *)
(*               (ATSRC: LinearC.at_external skenv_link_src prog st_src0 rs_arg_src m_arg_src) *)
(*             , *)
(*               exists (rs_arg_tgt : regset) (m_arg_tgt : mem) (sm_arg : SimMem.t), *)
(*                 (<<ATEXT: MachC.at_external skenv_link_tgt tprog st_tgt0 rs_arg_tgt m_arg_tgt >>) /\ *)
(*                 (<<MSRC: SimMem.src sm_arg = m_arg_src >>) /\ *)
(*                 (<<MTGT: SimMem.tgt sm_arg = m_arg_tgt >>) /\ *)
(*                 (<<SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt >>) /\ *)
(*                 (<<MLE: le' sm0 sm_arg >>) /\ (<<MWF: wf' sm_arg >>)). *)
(* { *)
(*   ii; ss. *)
(*   inv ATSRC; ss. inv BD. inv BC. *)
(*   rename blk into sp_src. *)
(*   inv MATCH; ss. inv MATCHST; ss. *)
(*   assert(ARGSTGT: forall l (IN: In l (regs_of_rpairs (loc_arguments sg_arg))), *)
(*             (exists v, Mach.extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls_arg l) v)). *)
(*   { eapply transl_external_argument; eauto. apply sep_pick1 in SEP. eauto. } *)
(*   inv MCOMPAT; ss. des. clarify. *)
(*   assert(sm0.(inj) = j). *)
(*   { admit "put sm inside match_states". } *)
(*   clarify. *)
(*   exploit match_stacks_parent_sp; eauto. i; des. *)
(*   u in H. des_ifs. clear_tac. rename b into sp_tgt. rename i into spdelta. *)
(*   rename Heq into PARENTPTR. *)

(*   exploit (@Call.B2C_mem_spec sg_arg m_alloc sp_src ls_arg); eauto. *)
(*   { eapply Mem_alloc_range_perm; eauto. } *)
(*   i; des. clarify. *)

(*   set (sm_arg := (mk (fun blk => if eq_block blk sp_src *)
(*                                  then Some (sp_tgt, spdelta.(Ptrofs.unsigned)) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_arg_src sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   unfold load_stack in *. ss. *)

(*   destruct (classic (length stack = 1%nat)). *)
(*   { (* this case, alloc with size 0 /\ no more store. *) *)
(*     inv STACKS; ss; cycle 1. *)
(*     { inv STK; ss. }  *)
(*     hexploit ABCD; eauto. *)
(*     { esplits; eauto. admit "genv". } *)
(*     intro TAIL. *)
(*     assert(m_alloc = m_arg_src). *)
(*     { admit "tailcall_possible". } *)
(*     clarify. *)
(*     inv CD. ss. *)
(*     assert(MLE: SimMem.le sm0 sm_arg). *)
(*     { admit "??". } *)
(*     assert(MWF0: SimMem.wf sm_arg). *)
(*     { admit "??". } *)
(*     do 2 eexists. exists sm_arg. cbn. *)
(*     esplits; cbn; try reflexivity; eauto. *)
(*     - econs; eauto. *)
(*       + fold tge. admit "this should hold". *)
(*       + econs; eauto. *)
(*         * reflexivity. *)
(*     - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*       + unfold agree_regs in AGREGS. *)
(*         eapply val_inject_incr; eauto. eapply MLE. *)
(*       + des_ifs; try (by econs; eauto). *)
(*         * eapply val_inject_incr; eauto. apply MLE. *)
(*         * econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*         * u in RAPTR. des_ifs. u in RAPTR0. des_ifs. admit "RA inject. unprovable?". *)
(*   } *)

(*   assert(ARGSTGTSTRONG: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg_arg))), *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef>> *)
(*            \/ *)
(*            exists v, *)
(*              <<STORED: Mem_storedv (chunk_of_type ty) (SimMem.tgt sm0) *)
(*                                    (Val.offset_ptr (parent_sp cs') (Ptrofs.repr (4 * ofs))) v>> *)
(*           /\ *)
(*           <<INJECT: Val.inject (inj sm0) (ls_arg (S Outgoing ofs ty)) v>>). *)
(*   { eapply transl_external_arguments_strong; eauto. apply sep_pick1 in SEP. eauto. } *)

(*   assert(spdelta = Ptrofs.zero). *)
(*   { inv STACKS; ss; clarify. } *)
(*   clarify. *)

(*   (* assert(MLE: SimMem.le sm0 sm_arg). *) *)
(*   (* { *) *)
(*   (*   subst sm_arg. *) *)
(*   (*   econs; cbn; eauto with mem; try xomega. *) *)
(*   (*   - ii; ss. des_ifs; ss. exfalso. *) *)
(*   (*     exploit Mem.mi_freeblocks; try apply MWF; eauto. *) *)
(*   (*     { eauto with mem. } *) *)
(*   (*     i; ss. clarify. *) *)
(*   (*   - eapply Mem_unchanged_on_trans_strong; eauto. *) *)
(*   (*     { eapply Mem.alloc_unchanged_on; eauto. } *) *)
(*   (*     eapply Mem.unchanged_on_implies; eauto. cbn. admit "ez". *) *)
(*   (*   - econs; eauto. *) *)
(*   (*     ii; ss. des; ss. des_ifs. *) *)
(*   (*     split; ss. *) *)
(*   (*     + admit "ez". *) *)
(*   (*     + admit "we should add this into match_states". *) *)
(*   (*   - admit "ez". *) *)
(*   (* } *) *)
(*   exploit Mem.alloc_result; eauto. i; des. clarify. *)
(*   exploit Mem.nextblock_alloc; eauto. intro ALLOCNB. *)

(*   set (sm_alloc := (mk (fun blk => if eq_block blk (Mem.nextblock (m_src sm0)) *)
(*                                  then Some (sp_tgt, 0) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_alloc sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   assert(MWF0: SimMem.wf sm_alloc /\ <<MLE0: SimMem.le sm0 sm_alloc>>). *)
(*   { rewrite sep_comm in SEP. rewrite sep_assoc in SEP. apply sep_drop2 in SEP. rewrite sep_comm in SEP. *)
(*     eapply alloc_left_zero_simmem; eauto. *)
(*     - u. ii. esplits; eauto. *)
(*       + rpapply arguments_private; eauto. *)
(*       + admit "ez". *)
(*     - admit "should add this in match_states". *)
(*     - i. apply Mem.perm_cur. eapply Mem.perm_implies. *)
(*       + rpapply arguments_perm; eauto. *)
(*       + eauto with mem. *)
(*     - admit "ez". *)
(*     - admit "should add this in match_states". *)
(*   } *)
(*   des. *)
(*   rewrite PARENTPTR in *. *)
(*   assert(MWF1: SimMem.wf sm_arg /\ <<MLE1: SimMem.le sm0 sm_arg>>). *)
(*   { subst_locals. exploit B2C_mem_simmem; eauto; ss. *)
(*     { des_ifs. } *)
(*     { ii. exploit ARGSTGTSTRONG; eauto. i; des; eauto. right. ss. *)
(*       psimpl. ss. *)
(*       esplits; eauto. *)
(*       eapply val_inject_incr; eauto. *)
(*       apply MLE0. *)
(*     } *)
(*     i; des. *)
(*     esplits; eauto. *)
(*     etransitivity; eauto. *)
(*   } *)
(*   des. *)

(*   inv CD. ss. *)
(*   do 2 eexists. exists sm_arg. cbn. *)
(*   esplits; cbn; try reflexivity; eauto. *)
(*   - econs; eauto. *)
(*     + fold tge. admit "this should hold". *)
(*     + econs; eauto. *)
(*       * reflexivity. *)
(*   - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*     + unfold agree_regs in AGREGS. *)
(*       eapply val_inject_incr; eauto. eapply MLE1. *)
(*     + des_ifs; try (by econs; eauto). *)
(*       * eapply val_inject_incr; eauto. apply MLE1. *)
(*       * rewrite PARENTPTR. econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*       * u in RAPTR. des_ifs. admit "ra inject. unprovable?". *)
(* } *)




(*     ii; ss. u in SAFESRC. des. *)
(*     inv SAFESRC; ss. rename rs_arg into rs_arg_src. rename m_arg into m_arg_src. *)
(*     inv BD. rename mrs into mrs_src. rename rsp_arg into rsp_arg_src. rename ra_arg into ra_arg_src. *)
(*     inv BC. rename blk into sp_src. *)
(*     inv MATCH; ss. inv MATCHST; ss. *)
(*     assert(ARGSTGT: forall l (IN: In l (regs_of_rpairs (loc_arguments sg_arg))), *)
(*               (exists v, Mach.extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls_arg l) v)). *)
(*     { eapply transl_external_argument; eauto. apply sep_pick1 in SEP. eauto. } *)
(*     inv MCOMPAT; ss. des. clarify. *)
(*     assert(sm0.(inj) = j). *)
(*     { admit "put sm inside match_states". } *)
(*     clarify. *)
(*     exploit match_stacks_parent_sp; eauto. i; des. *)
(*     u in H. des_ifs. clear_tac. rename b into sp_tgt. rename i into spdelta. *)
(*     rename Heq into PARENTPTR. *)

(*     exploit (@Call.B2C_mem_spec sg_arg m_alloc sp_src ls_arg); eauto. *)
(*     { eapply Mem_alloc_range_perm; eauto. } *)
(*     i; des. clarify. *)

(*     set (sm_arg := (mk (fun blk => if eq_block blk sp_src *)
(*                                    then Some (sp_tgt, spdelta.(Ptrofs.unsigned)) *)
(*                                    else sm0.(inj) blk) *)
(*                        m_arg_src sm0.(m_tgt) *)
(*                        sm0.(src_external) sm0.(tgt_external) *)
(*                        sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*     unfold load_stack in *. ss. *)

(*     destruct (classic (length stack = 1%nat)). *)
(*     { (* this case, alloc with size 0 /\ no more store. *) *)
(*       inv STACKS; ss; cycle 1. *)
(*       { inv STK; ss. }  *)
(*       hexploit ABCD; eauto. *)
(*       { esplits; eauto. admit "genv". } *)
(*       intro TAIL. *)
(*       assert(m_alloc = m_arg_src). *)
(*       { admit "tailcall_possible". } *)
(*       clarify. *)
(*       inv CD. ss. *)
(*       assert(MLE: SimMem.le sm0 sm_arg). *)
(*       { admit "??". } *)
(*       assert(MWF0: SimMem.wf sm_arg). *)
(*       { admit "??". } *)

(*       inv CALLTGT. ss. *)
(*       do 2 eexists. exists sm_arg. cbn. *)
(*       esplits; cbn; try reflexivity; eauto. *)
(*       - econs; eauto. *)
(*         econs; eauto. *)
(*         + instantiate (1:= ra.(to_fake)). *)
(*           econs; eauto. *)
(*           reflexivity. *)
(*           destruct ra; ss. des_ifs. *)
(*         + econs; eauto. *)
(*           reflexivity. *)
(*       - inv CD. ii; ss. des_ifs. *)
(*         + eapply val_inject_incr; eauto. apply MLE. *)
(*         + eapply val_inject_incr; eauto. apply MLE. *)
(*         + econs; eauto. { des_ifs. } psimpl. ss. *)
(*         + destruct ra; ss. des_ifs. econs; eauto. *)
(*       - econs; eauto. *)
(*         + fold tge. admit "this should hold". *)
(*         + econs; eauto. *)
(*           * reflexivity. *)
(*       - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*         + unfold agree_regs in AGREGS. *)
(*           eapply val_inject_incr; eauto. eapply MLE. *)
(*         + des_ifs; try (by econs; eauto). *)
(*           * eapply val_inject_incr; eauto. apply MLE. *)
(*           * econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*           * u in RAPTR. des_ifs. u in RAPTR0. des_ifs. admit "RA inject. unprovable?". *)
(*     } *)

(*   assert(ARGSTGTSTRONG: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg_arg))), *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef>> *)
(*            \/ *)
(*            exists v, *)
(*              <<STORED: Mem_storedv (chunk_of_type ty) (SimMem.tgt sm0) *)
(*                                    (Val.offset_ptr (parent_sp cs') (Ptrofs.repr (4 * ofs))) v>> *)
(*           /\ *)
(*           <<INJECT: Val.inject (inj sm0) (ls_arg (S Outgoing ofs ty)) v>>). *)
(*   { eapply transl_external_arguments_strong; eauto. apply sep_pick1 in SEP. eauto. } *)

(*   assert(spdelta = Ptrofs.zero). *)
(*   { inv STACKS; ss; clarify. } *)
(*   clarify. *)

(*   (* assert(MLE: SimMem.le sm0 sm_arg). *) *)
(*   (* { *) *)
(*   (*   subst sm_arg. *) *)
(*   (*   econs; cbn; eauto with mem; try xomega. *) *)
(*   (*   - ii; ss. des_ifs; ss. exfalso. *) *)
(*   (*     exploit Mem.mi_freeblocks; try apply MWF; eauto. *) *)
(*   (*     { eauto with mem. } *) *)
(*   (*     i; ss. clarify. *) *)
(*   (*   - eapply Mem_unchanged_on_trans_strong; eauto. *) *)
(*   (*     { eapply Mem.alloc_unchanged_on; eauto. } *) *)
(*   (*     eapply Mem.unchanged_on_implies; eauto. cbn. admit "ez". *) *)
(*   (*   - econs; eauto. *) *)
(*   (*     ii; ss. des; ss. des_ifs. *) *)
(*   (*     split; ss. *) *)
(*   (*     + admit "ez". *) *)
(*   (*     + admit "we should add this into match_states". *) *)
(*   (*   - admit "ez". *) *)
(*   (* } *) *)
(*   exploit Mem.alloc_result; eauto. i; des. clarify. *)
(*   exploit Mem.nextblock_alloc; eauto. intro ALLOCNB. *)

(*   set (sm_alloc := (mk (fun blk => if eq_block blk (Mem.nextblock (m_src sm0)) *)
(*                                  then Some (sp_tgt, 0) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_alloc sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   assert(MWF0: SimMem.wf sm_alloc /\ <<MLE0: SimMem.le sm0 sm_alloc>>). *)
(*   { rewrite sep_comm in SEP. rewrite sep_assoc in SEP. apply sep_drop2 in SEP. rewrite sep_comm in SEP. *)
(*     eapply alloc_left_zero_simmem; eauto. *)
(*     - u. ii. esplits; eauto. *)
(*       + rpapply arguments_private; eauto. *)
(*       + admit "ez". *)
(*     - admit "should add this in match_states". *)
(*     - i. apply Mem.perm_cur. eapply Mem.perm_implies. *)
(*       + rpapply arguments_perm; eauto. *)
(*       + eauto with mem. *)
(*     - admit "ez". *)
(*     - admit "should add this in match_states". *)
(*   } *)
(*   des. *)
(*   rewrite PARENTPTR in *. *)
(*   assert(MWF1: SimMem.wf sm_arg /\ <<MLE1: SimMem.le sm0 sm_arg>>). *)
(*   { subst_locals. exploit B2C_mem_simmem; eauto; ss. *)
(*     { des_ifs. } *)
(*     { ii. exploit ARGSTGTSTRONG; eauto. i; des; eauto. right. ss. *)
(*       psimpl. ss. *)
(*       esplits; eauto. *)
(*       eapply val_inject_incr; eauto. *)
(*       apply MLE0. *)
(*     } *)
(*     i; des. *)
(*     esplits; eauto. *)
(*     etransitivity; eauto. *)
(*   } *)
(*   des. *)

(*   inv CD. ss. *)
(*   do 2 eexists. exists sm_arg. cbn. *)
(*   esplits; cbn; try reflexivity; eauto. *)
(*   - econs; eauto. *)
(*     + fold tge. admit "this should hold". *)
(*     + econs; eauto. *)
(*       * reflexivity. *)
(*   - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*     + unfold agree_regs in AGREGS. *)
(*       eapply val_inject_incr; eauto. eapply MLE1. *)
(*     + des_ifs; try (by econs; eauto). *)
(*       * eapply val_inject_incr; eauto. apply MLE1. *)
(*       * rewrite PARENTPTR. econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*       * u in RAPTR. des_ifs. admit "ra inject. unprovable?". *)
(*   - admit "todo". *)
(*   - admit "todo". *)
(*   - admit "todo". *)
(* Unshelve. *)
(*   all: try (by econs). *)
(* Qed. *)

(* End SIMMODSEM. *)




(* Section SIMMOD. *)

(* Variables prog: Linear.program. *)
(* Variables tprog: Mach.program. *)
(* Hypothesis TRANSL: match_prog prog tprog. *)

(* Definition mp: ModPair.t := *)
(*   ModPair.mk (LinearC.module prog) (MachC.module tprog) tt *)
(* . *)

(* Theorem sim_mod *)
(*   : *)
(*     ModPair.sim mp *)
(* . *)
(* Proof. *)
(*   econs; ss. *)
(*   - econs; eauto. admit "easy". *)
(*   - ii. eapply sim_modsem; eauto. *)
(* Qed. *)

(* End SIMMOD. *)




















(* Section PRESERVATION. *)

(* Local Existing Instance Val.mi_normal. *)
(* Context `{SimSymbId: @SimSymb.SimSymb.class SimMemInj}. *)
(* Variable prog: Linear.program. *)
(* Variable tprog: Mach.program. *)
(* Hypothesis TRANSF: match_prog prog tprog. *)
(* Variable return_address_offset: function -> code -> ptrofs -> Prop. *)
(* Let match_states := match_states prog tprog return_address_offset. *)

(* Lemma functions_translated_inject *)
(*       j *)
(*       (GENV: True) *)
(*       fptr_src fd_src *)
(*       (FUNCSRC: Genv.find_funct (Genv.globalenv prog) fptr_src = Some fd_src) *)
(*       fptr_tgt *)
(*       (INJ: Val.inject j fptr_src fptr_tgt) *)
(*   : *)
(*     exists fd_tgt, *)
(*       <<FUNCTGT: Genv.find_funct (Genv.globalenv tprog) fptr_tgt = Some fd_tgt>> *)
(*       /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>> *)
(* . *)
(* Proof. *)
(*   admit "easy". *)
(* Qed. *)

(* Definition msp: ModSemPair.t := *)
(*   ModSemPair.mk (LinearC.modsem prog) (MachC.modsem return_address_offset tprog) (admit "simsymb") Nat.lt. *)

(* Local Transparent dummy_stack. *)

(* Ltac sep_split := econs; [|split]; swap 2 3. *)
(* Hint Unfold fe_ofs_arg. *)
(* Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *) *)
(* Hint Unfold mregset_of. *)
(* Ltac perm_impl_tac := eapply Mem.perm_implies with Writable; [|eauto with mem]. *)

(* Lemma match_stack_contents *)
(*       sm_init *)
(*       (MWF: SimMem.SimMem.wf sm_init) *)
(*       ra_blk delta_ra *)
(*       rs_init_src rs_init_tgt *)
(*       (RSREL: (SimMem.SimMem.sim_regset) sm_init rs_init_src rs_init_tgt) *)
(*       (RA: rs_init_tgt RA = Vptr ra_blk delta_ra true) *)
(*       fd_src fd_tgt *)
(*       (FINDFSRC: Genv.find_funct (Genv.globalenv prog) (rs_init_src PC) = Some (Internal fd_src)) *)
(*       (FINDFTGT: Genv.find_funct (Genv.globalenv tprog) (rs_init_tgt PC) = Some (Internal fd_tgt)) *)
(*       (TRANSFF: transf_function fd_src = OK fd_tgt) *)
(*       ls_init vs_init m_init_src *)
(*       (LOADARGSSRC: load_arguments rs_init_src (src_mem sm_init) (Linear.fn_sig fd_src) vs_init m_init_src) *)
(*       (LOCSET: fill_arguments (Locmap.init Vundef) vs_init (Linear.fn_sig fd_src).(loc_arguments) *)
(*                = Some ls_init) *)
(*       sp_src sp_tgt delta_sp *)
(*       (RSPSRC: rs_init_src RSP = Vptr sp_src Ptrofs.zero true) *)
(*       (RSPTGT: rs_init_tgt RSP = Vptr sp_tgt (Ptrofs.repr delta_sp) true) *)
(*       (RSPINJ: inj sm_init sp_src = Some (sp_tgt, delta_sp)) *)
(*   : *)
(*     <<MATCHSTACK: *)
(*     sm_init.(tgt_mem) |= stack_contents tprog return_address_offset (inj sm_init) *)
(*                       [LinearC.dummy_stack (Linear.fn_sig fd_src) ls_init] *)
(*                       [dummy_stack (rs_init_tgt RSP) (Vptr ra_blk delta_ra true)] ** *)
(*                       minjection (inj sm_init) m_init_src ** *)
(*                       globalenv_inject (Genv.globalenv prog) sm_init.(inj)>> *)
(* . *)
(* Proof. *)
(*   u in RSREL. *)
(* Local Opaque sepconj. *)
(* Local Opaque function_bounds. *)
(* Local Opaque make_env. *)
(*   rewrite RSPTGT. u. *)
(*   unfold dummy_frame_contents. *)
(*   rewrite sep_comm. rewrite sep_assoc. *)
(*   inv LOADARGSSRC. rename PERM into PERMSRC. rename VAL into VALSRC. rename DROP into DROPSRC. *)
(*   rewrite RSPSRC in *. clarify. rename sp into sp_src. *)
(*   assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) -> *)
(*                 0 <= delta_sp <= Ptrofs.max_unsigned *)
(*                 /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned). *)
(*   { *)
(*     i. *)
(*     Print Mem.inject'. *)
(*     split. *)
(*     - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1. *)
(*       { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. } *)
(*       left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max. *)
(*       perm_impl_tac. eapply PERMSRC. split; try xomega. *)
(*     - *)
(*       assert(SZARGBOUND: 4 * size_arguments (Linear.fn_sig fd_src) <= Ptrofs.max_unsigned). *)
(*       { *)
(*         hexploit size_no_overflow; eauto. intro OVERFLOW. *)
(*         clear - OVERFLOW. *)
(*         Local Transparent function_bounds. *)
(*         Local Transparent make_env. *)
(*         u in *. *)
(*         ss. *)
(*         des_ifs. unfold function_bounds in *. cbn in *. *)
(*         admit "Add this in initial_frame of LinearC". *)
(*       } *)
(*       exploit Mem.mi_representable; try apply MWF; eauto; cycle 1. *)
(*       { instantiate (1:= (4 * size_arguments (Linear.fn_sig fd_src)).(Ptrofs.repr)). *)
(*         rewrite Ptrofs.unsigned_repr; cycle 1. *)
(*         { split; try xomega. } *)
(*         i. des. xomega. *)
(*       } *)
(*       right. *)
(*       rewrite Ptrofs.unsigned_repr; cycle 1. *)
(*       { split; try xomega. } *)
(*       eapply Mem.perm_cur_max. perm_impl_tac. *)
(*       eapply PERMSRC. split; try xomega. *)
(*   } *)
(*   assert(MINJ: Mem.inject (inj sm_init) m_init_src (tgt_mem sm_init)). *)
(*   { eapply Mem_set_perm_none_left_inject; eauto. apply MWF. } *)
(*   sep_split. *)
(*   { simpl. eassumption. } *)
(*   { apply disjoint_footprint_drop_empty. *)
(*     { ss. } *)
(*     intros ? delta INJDUP. ii. ss. des. clarify. *)
(*     rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'. *)
(*     destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*     { omega. } *)
(*     special DELTA; ss. clear_tac. *)
(*     rewrite Ptrofs.unsigned_repr in *; try omega. *)
(*     (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *) *)
(*     assert(sp_src' = sp_src). *)
(*     { apply NNPP. intro DISJ. *)
(*       hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP. *)
(*       exploit OVERLAP; eauto. *)
(*       { eapply Mem_set_perm_none_impl; eauto. } *)
(*       { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. } *)
(*       { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. } *)
(*     } *)
(*     clarify. *)
(*     hexploit Mem_set_perm_none_spec; eauto. i; des. *)
(*     eapply INSIDE; eauto. omega. *)
(*   } *)
(*   sep_split. *)
(*   { ss. admit "sim_genv". } *)
(*   { ss. } *)
(*   ss. rewrite Ptrofs.unsigned_repr_eq. *)
(*   assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus). *)
(*   { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. } *)
(*   split; eauto. *)
(*   split; eauto. *)
(*   { eapply POSBOUND. } *)
(*   destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*   { esplits; auto. *)
(*     - specialize (POSBOUND delta_sp). xomega. *)
(*     - ii. xomega. *)
(*     - i. generalize (typesize_pos ty). i. xomega. *)
(*   } *)
(*   special DELTA; ss. *)
(*   des. *)
(*   specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *. *)
(*   erewrite Z.mod_small; try xomega. *)
(*   split; try xomega. *)
(*   Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name]. *)
(*   dsplit_r; try xomega. *)
(*   { rewrite Z.add_comm. *)
(*     change (delta_sp) with (0 + delta_sp). *)
(*     eapply Mem.range_perm_inject; try apply MWF; eauto. *)
(*   } *)
(*   ii; des. *)
(*   { *)
(*     rename H1 into OFS0. rename H2 into OFS1. rename H3 into OFS2. *)
(*     clear - VALSRC LOCSET PERMSRC DSPLIT (* DROPSRC *) RSPSRC RSPTGT RSPINJ OFS0 OFS1 OFS2 MWF. *)
(*     abstr (Linear.fn_sig fd_src) sg. *)
(*     unfold extcall_arguments in *. *)
(*     exploit fill_arguments_spec_slot; eauto. *)
(*     { admit "Add this in initial_frame of LinearC". } *)
(*     i; des. *)
(*     set (loc_arguments sg) as locs in *. *)
(*     assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (tgt_mem sm_init) sp_tgt (delta_sp + 4 * ofs) = Some v). *)
(*     { eapply Mem.valid_access_load; eauto. *)
(*       hnf. *)
(*       rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*       split; try xomega. *)
(*       - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*       - apply Z.divide_add_r. *)
(*         + rewrite <- align_type_chunk. *)
(*           eapply Mem.mi_align; try apply MWF; eauto. *)
(*           instantiate (1:= Nonempty). *)
(*           instantiate (1:= 0). *)
(*           rewrite Z.add_0_l. *)
(*           ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*           rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*         + apply Z.mul_divide_mono_l. ss. *)
(*     } *)
(*     destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs locs))). *)
(*     - exploit INSIDE; eauto. i; des. *)
(*       + rewrite Z.add_comm. *)
(*         eapply Mem.load_inject; try apply MWF; eauto. *)
(*       + rewrite UNDEF. *)
(*         esplits; eauto. *)
(*     - exploit OUTSIDE; eauto. intro LOCSRC; des. *)
(*       rewrite LOCSRC. *)
(*       exploit Mem.valid_access_load; eauto. *)
(*       { hnf. instantiate (2:= chunk_of_type ty). *)
(*         rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*         instantiate (1:= delta_sp + 4 * ofs). *)
(*         instantiate (1:= sp_tgt). *)
(*         instantiate (1:= sm_init.(tgt_mem)). *)
(*         split; try xomega. *)
(*         - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*         - apply Z.divide_add_r. *)
(*           + rewrite <- align_type_chunk. *)
(*             eapply Mem.mi_align; try apply MWF; eauto. *)
(*             instantiate (1:= Nonempty). *)
(*             instantiate (1:= 0). *)
(*             rewrite Z.add_0_l. *)
(*             ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*             rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*           + apply Z.mul_divide_mono_l. ss. *)
(*       } *)
(*   } *)
(* Qed. *)

(* Theorem init_match_states *)
(*         (sm_init: SimMem.SimMem.t) fptr_init_src fptr_init_tgt *)
(*         (FPTRREL: Val.inject (inj sm_init) fptr_init_src fptr_init_tgt) *)
(*         rs_init_src rs_init_tgt *)
(*         (RSREL: SimMem.SimMem.sim_regset sm_init rs_init_src rs_init_tgt) *)
(*         (WF: wf' sm_init) *)
(*         (SIMSKENV: ModSemPair.sim_skenv msp sm_init) *)
(*         st_init_src *)
(*         (INITSRC: LinearC.initial_frame prog rs_init_src sm_init.(src_mem) st_init_src) *)
(*   : *)
(*     exists st_init_tgt, *)
(*       <<INITTGT: initial_frame tprog rs_init_tgt (tgt_mem sm_init) st_init_tgt>> *)
(*                                /\ <<MATCH: match_states st_init_src st_init_tgt>> *)
(* . *)
(* Proof. *)
(*   ss. u in *. unfold ModSemPair.sim_skenv in *. ss. clear SIMSKENV. *)
(*   inv INITSRC. *)
(*   exploit (functions_translated_inject); eauto. intro FPTRTGT; des. *)
(*   destruct fd_tgt; ss; unfold bind in *; ss; des_ifs. *)
(*   rename fd into fd_src. rename f into fd_tgt. *)
(*   assert(RSPINJ:= RSREL SP). *)
(*   ss. rewrite RSPPTR in *. inv RSPINJ. *)
(*   rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ. *)
(*   rename sp into sp_src. rename b2 into sp_tgt. rename m_init into m_init_src. *)
(*   rewrite Ptrofs.add_zero_l in *. *)
(*   esplits; eauto. *)
(*   - econs; eauto. *)
(*   - *)
(*     assert(PTRRA: is_real_ptr (rs_init_tgt RA)). *)
(*     { admit "add to sem (of LinearC)". } *)
(*     u in PTRRA. des_ifs. clear_tac. *)
(*     rename b into ra. rename i into delta_ra. rename delta into delta_sp. clear_tac. *)

(*     econs; eauto. *)
(*     + econs 1; eauto; cycle 1. *)
(*       { rewrite RSPPTRTGT. ss. } *)
(*       i. *)
(*       assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)). *)
(*       { eapply loc_arguments_acceptable_2; eauto. } *)
(*       assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty). *)
(*       { destruct ACC. unfold slot_valid, proj_sumbool. *)
(*         rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. } *)
(*       { *)
(*         intros; red. *)
(*           eapply Z.le_trans with (size_arguments _); eauto. *)
(*           apply loc_arguments_bounded; eauto. *)
(*         u. *)
(*         xomega. *)
(*       } *)
(*     + ii. *)
(*       u in RSREL. *)
(*       u in RSREL. u. *)
(*       u. *)
(*       assert((ls_init (R r)) = Vundef \/ (ls_init (R r)) = rs_init_src (preg_of r)). *)
(*       { hexploit fill_arguments_spec_reg; eauto. *)
(*         { apply LOADARG. } *)
(*         i; des. *)
(*         specialize (H r). des. *)
(*         destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (Linear.fn_sig fd_src))))). *)
(*         - special INSIDE; ss. des; eauto. *)
(*         - special OUTSIDE; ss. eauto. } *)
(*       des. *)
(*       * rewrite H. econs; eauto. *)
(*       * rewrite H. eapply RSREL. *)
(*     + ii. des_ifs. *)
(*     + eapply match_stack_contents; eauto. ss. *)
(* Qed. *)

(* Theorem sim *)
(*   : *)
(*     ModSemPair.sim msp *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   { admit "garbage". } *)
(*   ii. *)
(*   ss. *)
(*   split; ss. *)
(* Qed. *)

(* End PRESERVATION. *)

(* Require Import CoqlibC Errors. *)
(* Require Import Integers ASTC Linking. *)
(* Require Import ValuesC MemoryC SeparationC Events GlobalenvsC Smallstep. *)
(* Require Import LTL Op LocationsC LinearC MachC. *)
(* (* Require Import BoundsC Conventions StacklayoutC Lineartyping. *) *)
(* Require Import Bounds Conventions Stacklayout Lineartyping. *)
(* Require Import Stacking. *)

(* Local Open Scope string_scope. *)
(* Local Open Scope sep_scope. *)

(* (* newly added *) *)
(* Require Export StackingproofC0. *)
(* Require Import Simulation. *)
(* Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC ArgPassing MatchSimModSem. *)
(* Require Import SimMemInj. *)

(* Set Implicit Arguments. *)






(* Local Opaque Z.add Z.mul Z.div. *)

(* (* Section DUMMY_FUNCTION. *) *)

(* (*   Variable sg: signature. *) *)

(* (*   Lemma dummy_function_used_callee_save *) *)
(* (*     : *) *)
(* (*     (dummy_function sg).(function_bounds).(used_callee_save) = [] *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_bound_local *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_local) = 0 *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_bound_outgoing *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_outgoing) = (size_arguments sg) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     ss. unfold dummy_function. cbn. *) *)
(* (*     rewrite Z.max_l; try xomega. rewrite Z.max_r; try xomega. *) *)
(* (*     generalize (size_arguments_above sg). i. xomega. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_bound_stack_data *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(bound_stack_data) = 0 *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_size_callee_save_area *) *)
(* (*         ofs *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(size_callee_save_area) ofs = ofs *) *)
(* (*   . *) *)
(* (*   Proof. ss. Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_local *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_local) = (align (4 * size_arguments sg) 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_link *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_link) = (align (4 * size_arguments sg) 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     ss. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_ofs_retaddr *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_ofs_retaddr) = (align (4 * size_arguments sg) 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. ss. des_ifs_safe. *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (*   Lemma dummy_function_fe_size *) *)
(* (*     : *) *)
(* (*       (dummy_function sg).(function_bounds).(make_env).(fe_size) = (align (4 * size_arguments sg) 8 + 8 + 8) *) *)
(* (*   . *) *)
(* (*   Proof. *) *)
(* (*     unfold make_env. *) *)
(* (*     (*??????????????? simpl. -> inf loop, but cbn works!!!!!!!!!!!!! *) *) *)
(* (*     cbn. des_ifs_safe. rewrite Z.max_l; try xomega. rewrite Z.max_r; cycle 1. *) *)
(* (*     { generalize (size_arguments_above sg). i. xomega. } *) *)
(* (*     rewrite Z.mul_0_r. rewrite ! Z.add_0_r. *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     { apply align_divides. xomega. } *) *)
(* (*     rewrite align_divisible; try xomega; cycle 1. *) *)
(* (*     apply Z.divide_add_r; try xomega. *) *)
(* (*     - apply align_divides; auto. xomega. *) *)
(* (*     - reflexivity. *) *)
(* (*   Qed. *) *)

(* (* End DUMMY_FUNCTION. *) *)

(* (* Hint Rewrite dummy_function_used_callee_save: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_local: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_outgoing: dummy. *) *)
(* (* Hint Rewrite dummy_function_bound_stack_data: dummy. *) *)
(* (* Hint Rewrite dummy_function_size_callee_save_area: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_local: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_link: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_ofs_retaddr: dummy. *) *)
(* (* Hint Rewrite dummy_function_fe_size: dummy. *) *)

(* Print typesize. *)
(* Print loc_arguments_64. (* always + 2 *) *)
(* (* Lemma loc_arguments_64_complete *) *)
(* (*       x tys ir fr *) *)
(* (*       (SIZE0: x < 4 * size_arguments_64 tys ir fr 0) *) *)
(* (*       (SIZE1: 0 <= x) *) *)
(* (*       (IR: 0 <= ir) *) *)
(* (*       (FR: 0 <= fr) *) *)
(* (*   : *) *)
(* (*     exists sl pos ty, <<IN: In (S sl pos ty) (loc_arguments_64 tys ir fr 0).(regs_of_rpairs)>> *) *)
(* (*                             /\ <<OFS: pos <= x < pos + 4 * ty.(typesize)>> *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   ginduction tys; ii; ss. *) *)
(* (*   { xomega. } *) *)
(* (*   destruct a; ss. *) *)
(* (*   - des. *) *)
(* (*     des_ifs; try (exploit IHtys; eauto; try xomega; i; des; []; esplits; eauto; ss; right; eauto). *) *)
(* (*     assert(6 <= ir). *) *)
(* (*     { xomega. } *) *)
(* (*     ss. esplits; eauto; try xomega. ss. rewrite Z.add_0_l in *. rewrite Z.mul_1_r. *) *)
(* (*     unfold size_arguments_64 in SIZE0. ss. des_ifs. *) *)
(* (*     u in SIZE0. *) *)
(* (*     destruct ir; try xomega. *) *)
(* (*     ss. *) *)
(* (*   - *) *)
(* (* Qed. *) *)

(* (* Lemma size_arguments_loc_arguments *) *)
(* (*       ofs sg *) *)
(* (*       (SIZE: 0 <= ofs < 4 * size_arguments sg) *) *)
(* (*   : *) *)
(* (*     exists sl pos ty, In (S sl pos ty) (loc_arguments sg).(regs_of_rpairs) *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   destruct sg; ss. unfold size_arguments in *. unfold loc_arguments in *. des_ifs_safe. ss. clear_tac. *) *)
(* (*   ginduction sig_args; ii; ss. *) *)
(* (*   { xomega. } *) *)
(* (* Qed. *) *)










(* (* TODO: Move to CoqlibC *) *)
(* Ltac psimpl := *)
(*   repeat (try rewrite ! Ptrofs.unsigned_zero in *; *)
(*           try rewrite ! Ptrofs.add_zero in *; *)
(*           try rewrite ! Ptrofs.add_zero_l in *; *)
(*           try rewrite ! Ptrofs.repr_unsigned in *; *)
(*           try rewrite ! IntegersC.Ptrofs_add_repr in *; *)
(*           try (rewrite Ptrofs.unsigned_repr in *; ss; try xomega; []) *)
(*          ) *)
(* . *)






(* Section ARGPASSING. *)

(* Local Existing Instance Val.mi_final. *)

(* (* Lemma store_stored_inject *) *)
(* (*       j0 m_src0 m_src1 m_tgt *) *)
(* (*       (INJ: Mem.inject j0 m_src0 m_tgt) *) *)
(* (*       v_src v_tgt *) *)
(* (*       (INJV: Val.inject j0 v_src v_tgt)  *) *)
(* (*       ty rsp_src rsp_tgt rspdelta ofs *) *)
(* (*       (SRC: Mem.storev (chunk_of_type ty) m_src0 (Vptr rsp_src ofs true) v_src = Some m_src1) *) *)
(* (*       (TGT: Mem_stored (chunk_of_type ty) m_tgt rsp_tgt (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) v_tgt) *) *)
(* (*       (INJRSP: j0 rsp_src = Some (rsp_tgt, rspdelta.(Ptrofs.unsigned))) *) *)
(* (*   : *) *)
(* (*     <<INJ: Mem.inject j0 m_src1 m_tgt>> *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   ss. red. *) *)
(* (*   exploit Mem.store_mapped_inject; eauto. i; des. *) *)
(* (*   eapply Mem.inject_extends_compose; eauto. *) *)
(* (*   clear - TGT H. *) *)
(* (* Local Transparent Mem.store. *) *)
(* (*   hexploit MemoryC.Mem_store_perm_eq; eauto. intro PERM. des. *) *)
(* (*   replace (Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta) with *) *)
(* (*       (Ptrofs.unsigned (Ptrofs.add ofs rspdelta)) in *; cycle 1. *) *)
(* (*   { rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; ss. split; try xomega. *) *)
(* (*     hexploit (Ptrofs.unsigned_range ofs); eauto. i. *) *)
(* (*     hexploit (Ptrofs.unsigned_range rspdelta); eauto. i. *) *)
(* (*     xomega. *) *)
(* (*   } *) *)
(* (*   abstr (Ptrofs.unsigned ofs + Ptrofs.unsigned rspdelta) ofs0. *) *)
(* (*   unfold Mem.store in *. inv TGT. des_ifs. *) *)
(* (*   econs; eauto. *) *)
(* (*   unfold inject_id. *) *)
(* (*   econs; ss; eauto. *) *)
(* (*   - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss. *) *)
(* (*   - ii; clarify. unfold Mem.range_perm, Mem.perm in *. ss. rewrite Z.divide_0_r. reflexivity. *) *)
(* (*   - ii; clarify. unfold Mem.perm in *; ss. rewrite Z.add_0_r. ss. *) *)
(* (*     rewrite Maps.PMap.gsspec. des_ifs; cycle 1. *) *)
(* (*     { apply memval_inject_refl. } *) *)
(* (*     rewrite <- STORED. *) *)
(* (*     rename rsp_tgt into b. abstr (chunk_of_type ty) chunk. clear_tac. *) *)
(* (*     destruct chunk; ss; rewrite ! Maps.ZMap.gsspec; des_ifs; try apply memval_inject_refl. *) *)
(* (* Qed. *) *)

(* Lemma B2C_mem_inject *)
(*       j m_alloc ls_arg sg m_arg m_tgt *)
(*       (INJ: Mem.inject j m_alloc m_tgt) *)
(*       (* rsp_src rsp_tgt *) *)
(*       (* (INJRSP: Val.inject j rsp_src rsp_tgt) *) *)
(*       blk_src blk_tgt (* delta *) *)
(*       (INJRSP: j blk_src = Some (blk_tgt, 0)) *)
(*       (* (DELTA: 0 <= delta <= Ptrofs.max_unsigned) *) *)
(*       (BCM: Call.B2C_mem m_alloc (Vptr blk_src Ptrofs.zero true) ls_arg *)
(*                     (regs_of_rpairs (loc_arguments sg)) = Some m_arg) *)
(*       (ARGSTGTSTRONG: forall ofs ty, *)
(*           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef >> \/ *)
(*           (exists v, *)
(*               <<STORED: Mem_storedv (chunk_of_type ty) m_tgt *)
(*                                     (Val.offset_ptr (Vptr blk_tgt Ptrofs.zero(* delta.(Ptrofs.repr) *) true) *)
(*                                                     (Ptrofs.repr (4 * ofs))) v >> /\ *)
(*               <<INJECT: Val.inject j (ls_arg (S Outgoing ofs ty)) v >>)) *)
(*       (SZARG: 4 * (size_arguments sg) <= Ptrofs.max_unsigned) *)
(*   : *)
(*     <<INJ: Mem.inject j m_arg m_tgt>> *)
(* . *)
(* Proof. *)
(*   generalize (loc_arguments_acceptable_2 sg); eauto. i. *)
(*   generalize (loc_arguments_bounded sg); eauto. i. *)
(*   abstr (regs_of_rpairs (loc_arguments sg)) locs. *)
(*   ss. *)
(*   ginduction locs; ii; ss; psimpl. *)
(*   { clarify. } *)
(*   u in *. *)
(*   des_ifs; ss; try (by eapply IHlocs; eauto). *)
(*   exploit IHlocs; try eassumption; eauto. intro INJ0. *)
(*   (* rewrite Ptrofs.add_unsigned in H0. *) *)
(*   exploit ARGSTGTSTRONG; eauto. i; des. *)
(*   { eapply Mem_store_mapped_inject_undef; eauto. rewrite H1 in *. eauto. } *)
(*   eapply store_stored_inject; eauto; cycle 1. *)
(*   { rewrite INJRSP. repeat f_equal; eauto. *)
(*     rewrite Ptrofs.unsigned_repr; ss. *)
(*   } *)
(*   { rewrite Ptrofs.unsigned_repr; ss. psimpl. *)
(*     hexploit H; eauto. i; des. *)
(*     hexploit H0; eauto. i; des. *)
(*     generalize (typesize_pos ty); i. *)
(*     rewrite Ptrofs.unsigned_repr; ss; try xomega. *)
(*   } *)
(*   psimpl. rpapply H1. *)
(* Qed. *)

(* Lemma B2C_mem_simmem *)
(*       ls_arg sg sm0 m_src1 *)
(*       (MWF: SimMem.wf sm0) *)
(*       blk_src blk_tgt (* delta *) *)
(*       (INJRSP: sm0.(inj) blk_src = Some (blk_tgt, 0)) *)
(*       (BCM: Call.B2C_mem sm0.(SimMem.src) (Vptr blk_src Ptrofs.zero true) ls_arg *)
(*                     (regs_of_rpairs (loc_arguments sg)) = Some m_src1) *)
(*       (ARGSTGTSTRONG: forall ofs ty, *)
(*           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef >> \/ *)
(*           (exists v, *)
(*               <<STORED: Mem_storedv (chunk_of_type ty) sm0.(SimMem.tgt) *)
(*                                     (Val.offset_ptr (Vptr blk_tgt Ptrofs.zero(* delta.(Ptrofs.repr) *) true) *)
(*                                                     (Ptrofs.repr (4 * ofs))) v >> /\ *)
(*               <<INJECT: Val.inject sm0.(inj) (ls_arg (S Outgoing ofs ty)) v >>)) *)
(*       (SZARG: 4 * (size_arguments sg) <= Ptrofs.max_unsigned) *)
(*   : *)
(*     let sm1 := (mk sm0.(inj) m_src1 sm0.(m_tgt) *)
(*                          sm0.(src_external) sm0.(tgt_external) *)
(*                          sm0.(src_parent_nb) sm0.(tgt_parent_nb)) in *)
(*     <<MWF: SimMem.wf sm1>> /\ <<MLE: SimMem.le sm0 sm1>> *)
(* . *)
(* Proof. *)
(*   generalize (loc_arguments_acceptable_2 sg); eauto. i. *)
(*   generalize (loc_arguments_bounded sg); eauto. i. *)
(*   abstr (regs_of_rpairs (loc_arguments sg)) locs. *)
(*   subst_locals. *)
(*   ss. *)
(*   ginduction locs; ii; ss; psimpl. *)
(*   { clarify. destruct sm0; ss. esplits; eauto. reflexivity. } *)
(*   u in *. *)
(*   des_ifs; ss; try (by eapply IHlocs; eauto). *)
(*   exploit IHlocs; try eassumption; eauto. intro INJ0. *)
(*   (* rewrite Ptrofs.add_unsigned in H0. *) *)
(*   exploit ARGSTGTSTRONG; eauto. i; des_safe. *)
(*   des. *)
(*   { rewrite H1 in *. eapply store_undef_simmem in INJ0; eauto; cycle 1. *)
(*     { u. unfold loc_unmapped. i; des. clarify. } *)
(*     ss. des. esplits; eauto. etransitivity; eauto. } *)
(*   psimpl. *)
(*   exploit store_stored_simmem; try apply INJ0; eauto; ss. *)
(*   { rpapply H1. rewrite Ptrofs.add_zero. eauto. } *)
(*   { rewrite INJRSP. repeat f_equal; eauto. } *)
(*   { psimpl. *)
(*     hexploit H; eauto. i; des. *)
(*     hexploit H0; eauto. i; des. *)
(*     generalize (typesize_pos ty); i. *)
(*     rewrite Ptrofs.unsigned_repr; ss; try xomega. *)
(*   } *)
(*   i; des. *)
(*   esplits; eauto. *)
(*   etransitivity; eauto. *)
(* Qed. *)

(* End ARGPASSING. *)


(* Section SIMMODSEM. *)

(* Local Existing Instance Val.mi_final. *)
(* Variable skenv_link_src skenv_link_tgt: SkEnv.t. *)
(* Variable prog: Linear.program. *)
(* Variable tprog: Mach.program. *)
(* Hypothesis TRANSF: match_prog prog tprog. *)
(* Variable rao: Mach.function -> Mach.code -> ptrofs -> Prop. *)
(* Let ge := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog). *)
(* Let tge := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog). *)

(* Definition msp: ModSemPair.t := *)
(*   ModSemPair.mk (LinearC.modsem skenv_link_src prog) (MachC.modsem rao skenv_link_tgt tprog) tt *)
(* . *)

(* Inductive match_states (rs_init_src rs_init_tgt: regset) *)
(*           (sm_init: SimMem.t) *)
(*           (idx: nat) (st_src0: Linear.state) (st_tgt0: Mach.state) (sm0: SimMem.t): Prop := *)
(* | match_states_intro *)
(*     (SIMRSINIT: SimMem.sim_regset sm0 rs_init_src rs_init_tgt) *)
(*     (MATCHST: StackingproofC0.match_states prog tprog rao st_src0 st_tgt0) *)
(*     (MCOMPAT: mem_compat msp.(ModSemPair.src) msp.(ModSemPair.tgt) st_src0 st_tgt0 sm0) *)
(*     (* TODO: put sm intside match_states. j is actually sm0.(inj) *) *)
(*     (MWF: SimMem.wf sm0) *)
(*     (* (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge) *) *)
(* . *)

(* Lemma functions_translated_inject *)
(*       j *)
(*       (SIMGE: Genv.match_genvs (match_globdef (fun _ f tf => transf_fundef f = OK tf) eq prog) ge tge) *)
(*       (SIMGE0: DUMMY_PROP) (* globalenv_inject match_globalenvs *) *)
(*       fptr_src fd_src *)
(*       (FUNCSRC: Genv.find_funct ge fptr_src = Some fd_src) *)
(*       fptr_tgt *)
(*       (INJ: Val.inject j fptr_src fptr_tgt) *)
(*   : *)
(*     exists fd_tgt, *)
(*       <<FUNCTGT: Genv.find_funct tge fptr_tgt = Some fd_tgt>> *)
(*       /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>> *)
(* . *)
(* Proof. *)
(*   admit "ez". *)
(* Qed. *)

(* Local Opaque sepconj. *)
(* Local Opaque function_bounds. *)
(* Local Opaque make_env. *)
(* Ltac sep_split := econs; [|split]; swap 2 3. *)
(* Hint Unfold fe_ofs_arg. *)
(* Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *) *)
(* Hint Unfold to_mregset. *)

(* Theorem init_match_states *)
(*         sm_arg *)
(*         (SIMSKENV: SimSymb.sim_skenv sm_arg tt (SkEnv.project skenv_link_src (defs prog)) *)
(*                                      (SkEnv.project skenv_link_tgt (defs tprog))) *)
(*         (MWF: SimMem.wf sm_arg) *)
(*         rs_arg_src rs_arg_tgt *)
(*         (SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt) *)
(*         st_init_src *)
(*         (INITSRC: LinearC.initial_frame skenv_link_src prog rs_arg_src sm_arg.(SimMem.src) st_init_src) *)
(*   : *)
(*     exists st_init_tgt sm_init idx_init, *)
(*     <<INITTGT: initial_frame skenv_link_tgt tprog rs_arg_tgt sm_arg.(SimMem.tgt) st_init_tgt >> /\ *)
(*     <<MCOMPAT: mem_compat (LinearC.modsem skenv_link_src prog) (modsem rao skenv_link_tgt tprog) *)
(*                           st_init_src st_init_tgt sm_init >> /\ *)
(*     <<MLE: SimMem.le sm_arg sm_init >> /\ *)
(*     <<MATCH: match_states rs_arg_src rs_arg_tgt sm_arg idx_init st_init_src st_init_tgt sm_init>> *)
(* . *)
(* Proof. *)
(*   ss. *)
(*   inv INITSRC. *)
(*   assert(RSPINJ:= SIMRS SP). *)
(*   assert(PCINJ:= SIMRS PC). *)
(*   dup DB. inv DB. ss. inv DC. inv CB. ss. *)
(*   exploit (functions_translated_inject); eauto. *)
(*   { admit "sim ge". } *)
(*   intro FPTRTGT; des. *)
(*   destruct fd_tgt; ss; unfold bind in *; ss; des_ifs. *)
(*   rename fd into fd_src. rename f into fd_tgt. *)
(*   ss. rewrite RSPPTR in *. inv RSPINJ. *)
(*   rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ. *)
(*   rename blk into sp_src. rename b2 into sp_tgt. *)
(*   rename m_init into m_init_src. *)
(*   rewrite Ptrofs.add_zero_l in *. *)
(*   hexploit Mem.free_range_perm; eauto. intro PERMSRC. *)
(*   set (sm_init := (mk sm_arg.(inj) *)
(*                    m_init_src sm_arg.(m_tgt) *)
(*                    sm_arg.(src_external) sm_arg.(tgt_external) *)
(*                    sm_arg.(src_parent_nb) sm_arg.(tgt_parent_nb))). *)
(*   exploit Mem.free_result; eauto. i; des. clarify. *)
(*   assert(MWF0: SimMem.wf sm_init). *)
(*   { ss. econs; ss; try apply MWF; eauto. *)
(*     + eapply Mem.free_left_inject; eauto. apply MWF. *)
(*     + etransitivity; try apply MWF; eauto. admit "ez". *)
(*   } *)
(*   eexists _, sm_init, 0%nat; cbn. *)
(*   esplits; eauto. *)
(*   - econs; eauto. *)
(*   - ss. *)
(*   - ss. econs; ss; eauto. *)
(*     + admit "drop_perm ez". *)
(*     + reflexivity. *)
(*     + eapply frozen_refl. *)
(*     + admit "drop_perm ez". *)
(*     + reflexivity. *)
(*   - ss. *)
(*     econs; ss; eauto. *)
(*     assert(PTRRA: is_ptr (rs_arg_tgt RA)). *)
(*     { u in RAPTR. des_ifs. specialize (SIMRS RA). rewrite Heq0 in *. inv SIMRS; ss. } *)
(*     (* autounfold with * in PTRRA. *) *)
(*     (* u in PTRRA. des_ifs. clear_tac. *) *)
(*     (* rename b into ra. rename i into delta_ra. *) *)
(*     rename delta into delta_sp. clear_tac. *)

(*     econs; eauto. *)
(*     + econs 1; eauto; cycle 1. *)
(*       { rewrite RSPPTRTGT. ss. } *)
(*       i. *)
(*       assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)). *)
(*       { eapply loc_arguments_acceptable_2; eauto. } *)
(*       assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty). *)
(*       { destruct ACC. unfold slot_valid, proj_sumbool. *)
(*         rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. } *)
(*       { *)
(*         intros; red. *)
(*           eapply Z.le_trans with (size_arguments _); eauto. *)
(*           apply loc_arguments_bounded; eauto. *)
(*         u. *)
(*         xomega. *)
(*       } *)
(*     + ii. *)
(*       ss. u. eapply SIMRS; eauto. *)
(*     + ii. des_ifs. *)
(*     + u. des_ifs. *)
(*       rename Heq0 into RSPTGT. *)
(*       assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) -> *)
(*                     0 <= delta_sp <= Ptrofs.max_unsigned *)
(*                     /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned). *)
(*       { i; eapply delta_range; eauto. apply MWF. xomega. } *)
(*       rewrite sep_comm. rewrite sep_assoc. *)
(*       sep_split. *)
(*       { simpl. apply MWF0. } *)
(*       { apply disjoint_footprint_drop_empty. *)
(*         { ss. } *)
(*         intros ? delta INJDUP. ii. ss. des. clarify. *)
(*         rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'. *)
(*         destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*         { omega. } *)
(*         special DELTA; ss. clear_tac. *)
(*         rewrite Ptrofs.unsigned_repr in *; try omega. *)
(*         (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *) *)
(*         assert(sp_src' = sp_src). *)
(*         { apply NNPP. intro DISJ. *)
(*           hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP. *)
(*           exploit OVERLAP; eauto. *)
(*           { eapply Mem.perm_free_3; eauto. } *)
(*           { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. } *)
(*           { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. } *)
(*         } *)
(*         clarify. *)
(*         hexploit (Mem_drop_perm_none_spec (SimMem.src sm_arg) sp_src 0 *)
(*                                           (4 * size_arguments (Linear.fn_sig fd_src))); eauto. i; des. *)
(*         eapply INSIDE; eauto. omega. *)
(*       } *)
(*       sep_split. *)
(*       { ss. admit "sim_genv". } *)
(*       { ss. } *)
(* { *)
(*   ss. rewrite Ptrofs.unsigned_repr_eq. *)
(*   assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus). *)
(*   { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. } *)
(*   split; eauto. *)
(*   split; eauto. *)
(*   { eapply POSBOUND. } *)
(*   destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*   { esplits; auto. *)
(*     - specialize (POSBOUND delta_sp). xomega. *)
(*     - ii. xomega. *)
(*     - i. generalize (typesize_pos ty). i. xomega. *)
(*   } *)
(*   special DELTA; ss. *)
(*   des. *)
(*   specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *. *)
(*   erewrite Z.mod_small; try xomega. *)
(*   split; try xomega. *)
(*   Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name]. *)
(*   dsplit_r; try xomega. *)
(*   { rewrite Z.add_comm. *)
(*     change (delta_sp) with (0 + delta_sp). *)
(*     eapply Mem.range_perm_inject; try apply MWF; eauto. *)
(*   } *)
(*   ii; des. *)
(*   { *)
(*     assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (SimMem.tgt sm_arg) sp_tgt (delta_sp + 4 * ofs) = Some v). *)
(*     { eapply Mem.valid_access_load; eauto. *)
(*       hnf. *)
(*       rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*       split; try xomega. *)
(*       - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*       - apply Z.divide_add_r. *)
(*         + rewrite <- align_type_chunk. *)
(*           eapply Mem.mi_align; try apply MWF; eauto. *)
(*           instantiate (1:= Nonempty). *)
(*           instantiate (1:= 0). *)
(*           rewrite Z.add_0_l. *)
(*           ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*           rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*         + apply Z.mul_divide_mono_l. ss. *)
(*     } *)
(*     des. *)
(*     esplits; eauto. *)
(*     - des_ifs; try (by econs; eauto). *)
(*       Local Opaque Ptrofs.modulus. *)
(*       unfold load_stack in *. ss. *)
(*       rewrite ! Ptrofs.add_zero_l in *. unfold fe_ofs_arg in *. rewrite Z.add_0_l in *. *)
(*       exploit Mem.load_inject; try apply MWF; eauto. intro LOADTGT0; des. *)
(*       assert(v = v2). *)
(*       { erewrite Ptrofs.unsigned_repr in LOADTGT0; eauto. rewrite Z.add_comm in LOADTGT0. clarify. *)
(*         split; try xomega. *)
(*         unfold Ptrofs.max_unsigned. *)
(*         generalize (typesize_pos ty); i. *)
(*         xomega. *)
(*       } *)
(*       clarify. *)
(*   } *)
(* } *)
(*     + i; des; ss. clear - FINDFUNC H. admit "ge". *)
(* Qed. *)

(* Lemma match_stacks_parent_sp *)
(*       j cs stack sg *)
(*       (MATCH: match_stacks tprog j cs stack sg) *)
(*   : *)
(*     <<RSPPTR: is_real_ptr (parent_sp stack)>> *)
(* . *)
(* Proof. *)
(*   induction MATCH; ss. *)
(* Qed. *)

(* Theorem sim_modsem *)
(*   : *)
(*     ModSemPair.sim msp *)
(* . *)
(* Proof. *)
(*   eapply match_states_sim with (match_states := match_states); eauto; ii; ss. *)
(*   - instantiate (1:= Nat.lt). apply lt_wf. *)
(*   - (* INITFSIM *) *)
(*     exploit init_match_states; eauto. i; des. *)
(*     esplits; eauto. *)
(*   - (* ATPROGRESS *) *)
(*     (* NNNNNNNNNNNNNNNNNNNNNNNNOTE WE CAN DO FSIM HERE TOO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *) *)
(*     inv MATCH. *)
(*     esplits; eauto. *)
(*     u in CALLSRC. des. *)
(*     destruct sm0; ss. inv MCOMPAT; ss. des. clarify. *)
(*     inv CALLSRC; ss. inv MATCHST; ss. *)
(*     fold_all ge. *)
(*     u. *)
(*     inv BD. inv BC. *)
(*     esplits; eauto. *)
(*     econs; eauto. *)
(*     + fold_all tge. *)
(*       admit "this should hold. is_call_progress". *)
(*     + econs; eauto. *)
(*       { reflexivity. } *)
(*     (* inv STORE; ss. *) *)
(*     (* u in PCPTR. des_ifs. clear_tac. ss. *) *)
(*     (* destruct b0; ss; cycle 1. *) *)
(*     (* { inv FPTR. ss. esplits; eauto. econs; eauto. } *) *)
(*     (* destruct (Genv.find_funct tge tfptr) eqn:T; cycle 1. *) *)
(*     (* { esplits; eauto. econs; eauto. } *) *)
(*     (* unfold Genv.find_funct in *. des_ifs_safe; inv FPTR; ss. *) *)
(*     (* assert(delta = 0). *) *)
(*     (* { admit "by genv match". } *) *)
(*     (* clarify. rewrite Ptrofs.add_zero in *. clarify. *) *)
(*     (* des_ifs. *) *)
(*     (* esplits; eauto. *) *)
(*     (* econs; eauto. *) *)
(*     (* ss. fold_all tge. des_ifs. *) *)
(*     (* admit "by genv match". *) *)
(*   - (* ATBSIM *) *)
(*     revert_until MATCH. *)
(*     assert(ATFSIM: forall *)
(*               rs_arg_src m_arg_src *)
(*               (ATSRC: LinearC.at_external skenv_link_src prog st_src0 rs_arg_src m_arg_src) *)
(*             , *)
(*               exists (rs_arg_tgt : regset) (m_arg_tgt : mem) (sm_arg : SimMem.t), *)
(*                 (<<ATEXT: MachC.at_external skenv_link_tgt tprog st_tgt0 rs_arg_tgt m_arg_tgt >>) /\ *)
(*                 (<<MSRC: SimMem.src sm_arg = m_arg_src >>) /\ *)
(*                 (<<MTGT: SimMem.tgt sm_arg = m_arg_tgt >>) /\ *)
(*                 (<<SIMRS: SimMem.sim_regset sm_arg rs_arg_src rs_arg_tgt >>) /\ *)
(*                 (<<MLE: le' sm0 sm_arg >>) /\ (<<MWF: wf' sm_arg >>)). *)
(* { *)
(*   ii; ss. *)
(*   inv ATSRC; ss. inv BD. inv BC. *)
(*   rename blk into sp_src. *)
(*   inv MATCH; ss. inv MATCHST; ss. *)
(*   assert(ARGSTGT: forall l (IN: In l (regs_of_rpairs (loc_arguments sg_arg))), *)
(*             (exists v, Mach.extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls_arg l) v)). *)
(*   { eapply transl_external_argument; eauto. apply sep_pick1 in SEP. eauto. } *)
(*   inv MCOMPAT; ss. des. clarify. *)
(*   assert(sm0.(inj) = j). *)
(*   { admit "put sm inside match_states". } *)
(*   clarify. *)
(*   exploit match_stacks_parent_sp; eauto. i; des. *)
(*   u in H. des_ifs. clear_tac. rename b into sp_tgt. rename i into spdelta. *)
(*   rename Heq into PARENTPTR. *)

(*   exploit (@Call.B2C_mem_spec sg_arg m_alloc sp_src ls_arg); eauto. *)
(*   { eapply Mem_alloc_range_perm; eauto. } *)
(*   i; des. clarify. *)

(*   set (sm_arg := (mk (fun blk => if eq_block blk sp_src *)
(*                                  then Some (sp_tgt, spdelta.(Ptrofs.unsigned)) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_arg_src sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   unfold load_stack in *. ss. *)

(*   destruct (classic (length stack = 1%nat)). *)
(*   { (* this case, alloc with size 0 /\ no more store. *) *)
(*     inv STACKS; ss; cycle 1. *)
(*     { inv STK; ss. }  *)
(*     hexploit ABCD; eauto. *)
(*     { esplits; eauto. admit "genv". } *)
(*     intro TAIL. *)
(*     assert(m_alloc = m_arg_src). *)
(*     { admit "tailcall_possible". } *)
(*     clarify. *)
(*     inv CD. ss. *)
(*     assert(MLE: SimMem.le sm0 sm_arg). *)
(*     { admit "??". } *)
(*     assert(MWF0: SimMem.wf sm_arg). *)
(*     { admit "??". } *)
(*     do 2 eexists. exists sm_arg. cbn. *)
(*     esplits; cbn; try reflexivity; eauto. *)
(*     - econs; eauto. *)
(*       + fold tge. admit "this should hold". *)
(*       + econs; eauto. *)
(*         * reflexivity. *)
(*     - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*       + unfold agree_regs in AGREGS. *)
(*         eapply val_inject_incr; eauto. eapply MLE. *)
(*       + des_ifs; try (by econs; eauto). *)
(*         * eapply val_inject_incr; eauto. apply MLE. *)
(*         * econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*         * u in RAPTR. des_ifs. u in RAPTR0. des_ifs. admit "RA inject. unprovable?". *)
(*   } *)

(*   assert(ARGSTGTSTRONG: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg_arg))), *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef>> *)
(*            \/ *)
(*            exists v, *)
(*              <<STORED: Mem_storedv (chunk_of_type ty) (SimMem.tgt sm0) *)
(*                                    (Val.offset_ptr (parent_sp cs') (Ptrofs.repr (4 * ofs))) v>> *)
(*           /\ *)
(*           <<INJECT: Val.inject (inj sm0) (ls_arg (S Outgoing ofs ty)) v>>). *)
(*   { eapply transl_external_arguments_strong; eauto. apply sep_pick1 in SEP. eauto. } *)

(*   assert(spdelta = Ptrofs.zero). *)
(*   { inv STACKS; ss; clarify. } *)
(*   clarify. *)

(*   (* assert(MLE: SimMem.le sm0 sm_arg). *) *)
(*   (* { *) *)
(*   (*   subst sm_arg. *) *)
(*   (*   econs; cbn; eauto with mem; try xomega. *) *)
(*   (*   - ii; ss. des_ifs; ss. exfalso. *) *)
(*   (*     exploit Mem.mi_freeblocks; try apply MWF; eauto. *) *)
(*   (*     { eauto with mem. } *) *)
(*   (*     i; ss. clarify. *) *)
(*   (*   - eapply Mem_unchanged_on_trans_strong; eauto. *) *)
(*   (*     { eapply Mem.alloc_unchanged_on; eauto. } *) *)
(*   (*     eapply Mem.unchanged_on_implies; eauto. cbn. admit "ez". *) *)
(*   (*   - econs; eauto. *) *)
(*   (*     ii; ss. des; ss. des_ifs. *) *)
(*   (*     split; ss. *) *)
(*   (*     + admit "ez". *) *)
(*   (*     + admit "we should add this into match_states". *) *)
(*   (*   - admit "ez". *) *)
(*   (* } *) *)
(*   exploit Mem.alloc_result; eauto. i; des. clarify. *)
(*   exploit Mem.nextblock_alloc; eauto. intro ALLOCNB. *)

(*   set (sm_alloc := (mk (fun blk => if eq_block blk (Mem.nextblock (m_src sm0)) *)
(*                                  then Some (sp_tgt, 0) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_alloc sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   assert(MWF0: SimMem.wf sm_alloc /\ <<MLE0: SimMem.le sm0 sm_alloc>>). *)
(*   { rewrite sep_comm in SEP. rewrite sep_assoc in SEP. apply sep_drop2 in SEP. rewrite sep_comm in SEP. *)
(*     eapply alloc_left_zero_simmem; eauto. *)
(*     - u. ii. esplits; eauto. *)
(*       + rpapply arguments_private; eauto. *)
(*       + admit "ez". *)
(*     - admit "should add this in match_states". *)
(*     - i. apply Mem.perm_cur. eapply Mem.perm_implies. *)
(*       + rpapply arguments_perm; eauto. *)
(*       + eauto with mem. *)
(*     - admit "ez". *)
(*     - admit "should add this in match_states". *)
(*   } *)
(*   des. *)
(*   rewrite PARENTPTR in *. *)
(*   assert(MWF1: SimMem.wf sm_arg /\ <<MLE1: SimMem.le sm0 sm_arg>>). *)
(*   { subst_locals. exploit B2C_mem_simmem; eauto; ss. *)
(*     { des_ifs. } *)
(*     { ii. exploit ARGSTGTSTRONG; eauto. i; des; eauto. right. ss. *)
(*       psimpl. ss. *)
(*       esplits; eauto. *)
(*       eapply val_inject_incr; eauto. *)
(*       apply MLE0. *)
(*     } *)
(*     i; des. *)
(*     esplits; eauto. *)
(*     etransitivity; eauto. *)
(*   } *)
(*   des. *)

(*   inv CD. ss. *)
(*   do 2 eexists. exists sm_arg. cbn. *)
(*   esplits; cbn; try reflexivity; eauto. *)
(*   - econs; eauto. *)
(*     + fold tge. admit "this should hold". *)
(*     + econs; eauto. *)
(*       * reflexivity. *)
(*   - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*     + unfold agree_regs in AGREGS. *)
(*       eapply val_inject_incr; eauto. eapply MLE1. *)
(*     + des_ifs; try (by econs; eauto). *)
(*       * eapply val_inject_incr; eauto. apply MLE1. *)
(*       * rewrite PARENTPTR. econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*       * u in RAPTR. des_ifs. admit "ra inject. unprovable?". *)
(* } *)




(*     ii; ss. u in SAFESRC. des. *)
(*     inv SAFESRC; ss. rename rs_arg into rs_arg_src. rename m_arg into m_arg_src. *)
(*     inv BD. rename mrs into mrs_src. rename rsp_arg into rsp_arg_src. rename ra_arg into ra_arg_src. *)
(*     inv BC. rename blk into sp_src. *)
(*     inv MATCH; ss. inv MATCHST; ss. *)
(*     assert(ARGSTGT: forall l (IN: In l (regs_of_rpairs (loc_arguments sg_arg))), *)
(*               (exists v, Mach.extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls_arg l) v)). *)
(*     { eapply transl_external_argument; eauto. apply sep_pick1 in SEP. eauto. } *)
(*     inv MCOMPAT; ss. des. clarify. *)
(*     assert(sm0.(inj) = j). *)
(*     { admit "put sm inside match_states". } *)
(*     clarify. *)
(*     exploit match_stacks_parent_sp; eauto. i; des. *)
(*     u in H. des_ifs. clear_tac. rename b into sp_tgt. rename i into spdelta. *)
(*     rename Heq into PARENTPTR. *)

(*     exploit (@Call.B2C_mem_spec sg_arg m_alloc sp_src ls_arg); eauto. *)
(*     { eapply Mem_alloc_range_perm; eauto. } *)
(*     i; des. clarify. *)

(*     set (sm_arg := (mk (fun blk => if eq_block blk sp_src *)
(*                                    then Some (sp_tgt, spdelta.(Ptrofs.unsigned)) *)
(*                                    else sm0.(inj) blk) *)
(*                        m_arg_src sm0.(m_tgt) *)
(*                        sm0.(src_external) sm0.(tgt_external) *)
(*                        sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*     unfold load_stack in *. ss. *)

(*     destruct (classic (length stack = 1%nat)). *)
(*     { (* this case, alloc with size 0 /\ no more store. *) *)
(*       inv STACKS; ss; cycle 1. *)
(*       { inv STK; ss. }  *)
(*       hexploit ABCD; eauto. *)
(*       { esplits; eauto. admit "genv". } *)
(*       intro TAIL. *)
(*       assert(m_alloc = m_arg_src). *)
(*       { admit "tailcall_possible". } *)
(*       clarify. *)
(*       inv CD. ss. *)
(*       assert(MLE: SimMem.le sm0 sm_arg). *)
(*       { admit "??". } *)
(*       assert(MWF0: SimMem.wf sm_arg). *)
(*       { admit "??". } *)

(*       inv CALLTGT. ss. *)
(*       do 2 eexists. exists sm_arg. cbn. *)
(*       esplits; cbn; try reflexivity; eauto. *)
(*       - econs; eauto. *)
(*         econs; eauto. *)
(*         + instantiate (1:= ra.(to_fake)). *)
(*           econs; eauto. *)
(*           reflexivity. *)
(*           destruct ra; ss. des_ifs. *)
(*         + econs; eauto. *)
(*           reflexivity. *)
(*       - inv CD. ii; ss. des_ifs. *)
(*         + eapply val_inject_incr; eauto. apply MLE. *)
(*         + eapply val_inject_incr; eauto. apply MLE. *)
(*         + econs; eauto. { des_ifs. } psimpl. ss. *)
(*         + destruct ra; ss. des_ifs. econs; eauto. *)
(*       - econs; eauto. *)
(*         + fold tge. admit "this should hold". *)
(*         + econs; eauto. *)
(*           * reflexivity. *)
(*       - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*         + unfold agree_regs in AGREGS. *)
(*           eapply val_inject_incr; eauto. eapply MLE. *)
(*         + des_ifs; try (by econs; eauto). *)
(*           * eapply val_inject_incr; eauto. apply MLE. *)
(*           * econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*           * u in RAPTR. des_ifs. u in RAPTR0. des_ifs. admit "RA inject. unprovable?". *)
(*     } *)

(*   assert(ARGSTGTSTRONG: forall ofs ty (IN: In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg_arg))), *)
(*           <<UNDEF: ls_arg (S Outgoing ofs ty) = Vundef>> *)
(*            \/ *)
(*            exists v, *)
(*              <<STORED: Mem_storedv (chunk_of_type ty) (SimMem.tgt sm0) *)
(*                                    (Val.offset_ptr (parent_sp cs') (Ptrofs.repr (4 * ofs))) v>> *)
(*           /\ *)
(*           <<INJECT: Val.inject (inj sm0) (ls_arg (S Outgoing ofs ty)) v>>). *)
(*   { eapply transl_external_arguments_strong; eauto. apply sep_pick1 in SEP. eauto. } *)

(*   assert(spdelta = Ptrofs.zero). *)
(*   { inv STACKS; ss; clarify. } *)
(*   clarify. *)

(*   (* assert(MLE: SimMem.le sm0 sm_arg). *) *)
(*   (* { *) *)
(*   (*   subst sm_arg. *) *)
(*   (*   econs; cbn; eauto with mem; try xomega. *) *)
(*   (*   - ii; ss. des_ifs; ss. exfalso. *) *)
(*   (*     exploit Mem.mi_freeblocks; try apply MWF; eauto. *) *)
(*   (*     { eauto with mem. } *) *)
(*   (*     i; ss. clarify. *) *)
(*   (*   - eapply Mem_unchanged_on_trans_strong; eauto. *) *)
(*   (*     { eapply Mem.alloc_unchanged_on; eauto. } *) *)
(*   (*     eapply Mem.unchanged_on_implies; eauto. cbn. admit "ez". *) *)
(*   (*   - econs; eauto. *) *)
(*   (*     ii; ss. des; ss. des_ifs. *) *)
(*   (*     split; ss. *) *)
(*   (*     + admit "ez". *) *)
(*   (*     + admit "we should add this into match_states". *) *)
(*   (*   - admit "ez". *) *)
(*   (* } *) *)
(*   exploit Mem.alloc_result; eauto. i; des. clarify. *)
(*   exploit Mem.nextblock_alloc; eauto. intro ALLOCNB. *)

(*   set (sm_alloc := (mk (fun blk => if eq_block blk (Mem.nextblock (m_src sm0)) *)
(*                                  then Some (sp_tgt, 0) *)
(*                                  else sm0.(inj) blk) *)
(*                      m_alloc sm0.(m_tgt) *)
(*                      sm0.(src_external) sm0.(tgt_external) *)
(*                      sm0.(src_parent_nb) sm0.(tgt_parent_nb))). *)
(*   assert(MWF0: SimMem.wf sm_alloc /\ <<MLE0: SimMem.le sm0 sm_alloc>>). *)
(*   { rewrite sep_comm in SEP. rewrite sep_assoc in SEP. apply sep_drop2 in SEP. rewrite sep_comm in SEP. *)
(*     eapply alloc_left_zero_simmem; eauto. *)
(*     - u. ii. esplits; eauto. *)
(*       + rpapply arguments_private; eauto. *)
(*       + admit "ez". *)
(*     - admit "should add this in match_states". *)
(*     - i. apply Mem.perm_cur. eapply Mem.perm_implies. *)
(*       + rpapply arguments_perm; eauto. *)
(*       + eauto with mem. *)
(*     - admit "ez". *)
(*     - admit "should add this in match_states". *)
(*   } *)
(*   des. *)
(*   rewrite PARENTPTR in *. *)
(*   assert(MWF1: SimMem.wf sm_arg /\ <<MLE1: SimMem.le sm0 sm_arg>>). *)
(*   { subst_locals. exploit B2C_mem_simmem; eauto; ss. *)
(*     { des_ifs. } *)
(*     { ii. exploit ARGSTGTSTRONG; eauto. i; des; eauto. right. ss. *)
(*       psimpl. ss. *)
(*       esplits; eauto. *)
(*       eapply val_inject_incr; eauto. *)
(*       apply MLE0. *)
(*     } *)
(*     i; des. *)
(*     esplits; eauto. *)
(*     etransitivity; eauto. *)
(*   } *)
(*   des. *)

(*   inv CD. ss. *)
(*   do 2 eexists. exists sm_arg. cbn. *)
(*   esplits; cbn; try reflexivity; eauto. *)
(*   - econs; eauto. *)
(*     + fold tge. admit "this should hold". *)
(*     + econs; eauto. *)
(*       * reflexivity. *)
(*   - u. i. destruct (to_mreg pr) eqn:T; ss. *)
(*     + unfold agree_regs in AGREGS. *)
(*       eapply val_inject_incr; eauto. eapply MLE1. *)
(*     + des_ifs; try (by econs; eauto). *)
(*       * eapply val_inject_incr; eauto. apply MLE1. *)
(*       * rewrite PARENTPTR. econs; eauto. des_ifs. rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned; ss. *)
(*       * u in RAPTR. des_ifs. admit "ra inject. unprovable?". *)
(*   - admit "todo". *)
(*   - admit "todo". *)
(*   - admit "todo". *)
(* Unshelve. *)
(*   all: try (by econs). *)
(* Qed. *)

(* End SIMMODSEM. *)




(* Section SIMMOD. *)

(* Variables prog: Linear.program. *)
(* Variables tprog: Mach.program. *)
(* Hypothesis TRANSL: match_prog prog tprog. *)

(* Definition mp: ModPair.t := *)
(*   ModPair.mk (LinearC.module prog) (MachC.module tprog) tt *)
(* . *)

(* Theorem sim_mod *)
(*   : *)
(*     ModPair.sim mp *)
(* . *)
(* Proof. *)
(*   econs; ss. *)
(*   - econs; eauto. admit "easy". *)
(*   - ii. eapply sim_modsem; eauto. *)
(* Qed. *)

(* End SIMMOD. *)




















(* Section PRESERVATION. *)

(* Local Existing Instance Val.mi_normal. *)
(* Context `{SimSymbId: @SimSymb.SimSymb.class SimMemInj}. *)
(* Variable prog: Linear.program. *)
(* Variable tprog: Mach.program. *)
(* Hypothesis TRANSF: match_prog prog tprog. *)
(* Variable return_address_offset: function -> code -> ptrofs -> Prop. *)
(* Let match_states := match_states prog tprog return_address_offset. *)

(* Lemma functions_translated_inject *)
(*       j *)
(*       (GENV: True) *)
(*       fptr_src fd_src *)
(*       (FUNCSRC: Genv.find_funct (Genv.globalenv prog) fptr_src = Some fd_src) *)
(*       fptr_tgt *)
(*       (INJ: Val.inject j fptr_src fptr_tgt) *)
(*   : *)
(*     exists fd_tgt, *)
(*       <<FUNCTGT: Genv.find_funct (Genv.globalenv tprog) fptr_tgt = Some fd_tgt>> *)
(*       /\ <<TRANSF: transf_fundef fd_src = OK fd_tgt>> *)
(* . *)
(* Proof. *)
(*   admit "easy". *)
(* Qed. *)

(* Definition msp: ModSemPair.t := *)
(*   ModSemPair.mk (LinearC.modsem prog) (MachC.modsem return_address_offset tprog) (admit "simsymb") Nat.lt. *)

(* Local Transparent dummy_stack. *)

(* Ltac sep_split := econs; [|split]; swap 2 3. *)
(* Hint Unfold fe_ofs_arg. *)
(* Hint Unfold SimMem.SimMem.sim_regset. (* TODO: move to proper place *) *)
(* Hint Unfold mregset_of. *)
(* Ltac perm_impl_tac := eapply Mem.perm_implies with Writable; [|eauto with mem]. *)

(* Lemma match_stack_contents *)
(*       sm_init *)
(*       (MWF: SimMem.SimMem.wf sm_init) *)
(*       ra_blk delta_ra *)
(*       rs_init_src rs_init_tgt *)
(*       (RSREL: (SimMem.SimMem.sim_regset) sm_init rs_init_src rs_init_tgt) *)
(*       (RA: rs_init_tgt RA = Vptr ra_blk delta_ra true) *)
(*       fd_src fd_tgt *)
(*       (FINDFSRC: Genv.find_funct (Genv.globalenv prog) (rs_init_src PC) = Some (Internal fd_src)) *)
(*       (FINDFTGT: Genv.find_funct (Genv.globalenv tprog) (rs_init_tgt PC) = Some (Internal fd_tgt)) *)
(*       (TRANSFF: transf_function fd_src = OK fd_tgt) *)
(*       ls_init vs_init m_init_src *)
(*       (LOADARGSSRC: load_arguments rs_init_src (src_mem sm_init) (Linear.fn_sig fd_src) vs_init m_init_src) *)
(*       (LOCSET: fill_arguments (Locmap.init Vundef) vs_init (Linear.fn_sig fd_src).(loc_arguments) *)
(*                = Some ls_init) *)
(*       sp_src sp_tgt delta_sp *)
(*       (RSPSRC: rs_init_src RSP = Vptr sp_src Ptrofs.zero true) *)
(*       (RSPTGT: rs_init_tgt RSP = Vptr sp_tgt (Ptrofs.repr delta_sp) true) *)
(*       (RSPINJ: inj sm_init sp_src = Some (sp_tgt, delta_sp)) *)
(*   : *)
(*     <<MATCHSTACK: *)
(*     sm_init.(tgt_mem) |= stack_contents tprog return_address_offset (inj sm_init) *)
(*                       [LinearC.dummy_stack (Linear.fn_sig fd_src) ls_init] *)
(*                       [dummy_stack (rs_init_tgt RSP) (Vptr ra_blk delta_ra true)] ** *)
(*                       minjection (inj sm_init) m_init_src ** *)
(*                       globalenv_inject (Genv.globalenv prog) sm_init.(inj)>> *)
(* . *)
(* Proof. *)
(*   u in RSREL. *)
(* Local Opaque sepconj. *)
(* Local Opaque function_bounds. *)
(* Local Opaque make_env. *)
(*   rewrite RSPTGT. u. *)
(*   unfold dummy_frame_contents. *)
(*   rewrite sep_comm. rewrite sep_assoc. *)
(*   inv LOADARGSSRC. rename PERM into PERMSRC. rename VAL into VALSRC. rename DROP into DROPSRC. *)
(*   rewrite RSPSRC in *. clarify. rename sp into sp_src. *)
(*   assert(DELTA: 0 < size_arguments (Linear.fn_sig fd_src) -> *)
(*                 0 <= delta_sp <= Ptrofs.max_unsigned *)
(*                 /\ 4 * size_arguments (Linear.fn_sig fd_src) + delta_sp <= Ptrofs.max_unsigned). *)
(*   { *)
(*     i. *)
(*     Print Mem.inject'. *)
(*     split. *)
(*     - exploit Mem.mi_representable; try apply MWF; eauto; cycle 1. *)
(*       { instantiate (1:= Ptrofs.zero). rewrite Ptrofs.unsigned_zero. xomega. } *)
(*       left. rewrite Ptrofs.unsigned_zero. eapply Mem.perm_cur_max. *)
(*       perm_impl_tac. eapply PERMSRC. split; try xomega. *)
(*     - *)
(*       assert(SZARGBOUND: 4 * size_arguments (Linear.fn_sig fd_src) <= Ptrofs.max_unsigned). *)
(*       { *)
(*         hexploit size_no_overflow; eauto. intro OVERFLOW. *)
(*         clear - OVERFLOW. *)
(*         Local Transparent function_bounds. *)
(*         Local Transparent make_env. *)
(*         u in *. *)
(*         ss. *)
(*         des_ifs. unfold function_bounds in *. cbn in *. *)
(*         admit "Add this in initial_frame of LinearC". *)
(*       } *)
(*       exploit Mem.mi_representable; try apply MWF; eauto; cycle 1. *)
(*       { instantiate (1:= (4 * size_arguments (Linear.fn_sig fd_src)).(Ptrofs.repr)). *)
(*         rewrite Ptrofs.unsigned_repr; cycle 1. *)
(*         { split; try xomega. } *)
(*         i. des. xomega. *)
(*       } *)
(*       right. *)
(*       rewrite Ptrofs.unsigned_repr; cycle 1. *)
(*       { split; try xomega. } *)
(*       eapply Mem.perm_cur_max. perm_impl_tac. *)
(*       eapply PERMSRC. split; try xomega. *)
(*   } *)
(*   assert(MINJ: Mem.inject (inj sm_init) m_init_src (tgt_mem sm_init)). *)
(*   { eapply Mem_set_perm_none_left_inject; eauto. apply MWF. } *)
(*   sep_split. *)
(*   { simpl. eassumption. } *)
(*   { apply disjoint_footprint_drop_empty. *)
(*     { ss. } *)
(*     intros ? delta INJDUP. ii. ss. des. clarify. *)
(*     rename delta into ofstgt. rename b0 into sp_src'. rename delta0 into delta_sp'. *)
(*     destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*     { omega. } *)
(*     special DELTA; ss. clear_tac. *)
(*     rewrite Ptrofs.unsigned_repr in *; try omega. *)
(*     (* exploit Mem_set_perm_none_impl; eauto. clear INJDUP0. intro INJDUP0. *) *)
(*     assert(sp_src' = sp_src). *)
(*     { apply NNPP. intro DISJ. *)
(*       hexploit Mem.mi_no_overlap; try apply MWF. intro OVERLAP. *)
(*       exploit OVERLAP; eauto. *)
(*       { eapply Mem_set_perm_none_impl; eauto. } *)
(*       { eapply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. instantiate (1:= ofstgt - delta_sp). xomega. } *)
(*       { intro TMP. des; eauto. apply TMP; eauto. rewrite ! Z.sub_add. ss. } *)
(*     } *)
(*     clarify. *)
(*     hexploit Mem_set_perm_none_spec; eauto. i; des. *)
(*     eapply INSIDE; eauto. omega. *)
(*   } *)
(*   sep_split. *)
(*   { ss. admit "sim_genv". } *)
(*   { ss. } *)
(*   ss. rewrite Ptrofs.unsigned_repr_eq. *)
(*   assert(POSBOUND: forall p, 0 <= p mod Ptrofs.modulus < Ptrofs.modulus). *)
(*   { i. eapply Z.mod_pos_bound; eauto. generalize Ptrofs.modulus_pos. xomega. } *)
(*   split; eauto. *)
(*   split; eauto. *)
(*   { eapply POSBOUND. } *)
(*   destruct (classic (0 < size_arguments (Linear.fn_sig fd_src))); cycle 1. *)
(*   { esplits; auto. *)
(*     - specialize (POSBOUND delta_sp). xomega. *)
(*     - ii. xomega. *)
(*     - i. generalize (typesize_pos ty). i. xomega. *)
(*   } *)
(*   special DELTA; ss. *)
(*   des. *)
(*   specialize (POSBOUND delta_sp). unfold Ptrofs.max_unsigned in *. *)
(*   erewrite Z.mod_small; try xomega. *)
(*   split; try xomega. *)
(*   Ltac dsplit_r := let name := fresh "DSPLIT" in eapply dependent_split_right; [|intro name]. *)
(*   dsplit_r; try xomega. *)
(*   { rewrite Z.add_comm. *)
(*     change (delta_sp) with (0 + delta_sp). *)
(*     eapply Mem.range_perm_inject; try apply MWF; eauto. *)
(*   } *)
(*   ii; des. *)
(*   { *)
(*     rename H1 into OFS0. rename H2 into OFS1. rename H3 into OFS2. *)
(*     clear - VALSRC LOCSET PERMSRC DSPLIT (* DROPSRC *) RSPSRC RSPTGT RSPINJ OFS0 OFS1 OFS2 MWF. *)
(*     abstr (Linear.fn_sig fd_src) sg. *)
(*     unfold extcall_arguments in *. *)
(*     exploit fill_arguments_spec_slot; eauto. *)
(*     { admit "Add this in initial_frame of LinearC". } *)
(*     i; des. *)
(*     set (loc_arguments sg) as locs in *. *)
(*     assert(LOADTGT: exists v, Mem.load (chunk_of_type ty) (tgt_mem sm_init) sp_tgt (delta_sp + 4 * ofs) = Some v). *)
(*     { eapply Mem.valid_access_load; eauto. *)
(*       hnf. *)
(*       rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*       split; try xomega. *)
(*       - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*       - apply Z.divide_add_r. *)
(*         + rewrite <- align_type_chunk. *)
(*           eapply Mem.mi_align; try apply MWF; eauto. *)
(*           instantiate (1:= Nonempty). *)
(*           instantiate (1:= 0). *)
(*           rewrite Z.add_0_l. *)
(*           ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*           rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*         + apply Z.mul_divide_mono_l. ss. *)
(*     } *)
(*     destruct (classic (In (S Outgoing ofs ty) (regs_of_rpairs locs))). *)
(*     - exploit INSIDE; eauto. i; des. *)
(*       + rewrite Z.add_comm. *)
(*         eapply Mem.load_inject; try apply MWF; eauto. *)
(*       + rewrite UNDEF. *)
(*         esplits; eauto. *)
(*     - exploit OUTSIDE; eauto. intro LOCSRC; des. *)
(*       rewrite LOCSRC. *)
(*       exploit Mem.valid_access_load; eauto. *)
(*       { hnf. instantiate (2:= chunk_of_type ty). *)
(*         rewrite align_type_chunk. rewrite <- PLAYGROUND.typesize_chunk. *)
(*         instantiate (1:= delta_sp + 4 * ofs). *)
(*         instantiate (1:= sp_tgt). *)
(*         instantiate (1:= sm_init.(tgt_mem)). *)
(*         split; try xomega. *)
(*         - ii. perm_impl_tac. eapply DSPLIT. xomega. *)
(*         - apply Z.divide_add_r. *)
(*           + rewrite <- align_type_chunk. *)
(*             eapply Mem.mi_align; try apply MWF; eauto. *)
(*             instantiate (1:= Nonempty). *)
(*             instantiate (1:= 0). *)
(*             rewrite Z.add_0_l. *)
(*             ii. apply Mem.perm_cur_max. perm_impl_tac. eapply PERMSRC. *)
(*             rewrite <- PLAYGROUND.typesize_chunk in *. xomega. *)
(*           + apply Z.mul_divide_mono_l. ss. *)
(*       } *)
(*   } *)
(* Qed. *)

(* Theorem init_match_states *)
(*         (sm_init: SimMem.SimMem.t) fptr_init_src fptr_init_tgt *)
(*         (FPTRREL: Val.inject (inj sm_init) fptr_init_src fptr_init_tgt) *)
(*         rs_init_src rs_init_tgt *)
(*         (RSREL: SimMem.SimMem.sim_regset sm_init rs_init_src rs_init_tgt) *)
(*         (WF: wf' sm_init) *)
(*         (SIMSKENV: ModSemPair.sim_skenv msp sm_init) *)
(*         st_init_src *)
(*         (INITSRC: LinearC.initial_frame prog rs_init_src sm_init.(src_mem) st_init_src) *)
(*   : *)
(*     exists st_init_tgt, *)
(*       <<INITTGT: initial_frame tprog rs_init_tgt (tgt_mem sm_init) st_init_tgt>> *)
(*                                /\ <<MATCH: match_states st_init_src st_init_tgt>> *)
(* . *)
(* Proof. *)
(*   ss. u in *. unfold ModSemPair.sim_skenv in *. ss. clear SIMSKENV. *)
(*   inv INITSRC. *)
(*   exploit (functions_translated_inject); eauto. intro FPTRTGT; des. *)
(*   destruct fd_tgt; ss; unfold bind in *; ss; des_ifs. *)
(*   rename fd into fd_src. rename f into fd_tgt. *)
(*   assert(RSPINJ:= RSREL SP). *)
(*   ss. rewrite RSPPTR in *. inv RSPINJ. *)
(*   rename H1 into RSPPTRTGT. symmetry in RSPPTRTGT. rename H2 into RSPINJ. *)
(*   rename sp into sp_src. rename b2 into sp_tgt. rename m_init into m_init_src. *)
(*   rewrite Ptrofs.add_zero_l in *. *)
(*   esplits; eauto. *)
(*   - econs; eauto. *)
(*   - *)
(*     assert(PTRRA: is_real_ptr (rs_init_tgt RA)). *)
(*     { admit "add to sem (of LinearC)". } *)
(*     u in PTRRA. des_ifs. clear_tac. *)
(*     rename b into ra. rename i into delta_ra. rename delta into delta_sp. clear_tac. *)

(*     econs; eauto. *)
(*     + econs 1; eauto; cycle 1. *)
(*       { rewrite RSPPTRTGT. ss. } *)
(*       i. *)
(*       assert(ACC: loc_argument_acceptable (S Outgoing ofs ty)). *)
(*       { eapply loc_arguments_acceptable_2; eauto. } *)
(*       assert(VALID: slot_valid (dummy_function (Linear.fn_sig fd_src)) Outgoing ofs ty). *)
(*       { destruct ACC. unfold slot_valid, proj_sumbool. *)
(*         rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. } *)
(*       { *)
(*         intros; red. *)
(*           eapply Z.le_trans with (size_arguments _); eauto. *)
(*           apply loc_arguments_bounded; eauto. *)
(*         u. *)
(*         xomega. *)
(*       } *)
(*     + ii. *)
(*       u in RSREL. *)
(*       u in RSREL. u. *)
(*       u. *)
(*       assert((ls_init (R r)) = Vundef \/ (ls_init (R r)) = rs_init_src (preg_of r)). *)
(*       { hexploit fill_arguments_spec_reg; eauto. *)
(*         { apply LOADARG. } *)
(*         i; des. *)
(*         specialize (H r). des. *)
(*         destruct (classic (In (R r) (regs_of_rpairs (loc_arguments (Linear.fn_sig fd_src))))). *)
(*         - special INSIDE; ss. des; eauto. *)
(*         - special OUTSIDE; ss. eauto. } *)
(*       des. *)
(*       * rewrite H. econs; eauto. *)
(*       * rewrite H. eapply RSREL. *)
(*     + ii. des_ifs. *)
(*     + eapply match_stack_contents; eauto. ss. *)
(* Qed. *)

(* Theorem sim *)
(*   : *)
(*     ModSemPair.sim msp *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   { admit "garbage". } *)
(*   ii. *)
(*   ss. *)
(*   split; ss. *)
(* Qed. *)

(* End PRESERVATION. *)
