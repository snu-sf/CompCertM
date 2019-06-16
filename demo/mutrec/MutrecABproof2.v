Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import MutrecAspec MutrecBspec MutrecABspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SimMemId.
Require SoundTop.
Require Import Clightdefs.
Require Import CtypesC.
Require Import BehaviorsC.
Require Import Simulation Sem SemProps LinkingC.

Set Implicit Arguments.

(* Section SIMMODSEM. *)

(* Variable skenv_link: SkEnv.t. *)
(* Variable sm_link: SimMem.t. *)
(* Let md_src: Mod.t := (MutrecAspec.module). *)
(* Let md_tgt: Mod.t := (MutrecBspec.module). *)
(* Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)). *)
(* Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)). *)
(* Hypothesis (WF: SkEnv.wf skenv_link). *)
(* Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) MutrecA.prog) MutrecA.prog.(prog_comp_env). *)
(* Let tge := skenv_link.(SkEnv.revive) MutrecB.prog. *)
(* Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link. *)

(* End SIMMODSEM. *)

Lemma link_sk_same
      ctx
  :
    link_sk (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)])
    = link_sk (ctx ++ [module])
.
Proof.
  admit "see UpperBound_A extra".
Qed.

Lemma wf_module_Aspec: Sk.wf MutrecAspec.module.
Proof.
  admit "ez".
Qed.

Lemma wf_module_Bspec: Sk.wf MutrecBspec.module.
Proof.
  admit "ez".
Qed.

Definition is_focus (x: Mod.t) := x = MutrecAspec.module \/ x = MutrecBspec.module.

Section LXSIM.

  Variable ctx: Syntax.program.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk (ctx ++ [module]) = Some sk_link).
  Let LINKTGT: link_sk (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)]) = Some sk_link.
  Proof. rewrite link_sk_same. ss. Qed.

  Lemma genv_sim
        fptr if_sig
    :
      (<<FINDF: Genv.find_funct (SkEnv.project skenv_link MutrecABspec.sk_link) fptr =
                Some (AST.Internal if_sig)>>)
      <->
      (<<FINDF: exists md, (<<FOCUS: is_focus md>>) /\
                           (<<FINDF: Genv.find_funct (ModSem.skenv (flip Mod.modsem skenv_link md)) fptr =
                                     Some (AST.Internal if_sig)>>)>>)
  .
  Proof.
    admit "ez".
  Qed.

  Lemma find_symbol_find_funct_ptr_A
        blk
        (SYMB: Genv.find_symbol skenv_link f_id = Some blk)
    :
      Genv.find_funct_ptr (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog)) blk =
      Some (AST.Internal (mksignature [AST.Tint] (Some AST.Tint) cc_default))
  .
  Proof.
    admit "ez".
  Qed.

  Lemma find_symbol_find_funct_ptr_B
        blk
        (SYMB: Genv.find_symbol skenv_link g_id = Some blk)
    :
      Genv.find_funct_ptr (SkEnv.project skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog)) blk =
      Some (AST.Internal (mksignature [AST.Tint] (Some AST.Tint) cc_default))
  .
  Proof.
    admit "ez".
  Qed.

  Inductive match_focus: mem -> int -> int -> list Frame.t -> Prop :=
  | match_focus_nil
      cur max m
      (OVER: cur.(Int.intval) > max.(Int.intval))
    :
      match_focus m cur max []
  | match_focus_cons_A
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
    :
      match_focus m cur max ((Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
    :
      match_focus m cur max ((Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m)) :: tl_tgt)
  .

  Lemma match_focus_over_nil
        m max hds_tgt
        (FOCUS: match_focus m (Int.add max Int.one) max hds_tgt)
    :
      hds_tgt = nil
  .
  Proof.
    admit "not true now. -- we should know it does not overflow, then it is trivial".
  Qed.

  Inductive match_stacks (fromcall: bool) (idx: Z): list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_ctx
      ctx_stk
      (IDX: idx = 0%Z)
    :
      match_stacks fromcall idx ctx_stk ctx_stk
  (* | match_stacks_focus_top_call *)
  (*     ctx_stk *)
  (*     cur max m hd_src hds_tgt *)
  (*     (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate max m)) *)
  (*     (LE: (cur <= max.(Int.intval))%Z) *)
  (*     (TGT: match_focus m cur max.(Int.intval) hds_tgt) *)
  (*   : *)
  (*     match_stacks cur (hd_src :: ctx_stk) (hds_tgt ++ ctx_stk) *)
  | match_stacks_focus_top_call
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate max m))
      hd_tgt
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (* (IDX: idx = (max.(Int.intval) + cur.(Int.intval)) + 1) *)
      (IDX: idx = cur.(Int.intval))
    :
      match_stacks fromcall idx (hd_src :: ctx_stk) (hd_tgt :: hds_tgt ++ ctx_stk)
  | match_stacks_focus_top_return
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Returnstate (sum max) m))
      hd_tgt
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Returnstate (sum cur) m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Returnstate (sum cur) m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = max.(Int.intval) - cur.(Int.intval))
    :
      match_stacks fromcall idx (hd_src :: ctx_stk) (hd_tgt :: hds_tgt ++ ctx_stk)
  .

  Inductive match_states (i: Z): Sem.state -> Sem.state -> Prop :=
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks true i frs_src frs_tgt)
      (* blk *)
      (* (FPTR: args.(Args.fptr) = Vptr blk Ptrofs.zero) *)
      (* (NFOCUS: ~(Genv.find_symbol skenv_link f_id = Some blk \/ Genv.find_symbol skenv_link g_id = Some blk) -> frs_src = frs_tgt) *)
      (* (FOCUS: (Genv.find_symbol skenv_link f_id = Some blk \/ Genv.find_symbol skenv_link g_id = Some blk) -> match_stacks i frs_src frs_tgt) *)
    :
      match_states i (Callstate args frs_src) (Callstate args frs_tgt)
  | match_states_normal
      frs_src frs_tgt
      (STK: match_stacks false i frs_src frs_tgt)
    :
      match_states i (State frs_src) (State frs_tgt)
  .

  Lemma int_zero_intval: Int.intval Int.zero = 0%Z.
  Proof. unfold Int.intval. ss. Qed.

  Lemma int_sub_add: forall cur x, (Int.add (Int.sub cur x) x) = cur.
  Proof.
    i.
    rewrite Int.sub_add_opp. rewrite Int.add_assoc.
    rewrite Int.add_commut with (y := x).
    rewrite Int.add_neg_zero. rewrite Int.add_zero. ss.
  Qed.

  Lemma match_states_xsim
        i st_src0 st_tgt0
        (MATCH: match_states i st_src0 st_tgt0)
    :
      xsim (sem (ctx ++ [module])) (sem (ctx ++ [MutrecAspec.module; MutrecBspec.module]))
           (Zwf.Zwf 0) i st_src0 st_tgt0
  .
  Proof.
    revert_until LINKTGT. pcofix CIH. i.
    inv MATCH.
    - (* call *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; et.
        { i; ss. des_ifs. inv FINALTGT. }
        i.
        admit "ctx".
      + (* focus-call *)
        pfold. left; right. econs; et.
        econs; et; cycle 1.
        { i; ss. inv FINALSRC. }
        i.
        admit "todo".
      + (* focus-return *)
        ss.
    - (* normal *)
      inv STK.
      + (* ctx *)
        admit "ctx".
      + (* focus-call *)
        pfold. left; right. econs; et.
        (* econs; et; cycle 1. *)
        (* { i; ss. inv FINALSRC. ss. inv FINAL. } *)
        (* i. ss. des_ifs. *)
        (* assert(tr = E0). *)
        (* { inv STEPSRC; clarify. ss. inv STEP. ss. } *)
        (* clarify. *)
        destruct (classic (cur = Int.zero)).
        * clarify.
          unsguard TGT. des; clarify.
          { ss.
            rewrite int_zero_intval in *.
            econs 1; et; cycle 1.
            { i; ss. inv FINALSRC. ss. inv FINAL. }
            i. inv STEPSRC; ss; cycle 1.
            { inv FINAL. }
            inv STEP.
            esplits; et.
            - left. esplits; eauto.
              + apply plus_one. econs; eauto.
                { admit "ez - determinate". }
                ss. des_ifs. rpapply step_internal. ss.
              + { admit "ez - receptive". }
            - right. eapply CIH. econs 2; eauto. econs 3; eauto.
              + ss.
              + unfold Frame.update_st. ss. unfold __GUARD__. rewrite sum_recurse. des_ifs; et.
              + rewrite int_zero_intval. lia.
          }
          { ss.
            rewrite int_zero_intval in *.
            econs 1; et; cycle 1.
            { i; ss. inv FINALSRC. ss. inv FINAL. }
            i. inv STEPSRC; ss; cycle 1.
            { inv FINAL. }
            inv STEP.
            esplits; et.
            - left. esplits; eauto.
              + apply plus_one. econs; eauto.
                { admit "ez - determinate". }
                ss. des_ifs. rpapply step_internal. ss.
              + { admit "ez - receptive". }
            - right. eapply CIH. econs 2; eauto. econs 3; eauto.
              + ss.
              + unfold Frame.update_st. ss. unfold __GUARD__. rewrite sum_recurse. des_ifs; et.
              + rewrite int_zero_intval. lia.
          }
        * unsguard TGT. des; clarify.
          {
            econs 2; et.
            - esplits; et.
              + eapply plus_two with (t1 := E0) (t2 := E0); ss.
                * econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs. econs; eauto. ss. econs; eauto.
                  { admit "ez - genv g_id some". }
                  ii. destruct cur; ss. clarify. apply H.
                  Local Transparent Int.repr.
                  eapply eta.
                  Local Opaque Int.repr.
                  ss.
                * econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs. econs; eauto.
                  { ss. instantiate (1:= MutrecBspec.modsem skenv_link tt). econs; ss; eauto.
                    - right. unfold load_modsems. rewrite in_map_iff. esplits; et; cycle 1.
                      + rewrite in_app_iff. right. ss. right; et.
                      + ss.
                    - des_ifs. instantiate (2 := g_id). admit "ez - genv g_id some".
                  }
                  ss. econs; ss; eauto.
                  admit "ez - genv g_id some".
              + instantiate (1:= Int.intval cur - 1). rr. esplits; try lia. admit "by definition".
            - right. eapply CIH. econs; eauto.
              assert(ARITH: Int.intval (Int.sub cur (Int.repr 1)) = Int.intval cur - 1).
              { admit "ez - arithmetic. it does not underflow". }
              replace
                ({| Frame.ms := MutrecBspec.modsem skenv_link tt; Frame.st := MutrecBspec.Callstate (Int.sub cur (Int.repr 1)) m |}
                   :: {| Frame.ms := MutrecAspec.modsem skenv_link tt; Frame.st := MutrecAspec.Callstate cur m |} :: hds_tgt ++ ctx_stk) with
                 ({| Frame.ms := MutrecBspec.modsem skenv_link tt; Frame.st := MutrecBspec.Callstate (Int.sub cur (Int.repr 1)) m |}
                   :: ({| Frame.ms := MutrecAspec.modsem skenv_link tt; Frame.st := MutrecAspec.Callstate cur m |} :: hds_tgt) ++ ctx_stk) by ss.
              econs 2.
              + refl.
              + unfold __GUARD__. ss. eauto.
              + rewrite ARITH. lia.
              + rewrite int_sub_add.
                econs; eauto.
                (* left. rpapply FOCUS. f_equal. rewrite Int.sub_add_opp. rewrite Int.add_assoc. *)
                (* rewrite Int.add_commut with (y := Int.one). *)
                (* rewrite Int.add_neg_zero. rewrite Int.add_zero. ss. *)
                (* admit "". *)
                (* admit "". *)
              + rewrite ARITH. lia.
          }
          {
            econs 2; et.
            - esplits; et.
              + eapply plus_two with (t1 := E0) (t2 := E0); ss.
                * econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs. econs; eauto. ss. econs; eauto.
                  { admit "ez - genv f_id some". }
                  ii. destruct cur; ss. clarify. apply H.
                  Local Transparent Int.repr.
                  eapply eta.
                  Local Opaque Int.repr.
                  ss.
                * econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs. econs; eauto.
                  { ss. instantiate (1:= MutrecAspec.modsem skenv_link tt). econs; ss; eauto.
                    - right. unfold load_modsems. rewrite in_map_iff. esplits; et; cycle 1.
                      + rewrite in_app_iff. right. ss. left; et.
                      + ss.
                    - des_ifs. instantiate (2 := f_id). admit "ez - genv f_id some".
                  }
                  ss. econs; ss; eauto.
                  admit "ez - genv f_id some".
              + instantiate (1:= Int.intval cur - 1). split; try lia. admit "by definition".
            - right. eapply CIH. econs; eauto.
              assert(ARITH: Int.intval (Int.sub cur (Int.repr 1)) = Int.intval cur - 1).
              { admit "ez - arithmetic. it does not underflow". }
              replace
                ({| Frame.ms := MutrecAspec.modsem skenv_link tt; Frame.st := MutrecAspec.Callstate (Int.sub cur (Int.repr 1)) m |}
                   :: {| Frame.ms := MutrecBspec.modsem skenv_link tt; Frame.st := MutrecBspec.Callstate cur m |} :: hds_tgt ++ ctx_stk) with
                  ({| Frame.ms := MutrecAspec.modsem skenv_link tt; Frame.st := MutrecAspec.Callstate (Int.sub cur (Int.repr 1)) m |}
                     :: ({| Frame.ms := MutrecBspec.modsem skenv_link tt; Frame.st := MutrecBspec.Callstate cur m |} :: hds_tgt) ++ ctx_stk) by ss.
              econs 2.
              + refl.
              + unfold __GUARD__. ss. eauto.
              + rewrite ARITH. lia.
              + rewrite int_sub_add.
                econs; eauto.
                (* left. rpapply FOCUS. f_equal. rewrite Int.sub_add_opp. rewrite Int.add_assoc. *)
                (* rewrite Int.add_commut with (y := Int.one). *)
                (* rewrite Int.add_neg_zero. rewrite Int.add_zero. ss. *)
                (* admit "". *)
                (* admit "". *)
              + rewrite ARITH. lia.
          }
      + (* focus - return *)
        destruct (classic (cur = max)).
        * clarify. exploit match_focus_over_nil; eauto. i; clarify.
          pfold. right. econs; eauto.
          { i. ss. inv FINALTGT.
            unsguard TGT. des; clarify; ss.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto.
          }
          i. econs; eauto; cycle 1.
          { i. specialize (SAFESRC _ (star_refl _ _ _ _)). desH SAFESRC; ss.
            - inv SAFESRC; ss. inv FINAL. ss. clarify. left.
              unsguard TGT. des; clarify.
              { esplits; eauto. econs; ss; eauto. }
              { esplits; eauto. econs; ss; eauto. }
            - des_ifs. right. inv SAFESRC; ss.
              { inv STEP. }
              inv FINAL. esplits; eauto. econs 4; eauto.
              unsguard TGT. des; clarify.
          }
          i. ss. des_ifs. inv STEPTGT; ss.
          { unsguard TGT. des; clarify; inv AT. }
          { unsguard TGT. des; clarify; inv STEP. }
          esplits; eauto.
          -- left. apply plus_one. econs 4; eauto. ss. unsguard TGT. des; clarify; ss; inv FINAL; econs; eauto.
          -- right. eapply CIH. econs; eauto. econs; eauto.
        * pfold. left. right. econs; eauto.
          (* TODO: ---------> we can remove redundancy. current match_states include A-A-B-A-B-A... or B-B-A-B-A-B ... *)
          unsguard TGT. des; clarify.
          { inv FOCUS; ss.
            { exfalso. admit "ez - arithmetic". }
            {
              econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + admit "ez - arithmetic".
                + ss.
                + admit "ez - arithmetic. no overflow".
            }
            {
              econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + admit "ez - arithmetic".
                + ss.
                + admit "ez - arithmetic. no overflow".
            }
          }
          { inv FOCUS; ss.
            { exfalso. admit "ez - arithmetic". }
            {
              econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + admit "ez - arithmetic".
                + ss.
                + admit "ez - arithmetic. no overflow".
            }
            {
              econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { admit "ez - determinate". }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss. econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + admit "ez - arithmetic".
                + ss.
                + admit "ez - arithmetic. no overflow".
            }
          }
  Unshelve.
    all: admit "abc".
  Qed.

End LXSIM.
  

Theorem mutrecABcorrect
        ctx
  :
    (<<REFINE: improves (Sem.sem (ctx ++ [(MutrecABspec.module)]))
                        (Sem.sem (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)]))
                        >>)
.
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  econs; eauto.
  econs; swap 2 3.
  { instantiate (1:= Zwf.Zwf 0%Z). eapply Zwf.Zwf_well_founded. }
  { i; des. ss. inv SAFESRC. rewrite INITSK.
    ss. rewrite link_sk_same. des_ifs.
  }
  econs; eauto.
  i. ss. inv INITSRC.
  esplits; eauto.
  { econs; ss; eauto.
    - econs; eauto.
      + rewrite link_sk_same. ss.
      + ii; ss. rewrite in_app_iff in *. des; ss.
        { eapply WF; et. rewrite in_app_iff. et. }
        des; ss; clarify.
        * eapply wf_module_Aspec; et.
        * eapply wf_module_Bspec; et.
    - i; ss. inv INIT0. inv INIT1. clarify.
  }
  eapply match_states_xsim; eauto.
  econs; eauto. econs; eauto.
Qed.
