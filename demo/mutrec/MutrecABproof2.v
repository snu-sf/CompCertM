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
  (* | match_focus_nil *)
  (*     cur max m *)
  (*     (OVER: cur = Int.add max Int.one) *)
  (*   : *)
  (*     match_focus m cur max [] *)
  | match_focus_cons_A
      cur max m tl_tgt
      (REC: max <> cur -> match_focus m (Int.add cur Int.one) max tl_tgt)
      (END: max = cur -> tl_tgt = [(Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m))])
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
    :
      match_focus m cur max ((Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m tl_tgt
      (REC: max <> cur -> match_focus m (Int.add cur Int.one) max tl_tgt)
      (END: max = cur -> tl_tgt = [(Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m))])
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
    :
      match_focus m cur max ((Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m)) :: tl_tgt)
  .

  (* Lemma match_focus_over_implies_nil *)
  (*       m max hds_tgt *)
  (*       (MATCH :match_focus m (Int.add max Int.one) max hds_tgt) *)
  (*   : *)
  (*     hds_tgt = nil *)
  (* . *)
  (* Proof. *)
  (*   inv MATCH; ss. *)
  (*   -  *)
  (*   clear - MATCH. *)
  (*   ginduction MATCH; ii; ss; clarify. *)
  (*   - inv MATCH. *)
  (* Qed. *)

  Lemma match_focus_le
        m cur max tls
        (MATCH: match_focus m cur max tls)
    :
      cur.(Int.intval) <= max.(Int.intval)
  .
  Proof.
    inv MATCH; ss.
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
      (* (LE: (cur.(Int.intval) <= max.(Int.intval))%Z) *)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (IDX: idx = (max.(Int.intval) + cur.(Int.intval)) + 1)
    :
      match_stacks fromcall idx (hd_src :: ctx_stk) (hd_tgt :: hds_tgt ++ ctx_stk)
  | match_stacks_focus_top_return
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate max m))
      hd_tgt
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Returnstate (sum cur) m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Returnstate (sum cur) m))))
      (* (LE: (cur.(Int.intval) <= max.(Int.intval))%Z) *)
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

  Lemma int_add_sub: forall cur x, (Int.add (Int.sub cur x) x) = cur.
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
           Z.lt i st_src0 st_tgt0
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
      + (* foccs-call *)
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
            econs 2; et.
            - esplits; et.
              + apply plus_one. econs; eauto.
                { admit "ez - determinate". }
                ss. des_ifs. rpapply step_internal. ss.
              + instantiate (1:= Int.intval max%Z). lia.
            - right. eapply CIH. econs 2; eauto. econs 3; eauto.
              + unfold Frame.update_st. ss. unfold __GUARD__. rewrite sum_recurse. des_ifs; et.
              + rewrite int_zero_intval. lia.
          }
          { ss.
            rewrite int_zero_intval in *.
            econs 2; et.
            - esplits; et.
              + apply plus_one. econs; eauto.
                { admit "ez - determinate". }
                ss. des_ifs. rpapply step_internal. ss.
              + instantiate (1:= Int.intval max%Z). lia.
            - right. eapply CIH. econs 2; eauto. econs 3; eauto.
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
              + instantiate (1:= Int.intval max + Int.intval cur). lia.
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
              + rewrite int_add_sub. dup FOCUS. apply match_focus_le in FOCUS. econs; eauto; ss.
                * ii. clarify.
                  admit "ez - arithmetic. it does not overflow".
                * admit "ez - arithmetic. it does not overflow".
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
              + instantiate (1:= Int.intval max + Int.intval cur). lia.
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
              + rewrite int_add_sub. dup FOCUS. apply match_focus_le in FOCUS. econs; eauto; ss.
                * ii. clarify.
                  admit "ez - arithmetic. it does not overflow".
                * admit "ez - arithmetic. it does not overflow".
              + rewrite ARITH. lia.
          }
      + (* focus - return *)
        destruct (classic (cur = max)).
        {
          clarify.
          dup FOCUS. apply match_focus_le in FOCUS.
          exfalso.
          admit "ez - arithmetic. it does not overflow".
        }
        inv FOCUS.
        * pfold.
        admit "".
  Unshelve.
    all: admit "abc".
  Qed.

    - (* call *)
      pfold. right. econs; et.
      { i; ss. des_ifs. inv FINALTGT. }
      i.
      econs; et; cycle 1.
      + i. specialize (SAFESRC _ (star_refl _ _ _ _)). desH SAFESRC; ss.
        * left. inv SAFESRC.
        * right. des_ifs. inv SAFESRC. inv MSFIND. ss. des; clarify.
          { esplits; et. econs; et. econs; et. ss. et. }
          folder.
          unfold load_modsems in *. rewrite in_map_iff in *. des_safe. rewrite in_app_iff in *. ss; des; clarify.
          { esplits; et. econs; et. econs; et. ss. right. unfold load_modsems in *. rewrite in_map_iff.
            esplits; et. rewrite in_app_iff. et. }
          { apply genv_sim in INTERNAL. des. ss. rr in FOCUS0. inv INIT.
            unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
            des; clarify.
            - esplits; et. econs; et.
              + econs; et.
                * ss. right. unfold load_modsems in *. rewrite in_map_iff. esplits; et. 
                  rewrite in_app_iff. right. left. ss; et.
                * unfold Genv.find_funct, Genv.find_funct_ptr in *. rewrite Heq1. ss. des_ifs.
              + econs; ss; et.
                admit "ez - genv".
            - esplits; et. econs; et.
              + econs; et.
                * ss. right. unfold load_modsems in *. rewrite in_map_iff. esplits; et. 
                  rewrite in_app_iff. right. right. ss; et.
                * unfold Genv.find_funct, Genv.find_funct_ptr in *. rewrite Heq1. ss. des_ifs.
              + econs; ss; et.
                admit "ez - genv".
          }
      + i. ss. des_ifs. inv STEPTGT. inv MSFIND. ss.
        unfold load_modsems in *.
        des; clarify.
        { exploit NFOCUS; et.
          { admit "this should hold". }
          i. clarify.
          esplits; et.
          - left. apply plus_one. econs; et. econs; et. ss. et.
          - right. eapply CIH. econs; et. econs; et.
        }
        rewrite in_map_iff in *. des. clarify. rewrite in_app_iff in *. des; clarify.
        { exploit NFOCUS; et.
          { admit "this should hold". }
          i. clarify.
          esplits; et.
          - left. apply plus_one. econs; et. econs; et. ss. right.
            unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. et.
          - right. eapply CIH. econs; et. econs; et.
        }
        { ss.
          exploit FOCUS; et.
          { admit "this should hold". }
          intro STK. inv STK; ss.
          des; clarify; ss; inv INIT.
          - esplits; et.
            + left. apply plus_one. econs.
              * instantiate (1:= modsem skenv_link tt).
                econs; et.
                -- ss. right. unfold load_modsems. rewrite in_map_iff. esplits; cycle 1.
                   { rewrite in_app_iff. right; ss; et. }
                   ss.
                -- instantiate (1:= if_sig). apply genv_sim. exists (MutrecAspec.module). esplits; et; rr; et.
              * econs; et.
                -- instantiate (1:= if_sig). apply genv_sim. exists (MutrecAspec.module). esplits; et; rr; et.
            + right. eapply CIH. econs; et.
              rewrite cons_app with (xhd := {|
                Frame.ms := flip Mod.modsem (Sk.load_skenv sk_link) MutrecAspec.module;
                Frame.st := MutrecAspec.Callstate i0 (Args.m args) |}).
              econs 2; et.
              * refl.
              * econs; et.
          - esplits; et.
            + left. apply plus_one. econs.
              * instantiate (1:= modsem skenv_link tt).
                econs; et.
                -- ss. right. unfold load_modsems. rewrite in_map_iff. esplits; cycle 1.
                   { rewrite in_app_iff. right; ss; et. }
                   ss.
                -- instantiate (1:= if_sig). apply genv_sim. exists (MutrecBspec.module). esplits; et; rr; et.
              * econs; et.
                -- instantiate (1:= if_sig). apply genv_sim. exists (MutrecBspec.module). esplits; et; rr; et.
            + right. eapply CIH. econs; et.
              rewrite cons_app with (xhd := {|
                Frame.ms := flip Mod.modsem (Sk.load_skenv sk_link) MutrecBspec.module;
                Frame.st := MutrecBspec.Callstate i0 (Args.m args) |}).
              econs; et.
              * refl.
              * econs; et.
        }
    - (* call from focus *)
      pfold. right.
      econs; et.
      { ss. i. inv FINALTGT; ss. }
      i.
      econs; et; cycle 1.
      { i; ss. specialize (SAFESRC _ (star_refl _ _ _ _)). desH SAFESRC; ss.
        - left. inv SAFESRC.
        - right. des_ifs. inv SAFESRC.
          inv MSFIND. ss. desH MODSEM.
          { esplits; et. econs; et. econs; et. ss; et. }
          unfold load_modsems in *. rewrite in_map_iff in *. des_safe. clarify.
          rewrite in_app_iff in *. desH MODSEM0; clarify.
          { esplits; et. econs; et. econs; et. ss; et. right.
            unfold load_modsems in *. rewrite in_map_iff in *. esplits; et. rewrite in_app_iff. des; et.
          }
          ss. des_safe; clarify.
          exploit genv_sim; et. i; des_safe. exploit FINDF; et. i; des_safe. rr in FOCUS0.
          desH FOCUS0; clarify; inv INIT; esplits; et.
          + econs.
            * instantiate (1:= MutrecAspec.modsem skenv_link tt). econs; et. ss. right.
              unfold load_modsems, flip in *; rewrite in_map_iff in *; folder; esplits; et; cycle 1.
              { rewrite in_app_iff; ss. right. left. et. }
              ss.
            * econs; ss; et.
              admit "ez - revive// TODO: make lemma".
          + econs.
            * instantiate (1:= MutrecBspec.modsem skenv_link tt). econs; et. ss. right.
              unfold load_modsems, flip in *; rewrite in_map_iff in *; folder; esplits; et; cycle 1.
              { rewrite in_app_iff; ss. right. right. et. }
              ss.
            * econs; ss; et.
              admit "ez - revive// TODO: make lemma".
      }
      i. ss. des_ifs. inv STEPTGT. folder.
      assert(MSFIND0:
               Ge.find_fptr_owner
               (load_genv (ctx ++ [MutrecAspec.module; MutrecBspec.module]) skenv_link)
               (Args.fptr args) (MutrecAspec.modsem skenv_link tt)
             \/
             Ge.find_fptr_owner
               (load_genv (ctx ++ [MutrecAspec.module; MutrecBspec.module]) skenv_link)
               (Args.fptr args) (MutrecBspec.modsem skenv_link tt)
            ).
      { des.
        - left. econs; ss; et.
          + right. unfold load_modsems. rewrite in_map_iff. esplits; ss; et; cycle 1.
            { rewrite in_app_iff. right; left; ss; et. }
            ss.
          + rewrite FPTR. ss. des_ifs. eapply find_symbol_find_funct_ptr_A; et.
        - right. econs; ss; et.
          + right. unfold load_modsems. rewrite in_map_iff. esplits; ss; et; cycle 1.
            { rewrite in_app_iff. right; right; ss; et. }
            ss.
          + rewrite FPTR. ss. des_ifs. eapply find_symbol_find_funct_ptr_B; et.
      }
      inv MSFIND. ss. desH MODSEM; clarify.
      { (* system *)
        exfalso. ss. admit "exploit system_disjoint; et".
        (* unfold System.skenv in *. *)
        (* inv INIT. esplits; eauto. *)
        (* + left. apply plus_one. esplits; eauto; cycle 1. *)
        (*   econs; et. *)
        (*   { econs; ss; et. } *)
        (*   econs; et. *)
        (* + right. eapply CIH; et. econs; et. econs 3; et. *)
      }
      unfold load_modsems in *. rewrite in_map_iff in *. desH MODSEM. clarify.
      clarify.
      rewrite in_app_iff in *. desH MODSEM0; clarify.
      { (* ctx *)
        exfalso. ss. admit "somehow".
        (* esplits; eauto. *)
        (* + left. apply plus_one. econs; et. econs; et. ss. right. *)
        (*   unfold load_modsems in *. rewrite in_map_iff. esplits; et. *)
        (*   rewrite in_app_iff. ss. et. *)
        (* + right. eapply CIH; et. econs; et. *)
        (*   rewrite cons_app with (xtl := frs_tgt). *)
        (*   econs 3; et. *)
      }
      { (* focus *)
        folder.
        inv STK.
        assert(exists i, <<ARGS: Args.vs args = [Vint i]>>).
        { ss. des; clarify; inv INIT; et. }
        des.
        esplits; et.
        + left. apply plus_one. econs.
          { instantiate (1:= modsem skenv_link tt). econs; ss; et.
            - right.
              unfold load_modsems in *. rewrite in_map_iff. unfold flip. esplits; et; cycle 1.
              { rewrite in_app_iff. ss. et. }
              ss.
            - instantiate (1:= if_sig).
              eapply genv_sim; et. esplits; et. rr; des; ss; et.
          }
          econs; et.
          eapply genv_sim; et. esplits; et. rr; des; ss; et. des; clarify; et.
        + right. eapply CIH. instantiate (1:= i.(Int.intval)). econs; et.
          rewrite cons_app with (xhd := {| Frame.ms := flip Mod.modsem skenv_link x; Frame.st := st_init |}).
          econs 3.
          { et. }
          { refl. }
          { ss. des; clarify; ss; inv INIT. econs. et. }
          destruct args; ss. clarify.
          des; ss; clarify.
          * inv INIT; ss; clarify. econs; et. refl.
          * inv INIT; ss; clarify. econs; et. refl.
    - (* Sem.State *)
      inv STK.
      + pfold. left. right. econs; et.
        econs; et; cycle 1.
        { ss. i. inv FINALSRC; ss. }
        i. ss. des_ifs. inv STEPSRC.
      + pfold. right. econs; et.
        { ss. i. inv FINALTGT; ss. inv TAIL; ss; cycle 1.
          { destruct hds_tgt, tail_tgt; ss. inv TGT; ss. }
          esplits; et.
          { apply star_refl. }
          econs; ss; et.
        }
        i.
        econs; et; cycle 1.
        { ss. i. specialize (SAFESRC _ (star_refl _ _ _ _)). des.
          - left. inv SAFESRC. inv TAIL. esplits; et. econs; et.
          - right. des_ifs. inv SAFESRC; inv TAIL; try (by esplits; et; econs; et).
        }
        i. ss. des_ifs. inv STEPTGT; ss.
        * esplits; et.
          { left. apply plus_one. econs; et. }
          right. eapply CIH; et. econs; et. econs; et.
        * esplits; et.
          { left. apply plus_one. econs; et. }
          right. eapply CIH; et. econs; et. econs; et.
        * inv TAIL.
          -- esplits; et.
             { left. apply plus_one. econs 4; et. }
             right. eapply CIH; et. econs; et. econs; et.
          -- esplits; et.
             { left. apply plus_one. econs 4; et. }
             right. eapply CIH; et. econs; et. econs; et.
          econs; et.
      inv MSFIND. ss. des; clarify.
      { (* system *)
        inv INIT. esplits; eauto.
        + left. esplits; eauto; cycle 1.
          { admit "ez - semprops receptive". }
          apply plus_one.
          econs; et.
          { admit "ez - semprops determinate". }
          ss. des_ifs. econs; et.
          { econs; ss; et. }
          econs; et.
        + right. eapply CIH; et. econs; et. econs; et.
      }
      unfold load_modsems in *.
      rewrite in_map_iff in *. des. clarify. rewrite in_app_iff in *. des; clarify.
      { (* ctx *)
        esplits; eauto.
        + left. esplits; eauto; cycle 1.
          { admit "ez - semprops receptive". }
          apply plus_one.
          econs; et.
          { admit "ez - semprops determinate". }
          ss. des_ifs. econs; et.
          { econs; ss; et. }
          econs; et.
        + right. eapply CIH; et. econs; et. econs; et.
        +
      }
    -
    admit "".
  Qed.

End LXSIM.
  

Theorem mutrecABcorrect
        ctx
  :
    (* (<<REFINE: improves (Sem.sem ([(MutrecABspec.module)] ++ ctx)) *)
    (*                     (Sem.sem ([(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx)) *)
    (*                     >>) *)
    (<<REFINE: improves (Sem.sem (ctx ++ [(MutrecABspec.module)]))
                        (Sem.sem (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)]))
                        >>)
.
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  econs; eauto.
  econs; swap 2 3.
  { apply lt_wf. }
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
  eapply match_states_xsim; et.
  econs; et. econs; et.
Qed.


(* Inductive match_states_internal: MutrecABspec.state -> Clight.state -> Prop := *)
(* | match_callstate_nonzero *)
(*     i m_src m_tgt *)
(*     fptr *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_returnstate *)
(*     i m_src m_tgt *)
(*   : *)
(*     match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt) *)
(* . *)

(* Inductive match_states (sm_init: SimMem.t) *)
(*           (idx: nat) (st_src0: MutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop := *)
(* | match_states_intro *)
(*     (MATCHST: match_states_internal st_src0 st_tgt0) *)
(*     (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src)) *)
(*     (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt)) *)
(*     (MWF: SimMem.wf sm0) *)
(*     (IDX: (idx > 3)%nat) *)
(* . *)

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ => eq) eq tt) ge tge.
Proof.
  subst_locals. ss. ii.
  eapply SimSymbId.sim_skenv_revive; eauto.
  admit "ez - reflexivity".
Qed.

Lemma g_blk_exists
  :
    exists g_blk,
      (<<FINDG: Genv.find_symbol
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_id = Some g_blk>>)
      /\
      (<<FINDG: Genv.find_funct_ptr
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_blk = None>>)
      /\
      (<<FINDG: exists skd, Genv.find_funct_ptr skenv_link g_blk = Some skd /\
                            signature_of_type (Tcons tint Tnil) tint cc_default = SkEnv.get_sig skd>>)
.
Proof.
  exploit (prog_defmap_norepet prog g_id); eauto.
  { unfold prog_defs_names. ss. repeat (econs; eauto). ii; ss; des; ss. }
  { ss. eauto. }
  intro T; des.
  exploit SkEnv.project_impl_spec; eauto. intro PROJ.
  assert(PREC: SkEnv.genv_precise
                 (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                 prog).
  { eapply CSkEnv.project_revive_precise; ss; et. }
  inv PREC.
  exploit (P2GE g_id); eauto. i; des. des_ifs.
  rename b into g_blk.
  eexists. splits; et.
  { unfold Genv.find_funct_ptr. des_ifs. }
  (* exploit (@SkEnv.project_revive_precise _ _ skenv_link); eauto. *)
  { inv INCLSRC.
    exploit (CSk.of_program_prog_defmap prog signature_of_function); et. rewrite T. intro S.

    remember ((prog_defmap (CSk.of_program signature_of_function prog)) ! g_id) as U in *.
    destruct U eqn:V; try (by ss). inv S. inv H1.

    exploit DEFS; eauto. i; des.
    assert(blk = g_blk).
    { inv PROJ. exploit SYMBKEEP; et.
      - instantiate (1:= g_id). unfold defs. des_sumbool. ss. et.
      - i. rewrite SYMB0 in *. clear - SYMB H. unfold SkEnv.revive in *. rewrite Genv_map_defs_symb in *. ss.
        rewrite SYMB in *. des. clarify.
    }
    clarify. inv MATCH.
    esplits; eauto.
    - unfold Genv.find_funct_ptr. rewrite DEF0. et.
    - ss. des_ifs. clear - H1. inv H1; ss.
  }
Qed.

Lemma match_states_lxsim
      sm_init idx st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun st => exists su m_init, SoundTop.sound_state su m_init st)
                  sm_init (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until tge.
  pcofix CIH.
  i.
  pfold.
  generalize g_blk_exists; et. i; des.
  inv MATCH. ss. inv MATCHST; ss; clarify.
  - (* call *)
    destruct (classic (i = Int.zero)).
    + (* zero *)
      clarify.
      econs 1. i; des.
      econs 1; cycle 2.
      { admit "ez - spec is receptive". }
      { split; ii; rr in H; inv H; inv H0; ss. }
      i. ss. inv STEPSRC.
      esplits; eauto.
      * left.
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
          - ss.
        }

        apply star_refl.
      (* * refl. *)
      * right. eapply CIH. econs; ss; eauto. econs; eauto.
    + (* nonzero *)
      econs.
      i; des.
      econs 2; eauto.
      * esplits; cycle 1.
        { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). lia. }

        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
        }
        
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss. rewrite Int.eq_false; ss.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto; swap 1 2.
          - econs.
            + eapply eval_Evar_global; ss. et.
            + econs 2; et.
          - unfold Cop.classify_fun. ss.
          - repeat econs; ss; et.
        }

        apply star_refl.
      * left. pfold. econs 3; et.
        { rr. esplits; eauto. ss. econs; et. ii. destruct i; ss. clarify. apply H. unfold Int.zero.
          Local Transparent Int.repr.
          unfold Int.repr.
          Local Opaque Int.repr.
          ss. apply eta; ss.
        }
        ii; des.
        inv ATSRC. ss; clarify.
        destruct sm0; ss. clarify.
        unfold Clight.fundef in *.
        rewrite FINDG in *. clarify.
        eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _), (SimMemId.mk _ _).
        esplits; ss; eauto.
        { econs; ss; eauto. }
        i. inv AFTERSRC. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. inv SIMRETV; ss; clarify.
        esplits; eauto.
        { econs; eauto. }
        instantiate (2:= (Ord.lift_idx lt_wf 15%nat)).
        left. pfold. econs; eauto. i; des. econs 2; eauto.
        {
          esplits; eauto; cycle 1.
          { instantiate (1:= (Ord.lift_idx lt_wf 14%nat)). eapply Ord.lift_idx_spec; et. }

          eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }
          
          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; ss; eauto.
            - repeat (econs; ss; eauto).
              + unfold typify. des_ifs.
              + ss.
            - ss.
          }

          eapply star_refl.
        }
        
        right. eapply CIH. instantiate (1:= SimMemId.mk _ _).
        econs; ss; eauto; try lia.
        rewrite sum_recurse. des_ifs.
        { rewrite Z.eqb_eq in *. lia. }
        replace (Int.sub (Int.add (sum (Int.sub i Int.one)) i) (Int.repr 1)) with
            (Int.add (sum (Int.sub i Int.one)) (Int.sub i Int.one)); cycle 1.
        { abstr (sum (Int.sub i Int.one)) z. rewrite ! Int.sub_add_opp.
          rewrite Int.add_assoc. ss. }
        econs; eauto.
  - (* return *)
    econs 4; ss; eauto.
Unshelve.
  all: ss.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { eapply SoundTop.sound_state_local_preservation. }
  i. ss. esplits; eauto; cycle 1.
  { (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.

    (* hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR. *)

    esplits; eauto. econs; eauto.
    + rewrite <- FPTR. eauto.
    + instantiate (1:= [Vint i]). rewrite VS in *. inv VALS. econs; ss.
      cbn. unfold typify. des_ifs; ss.
  }
  (* init bsim *)
  ii.
  destruct sm_arg; ss. clarify.
  clear MFUTURE.
  inv SIMARGS; ss. clarify.
  inv INITTGT.
  (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
  exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
  eexists. eexists (SimMemId.mk _ _).
  esplits; eauto.
  + eapply match_states_lxsim.
    econs; ss; eauto; cycle 1.
    { inv SAFESRC. ss. }

    inv SAFESRC. destruct args_src, args_tgt; ss. clarify.
    assert(tvs = [Vint i]).
    {
      unfold signature_of_function in TYP. ss.
      inv TYP. ss. cbn. unfold typify. des_ifs; ss.
    } clarify.
    econs; eauto.
Unshelve.
  all: try (ss; econs).
Qed.

End SIMMODSEM.

Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (MutrecAspec.module prog) (ClightC.module2 prog) tt)
.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

