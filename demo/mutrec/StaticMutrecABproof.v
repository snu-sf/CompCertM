Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import StaticMutrecAspec StaticMutrecBspec StaticMutrecABspec.
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

Lemma link_sk_same
      ctx
  :
    link_sk (ctx ++ [(StaticMutrecAspec.module) ; (StaticMutrecBspec.module)])
    = link_sk (ctx ++ [module])
.
Proof.
  admit "see UpperBound_A extra".
Qed.

Lemma wf_module_Aspec: Sk.wf StaticMutrecAspec.module.
Proof.
  admit "ez".
Qed.

Lemma wf_module_Bspec: Sk.wf StaticMutrecBspec.module.
Proof.
  admit "ez".
Qed.

Definition is_focus (x: Mod.t) := x = StaticMutrecAspec.module \/ x = StaticMutrecBspec.module.

Section LXSIM.

  Variable ctx: Syntax.program.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk (ctx ++ [module]) = Some sk_link).
  Let LINKTGT: link_sk (ctx ++ [(StaticMutrecAspec.module) ; (StaticMutrecBspec.module)]) = Some sk_link.
  Proof. rewrite link_sk_same. ss. Qed.

  Let INCLA: SkEnv.includes skenv_link (CSk.of_program signature_of_function StaticMutrecA.prog).
  Proof.
    admit "ez".
  Qed.

  Let INCLB: SkEnv.includes skenv_link (Sk.of_program Asm.fn_sig StaticMutrecB.prog).
  Proof.
    admit "ez".
  Qed.

  Hypothesis SKWF: Sk.wf sk_link.
  Let SKEWF: SkEnv.wf skenv_link.
  Proof. eapply SkEnv.load_skenv_wf; et. Qed.

  Lemma genv_sim
        fptr if_sig
    :
      (<<FINDF: Genv.find_funct (SkEnv.project skenv_link StaticMutrecABspec.sk_link) fptr =
                Some (AST.Internal if_sig)>>)
      <->
      (<<FINDF: exists md, (<<FOCUS: is_focus md>>) /\
                           (<<FINDF: Genv.find_funct (ModSem.skenv (flip Mod.modsem skenv_link md)) fptr =
                                     Some (AST.Internal if_sig)>>)>>)
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
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
    :
      match_focus m cur max ((Frame.mk (StaticMutrecAspec.modsem skenv_link tt) (StaticMutrecAspec.Interstate cur m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
    :
      match_focus m cur max ((Frame.mk (StaticMutrecBspec.modsem skenv_link tt) (StaticMutrecBspec.Interstate cur m)) :: tl_tgt)
  .

  Lemma match_focus_over_nil
        m max hds_tgt
        (RANGE: max.(Int.intval) < MAX)
        (FOCUS: match_focus m (Int.add max Int.one) max hds_tgt)
    :
      hds_tgt = nil
  .
  Proof.
    clear - RANGE FOCUS.
    inv FOCUS; ss.
    - exfalso. admit "ez - arithmetic".
    - exfalso. admit "ez - arithmetic".
  Qed.

  Inductive match_stacks (fromcall: bool) (idx: Z): list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_ctx
      ctx_stk
      (IDX: idx = 0%Z)
    :
      match_stacks fromcall idx ctx_stk ctx_stk
  | match_stacks_focus_top_call
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (StaticMutrecABspec.modsem skenv_link tt) (StaticMutrecABspec.Callstate max m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (StaticMutrecAspec.modsem skenv_link tt) (StaticMutrecAspec.Callstate cur m)) \/
                       (hd_tgt = Frame.mk (StaticMutrecBspec.modsem skenv_link tt) (StaticMutrecBspec.Callstate cur m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (* (IDX: idx = (max.(Int.intval) + cur.(Int.intval)) + 1) *)
      (FROMCALL: fromcall = false)
      (IDX: idx = cur.(Int.intval))
    :
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar
  | match_stacks_focus_top_return
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (StaticMutrecABspec.modsem skenv_link tt) (StaticMutrecABspec.Returnstate (sum max) m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (StaticMutrecAspec.modsem skenv_link tt) (StaticMutrecAspec.Returnstate (sum cur) m)) \/
                       (hd_tgt = Frame.mk (StaticMutrecBspec.modsem skenv_link tt) (StaticMutrecBspec.Returnstate (sum cur) m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = max.(Int.intval) - cur.(Int.intval))
    :
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar 
  .

  Inductive match_states (i: Z): Sem.state -> Sem.state -> Prop :=
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks true i frs_src frs_tgt)
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

  Hint Unfold Frame.update_st.

  Lemma match_states_xsim
        i st_src0 st_tgt0
        (MATCH: match_states i st_src0 st_tgt0)
    :
      xsim (sem (ctx ++ [module])) (sem (ctx ++ [StaticMutrecAspec.module; StaticMutrecBspec.module]))
           (Zwf.Zwf 0) i st_src0 st_tgt0
  .
  Proof.
    revert_until SKEWF. pcofix CIH. i.
    inv MATCH.
    - (* call *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; et.
        { i; ss. des_ifs. inv FINALTGT. }
        i.
        econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. des_ifs. des.
          - inv SAFESRC.
          - inv SAFESRC. right. inv MSFIND. ss. des; clarify.
            { esplits; eauto. econs; eauto. econs; eauto. ss. eauto. }
            unfold load_modsems in *. rewrite in_map_iff in *. des. clarify. rewrite in_app_iff in *.
            ss. des; clarify.
            { esplits; eauto. econs; eauto. econs; eauto. ss. right. unfold load_modsems.
              rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. }
            apply genv_sim in INTERNAL. des. rr in FOCUS. inv INIT.
            unfold Genv.find_funct in *. des_ifs.
            des; clarify.
            { esplits; eauto. econs.
              { econs; eauto; cycle 1.
                { unfold Genv.find_funct. des_ifs. eauto. }
                ss. right. unfold load_modsems. rewrite in_map_iff.
                esplits; eauto. rewrite in_app_iff. ss. eauto. }
              econs; ss; eauto.
              - eapply StaticMutrecAspec.find_symbol_find_funct_ptr; et.
            }
            { esplits; eauto. econs.
              { econs; eauto; cycle 1.
                { unfold Genv.find_funct. des_ifs. eauto. }
                ss. right. unfold load_modsems. rewrite in_map_iff.
                esplits; eauto. rewrite in_app_iff. ss. eauto. }
              econs; ss; eauto.
              - eapply StaticMutrecBspec.find_symbol_find_funct_ptr; et.
            }
        }
        i. ss. des_ifs. inv STEPTGT. inv MSFIND. ss.
        unfold load_modsems in *. des; clarify.
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
        rewrite in_map_iff in *. des; clarify. rewrite in_app_iff in *. des; clarify.
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. right.
            unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
        ss. des; clarify.
        { inv INIT. ss. esplits; eauto.
          - left. apply plus_one. econs.
            { econs.
              { ss. right. unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff.
                ss. eauto. }
              eapply genv_sim. exists StaticMutrecAspec.module. esplits; ss; eauto. rr. eauto.
            }
            econs; ss; eauto.
            + eapply genv_sim. exists StaticMutrecAspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            (* rewrite cons_app with (xhd := {| *)
            (*   Frame.ms := flip Mod.modsem (Sk.load_skenv sk_link) StaticMutrecAspec.module; *)
            (*   Frame.st := StaticMutrecAspec.Callstate i (Args.m args) |}). *)
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            econs; eauto. admit "ez - no overflow".
        }
        { inv INIT. ss. esplits; eauto.
          - left. apply plus_one. econs.
            { econs.
              { ss. right. unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff.
                ss. eauto. }
              eapply genv_sim. exists StaticMutrecBspec.module. esplits; ss; eauto. rr. eauto.
            }
            econs; ss; eauto.
            + eapply genv_sim. exists StaticMutrecBspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            (* rewrite cons_app with (xhd := {| *)
            (*   Frame.ms := flip Mod.modsem (Sk.load_skenv sk_link) StaticMutrecBspec.module; *)
            (*   Frame.st := StaticMutrecBspec.Callstate i (Args.m args) |}). *)
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            econs; eauto. admit "ez - no overflow".
        }
      + (* focus-call *)
        ss.
      + (* focus-return *)
        ss.
    - (* normal *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; eauto.
        { ii; ss. inv FINALTGT. des_ifs. esplits; eauto. { apply star_refl. } econs; eauto. }
        i. ss. econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss; des_ifs. des; ss.
          - left. esplits; eauto.
          - right. inv SAFESRC; ss.
            { esplits; eauto. econs 1; eauto. }
            { esplits; eauto. econs 3; eauto. }
            { esplits; eauto. econs 4; eauto. }
        }
        i. ss. des_ifs.
        inv STEPTGT; ss.
        * esplits; eauto.
          { left. apply plus_one. econs 1; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
        * esplits; eauto.
          { left. apply plus_one. econs 3; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
        * esplits; eauto.
          { left. apply plus_one. econs 4; eauto. }
          right. eapply CIH; eauto. econs; eauto. econs; eauto.
      + (* focus-call *)
        pfold. right. econs; et.
        { ii; ss. inv FINALTGT. unsguard TGT. des; clarify; ss; inv FINAL. }
        i.
        econs; ss; des_ifs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. des.
          - inv SAFESRC. inv FINAL.
          - des_ifs. inv SAFESRC; ss.
            + inv STEP. right.
              unsguard TGT. des; clarify; ss; esplits; eauto; econs 3; ss; eauto; econs; eauto.
            + unsguard TGT. des; clarify; ss; inv FINAL.
        }
        i.
        inv STEPTGT; ss; swap 2 3.
        { unsguard TGT; des; clarify; inv AT. }
        { unsguard TGT; des; clarify; inv FINAL. }
        unsguard TGT; des; clarify; ss.
        {
          - inv STEP; ss.
            + esplits; eauto.
              * left. apply plus_one. econs 3; ss; et.
              * right. eapply CIH. unfold Frame.update_st. ss. econs; et. econs 3; et; ss. unfold __GUARD__. eauto.
            + esplits; eauto.
              * right. esplits; eauto.
                { apply star_refl. }
                { instantiate (1:= (Int.intval cur) - 1). rr. esplits; eauto; try lia. admit "ez - nonneg". }
              * left. pfold. left. right. econs; eauto. econs 2; eauto; esplits.
                -- eapply plus_two with (t1 := []) (t2 := []); ss.
                   ++ econs; eauto.
                      { (* ez - determinate_at *)
                        eapply lift_determinate_at; ss; des_ifs; eauto.
                        econs; eauto.
                        - ii; ss. inv H; inv H0; ss.
                        - econs; eauto. inv H.
                      }
                      econs; ss; eauto. econs; eauto.
                      admit "ez - genv find symbol - def".
                   ++ unfold Frame.update_st. ss. econs; eauto.
                      { admit "ez - determinate". }
                      econs; ss; eauto.
                      ** des_ifs. econs; ss.
                         { right. unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. right. right. ss. eauto. }
                         des_ifs.
                         admit "ez - genv find symbol - def".
                      ** econs; ss; eauto.
                         { admit "ez - genv find symbol - def". }
                         admit "ez - quantify MAX".
                -- admit "TODO: give proper index".
                   (* rr. esplits; try lia. *)
                   (* ++ admit "ez - arithmetic". *)
                   (* ++ admit "ez - arithmetic". *)
                -- right. eapply CIH. u. econs; eauto.
                   econs.
                   { f_equal. }
                   { f_equal. rewrite cons_app. rewrite app_assoc. f_equal. }
                   { unfold __GUARD__. eauto. }
                   { admit "ez". }
                   { ss. rewrite int_sub_add. econs 2; eauto. }
                   { ss. }
                   { ss. }
        }
        {
           admit "TODOLAST: copy-paste from above".
        }
      + (* focus - return *)
        destruct (classic (cur = max)).
        * clarify. exploit match_focus_over_nil; eauto.
          { admit "ez - quantify max". }
          i; clarify.
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
                  { eapply lift_determinate_at; ss; des_ifs; et. admit "ez - determinate". }
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
                  { eapply lift_determinate_at; ss; des_ifs; et. admit "ez - determinate". }
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
                  { eapply lift_determinate_at; ss; des_ifs; et. admit "ez - determinate". }
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
                  { eapply lift_determinate_at; ss; des_ifs; et. admit "ez - determinate". }
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
    (<<REFINE: improves (Sem.sem (ctx ++ [(StaticMutrecABspec.module)]))
                        (Sem.sem (ctx ++ [(StaticMutrecAspec.module) ; (StaticMutrecBspec.module)]))
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
  { eapply link_list_preserves_wf_sk; eauto. }
  econs; eauto. econs; eauto.
Qed.
