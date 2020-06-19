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
Require Import LinkingC2.
Require Import Simulation Sem SemProps LinkingC.
Require Import LinkingProps.
Require Import Any.

Set Implicit Arguments.

Lemma wf_module_Aspec: Sk.wf MutrecAspec.module.
Proof.
  ss. unfold MutrecA.prog. econs.
  - unfold prog_defs_names; ss.
    repeat (econs; ss; ii; des; clarify).
  - ss. i. des; clarify.
    unfold update_snd in *. ss. clarify. ss. des; clarify.
  - ii. ss. des; clarify; eauto.
  - i. ss. des; clarify; inv IN; ss; clarify.
Qed.

Lemma wf_module_Bspec: Sk.wf MutrecBspec.module.
Proof.
  ss. unfold MutrecB.prog. econs.
  - unfold prog_defs_names; ss.
    repeat (econs; ss; ii; des; clarify).
  - ss. i. des; clarify.
    unfold update_snd in *. ss. clarify. ss. des; clarify.
  - ii. ss. des; clarify; eauto.
  - i. ss. des; clarify; inv IN; ss; clarify.
Qed.

Lemma link_sk_same (ctx1 ctx2: list Mod.t) (WFCTX2: forall md, In md ctx2 -> Sk.wf md):
    link_sk (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2)
    = link_sk (ctx1 ++ [module] ++ ctx2).
Proof.
  assert ([(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2 <> [] /\ [module] ++ ctx2 <> []) by ss.
  exploit (link_sk_prepend_eq ctx1 H).
  { eapply link_sk_assoc_one; ss.
    - eapply wf_module_Aspec; et.
    - eapply wf_module_Bspec; et.
  } i. eauto.
Qed.
Definition is_focus (x: Mod.t) := x = MutrecAspec.module \/ x = MutrecBspec.module.

Section LXSIM.

  Variable ctx1: Syntax.program.
  Variable ctx2: Syntax.program.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk (ctx1 ++ [module] ++ ctx2) = Some sk_link).
  Hypothesis WFCTX1: forall md : Mod.t, In md ctx1 -> Sk.wf md.
  Hypothesis WFCTX2: forall md : Mod.t, In md ctx2 -> Sk.wf md.
  Let LINKTGT: link_sk (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2) = Some sk_link.
  Proof. rewrite link_sk_same; ss. Qed.

  Let INCLA: SkEnv.includes skenv_link (CSk.of_program signature_of_function MutrecA.prog).
  Proof.
    unfold skenv_link.
    exploit link_includes.
    eapply LINKTGT.
    instantiate (1:=MutrecAspec.module).
    eapply in_or_app; ss. auto. i. ss.
  Qed.

  Let INCLB: SkEnv.includes skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog).
  Proof.
    unfold skenv_link.
    exploit link_includes.
    eapply LINKTGT.
    instantiate (1:=MutrecBspec.module).
    eapply in_or_app; ss. auto. i. ss.
  Qed.

  Hypothesis SKWF: Sk.wf sk_link.
  Let SKEWF: SkEnv.wf skenv_link.
  Proof. eapply SkEnv.load_skenv_wf; et. Qed.

  Lemma genv_sim fptr if_sig :
      (<<FINDF: Genv.find_funct (SkEnv.project skenv_link MutrecABspec.sk_link) fptr = Some (AST.Internal if_sig)>>)
      <-> (<<FINDF: exists md, (<<FOCUS: is_focus md>>)
         /\ (<<FINDF: Genv.find_funct (ModSem.skenv (flip Mod.modsem skenv_link md)) fptr = Some (AST.Internal if_sig)>>)>>).
  Proof.
    destruct (link (MutrecAspec.module: Sk.t) MutrecBspec.module) eqn:T; cycle 1.
    { exfalso. ss. }
    exploit SkEnv.project_respects_union; et.
    { eapply Sk.link_union; et. }
    intro U; des. inv U.
    unfold MutrecABspec.sk_link in *. ss. rewrite T in *.
    split; i.
    - exploit UGE; et. i. des; et.
      + esplits; ss; et.
        { instantiate (1:= MutrecAspec.module). rr. et. }
        ss.
      + esplits; ss; et.
        { instantiate (1:= MutrecBspec.module). rr. et. }
        ss.
    - des. rr in FOCUS. des; clarify.
      + exploit ULE; et.
      + exploit ULE; et.
  Qed.

  Lemma find_f_id :
    exists blk, (<<SYMBBIG: Genv.find_symbol skenv_link f_id = Some blk>>)
            /\ (<<SYMBA: Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog)) f_id = Some blk>>)
            /\ (<<SYMBB: Genv.find_symbol (SkEnv.project skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog)) f_id = Some blk>>).
  Proof.
   inv INCLA. ss.
   inv SKEWF. ss.
   unfold prog_defmap in DEFS. ss.
   specialize (DEFS f_id). ss.
   exploit DEFS; eauto. i. des.
   esplits; eauto.
   - unfold Genv.find_symbol in *. ss. des_ifs.
     exploit MapsC.PTree_filter_key_spec.
     instantiate (6:=(fun id : ident => defs (CSk.of_program signature_of_function MutrecA.prog) id)).
     instantiate (2:=(PTree.Node
                        (PTree.Node t12 o8
                                    (PTree.Node
                                       (PTree.Node t13 o10
                                                   (PTree.Node t7 o11 (PTree.Node (PTree.Node (PTree.Node t15 (Some blk) t19) o13 t18) o12 t17))) o9 t14)) o7
                        t11)).
     instantiate (1:=f_id). rewrite Heq. ss.
   - unfold Genv.find_symbol in *. ss. des_ifs.
     exploit MapsC.PTree_filter_key_spec.
     instantiate (6:=(fun id : ident => defs (Sk.of_program Asm.fn_sig MutrecB.prog) id)).
     instantiate (2:=(PTree.Node
                        (PTree.Node t12 o8
                                    (PTree.Node
                                       (PTree.Node t13 o10
                                                   (PTree.Node t7 o11 (PTree.Node (PTree.Node (PTree.Node t15 (Some blk) t19) o13 t18) o12 t17))) o9 t14)) o7
                        t11)).
     instantiate (1:=f_id). rewrite Heq. ss.
  Qed.

  Lemma find_g_id :
    exists blk, (<<SYMBBIG: Genv.find_symbol skenv_link g_id = Some blk>>)
           /\ (<<SYMBA: Genv.find_symbol (SkEnv.project skenv_link (CSk.of_program signature_of_function MutrecA.prog)) g_id = Some blk>>)
           /\ (<<SYMBB: Genv.find_symbol (SkEnv.project skenv_link (Sk.of_program Asm.fn_sig MutrecB.prog)) g_id = Some blk>>)
  .
  Proof.
    inv INCLB. ss. inv SKEWF. ss.
    unfold prog_defmap in DEFS. ss.
    specialize (DEFS g_id). ss.
    exploit DEFS; eauto. i. des.
    esplits; eauto.
    - unfold Genv.find_symbol in *. ss. des_ifs.
      exploit MapsC.PTree_filter_key_spec.
      instantiate (6:=(fun id : ident => defs (CSk.of_program signature_of_function MutrecA.prog) id)).
      instantiate (2:=(PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node (PTree.Node t7 o11 (PTree.Node t12 o12 (PTree.Node (PTree.Node t17 (Some blk) t19) o13 t18))) o10
                      t15) o9 t14) o8 t13) o7 t11)).
      instantiate (1:=g_id). rewrite Heq. ss.
    - unfold Genv.find_symbol in *. ss. des_ifs.
      exploit MapsC.PTree_filter_key_spec.
      instantiate (6:=(fun id : ident => defs (Sk.of_program Asm.fn_sig MutrecB.prog) id)).
      instantiate (2:=(PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node (PTree.Node t7 o11 (PTree.Node t12 o12 (PTree.Node (PTree.Node t17 (Some blk) t19) o13 t18))) o10
                      t15) o9 t14) o8 t13) o7 t11)).
      instantiate (1:=g_id). rewrite Heq. ss.
  Qed.

  Inductive match_focus: mem -> int -> int -> list Frame.t -> Prop :=
  | match_focus_nil
      cur max m
      (OVER: cur.(Int.intval) > max.(Int.intval)):
      match_focus m cur max []
  | match_focus_cons_A
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z):
      match_focus m cur max ((Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Interstate cur m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m tl_tgt
      (REC: match_focus m (Int.add cur Int.one) max tl_tgt)
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z):
      match_focus m cur max ((Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Interstate cur m)) :: tl_tgt).

  Lemma add_one_same
        i
        (BOUND: 0 <= Int.intval i + 1 <= Int.max_unsigned):
      Int.intval (Int.add i Int.one) = Int.intval i + 1.
  Proof.
    unfold Int.add. unfold Int.unsigned.
    unfold Int.one.
    Local Transparent Int.repr.
    unfold Int.repr. ss.
    rewrite Int.Z_mod_modulus_eq.
    unfold Int.Z_mod_modulus. des_ifs.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.unsigned_repr. auto. split; omega.
  Qed.

  Lemma match_focus_over_nil
        m max hds_tgt
        (RANGE: max.(Int.intval) < MAX)
        (FOCUS: match_focus m (Int.add max Int.one) max hds_tgt):
      hds_tgt = nil.
  Proof.
    clear - RANGE FOCUS.
    inv FOCUS; ss.
    - exfalso.
      assert (Int.intval (Int.add max Int.one) = (Int.intval max) + 1); destruct max.
      { rewrite add_one_same; ss.
        unfold MAX, Int.max_unsigned in *; ss. split; omega. }
      ss. rewrite H in LE. omega.
    - exfalso.
      assert (Int.intval (Int.add max Int.one) = (Int.intval max) + 1); destruct max.
      { rewrite add_one_same; ss.
        unfold MAX, Int.max_unsigned in *; ss. split; omega. }
      ss. rewrite H in LE. omega.
  Qed.

  Inductive match_stacks (fromcall: bool) (idx: Z): list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_ctx
      ctx_stk
      (IDX: idx = 0%Z):
      match_stacks fromcall idx ctx_stk ctx_stk
  | match_stacks_focus_top_call
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate max m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate cur m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate cur m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = 2 * cur.(Int.intval))
      (RANGE: max.(Int.intval) < MAX):
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar
  | match_stacks_focus_top_return
      ctx_stk
      cur max m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Returnstate (sum max) m))
      hd_tgt
      tmpvar
      (TMPVAR: tmpvar = (hd_tgt :: hds_tgt ++ ctx_stk))
      (TGT: __GUARD__ ((hd_tgt = Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Returnstate (sum cur) m)) \/
                       (hd_tgt = Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Returnstate (sum cur) m))))
      (LE: (cur.(Int.intval) <= max.(Int.intval))%Z)
      (FOCUS: match_focus m (Int.add cur Int.one) max hds_tgt)
      (FROMCALL: fromcall = false)
      (IDX: idx = max.(Int.intval) - cur.(Int.intval))
      (RANGE: max.(Int.intval) < MAX):
      match_stacks fromcall idx (hd_src :: ctx_stk) tmpvar.

  Inductive match_states (i: Z): Sem.state -> Sem.state -> Prop :=
  | match_states_call
      frs_src frs_tgt
      args ohs
      (STK: match_stacks true i frs_src frs_tgt):
      match_states i (Callstate args frs_src ohs) (Callstate args frs_tgt ohs)
  | match_states_normal
      frs_src frs_tgt ohs
      (STK: match_stacks false i frs_src frs_tgt):
      match_states i (State frs_src ohs) (State frs_tgt ohs).

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

  Require Import SemTyping.

  Lemma match_states_xsim
        i st_src0 st_tgt0
        (MATCH: match_states i st_src0 st_tgt0):
    xsim (sem (ctx1 ++ [module] ++ ctx2))
         (sem (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)) (Zwf.Zwf 0)
         (SemTyping.sound_state (ctx1 ++ [module] ++ ctx2)) top1 i st_src0 st_tgt0.
  Proof.
    revert_until SKEWF. pcofix CIH. i.
    inv MATCH.
    - (* call *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; et.
        i. econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. rewrite LINKTGT. rewrite LINKSRC in *. ss. des.
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
              { ss; et. }
              econs; ss; eauto.
              - unfold Args.get_fptr in *. des_ifs. ss. clarify.
                eapply MutrecAspec.find_symbol_find_funct_ptr; et. }
            { esplits; eauto. econs.
              { econs; eauto; cycle 1.
                { unfold Genv.find_funct. des_ifs. eauto. }
                ss. right. unfold load_modsems. rewrite in_map_iff.
                esplits; eauto. rewrite in_app_iff. ss. eauto. }
              { ss; et. }
              econs; ss; eauto.
              - unfold Args.get_fptr in *. des_ifs. ss. clarify.
                eapply MutrecBspec.find_symbol_find_funct_ptr; et.
            }
            { esplits; eauto. econs; eauto. econs; eauto. ss. right. unfold load_modsems.
              rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. ss. auto. } }
        { i; ss. des_ifs. inv FINALTGT. }
        i. left. ss. rewrite LINKSRC, LINKTGT in *. inv STEPTGT. inv MSFIND. ss.
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
              eapply genv_sim. exists MutrecAspec.module. esplits; ss; eauto. rr. eauto. }
            { ss; et. }
            econs; ss; eauto.
            + eapply genv_sim. destruct args; ss. clarify. exists MutrecAspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            { econs; eauto.
              rewrite add_one_same. nia.
              unfold MAX, Int.max_unsigned in *; ss. omega. }
            { des; ss. } }
        { inv INIT. ss. esplits; eauto.
          - left. apply plus_one. econs.
            { econs.
              { ss. right. unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff.
                ss. eauto. }
              eapply genv_sim. exists MutrecBspec.module. esplits; ss; eauto. rr. eauto. }
            { ss; et. }
            econs; ss; eauto.
            + eapply genv_sim. destruct args; ss. clarify. exists MutrecBspec.module. esplits; ss; eauto. rr. eauto.
          - right. eapply CIH; eauto. econs; eauto.
            econs; ss; try refl; eauto.
            { f_equal. instantiate (1:= []). ss. }
            { unfold __GUARD__. eauto. }
            { econs; eauto.
              rewrite add_one_same. nia.
              unfold MAX, Int.max_unsigned in *; ss. omega. }
            { des; ss. } }
        { esplits; eauto.
          - left. apply plus_one. econs; eauto. econs; eauto. ss. right.
            unfold load_modsems. rewrite in_map_iff. esplits; eauto. rewrite in_app_iff; eauto. ss. eauto.
          - right. eapply CIH; eauto. econs; eauto. econs; eauto. }
      + (* focus-call *)
        ss.
      + (* focus-return *)
        ss.
    - (* normal *)
      inv STK.
      + (* ctx *)
        pfold. right. econs; eauto.
        i. ss. econs; eauto; cycle 1.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss; des_ifs. des; ss.
          - left. esplits; eauto.
          - right. inv SAFESRC; ss.
            { esplits; eauto. econs 1; eauto. }
            { esplits; eauto. econs 3; eauto. }
            { esplits; eauto. econs 4; eauto. } }
        { ii; ss. inv FINALTGT. des_ifs. esplits; eauto. { apply star_refl. } econs; eauto. }
        i. left. ss. des_ifs.
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
        i. econs; ss; try rewrite LINKSRC, LINKTGT in *; eauto; cycle 1; ss.
        { i. specialize (SAFESRC _ (star_refl _ _ _ _)). ss. des.
          - inv SAFESRC. inv FINAL.
          - des_ifs. inv SAFESRC; ss.
            + inv STEP. right.
              unsguard TGT. des; clarify; ss; esplits; eauto; econs 3; ss; eauto; econs; eauto.
            + unsguard TGT. des; clarify; ss; inv FINAL. }
        { ii; ss. inv FINALTGT. unsguard TGT. des; clarify; ss; inv FINAL. }
        i. left. inv STEPTGT; ss; swap 2 3.
        { unsguard TGT; des; clarify; inv AT. }
        { unsguard TGT; des; clarify; inv FINAL. }
        unsguard TGT; des; clarify; ss.
        { - inv STEP; ss.
            + esplits; eauto.
              * left. apply plus_one. econs 3; ss; et.
              * right. eapply CIH. unfold Frame.update_st. ss. econs; et. econs 3; et; ss. unfold __GUARD__. eauto.
            + esplits; eauto.
              * right. esplits; eauto.
                { apply star_refl. }
                { instantiate (1:= 2 * (Int.intval cur) - 1). rr. esplits; eauto; try lia.
                  destruct cur. ss. omega. }
              * left. pfold. left. right. econs; eauto.
                hexploit find_g_id; eauto. i; des.
                hexploit (MutrecBspec.find_symbol_find_funct_ptr); eauto. instantiate (1:= blk). i; des.
                exploit SYMB; eauto. intro T; des. clear SYMB FINDF.
                econs 2; eauto; esplits.
                -- eapply plus_two with (t1 := []) (t2 := []); ss.
                   ++ econs; eauto.
                      { eapply lift_determinate_at; ss; des_ifs; eauto.
                        econs; eauto.
                        - ii; ss. inv H; inv H0; ss.
                        - econs; eauto. inv H. }
                      econs; ss; eauto. econs; eauto.
                   ++ unfold Frame.update_st. ss. econs; eauto.
                      { econs; ss; des_ifs.
                        - i. inv H; inv H0; ss.
                          esplits; eauto.
                          { econs. }
                          { i.
                            assert (Ge.find_fptr_owner (load_genv (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2) (Sk.load_skenv sk_link))
                                                       (Vptr blk Ptrofs.zero) (Mod.get_modsem MutrecBspec.module skenv_link tt)).
                            { ss. econs.
                              - ss. right. unfold load_modsems. rewrite list_append_map. ss.
                                unfold MutrecBspec.module, flip, Mod.modsem. ss.
                                eapply in_or_app. ss. auto.
                              - ss. des_ifs. eauto. }
                            exploit find_fptr_owner_determ.
                            { instantiate (3 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                              ss. des_ifs. eapply MSFIND. }
                            { ss. des_ifs. eapply MSFIND0. }
                            i. subst ms.
                            exploit find_fptr_owner_determ.
                            { instantiate (3 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                              ss. des_ifs. eapply MSFIND. }
                            { ss. des_ifs. eapply H0. }
                            i. subst ms0. ss.
                            inv INIT; inv INIT0. ss. clarify. }
                        - i. inv FINAL; inv STEP.
                        - econs. inv H; ss. }
                      econs; ss; eauto.
                      ** des_ifs. econs; ss.
                         { right. unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. right. right. ss. eauto. }
                         des_ifs; eauto.
                      ** ss.
                      ** econs; ss; eauto.
                         { destruct cur,  max. ss. esplits; try omega.
                           exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                           assert (intval - 1 < MAX) by nia.
                           rewrite Int.Z_mod_modulus_eq.
                           rewrite <- Int.unsigned_repr_eq.
                           rewrite Int.unsigned_repr. auto. unfold Int.max_unsigned. split; nia. }
                -- instantiate (1:= 2 * Int.intval cur - 2). rr. esplits; try lia.
                   destruct cur. ss. nia.
                -- right. eapply CIH. u.
                   instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                   { unfold Midx.update. apply func_ext1. intro mi. des_ifs. ss.
                     exploit SSSRC0; et. { eapply star_refl. } i; des. rr in H. des. ss.
                   }
                   econs; eauto.
                   econs.
                   { f_equal. }
                   { f_equal. rewrite cons_app. rewrite app_assoc. f_equal. }
                   { unfold __GUARD__. eauto. }
                   { destruct cur,  max. ss. esplits; try omega.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. rewrite int_sub_add. econs 2; eauto. }
                   { ss. }
                   { destruct cur. ss.
                     exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. } }
        { - inv STEP; ss.
            + esplits; eauto.
              * left. apply plus_one. econs 3; ss; et.
              * right. eapply CIH. unfold Frame.update_st. ss. econs; et. econs 3; et; ss. unfold __GUARD__. eauto.
            + esplits; eauto.
              * right. esplits; eauto.
                { apply star_refl. }
                { instantiate (1:= 2 * (Int.intval cur) - 1). rr. esplits; eauto; try lia.
                  destruct cur. ss. omega. }
              * left. pfold. left. right. econs; eauto.
                hexploit find_f_id; eauto. i; des.
                hexploit (MutrecAspec.find_symbol_find_funct_ptr); eauto. instantiate (1:= blk). i; des.
                exploit SYMB; eauto. intro T; des. clear SYMB FINDF.
                econs 2; eauto; esplits.
                -- eapply plus_two with (t1 := []) (t2 := []); ss.
                   ++ econs; eauto.
                      {
                        eapply lift_determinate_at; ss; des_ifs; eauto.
                        econs; eauto.
                        - ii; ss. inv H; inv H0; ss.
                        - econs; eauto. inv H.
                      }
                      econs; ss; eauto. econs; eauto.
                   ++ unfold Frame.update_st. ss. econs; eauto.
                      { econs; ss; des_ifs.
                        - i. inv H; inv H0; ss.
                          esplits; eauto.
                          { econs. }
                          { i.
                            assert (Ge.find_fptr_owner (load_genv (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2) (Sk.load_skenv sk_link))
                                                       (Vptr blk Ptrofs.zero) (Mod.get_modsem MutrecAspec.module skenv_link tt)).
                            { ss. econs.
                              - ss. right. unfold load_modsems. rewrite list_append_map. ss.
                                unfold MutrecBspec.module, flip, Mod.modsem. ss.
                                eapply in_or_app. ss. auto.
                              - ss. des_ifs. eauto. }
                            exploit find_fptr_owner_determ.
                            { instantiate (3 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                              ss. des_ifs. eapply MSFIND. }
                            { ss. des_ifs. eapply MSFIND0. }
                            i. subst ms.
                            exploit find_fptr_owner_determ.
                            { instantiate (3 := (ctx1 ++ [MutrecAspec.module; MutrecBspec.module] ++ ctx2)).
                              ss. des_ifs. eapply MSFIND. }
                            { ss. des_ifs. eapply H0. }
                            i. subst ms0. ss.
                            inv INIT; inv INIT0. ss. clarify. }
                        - i. inv FINAL; inv STEP.
                        - econs. inv H; ss. }
                      econs; ss; eauto.
                      ** des_ifs. econs; ss.
                         { right. unfold load_modsems. rewrite in_map_iff. esplits; et. rewrite in_app_iff. right. left. ss. }
                         des_ifs; eauto.
                      ** ss.
                      ** econs; ss; eauto.
                         { destruct cur,  max. ss. esplits; try omega.
                           exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                           assert (intval - 1 < MAX) by nia.
                           rewrite Int.Z_mod_modulus_eq.
                           rewrite <- Int.unsigned_repr_eq.
                           rewrite Int.unsigned_repr. auto. unfold Int.max_unsigned. split; nia. }
                -- instantiate (1:= 2 * Int.intval cur - 2). rr. esplits; try lia.
                   destruct cur. ss. nia.
                -- right. eapply CIH. u.
                   instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                   { unfold Midx.update. apply func_ext1. intro mi. des_ifs. ss.
                     exploit SSSRC0; et. { eapply star_refl. } i; des. rr in H. des. ss.
                   }
                   econs; eauto.
                   econs.
                   { f_equal. }
                   { f_equal. rewrite cons_app. rewrite app_assoc. f_equal. }
                   { unfold __GUARD__. eauto. }
                   { destruct cur,  max. ss. esplits; try omega.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. rewrite int_sub_add. econs 3; eauto. }
                   { ss. }
                   { destruct cur. ss.
                     exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                     assert (intval - 1 < MAX) by nia.
                     rewrite Int.Z_mod_modulus_eq.
                     rewrite <- Int.unsigned_repr_eq.
                     rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
                   { ss. } }
      + (* focus - return *)
        destruct (classic (cur = max)).
        * clarify. exploit match_focus_over_nil; eauto.
          i; clarify.
          pfold. right. econs; eauto.
          i. econs; eauto; cycle 1.
          { i. specialize (SAFESRC _ (star_refl _ _ _ _)). desH SAFESRC; ss.
            - inv SAFESRC; ss. inv FINAL. ss. clarify. left.
              unsguard TGT. des; clarify.
              { esplits; eauto. econs; ss; eauto. }
              { esplits; eauto. econs; ss; eauto. }
            - des_ifs. right. inv SAFESRC; ss.
              { inv STEP. }
              inv FINAL. unsguard TGT. des; clarify.
              + esplits; eauto. econs 4; eauto. ss.
              + esplits; eauto. econs 4; eauto. ss.
          }
          { i. ss. inv FINALTGT.
            unsguard TGT. des; clarify; ss.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto.
            - inv FINAL. ss. clarify. esplits; eauto. { apply star_refl. } econs; ss; eauto. }
          i. left. ss. des_ifs. inv STEPTGT; ss.
          { unsguard TGT. des; clarify; inv AT. }
          { unsguard TGT. des; clarify; inv STEP. }
          esplits; eauto.
          -- left. apply plus_one.
             unsguard TGT. des; clarify; inv FINAL; ss; repeat des_u.
             { econs 4; et; ss. }
             { econs 4; et; ss. }
          -- right. eapply CIH. ss.
             replace (Midx.update ohs (ModSem.midx (Frame.ms hd_tgt)) (upcast oh0)) with ohs; cycle 1.
             { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
               exploit SSSRC; et. { eapply star_refl. } i; des. rr in H. des. ss. des_ifs.
               unsguard TGT. des; clarify; ss; des_u; ss.
             }
             replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
             { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
               exploit SSSRC; et. { eapply star_refl. } i; des. rr in H. des. ss.
             }
             econs; eauto. econs; eauto.
        * pfold. left. right. econs; eauto.
          unsguard TGT. des; clarify.
          { inv FOCUS; ss.
            { exfalso.
              exploit Int.eq_false; eauto. i.
              destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
              exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
              assert (intval - 1 < MAX) by nia.
              rewrite Int.Z_mod_modulus_eq in OVER.
              rewrite <- Int.unsigned_repr_eq in OVER.
              rewrite Int.unsigned_repr in OVER. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss.
                instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
                  exploit SSSRC; et. { eapply star_refl. } intro T; des. rr in T. des. ss.
                }
                econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss.
                instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
                  exploit SSSRC; et. { eapply star_refl. } intro T; des. rr in T. des. ss.
                }
                econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. } }
          { inv FOCUS; ss.
            { exfalso.
              exploit Int.eq_false; eauto. i.
              destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
              exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
              assert (intval - 1 < MAX) by nia.
              rewrite Int.Z_mod_modulus_eq in OVER.
              rewrite <- Int.unsigned_repr_eq in OVER.
              rewrite Int.unsigned_repr in OVER. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss.
                instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
                  exploit SSSRC; et. { eapply star_refl. } intro T; des. rr in T. des. ss.
                }
                econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. }
            { econs 2; eauto.
              - esplits; eauto.
                + apply plus_one. econs; eauto.
                  { eapply lift_determinate_at; ss; des_ifs; et.
                    econs; ss.
                    - ii. inv H0; inv H1.
                    - econs. inv H0; ss. }
                  ss. des_ifs.
                  econs 4; ss; eauto.
                  econs; ss; eauto.
                  rewrite Int.add_commut.
                  rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. ss.
                + instantiate (1:= Int.intval max - Int.intval cur - 1). split; try lia.
              - right. eapply CIH; eauto. unfold Frame.update_st. ss.
                instantiate (1:= tt). replace (Midx.update ohs None (upcast tt)) with ohs; cycle 1.
                { eapply func_ext1. intro mi. unfold Midx.update. des_ifs.
                  exploit SSSRC; et. { eapply star_refl. } intro T; des. rr in T. des. ss.
                }
                econs; eauto. econs 3; ss.
                + unfold __GUARD__. eauto.
                + ss.
                + ss.
                + exploit Int.eq_false; eauto. i.
                  destruct cur, max; ss. unfold Int.eq in H0. ss. des_ifs.
                  exploit Int.Z_mod_modulus_range. instantiate (1:=intval - 1). i. des; auto.
                  assert (intval - 1 < MAX) by nia.
                  rewrite Int.Z_mod_modulus_eq.
                  rewrite <- Int.unsigned_repr_eq.
                  rewrite Int.unsigned_repr. nia. unfold Int.max_unsigned. split; nia. } }
  Unshelve.
    all: ss.
  Qed.

End LXSIM.


Lemma nodup_sim
      ctx1 ctx2 skenv
      (NODUP: Midx.NoDup
                   (List.map ModSem.midx (load_genv (ctx1 ++ [module] ++ ctx2) skenv)))
  :
    <<NODUP: Midx.NoDup
      (List.map ModSem.midx
                   (load_genv (ctx1 ++ [MutrecAspec.module ; MutrecBspec.module] ++ ctx2) skenv))>>
.
Proof.
  rr. rr in NODUP. ss. erewrite f_equal; et.
  rewrite cons_app. rewrite cons_app with (xtl := ctx2).
  rewrite cons_app with (xtl := ctx2).
  unfold load_modsems.
  rewrite ! map_app.
  rewrite ! filter_map_app. ss.
Qed.

Theorem mutrecABcorrect ctx1 ctx2 :
    (<<REFINE: improves (Sem.sem (ctx1 ++ [(MutrecABspec.module)] ++ ctx2))
                        (Sem.sem (ctx1 ++ [(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx2))>>).
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  econs; eauto.
  econs.
  { apply SemTyping.preservation; eauto. }
  { apply preservation_top; eauto. }
  { instantiate (1:= Zwf.Zwf 0%Z). eapply Zwf.Zwf_well_founded. }
  all: swap 1 2.
  { i; des. ss. inv SAFESRC. rewrite INITSK.
    exploit link_sk_same; ss.
    { ii. eapply WF. rewrite in_app_iff. right. right. et. }
    i. erewrite H. des_ifs. }
  econs; eauto.
  i. ss. inv INITSRC.
  assert(WF2: forall md, In md ctx2 -> Sk.wf md).
  { ii. eapply WF. rewrite in_app_iff. right. right. et. }
  esplits; eauto.
  { econs; ss; eauto.
    - econs; eauto.
      + exploit link_sk_same; ss; et. i. erewrite H. des_ifs.
      + ii; ss. rewrite in_app_iff in *. des; ss.
        { eapply WF; et. rewrite in_app_iff. et. }
        des; cycle 2; subst.
        { eapply WF; et. rewrite in_app_iff. ss. et. }
        * eapply wf_module_Aspec; et.
        * eapply wf_module_Bspec; et.
      + exploit link_sk_same; ss; et. i. erewrite H. des_ifs. eapply nodup_sim; et.
    - i; ss. inv INIT0. inv INIT1. clarify. }
  eapply match_states_xsim; eauto.
  { eapply link_sk_preserves_wf_sk; eauto. }
  { exploit link_sk_same; ss; et. i. erewrite H. des_ifs. set (Sk.load_skenv sk_link) as skenv in *.
    rewrite cons_app. rewrite cons_app with (xtl := ctx2).
    rewrite cons_app with (xtl := [MutrecBspec.module] ++ ctx2).
    Local Opaque app.
    erewrite load_owned_heaps_same; cycle 1.
    { ss. }
    { Local Transparent app. ss. eapply nodup_sim in OHSUNIQ; et. Local Opaque app. }
    {
      ss. unfold load_modsems, flip. rewrite ! map_map.
      split; ii; des; clarify; ss; et.
      - rewrite in_map_iff in *. des. clarify. rewrite ! in_app_iff in *. des; clarify.
        { right. esplits; et. rewrite ! in_app_iff in *. et. }
        { ss. des; clarify. ss. left. et. }
        { right. esplits; et. rewrite ! in_app_iff in *. et. }
      - rewrite in_map_iff in *. des. clarify. rewrite ! in_app_iff in *. des; clarify.
        { right. esplits; et. rewrite ! in_app_iff in *. et. }
        { ss. des; clarify; ss; left; et. }
        { right. esplits; et. rewrite ! in_app_iff in *. et. }
    }
    econs; eauto. econs; eauto.
  }
Qed.
