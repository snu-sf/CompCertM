Require Import Coqlib Maps Errors AST Linking LinkingC sflib.

Remark link_transf_partial_fundef_rev:
  forall (A B: Type) (tr1 tr2: A -> res B) (f1 f2: fundef A) (tf1 tf2: fundef B) (tf: fundef B),
  link tf1 tf2 = Some tf ->
  transf_partial_fundef tr1 f1 = OK tf1 ->
  transf_partial_fundef tr2 f2 = OK tf2 ->
  exists f,
      link f1 f2 = Some f
  /\ (transf_partial_fundef tr1 f = OK tf \/ transf_partial_fundef tr2 f = OK tf).
Proof.
  Local Transparent Linker_fundef.
  ss; ii. destruct f1, f2; ss; monadInv H0; monadInv H1.
  - discriminate.
  - destruct e; clarify. esplits; eauto. ss. rewrite EQ. ss. clarify. eauto.
  - destruct e; clarify. esplits; eauto. ss. rewrite EQ. ss. clarify. eauto.
  - destruct (external_function_eq e e0); clarify; inv H; des_ifs. eauto.
Qed.

Instance TransfPartialContextualLink_rev
           {A B C V: Type} {LV: Linker V}
           (tr_fun: C -> A -> res B)
           (ctx_for: program (fundef B) V -> C):
  TransfLink (fun (p2: program (fundef B) V) (p1: program (fundef A) V) =>
              match_program
                (fun cu tf f => AST.transf_partial_fundef (tr_fun (ctx_for cu)) f = OK tf)
                eq p2 p1).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros. eapply link_transf_partial_fundef_rev; eauto.
- intros; subst. exists v; auto.
Qed.

Instance TransfPartialLink_rev
           {A B V: Type} {LV: Linker V}
           (tr_fun: A -> res B):
  TransfLink (fun (p2: program (fundef B) V) (p1: program (fundef A) V) =>
              match_program
                (fun cu tf f => AST.transf_partial_fundef tr_fun f = OK tf)
                eq p2 p1).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros. eapply link_transf_partial_fundef_rev; eauto.
- intros; subst. exists v; auto.
Qed.

Instance TransfTotallContextualLink_rev
           {A B C V: Type} {LV: Linker V}
           (tr_fun: C -> A -> B)
           (ctx_for: program (fundef B) V -> C):
  TransfLink (fun (p2: program (fundef B) V) (p1: program (fundef A) V) =>
              match_program
                (fun cu tf f => tf = AST.transf_fundef (tr_fun (ctx_for cu)) f)
                eq p2 p1).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros. subst. destruct tf1, tf2; simpl in *.
+ discriminate.
+ destruct e; inv H2. econstructor; eauto.
+ destruct e; inv H2. econstructor; eauto.
+ destruct (external_function_eq e e0); inv H2. econstructor; eauto.
- intros; subst. exists v; auto.
Qed.

Instance TransfTotalLink_rev
           {A B V: Type} {LV: Linker V}
           (tr_fun: A -> B):
  TransfLink (fun (p2: program (fundef B) V) (p1: program (fundef A) V) =>
              match_program
                (fun cu tf f => tf = AST.transf_fundef tr_fun f)
                eq p2 p1).
Proof.
  red. intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
- intros. subst. destruct tf1, tf2; simpl in *.
+ discriminate.
+ destruct e; inv H2. econstructor; eauto.
+ destruct e; inv H2. econstructor; eauto.
+ destruct (external_function_eq e e0); inv H2. econstructor; eauto.
- intros; subst. exists v; auto.
Qed.


Section LINK_LIST_MATCH.

  Context {A B: Type} {LA: Linker A} {LB: Linker B} (prog_match: A -> B -> Prop) {TL: TransfLink prog_match}.

  Theorem link_list_aux_match al bl
          (MATCH:list_forall2 prog_match al bl)
    :
      forall a (SUCCESS: link_list_aux al = success a),
      exists b, link_list_aux bl = success b /\ prog_match a b.
  Proof.
    revert bl MATCH.
    induction al; ss; i; ss; inv MATCH; ss.
    destruct (link_list_aux al) eqn:EQ; clarify.
    - assert (al = []).
      { destruct al; ss.
        des_ifs. }
      clarify. inv H3. ss. eauto.
    - des_ifs_safe.
      exploit IHal; eauto. i. des. rewrite H.
      exploit TL; eauto. i. des. rewrite H2. eauto.
  Qed.

  Theorem link_list_match al bl
          (MATCH:list_forall2 prog_match al bl)
    :
      forall a, link_list al = Some a ->
                exists b, link_list bl = Some b /\ prog_match a b.
  Proof.
    i. unfold link_list in *. des_ifs_safe.
    exploit link_list_aux_match; eauto.
    i. des. rewrite H. eauto.
  Qed.

End LINK_LIST_MATCH.
