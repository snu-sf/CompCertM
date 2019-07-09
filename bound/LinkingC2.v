Require Import CoqlibC Maps Errors AST Linking LinkingC sflib.

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
  - des_ifs; clarify; inv H; des_ifs; eauto.
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
+ des_ifs; eauto.
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
+ des_ifs; econstructor; eauto.
- intros; subst. exists v; auto.
Qed.

Lemma link_list_app_commut
      X `{Linker X}
      x_link xs0 xs1
      (LINK: link_list xs1 = Some x_link)
  :
    <<CMT: link_list (xs0 ++ xs1) = link_list (xs0 ++ [x_link])>>
.
Proof.
  ginduction xs1; ii; ss.
  { unfold link_list in LINK. des_ifs. ss. des_ifs.
    { destruct xs1; ss. des_ifs. }
    replace (xs0 ++ a :: xs1) with ((xs0 ++ [a]) ++ xs1); cycle 1.
    { rewrite <- app_assoc. ss. }
    erewrite IHxs1; ss; cycle 1.
    { unfold link_list. rewrite Heq0. ss. }
    rewrite <- app_assoc. ss.
    erewrite link_list_snoc_commut; eauto.
  }
Qed.

Lemma stricter_link_list_aux X `{L0: Linker X} `{L1: Linker X}
      (STRICT: forall x0 x1 xl, (@link _ L1) x0 x1 = Some xl -> (@link _ L0) x0 x1 = Some xl)
      (l: list X) (x: X)
      (LINK: @link_list_aux _ L1 l = success x)
  :
    @link_list_aux _ L0 l = success x.
Proof.
  revert x LINK. induction l; ss.
  i. des_ifs; ss; clarify.
  - eapply link_list_aux_empty_inv in Heq. des. clarify.
  - eapply link_list_aux_empty_inv in Heq0. des. clarify.
  - exploit IHl; eauto. clarify.
  - eapply link_list_aux_empty_inv in Heq1. des. clarify.
  - exploit IHl; eauto. i. clarify. exploit STRICT; eauto. i. clarify.
  - eapply link_list_aux_empty_inv in Heq1. des. clarify.
  - exploit IHl; eauto. i. clarify. exploit STRICT; eauto. i. clarify.
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

Require Import CtypesC CsemC.

(* Copied from CtypesC. The only difference is it checks type on external-internal function linking *)

Definition link_fundef (fd1 fd2: fundef) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External ef1 targs1 tres1 cc1, External ef2 targs2 tres2 cc2 =>
      if external_function_eq ef1 ef2
      && typelist_eq targs1 targs2
      && type_eq tres1 tres2
      && calling_convention_eq cc1 cc2
      then Some (External ef1 targs1 tres1 cc1)
      else None
  | Internal f, External ef targs tres cc =>
    if (list_eq_dec type_eq f.(fn_params).(map snd) targs.(typelist_to_listtype))
         && (type_eq f.(fn_return) tres)
         && (calling_convention_eq f.(fn_callconv) cc)
    then
      match ef with EF_external id sg => if signature_eq (signature_of_type targs tres cc) sg then Some (Internal f) else None | _ => None end
    else None
  | External ef targs tres cc, Internal f =>
    if (list_eq_dec type_eq f.(fn_params).(map snd) targs.(typelist_to_listtype))
         && (type_eq f.(fn_return) tres)
         && (calling_convention_eq f.(fn_callconv) cc)
    then
      match ef with EF_external id sg => if signature_eq (signature_of_type targs tres cc) sg then Some (Internal f) else None | _ => None end
    else None
  end.

Inductive linkorder_fundef: fundef -> fundef -> Prop :=
  | linkorder_fundef_refl: forall fd,
      linkorder_fundef fd fd
  | linkorder_fundef_ext_int: forall f id sg targs tres cc,
      linkorder_fundef (External (EF_external id sg) targs tres cc) (Internal f).

Instance Linker_fundef: Linker (fundef) := {
  link := link_fundef;
  linkorder := linkorder_fundef
}.
Proof.
- intros; constructor.
- intros. inv H; inv H0; constructor.
- intros x y z EQ. destruct x, y; simpl in EQ.
+ discriminate.
+ des_ifs. split; constructor.
+ des_ifs. split; constructor.
+ des_ifs. bsimpl. des. des_sumbool. clarify. split; constructor.
Defined.

Definition link_program (p1 p2: program): option (program) :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      match lift_option (link p1.(prog_types) p2.(prog_types)) with
      | inright _ => None
      | inleft (exist typs EQ) =>
          match link_build_composite_env
                   p1.(prog_types) p2.(prog_types) typs
                   p1.(prog_comp_env) p2.(prog_comp_env)
                   p1.(prog_comp_env_eq) p2.(prog_comp_env_eq) EQ with
          | exist env (conj P Q) =>
              Some {| prog_defs := p.(AST.prog_defs);
                      prog_public := p.(AST.prog_public);
                      prog_main := p.(AST.prog_main);
                      prog_types := typs;
                      prog_comp_env := env;
                      prog_comp_env_eq := P |}
          end
      end
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  /\ (forall id co, p1.(prog_comp_env)!id = Some co -> p2.(prog_comp_env)!id = Some co).

Instance Linker_program: Linker (program) := {
  link := link_program;
  linkorder := linkorder_program
}.
Proof.
- intros; split. apply linkorder_refl. auto. 
- intros. destruct H, H0. split. eapply linkorder_trans; eauto.
  intros; auto.
- intros until z. unfold link_program. 
  destruct (link (program_of_program x) (program_of_program y)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types x) (prog_types y))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types x) (prog_types y) typs
       (prog_comp_env x) (prog_comp_env y) (prog_comp_env_eq x)
       (prog_comp_env_eq y) EQ) as (env & P & Q & R).
  destruct (link_linkorder _ _ _ LP).
  intros X; inv X.
  split; split; auto.
Defined.
