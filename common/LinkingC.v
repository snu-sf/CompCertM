(** copied && added "C" **)
Require Import CoqlibC Maps Errors ASTC.

(** newly added **)
Require Export Linking.
Require Import Axioms.
Require Import sflib.

Set Implicit Arguments.

(* TODO: Why Function does not work ??? *)
(* Program Fixpoint link_list X `{Linker X} (xs: list X) { measure (length xs) }: option X := *)
(*   match xs with *)
(*   | [] => None *)
(*   | x0 :: nil => Some x0 *)
(*   | x0 :: x1 :: tl => *)
(*     match (link x0 x1) with *)
(*     | Some x => link_list (x :: tl) *)
(*     | None => None *)
(*     end *)
(*   end *)
(* . *)

Inductive link_res (A: Type): Type :=
| empty
| fail
| success: A -> link_res A
.

Arguments empty [A].
Arguments fail [A].

Fixpoint link_list_aux X `{Linker X} (xs: list X): link_res X :=
  match xs with
  | [] => empty
  | x0 :: tl =>
    match link_list_aux tl with
    | empty => success x0
    | fail => fail
    | success x1 =>
      match link x0 x1 with
      | Some x => success x
      | None => fail
      end
    end
  end
.

Definition link_list X `{Linker X} (xs: list X): option X :=
  match link_list_aux xs with
  | empty => None (* Note that we are not giving semantics to empty programs. *)
  | success x => Some x
  | fail => None
  end
.

Lemma link_list_cons
      X `{Linker X}
      hd tl restl res
      (TL: link_list tl = Some restl)
      (HD: link hd restl = Some res)
  :
    <<LINK: link_list (hd :: tl) = Some res>> /\ <<LINKORDER: Forall (fun x => linkorder x res) (hd :: tl)>>
.
Proof.
  split; red.
  - unfold link_list in *. des_ifs; ss; des_ifs.
  - eapply link_linkorder in HD. des.
    econs; auto. clear HD.
    unfold link_list in TL. des_ifs.
    generalize dependent restl. generalize dependent res.
    induction tl as [|h l]; auto.
    i. econs; unfold link_list_aux in *; des_ifs.
    { eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto. }
    { destruct l; auto. des_ifs. }
    eapply IHl; eauto. eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto.
Qed.

Lemma link_list_linkorder
      X `{Linker X}
      xs xs_res
      (LINK: link_list xs = Some xs_res)
  :
    <<LINKORDER: Forall (fun x => linkorder x xs_res) xs>>
.
Proof.
  destruct xs as [| hd tl]; auto.
  unfold link_list in LINK. des_ifs.
  unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. apply linkorder_refl. econs. des_ifs. }
  econs. { eapply link_linkorder in Heq1. des. auto. }
  assert (link_list tl = Some x).
  { unfold link_list. rewrite Heq0. auto. }
  exploit link_list_cons; eauto. i. des.
  inv LINKORDER. auto.
Qed.

Lemma link_list_cons_inv
      X `{Linker X}
      hd tl res
      (LINK: link_list (hd :: tl) = Some res)
      (LEN: tl <> [])
  :
    exists restl, <<TL: link_list tl = Some restl>> /\ <<HD: link hd restl = Some res>>
.
Proof.
  unfold link_list in LINK. des_ifs.
  unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. des_ifs. }
  exists x. split; auto.
  unfold link_list. rewrite Heq0. auto.
  Unshelve. auto.
Qed.

(* Just forget about nlist. We will use link_list in the final syntactic linking, too *)









Section LINKER_PROG.

Context {F V: Type} {LF: Linker F} {LV: Linker V} (p1 p2: program F V).

Let dm1 := prog_defmap p1.
Let dm2 := prog_defmap p2.

Inductive link_prog_spec (p: program F V): Prop :=
| link_prog_spec_intro
    (MAIN: p.(prog_main) = p1.(prog_main) /\ p.(prog_main) = p2.(prog_main))
    (PUBLIC: p.(prog_public) = p1.(prog_public) ++ p2.(prog_public))
    (DEFS: p.(prog_defs) = PTree.elements (PTree.combine link_prog_merge dm1 dm2))
    (BOTHHIT: (forall id gd1 gd2,
                  dm1!id = Some gd1 -> dm2!id = Some gd2 ->
                  In id p1.(prog_public) /\ In id p2.(prog_public) /\ exists gd, link gd1 gd2 = Some gd))
    (DEFREL: (forall id, p.(prog_defmap)!id = link_prog_merge (dm1!id) (dm2!id)))
    (LARGEHIT: (forall id gd,
                   p.(prog_defmap)!id = Some gd ->
                   (exists gd1, dm1!id = Some gd1) \/ (exists gd2, dm2!id = Some gd2)))
    (SMALLHIT: (forall id,
                   (exists gd1, dm1!id = Some gd1) \/ (exists gd2, dm2!id = Some gd2) ->
                   exists gd, p.(prog_defmap)!id = Some gd))
    (PRIVS_OLDPEC0: (forall id,
                    p1.(privs_old) id ->
                    p.(prog_defmap)!id = dm1!id /\ dm2!id = None))
    (PRIVS_OLDPEC1: (forall id,
                    p2.(privs_old) id ->
                    p.(prog_defmap)!id = dm2!id /\ dm1!id = None))
.

Lemma link_prog_inv
      p
      (LINK: link_prog p1 p2 = Some p)
  :
    <<SPEC: link_prog_spec p>>
.
Proof.
  assert(GOOD1: good_prog p1) by admit "good".
  assert(GOOD2: good_prog p2) by admit "good".

  hexploit (link_prog_inv _ _ _ LINK). intro LINKSPEC; des.
  assert(MAIN: prog_main p = prog_main p1 /\ prog_main p = prog_main p2).
  { clarify; ss. }
  assert(PUBLIC: prog_public p = prog_public p1 ++ prog_public p2).
  { clarify; ss. }
  assert(DEFS: prog_defs p = PTree.elements (PTree.combine link_prog_merge dm1 dm2)).
  { clarify; ss. }

  clear LINKSPEC1. (* "clarify"ing this will ruin everything; instead we use MAIN+PUBLIC+DEFS *)

  assert(DEFREL: forall id : positive, (prog_defmap p) ! id = link_prog_merge dm1 ! id dm2 ! id).
  {
    ii.
    clarify.
    unfold prog_defmap; ss.
    rewrite DEFS.
    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine; ss.
  }

  econs; eauto.
  {
    (* Corollary *)
    ii. erewrite DEFREL in H. unfold link_prog_merge in H.
    des_ifs; (try by left; esplits; eauto); (try by right; esplits; eauto).
  }
  {
    unfold link_prog in *.
    destruct (ident_eq (prog_main p1) (prog_main p2)); try discriminate.
    destruct (PTree_Properties.for_all (prog_defmap p1) (link_prog_check p1 p2)) eqn:C; ss.
    rewrite PTree_Properties.for_all_correct in C.
    ii. rewrite DEFREL. des.
    - rewrite H. ss. exploit C; eauto. intro D. unfold link_prog_check in D.
      fold dm2 in D.
      des_ifs; (try by esplits; ss).
      simpl_bool; ss.
    - rewrite H. ss.
      destruct (dm1!id) eqn:T; (try by esplits; eauto).
      exploit C; eauto. intro D. unfold link_prog_check in D.
      fold dm2 in D. ss.
      des_ifs; (try by esplits; ss).
      simpl_bool; ss.
  }
  {
    intros id PRIV.
    Fail hexploit (link_linkorder _ _ _ LINK); eauto.
    hexploit (@link_linkorder (program F V) (Linker_prog _ _)); eauto.
    intro ORD; des; ss.
    Local Transparent Linker_prog.
    ss.
    Local Opaque Linker_prog.
    des.
    u in *; des.
    split; ss.
    - exploit ORD4; eauto. i; des.
      rewrite H. rewrite H1; ss.
      rewrite PUBLIC. intro IN. apply in_app_iff in IN.
      des; ss.
      exploit GOOD2; eauto. i; ss.
      exploit prog_defmap_dom; eauto.
      i; des.
      exploit LINKSPEC0; eauto. i; des. ss.
    - destruct (dm2!id) eqn:T; ss.
      exploit LINKSPEC0; eauto. i; des. ss.
  }
  {
    intros id PRIV.
    hexploit (@link_linkorder (program F V) (Linker_prog _ _)); eauto.
    intro ORD; des; ss.
    Local Transparent Linker_prog.
    ss.
    Local Opaque Linker_prog.
    des.
    u in *; des.
    split; ss.
    - exploit ORD2; eauto. i; des.
      rewrite H. rewrite H1; ss.
      rewrite PUBLIC. intro IN. apply in_app_iff in IN.
      des; ss.
      exploit GOOD1; eauto. i; ss.
      exploit prog_defmap_dom; eauto.
      i; des.
      exploit LINKSPEC0; eauto. i; des. ss.
    - destruct (dm1!id) eqn:T; ss.
      exploit LINKSPEC0; eauto. i; des. ss.
  }
Qed.

Corollary link_prog_private_exclusive
          p
          (LINK: link_prog p1 p2 = Some p)
          id
          (PRIV1: p1.(privs_old) id)
          (PRIV2: p2.(privs_old) id)
  :
    False
.
Proof.
  u in *.
  des.
  hexploit (link_prog_inv LINK). intro LINKSPEC; inv LINKSPEC.
  exploit BOTHHIT; eauto. i; des. clarify.
Qed.

Lemma link_prog_private_rev
      p
      (LINK: link_prog p1 p2 = Some p)
  :
    forall id, p.(privs_old) id -> p1.(privs_old) id \/ p2.(privs_old) id
.
Proof.
  hexploit (link_prog_inv LINK). intro LINKSPEC; inv LINKSPEC.
  i.
  u in *. des.
  rewrite PUBLIC in *.
  exploit LARGEHIT; eauto. i; des.
  - left; esplits; eauto.
    ii. apply H0. apply in_app_iff. tauto.
  - right; esplits; eauto.
    ii. apply H0. apply in_app_iff. tauto.
Qed.

Lemma link_prog_private
      p
      (LINK: link_prog p1 p2 = Some p)
      (GOOD1: good_prog p1)
      (GOOD2: good_prog p2)
  :
    forall id, p1.(privs_old) id \/ p2.(privs_old) id -> p.(privs_old) id
.
Proof.
  hexploit (link_prog_inv LINK). intro LINKSPEC; inv LINKSPEC.
  (* apply Axioms.functional_extensionality. i. *)
  (* rewrite ClassicalFacts.prop_extensionality. *)
  i. u in *; ss.
  unfold prog_defmap in *; ss.
  rewrite PUBLIC in *.
  des.
  - exploit SMALLHIT; eauto. i; des.
    esplits; eauto.
    intro IN.
    apply in_app_iff in IN. des; ss.
    rewrite DEFS in H1.
    rewrite PTree_Properties.of_list_elements in H1.
    assert(exists gd2, dm2!id = Some gd2).
    { hnf in GOOD2. hexploit GOOD2; eauto. intro INDEF.
      unfold dm2.
      (* destruct p2; ss. unfold prog_defmap in INDEF. ss. *)
      (* apply in_map_iff in INDEF. des. clarify. destruct x; ss. *)
      (* erewrite PTree.elements_complete; eauto. *)
      destruct p2; ss. unfold prog_defs_names in INDEF. ss.
      apply PTree_Properties.of_list_dom; ss.
    }
    des.
    exploit BOTHHIT; eauto.
    i; des. ss.
  - exploit SMALLHIT; eauto. i; des.
    esplits; eauto.
    intro IN.
    apply in_app_iff in IN. des; ss.
    rewrite DEFS in H1.
    rewrite PTree_Properties.of_list_elements in H1.
    assert(exists gd1, dm1!id = Some gd1).
    { hnf in GOOD1. hexploit GOOD1; eauto. intro INDEF.
      apply PTree_Properties.of_list_dom; ss.
    }
    des.
    exploit BOTHHIT; eauto.
    i; des. ss.
Qed.

Axiom prop_ext: ClassicalFacts.prop_extensionality.

Lemma link_prog_private_eq
      p
      (LINK: link_prog p1 p2 = Some p)
      (GOOD1: good_prog p1)
      (GOOD2: good_prog p2)
  :
    p.(privs_old) = (p1.(privs_old) \1/ p2.(privs_old))
.
Proof.
  symmetry.
  apply functional_extensionality. ii.
  apply prop_ext.
  split; ss.
  - apply link_prog_private; ss.
  - apply link_prog_private_rev; ss.
Qed.

(* Corollary link_prog_private_public *)
(*           p *)
(*           (LINK: link_prog p1 p2 = Some p) *)
(*           id gd *)
(*           (FIND: p.(prog_defmap)!id = Some gd) *)
(*   : *)
(*     (* <<PUBLIC: In id p.(prog_public)>> \/ *) *)
(*     <<PUBLIC: In id p1.(prog_public) /\ In id p2.(prog_public)>> \/ *)
(*     <<PRIVATE1: is_private id p1 /\ ~ is_private id p2>> \/ *)
(*     <<PRIVATE2: ~ is_private id p1 /\ is_private id p2>> *)
(* . *)
(* Proof. *)
(*   hexploit (link_prog_inv _ _ _ LINK). intro LINKSPEC; des. clarify. ss. *)
(*   unfold prog_defmap in FIND. ss. *)
(*   rewrite PTree_Properties.of_list_elements in FIND. *)
(*   rewrite PTree.gcombine in FIND; ss. *)
(*   unfold link_prog_merge in FIND. *)
(*   des_ifs. *)
(*   - left. exploit LINKSPEC0; eauto. i; des. clarify. *)
(*   - right. left. *)
(*     esplits; eauto. *)
(*     + hnf. esplits; eauto. admit "this does not hold". *)
(*     + ii. inv H. des; ss. apply PRIV. admit "??". *)
(* Abort. *)



End LINKER_PROG.




