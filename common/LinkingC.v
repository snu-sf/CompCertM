(** copied && added "C" **)
Require Import CoqlibC Maps Errors ASTC.

(** newly added **)
Require Export Linking.
Require Import Axioms.
Require Import sflib.

Set Implicit Arguments.

Inductive link_res (A: Type): Type :=
| empty
| fail
| success: A -> link_res A.

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
  end.

Definition link_list X `{Linker X} (xs: list X): option X :=
  match link_list_aux xs with
  | empty => None (* Note that we are not giving semantics to empty programs. *)
  | success x => Some x
  | fail => None
  end.

Lemma link_list_cons
      X `{Linker X} hd tl restl res
      (TL: link_list tl = Some restl)
      (HD: link hd restl = Some res):
    <<LINK: link_list (hd :: tl) = Some res>> /\ <<LINKORDER: Forall (fun x => linkorder x res) (hd :: tl)>>.
Proof.
  split; red.
  - unfold link_list in *. des_ifs; ss; des_ifs.
  - eapply link_linkorder in HD. des. econs; auto. clear HD. unfold link_list in TL. des_ifs.
    generalize dependent restl. generalize dependent res.
    induction tl as [|h l]; auto. i. econs; unfold link_list_aux in *; des_ifs.
    { eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto. }
    { destruct l; auto. des_ifs. }
    eapply IHl; eauto. eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto.
Qed.

Lemma link_list_linkorder
      X `{Linker X} xs xs_res
      (LINK: link_list xs = Some xs_res):
    <<LINKORDER: Forall (fun x => linkorder x xs_res) xs>>.
Proof.
  destruct xs as [| hd tl]; auto.
  unfold link_list in LINK. des_ifs. unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. apply linkorder_refl. econs. des_ifs. }
  econs. { eapply link_linkorder in Heq1. des. auto. }
  assert (link_list tl = Some x).
  { unfold link_list. rewrite Heq0. auto. }
  exploit link_list_cons; eauto. i. des.
  inv LINKORDER. auto.
Qed.

Lemma link_list_cons_inv
      X `{Linker X} hd tl res
      (LINK: link_list (hd :: tl) = Some res)
      (LEN: tl <> []):
    exists restl, <<TL: link_list tl = Some restl>> /\ <<HD: link hd restl = Some res>>.
Proof.
  unfold link_list in LINK. des_ifs. unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. des_ifs. }
  exists x. split; auto. unfold link_list. rewrite Heq0. auto.
  Unshelve. auto.
Qed.

(* Just forget about nlist. We will use link_list in the final syntactic linking, too *)













Lemma link_list_aux_empty_inv
      X `{Linker X} xs
      (EMPTY: link_list_aux xs  = empty):
    <<NIL: xs = []>>.
Proof. ginduction xs; ii; ss. des_ifs. Qed.

Lemma link_list_snoc_commut
      X `{Linker X} x0 x1 x_link xs
      (LINK: link x0 x1 = Some x_link):
    <<CMT: link_list (xs ++ [x0 ; x1]) = link_list (xs ++ [x_link])>>.
Proof.
  ginduction xs; ii; ss.
  { unfold link_list. ss. des_ifs. }
  exploit IHxs; eauto. intro IH; des.
  unfold link_list in IH. unfold link_list. ss.
  des_ifs; apply_all_once link_list_aux_empty_inv; clarify; ss; destruct xs; ss.
Qed.

Lemma match_program_refl
      F V
      `{Linker F} `{Linker V}
      (prog: AST.program F V):
    match_program (fun _ => eq) eq prog prog.
Proof.
  econs; eauto. destruct prog; ss.
  ginduction prog_defs; ii; ss.
  { econs; eauto. }
  destruct a; ss. econs; eauto.
  - econs; eauto. ss. destruct g; ss.
    + econs; eauto. eapply linkorder_refl.
    + econs; eauto. destruct v; ss.
  - rpapply IHprog_defs; eauto.
    do 2 (apply Axioms.functional_extensionality; i; destruct x; ss).
    apply AxiomsC.prop_ext. split; ii; inv H1; ss; clarify; inv H3; econs; ss; eauto; econs; ss; eauto; apply linkorder_refl.
Unshelve.
  all: ss.
Qed.

Lemma match_globdef_eq
      C F V
      `{Linker C} ctx:
    match_globdef ((fun _ => eq): C -> F -> F -> Prop)
                  (eq: V -> V -> Prop)
                  ctx = eq.
Proof.
  do 2 (eapply Axioms.functional_extensionality; i).
  eapply AxiomsC.prop_ext. split; i.
  - inv H0; ss. inv H1; ss.
  - clarify. destruct x0; econs; try eapply linkorder_refl; eauto. destruct v; ss.
Qed.

Local Transparent Linker_def Linker_vardef Linker_varinit.

Lemma link_unit_same
      F (g g0: globdef F unit) (gv: globvar unit) `{Linker F}
      (LINK: link g g0 = Some (Gvar gv)):
    g = Gvar gv \/ g0 = Gvar gv.
Proof.
  ss. unfold link_def in *. des_ifs. ss. unfold link_vardef in *. destruct v; ss.
  des_ifs; bsimpl; des; des_sumbool; rewrite eqb_true_iff in *.
  destruct gvar_info; ss. destruct v0; ss. destruct gvar_info; ss. destruct u; ss.
  unfold link_varinit in *. des_ifs; eauto.
Qed.

Local Opaque Linker_def Linker_vardef Linker_varinit.

Definition link_skfundef (fd1 fd2: AST.fundef signature) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External ef1, External ef2 =>
    match ef1, ef2 with
    | EF_external _ sg1, EF_external _ sg2 => if signature_eq sg1 sg2 then Some (External ef1) else None
    | _, _ => if external_function_eq ef1 ef2 then Some (External ef1) else None
    end
  | Internal f, External ef =>
      match ef with
      | EF_external id sg =>
        if signature_eq f sg then Some (Internal f) else None
      | _ => None
      end
  | External ef, Internal f =>
      match ef with
      | EF_external id sg =>
        if signature_eq f sg then Some (Internal f) else None
      | _ => None
      end
  end.

Inductive linkorder_skfundef: AST.fundef signature -> AST.fundef signature -> Prop :=
  | linkorder_skfundef_refl: forall fd, linkorder_skfundef fd fd
  | linkorder_fundef_ext_ext: forall name0 name1 sg, linkorder_skfundef (External (EF_external name0 sg)) (External (EF_external name1 sg))
  | linkorder_skfundef_ext_int: forall id sg, linkorder_skfundef (External (EF_external id sg)) (Internal sg).

Program Instance Linker_skfundef: Linker (AST.fundef signature) :=
{| link := link_skfundef;
   linkorder := linkorder_skfundef;
|}.
Next Obligation. destruct x; econs; eauto. Qed.
Next Obligation. inv H; inv H0; econs; et. Qed.
Next Obligation.
  pose x as X. pose y as Y. destruct x, y; ss; des_ifs; esplits; eauto; try (econs; et).
Qed.


Definition link_option T `{Linker T} (t0 t1: option T): option T :=
  match t0, t1 with
  | Some t0, Some t1 => link t0 t1
  | Some t0, None => Some t0
  | None, Some t1 => Some t1
  | None, None => None
  end
.
Arguments link_option {T} {H}.