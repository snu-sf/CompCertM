Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

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

Set Implicit Arguments.


(*** TODO: move to CoqlibC ***)
Tactic Notation "renames" ident(a) "into"
       ident(x) :=
  rename a into x.

Tactic Notation "renames" ident(a) ident(b) "into"
       ident(x) ident(y) :=
  rename a into x; rename b into y.

Tactic Notation "renames" ident(a) ident(b) ident(c) "into"
       ident(x) ident(y) ident(z) :=
  rename a into x; rename b into y; rename c into z.

Tactic Notation "renames" ident(a) ident(b) ident(c) ident(d) "into"
       ident(x) ident(y) ident(z) ident(w) :=
  rename a into x; rename b into y; rename c into z; rename d into w.




Ltac des_bool :=
  repeat
    (match goal with
     | H: andb ?a ?b = true |- _ =>
       apply andb_true_iff in H;
       let H1 := fresh H in
       let H2 := fresh H in
       destruct H as [H1 H2]
     | H: andb ?a ?b = false |- _ => apply andb_false_iff in H
     end).

Ltac des_matchH H n :=
  match goal with
  | H':context [ if ?X then _ else _ ] |- _ =>
    let n' := fresh n in
    check_equal H' H; destruct X eqn: n
  | H':context [ match ?X with _ => _ end ] |- _ =>
    let n' := fresh n in
    check_equal H' H; destruct X eqn: n
  end.

Definition link_assoc F `{Linker F} : Prop :=
  forall (f0 f1 f2: F),
    match (link f0 f1) with
    | Some f01 => link f01 f2
    | _ => None
    end =
    match (link f1 f2) with
    | Some f12 => link f0 f12
    | _ => None
    end.
Arguments link_assoc F {_}.

Require Import mktac.

Lemma classify_init_case l
  :
    (<<EXTERN: l = []>>) \/
    (<<COMMON: exists sz, l = [Init_space sz]>>) \/
    (<<DEFINITIVE: classify_init l = Init_definitive l>>).
Proof.
  destruct l; ss; eauto. right. destruct i, l; ss; eauto.
Qed.

Lemma Z_max_double n m
  :
    Z.max (Z.max n m) m = Z.max n m.
Proof.
  unfold Z.max in *. des_ifs; clarify.
  - eapply Z.compare_eq in Heq0. eauto.
  - congruence.
Qed.

Lemma init_data_list_size_max_zero l
  :
    Z.max (init_data_list_size l) 0 = (init_data_list_size l).
Proof.
  unfold Z.max. des_ifs.
  set (init_data_list_size_pos l).
  exfalso. unfold Z.ge in *. auto.
Qed.

Lemma link_varinit_assoc
  :
    link_assoc (list init_data).
Proof.
  ii. Local Transparent Linker_varinit. ss. unfold link_varinit.
  set (classify_init_case f0).
  set (classify_init_case f1).
  set (classify_init_case f2). des; clarify; ss; des_ifs; ss; clarify; zsimpl.
  - rewrite Z_max_double in *. clarify.
  - repeat rewrite init_data_list_size_max_zero in *. f_equal. auto.
  - rewrite Z_max_double in *. clarify.
  - rewrite Z_max_double in *. clarify.
  - repeat rewrite init_data_list_size_max_zero in *. f_equal. auto.
  - repeat rewrite init_data_list_size_max_zero in *. clarify.
  - repeat rewrite init_data_list_size_max_zero in *. clarify.
  - repeat rewrite init_data_list_size_max_zero in *. f_equal. auto.
  - repeat rewrite init_data_list_size_max_zero in *. clarify.
  - repeat rewrite init_data_list_size_max_zero in *. clarify.
Qed.

Lemma link_vardef_assoc
      V `{Linker V}
      (ASSOCV: link_assoc V)
  :
    link_assoc (globvar V).
Proof.
  ii. Local Transparent Linker_vardef. ss. unfold link_vardef. des_ifs; ss.
  - f_equal. f_equal; ss.
    + specialize (ASSOCV (gvar_info f0) (gvar_info f1) (gvar_info f2)).
      rewrite Heq3 in *. rewrite Heq7 in *. rewrite Heq0 in *. rewrite Heq4 in *. clarify.
    + specialize (link_varinit_assoc (gvar_init f0) (gvar_init f1) (gvar_init f2)). i. ss.
      rewrite Heq10 in *. rewrite Heq8 in *. rewrite Heq1 in *. rewrite Heq5 in *. clarify.
  - exfalso. unfold proj_sumbool, andb in *. des_ifs.
  - exfalso.
    specialize (link_varinit_assoc (gvar_init f0) (gvar_init f1) (gvar_init f2)). i. ss.
    rewrite Heq9 in *. rewrite Heq7 in *. rewrite Heq1 in *. rewrite Heq5 in *. clarify.
  - exfalso.
    specialize (ASSOCV (gvar_info f0) (gvar_info f1) (gvar_info f2)).
    rewrite Heq3 in *. rewrite Heq5 in *. rewrite Heq0 in *. rewrite Heq4 in *. clarify.
  - exfalso. destruct f0, f1, f2. ss. unfold andb, eqb in *. des_ifs.
  - exfalso.
    specialize (link_varinit_assoc (gvar_init f0) (gvar_init f1) (gvar_init f2)). i. ss.
    rewrite Heq7 in *. rewrite Heq5 in *. rewrite Heq1 in *. clarify.
  - exfalso.
    specialize (ASSOCV (gvar_info f0) (gvar_info f1) (gvar_info f2)).
    rewrite Heq5 in *. rewrite Heq4 in *. rewrite Heq0 in *. clarify.
  - exfalso. destruct f0, f1, f2. ss. unfold andb, eqb in *. des_ifs.
  - exfalso.
    specialize (link_varinit_assoc (gvar_init f0) (gvar_init f1) (gvar_init f2)). i. ss.
    rewrite Heq9 in *. rewrite Heq7 in *. rewrite Heq4 in *. rewrite Heq1 in *. clarify.
  - exfalso.
    specialize (ASSOCV (gvar_info f0) (gvar_info f1) (gvar_info f2)).
    rewrite Heq1 in *. rewrite Heq5 in *. rewrite Heq2 in *. rewrite Heq0 in *. clarify.
  - exfalso. unfold proj_sumbool, andb in *. des_ifs.
  - exfalso.
    specialize (link_varinit_assoc (gvar_init f0) (gvar_init f1) (gvar_init f2)). i. ss.
    rewrite Heq7 in *. rewrite Heq5 in *. rewrite Heq2 in *. clarify.
  - exfalso.
    specialize (ASSOCV (gvar_info f0) (gvar_info f1) (gvar_info f2)).
    rewrite Heq0 in *. rewrite Heq4 in *. rewrite Heq1 in *. clarify.
Qed.

Lemma link_def_assoc
      F V `{Linker F} `{Linker V}
      (ASSOCF: link_assoc F)
      (ASSOCV: link_assoc V)
  :
    link_assoc (globdef F V).
Proof.
  ii. Local Transparent Linker_def. ss. unfold link_def. des_ifs; repeat f_equal.
  - specialize (ASSOCF f4 f6 f3).
    rewrite Heq1 in *. rewrite Heq3 in *. rewrite ASSOCF in *. clarify.
  - specialize (ASSOCF f4 f5 f3).
    rewrite Heq1 in *. rewrite Heq3 in *. rewrite ASSOCF in *. clarify.
  - specialize (ASSOCF f1 f4 f3).
    rewrite Heq3 in *. rewrite Heq2 in *. rewrite ASSOCF in *. clarify.
  - specialize (ASSOCF f2 f5 f3).
    rewrite Heq1 in *. rewrite Heq3 in *. rewrite ASSOCF in *. clarify.
  - specialize (link_vardef_assoc ASSOCV v1 v3 v0). i. ss.
    rewrite Heq1 in *. rewrite Heq0 in *. rewrite Heq3 in *. rewrite Heq2 in *. clarify.
  - specialize (link_vardef_assoc ASSOCV v1 v3 v0). i. ss.
    rewrite Heq1 in *. rewrite Heq0 in *. rewrite Heq3 in *. rewrite Heq2 in *. clarify.
  - specialize (link_vardef_assoc ASSOCV v2 v1 v0). i. ss.
    rewrite Heq3 in *. rewrite Heq0 in *. rewrite Heq2 in *. clarify.
  - specialize (link_vardef_assoc ASSOCV v1 v3 v0). i. ss.
    rewrite Heq1 in *. rewrite Heq0 in *. rewrite Heq3 in *. rewrite Heq2 in *. clarify.
  - specialize (ASSOCF f f4 f1).
    rewrite Heq2 in *. rewrite Heq1 in *. rewrite Heq0 in *. clarify.
  - specialize (link_vardef_assoc ASSOCV v v1 v2). i. ss.
    rewrite Heq2 in *. rewrite Heq1 in *. rewrite Heq0 in *. clarify.
Qed.

(* above by Minki *)

Lemma link_ef_either
      e1 e2 f3
      (L: link (AST.External e1) (AST.External e2) = Some f3)
  : f3 = AST.External e1 \/ f3 = AST.External e2.
Proof.
  unfold link in *. ss.
  destruct e1, e2; desf; eauto.
Qed.

(* Lemma link_ef_inv *)
(*       e1 e2 f3 *)
(*       (EF1: is_external_ef e1 = true) *)
(*       (EF2: is_external_ef e2 = true) *)
(*       (L: link (AST.External e1) (AST.External e2) = Some f3) *)
(*   : exists e3, f3 = AST.External e3 /\ is_external_ef e3. *)
(* Proof. *)
(*   destruct e1; ss. *)
(*   destruct e2; ss. *)
(*   desf. eexists. split; eauto. *)
(* Qed. *)

Lemma link_nef_inv
      e1 e2 f3
      (EF1: is_external_ef e1 = false)
      (EF2: is_external_ef e2 = false)
      (L: link (AST.External e1) (AST.External e2) = Some f3)
  : e1 = e2 /\ f3 = AST.External e1.
Proof.
  destruct e1; destruct e2; ss; desf.
Qed.

Lemma link_ef_no
      e1 e2
      (EF1: xorb (is_external_ef e1) (is_external_ef e2))
  : link (AST.External e1) (AST.External e2) = None.
Proof.
  destruct e1; destruct e2; desf.
Qed.

Lemma link_external_assoc e0 e1 e2
  : match link (AST.External e0) (AST.External e1) with
    | Some e01 => link e01 (AST.External e2)
    | None => None
    end = match link (AST.External e1) (AST.External e2) with
          | Some e12 => link (AST.External e0) e12
          | None => None
          end.
Proof.
  destruct (is_external_ef e0) eqn: EXT_EF0;
    destruct (is_external_ef e1) eqn: EXT_EF1.
  - destruct e0; ss. destruct e1; ss.
    destruct (is_external_ef e2) eqn: EXT_EF2.
    + destruct e2; ss.
      desf; ss; desf.
    + exploit (link_ef_no (EF_external name sg) e2); eauto; [desf| ]. i.
      desf.
  - exploit (link_ef_no e0 e1); eauto; [desf| ]. i.
    desf. symmetry.
    destruct (is_external_ef e2) eqn: EXT_EF2.
    + exploit (link_ef_no e1 e2); eauto; [desf| ]. i.
      congruence.
    + exploit (link_nef_inv e1 e2); eauto. i. des. clarify.
  - exploit (link_ef_no e0 e1); eauto; [desf| ]. i.
    desf. symmetry.
    destruct (is_external_ef e2) eqn: EXT_EF2.
    + exploit link_ef_either; eauto. i. des; clarify.
      apply link_ef_no. desf.
    + exploit (link_ef_no e1 e2); eauto; [desf| ]. i.
      congruence.
  - destruct (link (AST.External e0) (AST.External e1)) eqn:L01.
    + exploit (link_nef_inv e0 e1); eauto. i. des. clarify.
      destruct (is_external_ef e2) eqn: EXT_EF2.
      { exploit (link_ef_no e1 e2); eauto; [by desf|]. i.
        desf. }
      { desf.
        exploit (link_nef_inv e1 e2); eauto. i. des. clarify. }
    + destruct (is_external_ef e2) eqn: EXT_EF2.
      { exploit (link_ef_no e1 e2); eauto; [by desf|]. i.
        desf. }
      { desf.
        exploit (link_nef_inv e1 e2); eauto. i. des. clarify. }
Qed.

Lemma link_skfundef_assoc
  : link_assoc (AST.fundef signature).
Proof.
  unfold link_assoc. i.
  destruct f0 as [s0| e0]; destruct f1 as [s1| e1];
    destruct f2 as [s2| e2];
    first [by apply link_external_assoc | ss; desf; ss; desf].
Qed.

Corollary link_skdef_assoc
  : link_assoc (AST.globdef (AST.fundef signature) unit).
Proof.
  apply link_def_assoc; ss.
  apply link_skfundef_assoc.
Qed.

Lemma link_sk_assoc
      (m1 m2 m3: Sk.t)
      (WF1: Sk.wf m1)
      (WF2: Sk.wf m2)
      (WF3: Sk.wf m3)
  : match (link m1 m2) with
    | Some m12 => link m12 m3
    | _ => None
    end =
    match (link m2 m3) with
    | Some m23 => link m1 m23
    | _ => None
    end.
Proof.
  Local Transparent Linker_prog Linker_def.
  destruct (link m2 m3) as [m23|] eqn: L2_3.
  2: {
    ss. unfold link_prog in *. desf. ss.
    exfalso.

    renames Heq Heq1 Heq0 into P2_3F P1_2S P12_3S.

    des_bool. des.
    { unfold ident_eq in *.
      unfold proj_sumbool in *. desf.
      congruence.
    }
    renames P1_2S1 P12_3S1 into P1_2S P12_3S.

    rewrite PTree_Properties.for_all_false in P2_3F.
    destruct P2_3F as [x [d2 [DEF2 L2_3F]]].

    rewrite PTree_Properties.for_all_correct in P1_2S. specialize (P1_2S x).
    rewrite PTree_Properties.for_all_correct in P12_3S. specialize (P12_3S x).

    destruct ((prog_defmap m1) ! x) as [d1|] eqn: DEF1.
    - exploit P1_2S; eauto. intro C1_2S. clear P1_2S.
      unfold link_prog_check in C1_2S.
      rewrite DEF2 in C1_2S. desf.
      2: { des_bool. ss. }
      renames g Heq into d12 L1_2S.

      exploit P12_3S.
      { rewrite prog_defmap_elements.
        rewrite PTree.gcombine by ss.
        rewrite DEF1. rewrite DEF2. ss. eauto.
      }
      (* clear - LINK12 C2_3F. intro C12_3. *)
      clear P12_3S. intro C12_3S.
      unfold link_prog_check in *.
      destruct ((prog_defmap m3) ! x) as [d3|] eqn: DEF3; ss.

      des_bool.
      destruct L2_3F as [? | L2_3F'].
      { desf. }
      destruct (link_def d2 d3) as [d23| ] eqn: L2_3F; desf.
      renames g Heq into d123 L12_3S.

      assert (match link d1 d2 with
              | Some d12 => link d12 d3
              | None => None
              end = match link d2 d3 with
                    | Some d23 => link d1 d23
                    | None => None
                    end).
      { apply link_def_assoc.
        - apply link_skfundef_assoc.
        - ss. }
      unfold link in *. ss. desf.
    - clear P1_2S.
      exploit P12_3S.
      { rewrite prog_defmap_elements.
        rewrite PTree.gcombine by ss.
        rewrite DEF1. rewrite DEF2. ss.
      }
      clear P12_3S. intro C12_3S.
      destruct ((prog_defmap m3) ! x) as [d3| ] eqn: DEF3.
      2: { unfold link_prog_check in *. desf. }

      unfold link_prog_check in *. desf.
      2: { clear -C12_3S. des_bool. ss. }

      des_bool. des; ss.
      des_bool. des.
      + assert (IN1: In x (AST.prog_public m1)).
        { unfold proj_sumbool in *.
          desf.
          rewrite in_app in *. des; ss.
        }
        inv WF1.
        exploit PUBINCL; eauto.
        i. exploit prog_defmap_dom; eauto. i. des.
        congruence.
      + congruence.
  }

  (* link 2_3 succ *)
  destruct (link m1 m2) as [m12|] eqn: L1_2S.
  2: { (* link 1_2 fail *)
    ss. unfold link_prog in L2_3. unfold link_prog in L1_2S.
    desf.
    renames Heq0 Heq into C2_3S C1_2F.
    des_bool. rename C2_3S1 into P2_3S. des.
    { unfold link_prog. ss. desf. }

    rewrite PTree_Properties.for_all_false in C1_2F.
    destruct C1_2F as [x [d1 [DEF1 L1_2F]]].

    rewrite PTree_Properties.for_all_correct in P2_3S. specialize (P2_3S x).
    unfold link_prog_check in L1_2F.
    destruct ((prog_defmap m2) ! x) as [d2| ] eqn: DEF2; ss.
    exploit P2_3S; eauto.
    clear P2_3S. intro C2_3S.

    des_bool. des.
    { des_bool. des.
      - unfold link_prog. ss. desf. exfalso.
        rename Heq into P1_23S. des_bool.
        rename P1_23S1 into P1_23S.
        rewrite PTree_Properties.for_all_correct in P1_23S.
        exploit P1_23S; eauto. clear P1_23S. intro C1_23S.
        unfold link_prog_check in C1_23S. desf.
        clear C1_23S. rename Heq into C1_23S.

        rewrite prog_defmap_elements in C1_23S.
        rewrite PTree.gcombine in C1_23S by ss.

        clear - DEF2 C2_3S C1_23S.
        unfold link_prog_check, link_prog_merge in *. desf.
        des_bool. ss.

      - unfold link_prog. ss. desf. exfalso.
        rename Heq into P1_23S. des_bool.
        rename P1_23S1 into P1_23S.
        rewrite PTree_Properties.for_all_correct in P1_23S.
        exploit P1_23S; eauto. clear P1_23S. intro C1_23S.

        unfold link_prog_check in C2_3S. ss.
        destruct ((prog_defmap m3) ! x) as [d3|] eqn: DEF3.
        { desf. }

        assert (NOT_IN3: ~ In x (AST.prog_public m3)).
        { ii. inv WF3.
          exploit PUBINCL; eauto. i.
          exploit prog_defmap_dom; eauto. i. des. congruence.
        }

        unfold link_prog_check in C1_23S.
        rewrite prog_defmap_elements in C1_23S. ss.
        rewrite PTree.gcombine in C1_23S by ss.
        rewrite DEF2 in C1_23S. rewrite DEF3 in C1_23S. ss.

        des_bool.
        clear - L1_2F C1_23S3 NOT_IN3.
        des_sumbool. rewrite in_app in *. des; ss.
    }

    desf. clear L1_2F. rename Heq into L1_2F.

    unfold link_prog. ss. desf. exfalso.
    rename Heq into P1_23S. des_bool.
    rename P1_23S1 into P1_23S.

    rewrite PTree_Properties.for_all_correct in P1_23S.
    exploit P1_23S; eauto. clear P1_23S. intro C1_23S.

    destruct ((prog_defmap m3)! x) as [d3|] eqn: DEF3.
    - assert (exists d23, link_def d2 d3 = Some d23).
      { clear C1_23S.
        unfold link_prog_check in *.
        rewrite DEF3 in *.
        des_bool. ss. desf. esplits; eauto.
      }
      des.

      assert (exists d123, link_def d1 d23 = Some d123).
      { clear C2_3S.
        unfold link_prog_check in *.
        rewrite prog_defmap_elements in C1_23S.
        rewrite PTree.gcombine in * by ss.
        rewrite DEF2 in *. rewrite DEF3 in *. ss.
        desf.
        { esplits; eauto. }

        exfalso.
        des_bool. ss.
      }
      des.

      assert (match link_def d1 d2 with
              | Some d12 => link_def d12 d3
              | None => None
              end =
              match link_def d2 d3 with
              | Some d23 => link_def d1 d23
              | None => None
              end).
      { apply link_def_assoc.
        - apply link_skfundef_assoc.
        - ss.
      }
      desf. congruence.
    - unfold link_prog_check in C1_23S.
      rewrite prog_defmap_elements in C1_23S. ss.
      rewrite PTree.gcombine in C1_23S by ss.
      rewrite DEF2 in C1_23S. rewrite DEF3 in C1_23S. ss.
      des_bool. desf.
  }

  (* all succ *)

  unfold link in *. ss.

  destruct (link_prog m12 m3) as [[? ? ?]|] eqn: L12_3.
  2: {
    unfold link_prog in *.

    des_matchH L1_2S L1_2_COND; ss.
    des_matchH L12_3 L12_3_COND; ss.
    des_matchH L2_3 L2_3_COND; ss.
    clarify. des_bool.

    des.
    - exfalso. des_sumbool. ss. congruence.
    - rewrite PTree_Properties.for_all_correct in *.
      rewrite PTree_Properties.for_all_false in *. des.
      destruct ((prog_defmap m1) ! x) as [gd1|] eqn: DEF1.
      + exploit L1_2_COND1; eauto.
        unfold link_prog_check.
        destruct ((prog_defmap m2) ! x) as [gd2|] eqn: DEF2.
        2: {
          i. rewrite prog_defmap_elements in L12_3_COND.
          rewrite PTree.gcombine in * by ss.
          rewrite DEF1 in *. rewrite DEF2 in *. ss.
          symmetry in L12_3_COND. clarify.
          unfold link_prog_check in L12_3_COND0. ss.

          destruct ((prog_defmap m3) ! x) as [gd3|] eqn: DEF3; ss.
          desf.
          - exfalso.
            rename Heq into P1_23.
            rewrite PTree_Properties.for_all_correct in *.
            exploit P1_23; eauto. clear P1_23.
            rewrite prog_defmap_elements.
            rewrite PTree.gcombine by ss.
            rewrite DEF2. ss.
            des_bool. des; ss. des_bool.
            rewrite DEF3.
            do 2 rewrite andb_true_iff. i. desf.
            + des_sumbool.
              apply L12_3_COND0. apply in_app. eauto.
            + des_sumbool.
              rewrite in_app in *. des; ss.
              inv WF2. exploit PUBINCL; eauto.
              i. exploit prog_defmap_dom; eauto. i. des. congruence.

          - exfalso.
            rename Heq into P1_23.
            rewrite PTree_Properties.for_all_correct in *.
            exploit P1_23; eauto. clear P1_23.
            rewrite prog_defmap_elements.
            rewrite PTree.gcombine by ss.
            rewrite DEF2. rewrite DEF3. ss.
            do 2 rewrite andb_true_iff. i. des. desf.
        }

        i. des_bool.
        destruct (link gd1 gd2) as [gd12| ] eqn: L1_2; ss.

        rewrite prog_defmap_elements in L12_3_COND.
        rewrite PTree.gcombine in * by ss.
        rewrite DEF1 in *. rewrite DEF2 in *. ss.
        move L1_2 at top. clarify.
        unfold link_prog_check in L12_3_COND0. ss.

        destruct ((prog_defmap m3) ! x) as [gd3|] eqn: DEF3; ss.
        des_bool. des.
        { exfalso.
          des_bool. des.
          - des_sumbool.
            apply L12_3_COND0. apply in_app.
            des; eauto.
          - des_sumbool.
            exploit L2_3_COND1; eauto.
            unfold link_prog_check. rewrite DEF3.
            i. des_bool. des_sumbool. congruence.
        }

        desf.
        exfalso.
        rename Heq into P1_23.
        rewrite PTree_Properties.for_all_correct in *.
        exploit P1_23; eauto. clear P1_23.
        rewrite prog_defmap_elements.
        rewrite PTree.gcombine by ss.
        rewrite DEF2. rewrite DEF3. ss.

        exploit L2_3_COND1; eauto.
        unfold link_prog_check. rewrite DEF3.
        i. ss. des_bool.
        destruct (link_def gd2 gd3) as [gd23|] eqn: L2_3; ss.
        des_bool.
        destruct (link_def gd1 gd23) as [gd123|] eqn: L1_23; ss.

        generalize (link_skdef_assoc gd1 gd2 gd3).
        ss. rewrite L2_3. rewrite L1_23.
        rewrite L12_3_COND. congruence.
      +
        exfalso.
        rewrite prog_defmap_elements in L12_3_COND.
        rewrite PTree.gcombine in L12_3_COND by ss.
        rewrite DEF1 in *.

        destruct ((prog_defmap m2) ! x) as [gd2|] eqn: DEF2; ss.
        symmetry in L12_3_COND. clarify.

        unfold link_prog_check in L12_3_COND0. ss.

        destruct ((prog_defmap m3) ! x) as [gd3|] eqn: DEF3; ss.

        exploit L2_3_COND1; eauto.
        unfold link_prog_check. rewrite DEF3.
        i. ss. des_bool.
        destruct (link_def gd2 gd3) as [gd23|] eqn: L2_3; ss.
        des; ss.
        des_bool. des.
        * des_sumbool. apply L12_3_COND0.
          apply in_app. eauto.
        * des_sumbool. ss.
  }

  rename L12_3 into L12_3S.
  eapply link_prog_inv in L12_3S. des.
  clarify.

  unfold link_prog in L2_3.
  des_matchH L2_3 L2_3S_COND; ss. des_bool. clarify.
  unfold link_prog in L1_2S.
  des_matchH L1_2S L1_2S_COND; ss. des_bool. clarify. ss.
  rewrite PTree_Properties.for_all_correct in *.
  des_sumbool.

  rewrite link_prog_succeeds; ss.
  - rewrite <- app_assoc.
    f_equal. f_equal.
    apply PTree.elements_extensional.
    intro id.
    do 2 rewrite PTree.gcombine by ss.

    destruct ((prog_defmap m1) ! id) as [gd1|] eqn: DEF1;
      destruct ((prog_defmap m2) ! id) as [gd2|] eqn: DEF2.
    + exploit L1_2S_COND1; eauto.
      unfold link_prog_check. rewrite DEF2.
      do 2 rewrite andb_true_iff. intros [[? ?] L1_2S].
      des_sumbool.
      destruct (link gd1 gd2) as [gd12| ] eqn: LINK1_2; ss.

      do 2 rewrite prog_defmap_elements.
      do 2 rewrite PTree.gcombine by ss.
      rewrite DEF1. rewrite DEF2. ss. rewrite LINK1_2. ss.

      destruct ((prog_defmap m3) ! id) as [gd3|] eqn: DEF3; ss.
      exploit L2_3S_COND1; eauto.
      unfold link_prog_check. rewrite DEF3.
      do 2 rewrite andb_true_iff. intros [[? ?] L2_3S].
      des_sumbool.
      destruct (link gd2 gd3) as [gd23| ] eqn: LINK2_3; ss.
      rewrite LINK2_3.
      generalize (link_skdef_assoc gd1 gd2 gd3). ss. desf.
    + ss. do 2 rewrite prog_defmap_elements.
      do 2 rewrite PTree.gcombine by ss.
      rewrite DEF1. rewrite DEF2. ss.
    + ss. do 2 rewrite prog_defmap_elements.
      do 2 rewrite PTree.gcombine by ss.
      rewrite DEF1. rewrite DEF2. ss.
    + ss. do 2 rewrite prog_defmap_elements.
      do 2 rewrite PTree.gcombine by ss.
      rewrite DEF1. rewrite DEF2. ss.
  - setoid_rewrite prog_defmap_elements.
    setoid_rewrite PTree.gcombine.
    2: { ss. }
    intros x gd1 gd23 DEF1 DEF23.
    exploit L1_2S_COND1; eauto. unfold link_prog_check.

    destruct ((prog_defmap m2) ! x) as [gd2|] eqn: DEF2.
    2: { i. exploit L12_3S0; eauto.
         { rewrite prog_defmap_elements.
           rewrite PTree.gcombine by ss.
           rewrite DEF1. rewrite DEF2. ss.
         }

         i. des.
         rewrite in_app in *. des.
         - splits; auto. congruence.
         - exfalso. inv WF2.
           exploit PUBINCL; eauto. i.
           exploit prog_defmap_dom; eauto. i. des. congruence.
    }

    do 2 rewrite andb_true_iff.

    destruct (link gd1 gd2) as [gd12|] eqn: L1_2.
    2: { i. des. ss. }
    i. des.
    des_sumbool.
    splits; auto.
    { apply in_app; auto. }

    destruct ((prog_defmap m3) ! x) as [gd3| ] eqn: DEF3; ss.
    2: { clarify. congruence. }
    generalize (link_skdef_assoc gd1 gd2 gd3). ss. desf.
    intro R. rewrite <- R.
    exploit L12_3S0; eauto.
    { rewrite prog_defmap_elements.
      rewrite PTree.gcombine by ss.
      rewrite DEF1. rewrite DEF2. eauto. }

    i. des. congruence.
Qed.





Theorem link_list_prepend_eq
      (sk0 sk1 sk2: list Sk.t)
      (NOEMPTY: sk0 <> [] /\ sk1 <> [])
      (SAME: link_list sk0 = link_list sk1):
    <<EQ: link_list (sk2 ++ sk0) = link_list (sk2 ++ sk1)>>.
Proof.
  r. ginduction sk2; ss.
  ii. unfold link_sk in *. ss.
  exploit IHsk2; eauto. i.
  clear - NOEMPTY H. unfold link_list in H. des_ifs; ss.
  - unfold link_list. ss. rewrite Heq. rewrite Heq0. ss.
  - des. eapply link_list_aux_empty_inv in Heq. destruct sk2; destruct sk0; ss.
  - des. eapply link_list_aux_empty_inv in Heq0. destruct sk2; destruct sk1; ss.
  - unfold link_list. ss. rewrite Heq, Heq0. auto.
  - unfold link_list. ss. rewrite Heq, Heq0. auto.
Qed.

Theorem link_list_assoc_one
      (ctx: list Sk.t) sk0 sk1 sk_link
      (WF0: Sk.wf sk0)
      (WF1: Sk.wf sk1)
      (WFLINK: Sk.wf sk_link)
      (LINK: link sk0 sk1 = Some sk_link)
      (WFCTX: forall sk, In sk ctx -> Sk.wf sk)
  :
    <<EQ: link_list ([sk0 ; sk1] ++ ctx) = link_list ([sk_link] ++ ctx)>>
.
Proof.
  unfold link_list.
  remember (link_list_aux ctx) as link_ctx.
  destruct link_ctx; ss.
  { des_ifs. }
  { des_ifs. }

  exploit (@link_sk_assoc sk0 sk1 t); eauto.
  { eapply link_list_preserves_wf_sk; et. unfold link_list. des_ifs. }
  intro R.
  ss. desf; congruence.
Qed.

Theorem link_list_assoc
        (sk0 sk1 sk2: list Sk.t)
  :
    <<EQ: link_list (sk0 ++ sk1 ++ sk2) = link_list ((sk0 ++ sk1) ++ sk2)>>
.
Proof.
  ginduction sk0; ii; ss.
  destruct (classic (sk0 ++ sk1 ++ sk2 = nil)).
  { destruct sk0, sk1, sk2; ss. }
  replace (a :: sk0 ++ sk1 ++ sk2) with ([a] ++ (sk0 ++ sk1 ++ sk2)) by ss.
  replace (a :: (sk0 ++ sk1) ++ sk2) with ([a] ++ ((sk0 ++ sk1) ++ sk2)) by ss.
  eapply link_list_prepend_eq with (sk2 := [a]); ss.
  { destruct sk0, sk1, sk2; ss. }
  rewrite IHsk0; et.
Qed.

Lemma link_sk_prepend_eq
      A B C
      (NOEMPTY: A <> [] /\ B <> [])
      (SAME: link_sk A = link_sk B):
    link_sk (C ++ A) = link_sk (C ++ B).
Proof.
  unfold link_sk in *. rewrite ! map_app. eapply link_list_prepend_eq; et.
  des. destruct A, B; ss.
Qed.

Lemma link_sk_assoc_one ctx (mA mB mL: Mod.t)
      (WFA: Sk.wf mA)
      (WFB: Sk.wf mB)
      (WFL: Sk.wf mL)
      (LINK_OK: link (Mod.sk mA) (Mod.sk mB) = Some (Mod.sk mL))
      (WFCTX: forall md : Mod.t, In md ctx -> Sk.wf md)
  : link_sk ([mA; mB] ++ ctx)
    = link_sk ([mL] ++ ctx).
Proof.
  unfold link_sk. ss.
  apply link_list_assoc_one; ss. ii. rewrite in_map_iff in *. des; clarify. et.
Qed.

Lemma link_sk_main_eq
      ms sk
      (LINK_OK: link_sk ms = Some sk)
  : List.Forall (fun m => AST.prog_main (Mod.sk m) = AST.prog_main sk) ms.
Proof.
  Local Transparent Linker_prog.
  depgen sk.
  induction ms as [|ms]; i; ss.
  unfold link_sk in *. ss.
  unfold link_list in *. ss. desf.
  - destruct ms0; ss.
    2: { desf. }
    econs; ss.
  - exploit IHms; eauto. i.
    match goal with
    | H: link_prog _ _ = Some _ |- _ =>
      eapply link_prog_inv in H
    end.
    des. clarify. ss.
    econs; eauto.
    replace (AST.prog_main (Mod.sk ms)) with (AST.prog_main t). ss.
    Local Opaque Linker_prog.
Qed.


Lemma linkorder_internal_max
      fsig (gd: globdef (AST.fundef signature) unit)
      (LO: linkorder (Gfun (AST.Internal fsig)) gd)
  : gd = (Gfun (AST.Internal fsig)).
Proof.
  Local Transparent Linker_def.
  ss. inv LO.
  match goal with
  | H : linkorder _ _ |- _ => inv H
  end. reflexivity.
  Local Opaque Linker_def.
Qed.

Lemma globdef_linkorder
      skT gdT gid
      (skA skB skL: Sk.t)
      (sk_link_ok: link skA skB = Some skL)
      (FOCUS: skT = skA \/ skT = skB)
      (DEF_T: (prog_defmap skT) ! gid = Some gdT)
  : exists gdL, <<DEF_L: (prog_defmap skL) ! gid = Some gdL>> /\
                    <<LO: linkorder gdT gdL>>.
Proof.
  exploit (link_prog_inv skA skB skL).
  { apply sk_link_ok. }
  intros [MAIN_EQ [DEFMAP_LINK SKL]].

  des; clarify.
  - destruct ((prog_defmap skB) ! gid) as [gdB|] eqn: DEF_O.
    + exploit DEFMAP_LINK; eauto.
      intros [IN_SKA [IN_SKB [gdL LINK_SOME]]].
      (* rewrite SKL. *)
      rewrite prog_defmap_elements.
      rewrite PTree.gcombine by ss.
      rewrite DEF_T. rewrite DEF_O. ss.
      esplits; eauto.
      eapply link_linkorder in LINK_SOME.
      des. eauto.
    + (* rewrite SKL. *)
      rewrite prog_defmap_elements.
      rewrite PTree.gcombine by ss.
      rewrite DEF_T. rewrite DEF_O. ss.
      esplits; eauto.
      apply linkorder_refl.
  - destruct ((prog_defmap skA) ! gid) as [gdA|] eqn: DEF_O.
    + exploit DEFMAP_LINK; eauto.
      intros [IN_SKA [IN_SKB [gdL LINK_SOME]]].
      (* rewrite SKL. *)
      rewrite prog_defmap_elements.
      rewrite PTree.gcombine by ss.
      rewrite DEF_T. rewrite DEF_O. ss.
      esplits; eauto.
      eapply link_linkorder in LINK_SOME.
      des. eauto.
    + (* rewrite SKL. *)
      rewrite prog_defmap_elements.
      rewrite PTree.gcombine by ss.
      rewrite DEF_T. rewrite DEF_O. ss.
      esplits; eauto.
      apply linkorder_refl.
Qed.

Lemma prog_defmap_internal_impl
      skenv sk fid fsig
      (DEF_INT: (prog_defmap sk)!fid = Some (Gfun (AST.Internal fsig)))
      (INCL: SkEnv.includes skenv sk)
  : exists blk,
    (<<SKENV_SYMBOL: Genv.find_symbol skenv fid = Some blk>> /\
     <<SKENV_FUNCT_PTR: Genv.find_funct_ptr skenv blk = Some (AST.Internal fsig)>>) /\
    (<<PROJ_SYMBOL: Genv.find_symbol (SkEnv.project skenv sk) fid = Some blk>> /\
     <<PROJ_FUNCT_PTR: Genv.find_funct_ptr (SkEnv.project skenv sk) blk = Some (AST.Internal fsig)>>).
Proof.
  pose proof INCL as INCL2.
  inv INCL2. exploit DEFS; eauto. i. des.
  exploit linkorder_internal_max; eauto.
  i. subst.

  exists blk.
  pose proof DEF as DEF2.
  apply Genv.find_funct_ptr_iff in DEF2.
  split.
  { split; auto. }

  assert (internals sk fid = true) by (unfold internals; desf).
  hexploit (SkEnv.project_impl_spec INCL); eauto. intro PROJ. inv PROJ.
  rewrite SYMBKEEP by (apply internals_defs; eauto).
  split; auto.

  apply Genv.find_funct_ptr_iff.
  exploit DEFKEEP; eauto.
  { apply Genv.find_invert_symbol. auto. }
  i. des. rewrite DEFSMALL. congruence.
Qed.


Lemma link_defs
      (sk1 sk2 skl: Sk.t) fid
      (LINK: link sk1 sk2 = Some skl)
      (DEF_TGT: defs sk1 fid \/ defs sk2 fid)
  : defs skl fid.
Proof.
  unfold defs in *. des; des_sumbool.
  - rewrite prog_defmap_spec in *. des.
    exploit globdef_linkorder; try apply LINK; try apply DEF_TGT; eauto.
    i. des. eauto.
  - rewrite prog_defmap_spec in *. des.
    exploit globdef_linkorder; try apply LINK; try apply DEF_TGT; eauto.
    i. des. eauto.
Qed.

Section MORE_LINK_LEMMAS.
  Variable ms: list Mod.t.
  Variable sk_link : Sk.t.
  Hypothesis SK_LINK: link_sk ms = Some sk_link.
  Let skenv := Sk.load_skenv sk_link.
  Hypothesis MODS_WF: forall md : Mod.t, In md ms -> Sk.wf md.

  Lemma ge_disjoint
    : Ge.disjoint (load_genv ms skenv).
  Proof.
    cut (Ge.disjoint (Smallstep.globalenv (sem ms))).
    { ss. rewrite SK_LINK. eauto. }

    apply SemProps.genv_disjoint.
  Qed.

  Section INCL.
    Variable sk: Sk.t.
    Variable m: Mod.t.
    Hypothesis MOD_SK: Mod.sk m = sk.
    Hypothesis MOD_IN_MS: In m ms.

    (* Let m : Mod.t := ITreeMod.to_mod sk im. *)

    Lemma incl_sk: SkEnv.includes skenv sk.
    Proof.
      unfold skenv.
      exploit link_includes; eauto. clarify.
    Qed.
  End INCL.
End MORE_LINK_LEMMAS.
