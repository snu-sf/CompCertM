Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import ASTC.
Require Import Asmregs.
Require Import Skeleton.
Require Import LinkingC.
From Paco Require Import paco.

Set Implicit Arguments.








(* Recipe *)
Section SYMBINJ_DEFS.

  Print Values.Val.meminj.
  Print Mem.meminj_no_overlap.

  (* Q: use unique? -> no meaningful lemmas for it. also that presumes existance. *)
  Definition injective (inj: ident -> option ident): Prop := forall
    x0 x1 y
    (INJ0: inj x0 = Some y)
    (INJ1: inj x1 = Some y)
  ,
    x0 = x1
  .

  Definition symbinj := { inj: ident -> option ident | <<INJ: injective inj>> }.

  (* Definition domain (si: symbinj): ident -> Prop := fun id_src => is_some (si$ id_src). *)
  Definition domain (si: symbinj): ident -> Prop := is_some <*> (si$).

  (* complements. unmapped *)
  Definition domain_c (si: symbinj): ident -> Prop := ~1 si.(domain).

  Definition image (si: symbinj): ident -> Prop := fun id_tgt => exists id_src, si$ id_src = Some id_tgt.

  (* complements. unmapped *)
  Definition image_c (si: symbinj): ident -> Prop := ~1 si.(image).

  Inductive symbinj_incl (inj0 inj1: symbinj): Prop :=
  | symbinj_incl_intro
      (INCL: forall
          id_src id_tgt
          (SMALL: inj0$ id_src = Some id_tgt)
        ,
          <<LARGE: inj1$ id_src = Some id_tgt>>)
  .

  Global Program Instance symbinj_incl_PreOrder: PreOrder symbinj_incl.
  Next Obligation.
    ii.
    ss.
  Qed.
  Next Obligation.
    ii.
    eauto.
    inv H; inv H0.
    econs.
    i. eapply INCL0; eauto. eapply INCL; eauto.
  Qed.

End SYMBINJ_DEFS.

Hint Unfold domain domain_c image image_c.





Section SYMBINJ_PROPS.

  (* it only maps private area && mappings definitions are actually "matched" *)
  Inductive symbinj_closed (inj: symbinj) (prog_src prog_tgt: Sk.t): Prop :=
  | symbinj_closed_intro
      (CLOSED: forall
          id_src id_tgt
          (INJ: inj$ id_src = Some id_tgt)
        ,
          (* <<INSRC: In id_src prog_src.(prog_defs_names)>> *)
          (* /\ <<INTGT: In id_tgt prog_tgt.(prog_defs_names)>> *)
          <<INSRC: exists gd_src, prog_src.(prog_defmap)!id_src = Some gd_src>>
          /\ <<INTGT: exists gd_tgt, prog_tgt.(prog_defmap)!id_tgt = Some gd_tgt>>
          /\ <<MATCH: prog_src.(prog_defmap)!id_src = prog_tgt.(prog_defmap)!id_tgt>>
      )
  .

  Inductive symbinj_closed2 (si: symbinj) (prog_src prog_tgt: Sk.t): Prop :=
  | symbinj_closed2_intro
      (DOMAIN: all1 (si.(domain) <1= prog_src.(defs)))
      (IMAGE: all1 (si.(image) <1= prog_tgt.(defs)))
      (MATCH: forall
          id_src id_tgt
          (INJ: si$ id_src = Some id_tgt)
        ,
          <<MATCH: prog_src.(prog_defmap)!id_src = prog_tgt.(prog_defmap)!id_tgt>>)
  .

  Lemma symbinj_closed_iff
        si prog_src prog_tgt
    :
      symbinj_closed si prog_src prog_tgt <-> symbinj_closed2 si prog_src prog_tgt
  .
  Proof.
    split; i.
    - inv H.
      econs; eauto.
      + ii. u. des_ifs. ss.
        exploit CLOSED; eauto. i; des.
        hnf. eauto.
      + ii. u. des_ifs; des; ss.
        exploit CLOSED; eauto. i; des.
        hnf. eauto.
      + ii.
        exploit CLOSED; eauto. i; des.
        ss.
    - inv H.
      econs; eauto.
      i.
      exploit MATCH; eauto. i; des.
      exploit (DOMAIN id_src); eauto.
      { compute. des_ifs; ss. clarify. }
      i; des.
      exploit (IMAGE id_tgt); eauto.
  Qed.

  Inductive symbinj_private (inj: symbinj) (prog_src prog_tgt: Sk.t): Prop :=
  | symbinj_private_intro
      (PRIVATE: forall
          id_src id_tgt
          (INJ: inj$ id_src = Some id_tgt)
        ,
          <<PRIVSRC: prog_src.(privs) id_src>>
          /\ <<PRIVTGT: prog_tgt.(privs) id_tgt>>)
  .

  Inductive symbinj_private2 (si: symbinj) (prog_src prog_tgt: Sk.t): Prop :=
  | symbinj_private2_intro
      (DOMAIN: all1 (si.(domain) <1= prog_src.(privs)))
      (IMAGE: all1 (si.(image) <1= prog_tgt.(privs)))
  .

  Lemma symbinj_private_iff
        si prog_src prog_tgt
    :
      symbinj_private si prog_src prog_tgt <-> symbinj_private2 si prog_src prog_tgt
  .
  Proof.
    split; i.
    - inv H. econs; eauto.
      + ii. compute in PR. des_ifs. ss.
        exploit PRIVATE; eauto. i; des. ss.
      + ii. compute in PR. des; des_ifs. ss.
        exploit PRIVATE; eauto. i; des. ss.
    - inv H. econs; eauto.
      i.
      exploit (DOMAIN id_src); eauto. { compute. des_ifs; ss. clarify. } i.
      exploit (IMAGE id_tgt); eauto.
  Qed.

  Inductive link_symbinj (inj0 inj1 inj_linked: symbinj): Prop :=
  | link_symbinj_intro
      (NOCRASH: forall id, ~ (((inj0$ id).(is_some)) /\ ((inj1$ id).(is_some))))
      (LINK: forall id, inj_linked$ id = match inj0$ id with
                                         | Some id_tgt => Some id_tgt
                                         | None => inj1$ id
                                         end)
  .

  Lemma link_symbinj_spec
        inj0 inj1 inj_linked
        (LINK: link_symbinj inj0 inj1 inj_linked)
    :
      <<INCL0: symbinj_incl inj0 inj_linked>>
      /\ <<INCL1: symbinj_incl inj1 inj_linked>>
  (* TODO: domain/image is exactly the union *)
  .
  Proof.
    inv LINK.
    esplits; eauto.
    - econs; eauto.
      i. specialize (LINK0 id_src). des_ifs.
    - econs; eauto.
      i. specialize (LINK0 id_src). des_ifs.
      + exfalso. eapply NOCRASH; eauto.
        rewrite Heq; ss. rewrite SMALL; ss.
      + eq_closure_tac.
  Qed.

  (* Remark: We can safely assume LINKEDSRC/LINKEDTGT here. *)
  (* For this, we require "TransfSk.TLink" for each opt. *)
  Lemma symbinj_link
        inj0 prog_src0 prog_tgt0
        (CONF0: symbinj_closed inj0 prog_src0 prog_tgt0)
        (PRIV0: symbinj_private  inj0 prog_src0 prog_tgt0)
        (GOODSRC0: good_prog prog_src0)
        (GOODTGT0: good_prog prog_tgt0)
        inj1 prog_src1 prog_tgt1
        (CONF1: symbinj_closed inj1 prog_src1 prog_tgt1)
        (PRIV1: symbinj_private  inj1 prog_src1 prog_tgt1)
        (GOODSRC1: good_prog prog_src1)
        (GOODTGT1: good_prog prog_tgt1)
        prog_src_linked
        (LINKEDSRC: link prog_src0 prog_src1 = Some prog_src_linked)
        prog_tgt_linked
        (LINKEDTGT: link prog_tgt0 prog_tgt1 = Some prog_tgt_linked)
    :
      exists inj_linked,
        <<MERGE: link_symbinj inj0 inj1 inj_linked>>
        /\ <<CONF: symbinj_closed inj_linked prog_src_linked prog_tgt_linked>>
        /\ <<PRIV: symbinj_private inj_linked prog_src_linked prog_tgt_linked>>
        /\ <<UNMAPPEDSRC0: all1 (inj0.(domain_c) /1\ prog_src0.(privs) <1= inj_linked.(domain_c))>>
        /\ <<UNMAPPEDTGT0: all1 (inj0.(image_c) /1\ prog_tgt0.(privs) <1= inj_linked.(image_c))>>
        /\ <<UNMAPPEDSRC1: all1 (inj1.(domain_c) /1\ prog_src1.(privs) <1= inj_linked.(domain_c))>>
        /\ <<UNMAPPEDTGT1: all1 (inj1.(image_c) /1\ prog_tgt1.(privs) <1= inj_linked.(image_c))>>
  .
  Proof.
    i.
    destruct inj0 as [f0 proof0], inj1 as [f1 proof1]; ss.
    inv PRIV0. inv PRIV1. ss.
    inv CONF0. inv CONF1. ss.

    hexploit (link_prog_inv _ _ LINKEDSRC); eauto. intro SPECSRC.
    hexploit (link_prog_inv _ _ LINKEDTGT); eauto. intro SPECTGT.

    eexists (exist _ _ _).
    esplits; eauto.
    { econs; ss; eauto.
      ii; ss. des; ss.
      unfold is_some in *. des_ifs.
      eapply (link_prog_private_exclusive LINKEDSRC) with (id:= id); eauto.
      - exploit PRIVATE; eauto. i; des. ss.
      - exploit PRIVATE0; eauto. i; des. ss.
    }
    {
      econs; ss; eauto.
      ii.
      des_ifs.
      - clear CLOSED0 PRIVATE0.
        exploit CLOSED; eauto. i; des.
        splits; ss.
        + inv SPECSRC. eapply SMALLHIT; eauto.
        + inv SPECTGT. eapply SMALLHIT; eauto.
        + inv SPECSRC. erewrite DEFREL.
          inv SPECTGT. erewrite DEFREL0.
          unfold link_prog_merge.
          rewrite INSRC.
          rewrite INTGT.
          exploit PRIVATE; eauto. i; des.
          exploit PRIVSPEC0; eauto. i; des.
          exploit PRIVSPEC2; eauto. i; des.
          des_ifs_safe; ss.
          eq_closure_tac.
      - clear CLOSED PRIVATE.
        exploit CLOSED0; eauto. i; des.
        splits; ss.
        + inv SPECSRC. eapply SMALLHIT; eauto.
        + inv SPECTGT. eapply SMALLHIT; eauto.
        + inv SPECSRC. erewrite DEFREL.
          inv SPECTGT. erewrite DEFREL0.
          unfold link_prog_merge.
          rewrite INSRC.
          rewrite INTGT.
          exploit PRIVATE0; eauto. i; des.
          exploit PRIVSPEC1; eauto. i; des.
          exploit PRIVSPEC3; eauto. i; des.
          des_ifs_safe; ss.
          eq_closure_tac.
    }
    {
      clear CLOSED CLOSED0.
      econs; ss; eauto.
      i.
      des_ifs.
      - exploit PRIVATE; eauto. i; des. split ;ss.
        + eapply (link_prog_private LINKEDSRC); eauto.
        + eapply (link_prog_private LINKEDTGT); eauto.
      - exploit PRIVATE0; eauto. i; des. split ;ss.
        + eapply (link_prog_private LINKEDSRC); eauto.
        + eapply (link_prog_private LINKEDTGT); eauto.
    }
    {
      ii; ss. u. des. des_ifs_safe.
      exploit PRIVATE0; eauto. i ;des.
      eapply (link_prog_private_exclusive LINKEDSRC); econs; eauto.
    }
    {
      ii; ss. u. des. des_ifs; eauto.
      exploit PRIVATE0; eauto. i; des.
      eapply (link_prog_private_exclusive LINKEDTGT); econs; eauto.
    }
    {
      ii; ss. u. des. des_ifs_safe.
      exploit PRIVATE; eauto. i ;des.
      eapply (link_prog_private_exclusive LINKEDSRC); econs; eauto.
    }
    {
      ii; ss. u. des. des_ifs; eauto.
      exploit PRIVATE; eauto. i; des.
      eapply (link_prog_private_exclusive LINKEDTGT); econs; eauto.
    }
  Unshelve.
    unfold injective in *.
    ss.
    ii.
    des_ifs; eauto.
    - exfalso.
      exploit PRIVATE; eauto. i; des.
      exploit PRIVATE0; eauto. i; des.
      eapply (link_prog_private_exclusive LINKEDTGT); eauto.
    - exfalso.
      exploit PRIVATE; eauto. i; des.
      exploit PRIVATE0; eauto. i; des.
      eapply (link_prog_private_exclusive LINKEDTGT); eauto.
  Qed.

  (* TODO: link_list with these *)
  (* TODO: finally biject all public symbols. src~tgt public symbols should be the same *)
  (* TODO: is above restriction cruel? the only case public symbol is not equal is eliminating *)
  (* public symbol that was declared with "extern". but there is no point on doing that - *)
  (* generated code size will remain same (or almost same) and performance is exactly same. *)

  (* machine expects: *)
  (* 1) my recipe is alive: it was just unioned && added public. nothing is removed *)
  (* 2) my publics obey global rule: *)
  (*    - each recipe does not overlap with skelenv's public (corollary of "symbinj_link") *)
  (*    - skelenv's public obey global rule *)
  (*    - machine's public obey global rule (corollary) *)
  (* 3) no other mapping inside my private area <-------- ***important!! TODO****)

End SYMBINJ_PROPS.



(* TODO: Now actually build genv/initial memory/injection with these *)
(* TODO: these built injetion should meet the expectation of each machine: *)
(* namely, it should include all module's symb_inj && publics are bijected && no other link *)

Section INITMEM.



  Variable skel_src skel_tgt: Sk.t.
  Let skenv_src := skel_src.(Genv.globalenv).
  Let skenv_tgt := skel_tgt.(Genv.globalenv).

  Inductive symbinj_exact_meminj (si: symbinj) (mi: meminj): Prop :=
  | symbinj_exact_meminj_intro
      (* SI <= MI *)
      (SIMI: forall
          id_src id_tgt
          (SI: si$ id_src = Some id_tgt)
        ,
          exists b_src b_tgt,
            <<FINDSRC: skenv_src.(Genv.find_symbol) id_src = Some b_src>>
            /\ <<FINDTGT: skenv_tgt.(Genv.find_symbol) id_tgt = Some b_tgt>>
            /\ <<MI: mi b_src = Some (b_tgt, 0)>>)
      (* MI <= SI *)
      (MISI: forall
          b_src b_tgt delta
          (MI: mi b_src = Some (b_tgt, delta))
        ,
           exists id_src id_tgt,
            <<FINDSRC: skenv_src.(Genv.invert_symbol) b_src = Some id_src>>
            /\ <<FINDTGT: skenv_tgt.(Genv.invert_symbol) b_tgt = Some id_tgt>>
            /\ <<SI: si$ id_src = Some id_tgt>>
            /\ <<DELTA: delta = 0>>)
  .

  (* Copied from Unusedglobproof. *)
  Definition init_meminj_with_si (si: symbinj): meminj :=
    fun b =>
      match Genv.invert_symbol skenv_src b with
      | Some id_src =>
        match si$ id_src with
        | Some id_tgt => 
          match Genv.find_symbol skenv_tgt id_tgt with
          | Some b' => Some (b', 0)
          | None => None
          end
        | None => None
        end
      | None => None
      end
  .

  (* After adding public mapping, it is no more "symbinj_privat", but it is still "symbinj_closed" *)
  Lemma init_meminj_with_si_spec
        si
        (CLOSED: symbinj_closed si skel_src skel_tgt)
    :
      <<EXACT: symbinj_exact_meminj si (init_meminj_with_si si)>>
  .
  Proof.
    destruct si as [inj proof]; ss.
    unfold init_meminj_with_si.
    inv CLOSED. ss.
    econs; ss; eauto.
    - i.
      exploit CLOSED0; eauto. i; des. clear MATCH.
      eapply Genv.find_def_symbol in INSRC. des.
      eapply Genv.find_def_symbol in INTGT. des.
      esplits; eauto.
      erewrite Genv.find_invert_symbol; eauto.
      erewrite SI.
      unfold skenv_tgt.
      erewrite INTGT. ss.
    - i.
      des_ifs_safe; ss.
      esplits; eauto.
      erewrite Genv.find_invert_symbol; eauto.
  Qed.


(*** IMPORTANT TODO: ***)
(*** for each opt, exists src init_mem -> exists tgt init_mem kind of thing was stated in ***)
(*** "transf_initial_states" or something. opt actually knows src/tgt and it was their obligation. ***)
(*** For Sk.t, we need to know both Sk.ts are initializable ***)
(*** HOW DO WE KNOW THIS? ***)
(*** 1) When does init fail???? Define wf condition??? (ag admit no. 434343) ***)
(*** store_zeros (Mem.store), Genv.store_init_data_list, Mem.drop_perm ***)
(*** Um,,, it would be hard to define "wf" condition that guarantees succeed... ***)
(*** 2) We might need something like: Sk.t_linking_preserves_transf_initial_states ... ***)
(*** Add this condition on "TransfSk.TLink" ***)
About Genv.init_mem_exists.
About Genv.init_mem_inversion.

  Lemma init_mem_inject
        si
        (CONF: symbinj_closed si skel_src skel_tgt)
        m_src m_tgt
        (INITSRC: Genv.init_mem skel_src = Some m_src)
        (INITTGT: Genv.init_mem skel_tgt = Some m_tgt)
  :
    exists mi, (<<EXACT: symbinj_exact_meminj si mi>>)
               /\ <<INJ: @Mem.inject Val.mi_normal mi m_src m_tgt>>
  .
  Proof.
    exists (init_meminj_with_si si).
    apply dep_split_right.
    { eapply init_meminj_with_si_spec; eauto. }
    intro SPEC.

    inv SPEC.
    hexploit (Genv.init_mem_characterization_gen skel_src); eauto. intro MEMSRC.
    hexploit (Genv.init_mem_characterization_gen skel_tgt); eauto. intro MEMTGT.

    (* Mem.inject' *)
    econs; ss; eauto.
    - (* Mem.mem_inj *)
      econs; ss; eauto.

      + ii.

        exploit MISI; eauto. clear MISI. i; des. clarify.
        apply Genv.invert_find_symbol in FINDSRC.
        apply Genv.invert_find_symbol in FINDTGT.


        inv CONF.
        exploit CLOSED; eauto. clear CLOSED. i; des.


        rewrite INSRC in *. rewrite INTGT in *. clarify.
        apply Genv.find_def_symbol in INSRC.
        apply Genv.find_def_symbol in INTGT.
        des; clarify.
        eq_closure_tac.
        (* revert INSRC0. revert INTGT0. eq_closure_tac. i. *)


        exploit MEMSRC; eauto. clear MEMSRC. i; des.
        exploit MEMTGT; eauto. clear MEMTGT. i; des.


        des_ifs; des; ss.
        * exploit H4; try apply H0. i; des. clarify.
          apply Mem.perm_cur. rewrite Z.add_0_r. ss.
        * exploit H6; eauto. i; des.
          apply Mem.perm_cur. rewrite Z.add_0_r.
          eapply Mem.perm_implies; eauto.

      + ii.
        exploit MISI; eauto. i; des. clear MISI. clarify.
        apply Zdivide_0.

      + ii.

        exploit MISI; eauto. clear MISI. i; des. clarify.
        apply Genv.invert_find_symbol in FINDSRC.
        apply Genv.invert_find_symbol in FINDTGT.


        inv CONF.
        exploit CLOSED; eauto. clear CLOSED. i; des.


        rewrite INSRC in *. rewrite INTGT in *. clarify.
        apply Genv.find_def_symbol in INSRC.
        apply Genv.find_def_symbol in INTGT.
        des; clarify.
        eq_closure_tac.
        (* revert INSRC0. revert INTGT0. eq_closure_tac. i. *)


        exploit MEMSRC; eauto. clear MEMSRC. i; des.
        exploit MEMTGT; eauto. clear MEMTGT. i; des.


        des_ifs; ss.
        * exfalso. des.
          exploit H4; try apply H0. i; des. clarify.
        * des.
          admit "copy proof of 'init_mem_inj_1' in Unusedglobproof.".
    - admit "valid_block, closed".
    - admit "valid_block, closed".
    - admit "no_overlap, symbinj-partial_bijective".
    - ii.
      assert(delta = 0).
      { exploit MISI; eauto. i; des; ss. }
      clarify.
      hexploit (Integers.Ptrofs.unsigned_range_2 ofs). i.
      esplits; ss; try xomega.
    - i.
      
      exploit MISI; eauto. clear MISI. i; des. clarify.
      apply Genv.invert_find_symbol in FINDSRC.
      apply Genv.invert_find_symbol in FINDTGT.


      inv CONF.
      exploit CLOSED; eauto. clear CLOSED. i; des.


      rewrite INSRC in *. rewrite INTGT in *. clarify.
      apply Genv.find_def_symbol in INSRC.
      apply Genv.find_def_symbol in INTGT.
      des; clarify.
      eq_closure_tac.
      (* revert INSRC0. revert INTGT0. eq_closure_tac. i. *)


      exploit MEMSRC; eauto. clear MEMSRC. i; des.
      exploit MEMTGT; eauto. clear MEMTGT. i; des.


      rewrite Z.add_0_r in *.
      des_ifs; ss.
      + des; ss.
        exploit H3; try apply H0. i; des.
        clarify.
        left; ss.
        apply Mem.perm_cur; ss.
      + des; ss.
        exploit H3; try apply H0. i; des.
        clarify.
        left; ss.
        apply Mem.perm_cur; ss.
        eapply Mem.perm_implies; eauto.
  Qed.



End INITMEM.


