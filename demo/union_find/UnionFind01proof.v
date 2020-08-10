Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift.
Require SoundTop.
Require SimMemId.
Require Import ModSemProps.
Require Import Program.
Require Import Any.

Require Import SIRProps.
Require Import SIR SIRStack.
Require Import Clightdefs Op ClightC CtypesC CtypingC.
Require Import UnionFindHeader.
Require Import UnionFind1.
Require Import UnionFind0.
Require Import SIRUnstackproof.

Set Implicit Arguments.

(*** TODO: copied from unstackproof. move to coqlibc ***)
Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

Notation "'_'" := PTree.Leaf (at level 150).
Notation "a % x % b" := (PTree.Node a x b) (at level 150).
Notation "a %% b" := (PTree.Node a None b) (at level 150).

(*** TODO: remove redundancy with unstackproof ***)
Notation "'geof'" :=
  (fun skenv_link p_tgt =>
     Build_genv (SkEnv.revive ((SkEnv.project skenv_link)
                                 (CSk.of_program signature_of_function p_tgt)) p_tgt)
                (p_tgt.(prog_comp_env))) (at level 50).

(* Opaque composites. *)
Opaque build_composite_env'.
(* Opaque build_composite_env. *)
(* Opaque add_composite_definitions. *)

(* Local Opaque PTree.get. *)
(*** TODO: move to UnionFind0 ***)
Opaque _new _find _union.
Theorem correct: rusc defaultR [UnionFind1.module: Mod.t] [UnionFind0.module: Mod.t].
Proof.
  eapply SIRUnstackproof.correct; ss; et.
  econs; ss; et.
  { ii. u. des_ifs. unfold internal_funs. des_ifs.
    Local Transparent build_composite_env'. (*** TODO: avoid this ***)
    exploit in_prog_defmap; et; intro T; ss; unfold update_snd in *; ss; des; clarify; ss.
    Local Opaque build_composite_env'.
  }
  ii.
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(exists b_m, <<MSYMB: Genv.find_symbol (geof skenv_link prog) _malloc = Some b_m>>).
  {
    inv INCL. ss.
    exploit (DEFS _malloc); et.
    { unfold prog_defmap. ss. }
    i; des. ss. folder.
    clear - SYMB.
    Local Opaque PTree.get.
    (*** TODO: Current: I can't use global opaque because of some extensional proofs. fix it ***)
    uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. esplits; et.
    Local Transparent PTree.get.
  }
  des.
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(exists b_n, <<NSYMB: Genv.find_symbol (geof skenv_link prog) _new = Some b_n>>).
  {
    clear_until TGT.
    inv INCL. ss.
    exploit (DEFS _new); et.
    { unfold prog_defmap. ss. }
    i; des. ss. folder.
    clear - SYMB.
    Local Opaque PTree.get.
    (*** TODO: Current: I can't use global opaque because of some extensional proofs. fix it ***)
    uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. esplits; et.
    Local Transparent PTree.get.
  }
  des.
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(exists b_f, <<FSYMB: Genv.find_symbol (geof skenv_link prog) _find = Some b_f>>).
  {
    clear_until TGT.
    inv INCL. ss.
    exploit (DEFS _find); et.
    { unfold prog_defmap. ss. }
    i; des. ss. folder.
    clear - SYMB.
    Local Opaque PTree.get.
    (*** TODO: Current: I can't use global opaque because of some extensional proofs. fix it ***)
    uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. esplits; et.
    Local Transparent PTree.get.
  }
  des.
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(exists b_u, <<FSYMB: Genv.find_symbol (geof skenv_link prog) _union = Some b_u>>).
  {
    clear_until TGT.
    inv INCL. ss.
    exploit (DEFS _union); et.
    { unfold prog_defmap. ss. }
    i; des. ss. folder.
    clear - SYMB.
    Local Opaque PTree.get.
    (*** TODO: Current: I can't use global opaque because of some extensional proofs. fix it ***)
    uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. esplits; et.
    Local Transparent PTree.get.
  }
  des.

  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(_MDEF: forall
            fblk
            (SYMB: Genv.find_symbol (geof skenv_link prog) _malloc = Some fblk)
          ,
            <<NDEF: Genv.find_funct (geof skenv_link prog) (Vptr fblk Ptrofs.zero)
                   = Some (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)>>).
  { i.
    exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
    des. ss. des_ifs. clear_tac.
    exploit CSkEnv.project_revive_precise; et. intro T. inv T.
    exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
    exploit prog_defmap_dom; et. intro V; des.
    exploit P2GE; et. intro W; des.
    folder.
    assert(b_m = b).
    { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
    clarify.
    Local Transparent build_composite_env'. (*** TODO: avoid this ***)
    exploit (prog_defmap_norepet prog _malloc); ss; et.
    { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. }
    intro T. clarify. ss.
    unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss.
    Local Opaque build_composite_env'.
  }
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(_NDEF: forall
            fblk
            (SYMB: Genv.find_symbol (geof skenv_link prog) _new = Some fblk)
          ,
            <<NDEF: Genv.find_funct (geof skenv_link prog) (Vptr fblk Ptrofs.zero)
                   = Some (Ctypes.Internal f_new)>>).
  { i.
    exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
    des. ss. des_ifs. clear_tac.
    exploit CSkEnv.project_revive_precise; et. intro T. inv T.
    exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
    exploit prog_defmap_dom; et. intro V; des.
    exploit P2GE; et. intro W; des.
    folder.
    assert(b_n = b).
    { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
    clarify.
    Local Transparent build_composite_env'. (*** TODO: avoid this ***)
    exploit (prog_defmap_norepet prog _new); ss; et.
    { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. }
    intro T. clarify. ss.
    unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss.
    Local Opaque build_composite_env'.
  }
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(_FDEF: forall
            fblk
            (SYMB: Genv.find_symbol (geof skenv_link prog) _find = Some fblk)
          ,
            <<FDEF: Genv.find_funct (geof skenv_link prog) (Vptr fblk Ptrofs.zero)
                   = Some (Ctypes.Internal f_find)>>).
  { i.
    exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
    des. ss. des_ifs. clear_tac.
    exploit CSkEnv.project_revive_precise; et. intro T. inv T.
    exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
    exploit prog_defmap_dom; et. intro V; des.
    exploit P2GE; et. intro W; des.
    folder.
    assert(b_f = b).
    { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
    clarify.
    Local Transparent build_composite_env'. (*** TODO: avoid this ***)
    exploit (prog_defmap_norepet prog _find); ss; et.
    { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. }
    intro T. clarify. ss.
    unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss.
    Local Opaque build_composite_env'.
  }
  (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
  assert(_UDEF: forall
            fblk
            (SYMB: Genv.find_symbol (geof skenv_link prog) _union = Some fblk)
          ,
            <<FDEF: Genv.find_funct (geof skenv_link prog) (Vptr fblk Ptrofs.zero)
                   = Some (Ctypes.Internal f_union)>>).
  { i.
    exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
    des. ss. des_ifs. clear_tac.
    exploit CSkEnv.project_revive_precise; et. intro T. inv T.
    exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
    exploit prog_defmap_dom; et. intro V; des.
    exploit P2GE; et. intro W; des.
    folder.
    assert(b_u = b).
    { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
    clarify.
    Local Transparent build_composite_env'. (*** TODO: avoid this ***)
    exploit (prog_defmap_norepet prog _union); ss; et.
    { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. }
    intro T. clarify. ss.
    unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss.
    Local Opaque build_composite_env'.
  }

  exploit _MDEF; et. intro MDEF. clear _MDEF.
  exploit _NDEF; et. intro NDEF. clear _NDEF.
  exploit _FDEF; et. intro FDEF. clear _FDEF.
  exploit _UDEF; et. intro UDEF. clear _UDEF.
  des.

  ss. des_ifs. clear_tac.
  (* hexploit (prog_comp_env_eq prog); et. intro CE. *)
  (* hexploit build_composite_env_consistent; et. intro CEC. *)
  (*** above (CEC) will prevent future des_ifs, dependent type thing ***)
  (* exploit (CEC _Node); et. *)
  (* { ss. } *)
  (* intro V. inv V. ss. des_ifs. clear_tac. *)
  (*** it seems CEC is actually not that useful here --
       local transparent blah && extensional proof do the thing ***)



  exploit prog_defmap_image; et. ss. des_ifs.
  Local Transparent build_composite_env'. (*** TODO: avoid this ***)
  intro T; cbn in T; des; clarify.
  Local Opaque build_composite_env'.
  -
    exploit (prog_defmap_norepet prog _new); et.
    { repeat (econs; ss; et); ii; des; ss. }
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      ss; et.
      Local Opaque build_composite_env'.
    }
    ii; clarify. cbn in SRC. des_ifs. clear_tac.
    econs; ss; et. ii. inv TYP. ss. destruct vs0; ss.
    clear_tac.

    esplits; et.
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      repeat (econs; ss; et).
      Local Opaque build_composite_env'.
    }
    pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { econs; ss; et.
        - econs; ss; et.
          + econsby ss; et.
          + econsby ss; et.
        - repeat econs; ss; et.
      }
      apply star_refl.
    }

    rewrite bind_ret_l. left. pfold.
    unfold unwrapU, malloc. uo. des_ifs; cycle 1.
    { unfold triggerUB. irw. econs; ss; et. }
    ss. rewrite bind_ret_l. des_ifs; cycle 1.
    { unfold triggerUB. irw. econs; ss; et. }
    rewrite bind_ret_l. des_ifs; cycle 1.
    { unfold triggerUB. irw. econs; ss; et. }
    rewrite bind_ret_l.

    assert(SZ: co_sizeof c = 16).
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      cbn in Heq3.
      Local Opaque build_composite_env'.
      clarify.
    }
    assert(MEM: co_members c = [(_rank, tuint); (_parent, tptr (Tstruct _Node noattr))]).
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      cbn in Heq3.
      Local Opaque build_composite_env'.
      clarify.
    }
    assert(ALN: co_alignof c =  8).
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      cbn in Heq3.
      Local Opaque build_composite_env'.
      clarify.
    }

    econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { econsr; ss; et. econs; ss; et.
        { unfold Mptr. des_ifs; ss. rewrite SZ; et. }
        { unfold Mptr. des_ifs; ss. rewrite SZ; et. }
      }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { econs; ss; et.
        - econs; ss; et.
          + _step.
          + rewrite MEM. ss.
        - repeat econs; ss; et.
        - repeat econs; ss; et.
        - repeat econs; ss; et.
      }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { econs; ss; et.
        - econs; ss; et.
          + _step.
          + rewrite MEM. ss.
        - repeat econs; ss; et.
        - repeat econs; ss; et.
        - repeat econs; ss; et.
      }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      apply star_refl.
    }
    left. pfold. econs; ss; et.
    econs; ss; et.

  -
    exploit (prog_defmap_norepet prog _find); et.
    { repeat (econs; ss; et); ii; des; ss. }
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      ss; et.
      Local Opaque build_composite_env'.
    }
    ii; clarify. cbn in SRC. des_ifs. clear_tac.
    econs; ss; et. ii. inv TYP. ss. destruct vs0; ss. destruct vs0; ss.
    unfold typify_list, typify in TYP0. ss. des_ifs; ss. clear_tac.

    esplits; et.
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      repeat (econs; ss; et).
      _step.
      Local Opaque build_composite_env'.
    }
    unfold UnionFind1.f_find. ss.
    destruct (unblock v) eqn:T; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct v; ss. des_ifs. clear_tac.
    irw. unfold unwrapU. des_ifs; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    irw.
    des_ifs; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    irw.
    pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      (* { repeat (first[econsby ss; et|econs; ss; et]). } *) (*** TODO: <--- make this as a tactic ***)
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      apply star_refl.
    }
    destruct b0; ss.
    + left. pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et).
          - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
          - ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). (*** TODO: <--- make this as a tactic ***)
          cbn. des_ifs.
        }
        apply star_refl.
      }
      left. pfold. econs; ss; et.
      { econs; ss; et. clear_tac. clear - Heq0. cbn. unfold typify. destruct v; ss.
        - des_ifs_safe. ss. des_ifs.
        - des_ifs_safe. ss. des_ifs.
      }
      { econs; ss; et. ii; clarify. }
      ii. left. pfold.
      des_ifs; cycle 1.
      { unfold triggerUB. irw. econs; ss; et. }
      irw.
      econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). (*** TODO: <--- make this as a tactic ***)
          - rewrite Cop.cast_val_casted; ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). (*** TODO: <--- make this as a tactic ***)
          - rewrite Cop.cast_val_casted; ss.
        }
        apply star_refl.
      }
      left. pfold. econs; ss; et.
    + left. pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et).
          - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
          - ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). (*** TODO: <--- make this as a tactic ***)
          cbn. des_ifs.
        }
        apply star_refl.
      }
      left. pfold. econs; ss; et.
      { destruct v; ss.
        - econs; ss; et.
        - econs; ss; et.
      }

  -
    exploit (prog_defmap_norepet prog _union); et.
    { repeat (econs; ss; et); ii; des; ss. }
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      ss; et.
      Local Opaque build_composite_env'.
    }
    ii; clarify. cbn in SRC. des_ifs. clear_tac.
    econs; ss; et. ii. inv TYP. ss. destruct vs0; ss. destruct vs0; ss. destruct vs0; ss.
    unfold typify_list, typify in TYP0. ss. des_ifs; ss. clear_tac.

    esplits; et.
    {
      Local Transparent build_composite_env'. (*** TODO: avoid this ***)
      repeat (econs; ss; et).
      { ii; des; ss. }
      _step.
      Local Opaque build_composite_env'.
    }
    rename v into vx. rename v0 into vy.
    unfold UnionFind1.f_union. ss.
    destruct (unblock vx) eqn:BX; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct (unblock vy) eqn:BY; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct vx; ss. destruct vy; ss. des_ifs.
    rename b into b_x. rename b0 into b_y.
    irw. pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      apply star_refl.
    }
    left. pfold. econs; ss; et.
    { econs; ss; et. cbn. unfold typify. des_ifs. }
    { econs; ss; et. }
    ii.
    left. pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (first[econsby ss; et|econs; ss; et]). (*** TODO: <--- make this as a tactic ***) }
      apply star_refl.
    }
    left. pfold. irw. econs; ss; et.
    { econs; ss; et. cbn. unfold typify. des_ifs. }
    { econs; ss; et. }
    ii. left.
    destruct (Val.cmplu_bool (Mem.valid_pointer m2) Ceq v1 v0) eqn:T; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    ss. irw.
    pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      apply star_refl.
    }
    left.
    destruct b.
    { cbn.
      pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et).
          - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
          - ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        apply star_refl.
      }
      ss. left. pfold. econs; ss; et.
      { econs; et. }
    }
    cbn.
    destruct (unblock v1) eqn:BX; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct (unblock v0) eqn:BY; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    ss. irw.
    destruct (Mem.load Mint32 m2 b 0) eqn:LX; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct (Mem.load Mint32 m2 b0 0) eqn:LY; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    ss. irw.
    Local Opaque Val.cmplu_bool.
    destruct v1; ss. destruct v0; ss. des_ifs_safe. rename b into b_x0. rename b0 into b_y0.
    rename v into _xRank. rename v2 into _yRank.
    destruct (unint _xRank) eqn:IX; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct (unint _yRank) eqn:IY; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    destruct _xRank, _yRank; ss. clarify.
    rename i into xRank. rename i0 into yRank.
    irw.

    destruct (Int.ltu xRank yRank) eqn:C0; ss.
    { destruct (Mem.store Mptr m2 b_x0 8 (Vptr b_y0 Ptrofs.zero)) eqn:S; cycle 1.
      { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
      ss. irw. pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et).
          - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
          - ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). cbn. des_ifs. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { cbn. rewrite Int.eq_false; ss.
          repeat (first[econsby ss; et|econs; ss; et]).
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        apply star_refl.
      }
      left. pfold. econs; ss; et.
      { econs; ss; et. }
    }
    destruct (Int.ltu yRank xRank) eqn:C1; ss.
    { destruct (Mem.store Mptr m2 b_y0 8 (Vptr b_x0 Ptrofs.zero)) eqn:S; cycle 1.
      { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
      ss. irw. pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et).
          - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
          - ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (first[econsby ss; et|econs; ss; et]). cbn. des_ifs. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { cbn. rewrite Int.eq_true; ss.
          repeat (first[econsby ss; et|econs; ss; et]).
          cbn. des_ifs.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        apply star_refl.
      }
      left. pfold. econs; ss; et.
      { econs; ss; et. }
    }
    destruct (Mem.store Mptr m2 b_y0 8 (Vptr b_x0 Ptrofs.zero)) eqn:S0; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    ss. irw.
    destruct (Mem.store Mint32 m b_x0 0 (Vint (Int.add xRank Int.one))) eqn:S1; cycle 1.
    { ss. pfold. unfold triggerUB. irw. econs; ss; et. }
    ss. irw.
    pfold. econs; ss; et; cycle 1.
    { eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et).
        - cbn. unfold Cop.cmp_ptr. des_ifs. unfold option_map. des_ifs.
        - ss.
      }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (first[econsby ss; et|econs; ss; et]). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (first[econsby ss; et|econs; ss; et]). cbn. des_ifs. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { cbn. rewrite Int.eq_true; ss.
        repeat (first[econsby ss; et|econs; ss; et]).
        cbn. des_ifs.
      }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { _step. }
      apply star_refl.
    }
    left. pfold. econs; ss; et.
    { econs; ss; et. }
Qed.
