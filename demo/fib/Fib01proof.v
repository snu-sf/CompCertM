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
Require Import FibHeader.
Require Import Fib1.
Require Import Fib0.
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

(* Local Opaque PTree.get. *)
(*** TODO: move to Fib0 ***)
Opaque _fib.
Theorem correct: rusc defaultR [Fib1.module: Mod.t] [Fib0.module: Mod.t].
Proof.
  eapply SIRUnstackproof.correct; ss; et.
  econs; ss; et.
  - ii. u. des_ifs. unfold internal_funs. des_ifs. exploit prog_defmap_image; et. ss. ii; des; ss.
  - ii.
    (*** THIS SHOULD BE PROVIDED FROM META THEORY ***)
    assert(exists fblk, <<SYMB: Genv.find_symbol (geof skenv_link prog) _fib = Some fblk>>).
    {
      inv INCL. ss.
      exploit (DEFS _fib); et.
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
    assert(FIBDEF: forall
              fblk
              (SYMB: Genv.find_symbol (geof skenv_link prog) _fib = Some fblk)
            ,
              <<DEF: Genv.find_funct (geof skenv_link prog) (Vptr fblk Ptrofs.zero)
                     = Some (Ctypes.Internal f_fib)>>).
    { i.
      exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
      des. ss. des_ifs. clear_tac.
      exploit CSkEnv.project_revive_precise; et. intro T. inv T.
      exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
      exploit prog_defmap_dom; et. intro V; des.
      exploit P2GE; et. intro W; des.
      folder.
      assert(fblk = b).
      { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
      clarify.
      exploit (prog_defmap_norepet prog _fib); ss; et.
      { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. }
      intro T. clarify. ss.
      unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss.
    }
    exploit FIBDEF; et. intro DEF. clear FIBDEF.
    des.


    exploit prog_defmap_image; et. ss. ii; des; ss. clarify.
    exploit (prog_defmap_norepet prog _fib); et.
    { repeat (econs; ss; et). }
    { ss; et. }
    ii; clarify. cbn in SRC. des_ifs. clear_tac.
    econs; ss; et. ii. inv TYP. ss. destruct vs0; ss. destruct vs0; ss. cbn in TYP0. clarify.
    clear_tac.

    esplits; et.
    { repeat (econs; ss; et).
      ii; ss; try (by repeat des; ss; clarify).
    }
    assert(exists n, v = Vint n).
    { inv DEF0. unfold typify in H0. des_ifs. destruct v; ss; et. }
    des. clarify. clear H0.
    destruct (classic (Int.eq n Int.zero)).
    { apply_all_once Int.same_if_eq. clarify.
      pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        des_ifs.
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        apply star_refl.
      }
      { des_ifs. left. pfold. econs; ss; et. econs; ss; et. }
    }
    rename H into NZERO.
    destruct (classic (Int.eq n Int.one)).
    { apply_all_once Int.same_if_eq. clarify.
      pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        des_ifs.
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
      { des_ifs. left. pfold. econs; ss; et. econs; ss; et. }
    }
    rename H into NONE.

    {
      pfold. econs; ss; et; cycle 1.
      { eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). ss. rewrite Int.eq_false; ss. ii; clarify. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { _step. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). ss. rewrite Int.eq_false; ss. ii; clarify. }
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
      des_ifs. rewrite bind_trigger.
      left. pfold. econs; ss; et.
      { econs; ss; et. cbn. unfold typify. des_ifs; ss. }
      { econs; ss. }
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
        { _step. }
        apply star_refl.
      }
      left. pfold.
      rewrite bind_trigger.
      econs; ss; et.
      { econs; ss; et. cbn. unfold typify. des_ifs; ss. }
      { econs; ss; et. }
      ii. inv TYP; ss. inv TYP0; ss. clear_tac.
      left. pfold. econs; ss; et; cycle 1.
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
      { left. pfold. econs; ss; et. econs; ss; et. }
    }
Qed.



(* Section SIMMODSEM. *)

(* Variable skenv_link: SkEnv.t. *)
(* Variable sm_link: SimMem.t. *)
(* Let md_src: Mod.t := (Fib1.module). *)
(* Let md_tgt: Mod.t := (Fib0.module). *)
(* Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)). *)
(* (* Let INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt). *) *)
(* (* Proof. ss. Qed. *) *)
(* Hypothesis (WF: SkEnv.wf skenv_link). *)
(* Let ge := (SkEnv.project skenv_link (Mod.sk md_src)). *)
(* Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env). *)
(* Definition msp: ModSemPair.t := *)
(*   ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link. *)

(* Global Opaque _fib. *)
(* Lemma unsymb *)
(*       fid fblk *)
(*       (FID: Genv.find_symbol ge fid = Some fblk) *)
(*   : *)
(*     <<FID: fid = _fib>> *)
(* . *)
(* Proof. *)
(*   subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs. *)
(*   unfold defs in *. des_sumbool. ss. des; ss. *)
(* Qed. *)

(* Lemma symb_fib *)
(*   : *)
(*     exists fblk, <<FID: Genv.find_symbol tge _fib = Some fblk>> *)
(* . *)
(* Proof. *)
(*   inv INCL. ss. *)
(*   exploit (DEFS _fib); et. *)
(*   { unfold prog_defmap. ss. } *)
(*   i; des. ss. folder. *)
(*   clear - SYMB. *)
(*   subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. et. *)
(* Qed. *)

(* Lemma fib_def *)
(*       fblk *)
(*       (SYMB: Genv.find_symbol ge _fib = Some fblk) *)
(*   : *)
(*     <<DEF: Genv.find_funct tge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal f_fib)>> *)
(* . *)
(* Proof. *)
(*   exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC. *)
(*   des. subst tge. ss. des_ifs. clear_tac. *)
(*   exploit CSkEnv.project_revive_precise; et. intro T. inv T. *)
(*   exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool. *)
(*   exploit prog_defmap_dom; et. intro V; des. *)
(*   exploit P2GE; et. intro W; des. *)
(*   folder. *)
(*   assert(fblk = b). *)
(*   { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. } *)
(*   clarify. *)
(*   exploit (prog_defmap_norepet prog _fib); ss; et. *)
(*   { repeat (econs; ss; et; [ii; des; ss|]); repeat econs; ss; et. } *)
(*   intro T. clarify. ss. *)
(*   unfold Genv.find_funct_ptr. unfold Clight.fundef. rewrite DEF. ss. *)
(* Qed. *)


