Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.

Set Implicit Arguments.

Local Opaque Z.mul.

Section PRESERVATION.

  Existing Instance Val.mi_final.

(** PLAN B-0*)

(*
B-0
* : Physical
+ : Logical 
c0 * empty
>=
c0 + empty
*)
  
 
  Section PLANB0.
(** ********************* linking *********************************)  

  (* Variable prog0: Csyntax.program. *)

  (* Lemma empty_lemma *)
  (*   : *)
  (*     build_composite_env nil = Errors.OK (PTree.empty composite). *)
  (* Proof. auto. Qed. *)
  
  (* Let empty_prog : Csyntax.program := *)
  (*   Build_program nil nil prog0.(prog_main) nil empty_lemma. *)

  Variable prog: Csyntax.program.
  (* Hypothesis LINK : link prog0 empty_prog = Some prog. *)
  Let tprog : Syntax.program := List.map CsemC.module [prog].
  
  (* TODO: prog always exists *)

(** ********************* genv *********************************)

  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link := Sk.load_skenv sk_tgt.

  Let ge := globalenv prog.
  Let tge_ce : composite_env := prog_comp_env prog.
  Let tge := load_genv tprog skenv_link.

  Inductive match_states : Csem.state -> Sem.state -> nat -> Prop :=
  | match_states_intro
      fr frs (st: Csem.state)
      (* frs are frame of C *)
      (FRAME: fr = Frame.mk (CsemC.modsem skenv_link prog) st)
      (FRAMES: forall fr', In fr' frs -> exists st', fr' = Frame.mk (CsemC.modsem skenv_link prog) st')
    :
      match_states st (Sem.State (fr::frs)) 0
  .  
  
  Definition local_genv (p : Csyntax.program) :=
    (skenv_link.(SkEnv.project) p.(defs)).(revive) p.

  (* Inductive genv_match (j: meminj) (src_ge tgt_ge: Genv.t fundef unit): Prop := *)
  (* | genv_match_intro *)
  (*     (SYMB: forall id b (FIND: Genv.find_symbol tgt_ge id = Some b), *)
  (*         Genv.find_symbol src_ge id = Some b) *)
  (*     (DEFS: forall b d (FIND: Genv.find_def tgt_ge b = Some d), *)
  (*         Genv.find_def src_ge b = Some d). *)

  Lemma symb_preserved id
    :
      Senv.public_symbol (symbolenv (sem tprog)) id =
      Senv.public_symbol (symbolenv (semantics prog)) id.
  Proof.
  Admitted.

  Lemma transf_initial_states:
    forall st1, Csem.initial_state prog st1 ->
           exists st2, Sem.initial_state tprog st2 /\ match_states st1 st2 0.
  Proof.
    (* i. inv H. esplits. *)
    (* - econs; eauto. *)
  Admitted.

(** ********************* transf step  *********************************)

  Lemma match_state_xsim
    :
      forall st_src st_tgt (MTCHST: match_states st_src st_tgt 0),
        xsim (Csem.semantics prog) (Sem.sem tprog) lt 0%nat st_src st_tgt.
  Proof.
    pcofix CIH. i. pfold.
    inv MTCHST. destruct st_src.
    - (* State *)
      right. econs.
      + i. inv FINALTGT. inv FINAL.
      + i. econs. i. inv STEPTGT; try (by (ss; des_ifs)).
        * ss. des_ifs. inv AT.
        * ss. inv STEP; ss.
          { inv H. }
          exists 0%nat, st0.
          split.
          ** left. apply plus_one. econs 2.
             inv H; try (by econs).
          ** right. eapply CIH.
             econs; eauto.
        * inv FINAL.
      + (* progress *)
        i.
        specialize (SAFESRC _ (star_refl _ _ _)). inv SAFESRC.
        * des. inv H.
        * right. des.
          exists t. des_ifs. ss. eexists. econs. ss.
          inv H. inv H0.
          right. inv H0; try (by econs).
    - (* ExprState *)
      right. econs.
      + i. inv FINALTGT. inv FINAL.
      + i. econs. i. inv STEPTGT; try (by (ss; des_ifs)).
        * ss. des_ifs. inv AT.
        * ss. inv STEP; ss.
          ** exists 0%nat, st0.
             split; cycle 1.
             { right. eapply CIH.
               econs; eauto. }
             { left. apply plus_one. econs 1.
               inv H; try (econs; eauto).
               - inv H7; try (by econs; eauto).
                 econs 2; eauto.
                 exploit Sk.load_skenv_wf. instantiate (1 := sk_tgt). i.
                 inv H1.
                 unfold Genv.find_symbol in *. ss.
                 rewrite MapsC.PTree_filter_key_spec in H0.
                 des_ifs. admit "".
               - inv H7; try (by econs; eauto).
                 + econs; eauto.
                   inv H; try (by econs; eauto).
                   econs; eauto.
                   admit "".
                 + unfold sizeof. ss. fold sizeof.
                   econs.
                 + unfold sizeof. ss. fold sizeof.
                   econs.
                 + econs; eauto. admit "".
                 + econs. admit "".
                 + econs; eauto. admit "".
                 + econs; eauto. admit "".
               - admit "". }
          ** exists 0%nat, st0.
             split; cycle 1.
             { right. eapply CIH.
               econs; eauto. }
             { left. apply plus_one. econs 2.
               inv H; try (by econs). }
        * inv FINAL.
      + (* progress *)
        i.
        specialize (SAFESRC _ (star_refl _ _ _)). des.
        * left. inv SAFESRC.
        * right.
          inv SAFESRC.
          ** inv H.
             { exploit step_internal; eauto; ss. econs 1. econs; eauto. admit "". }
             { exploit step_internal; eauto; ss. econs 1. econs 2; eauto. admit "". }
             { exploit step_internal; eauto; ss. econs 1. econs 3; eauto. }
             { exploit step_internal; eauto; ss. econs 1. econs 4; eauto. admit "". }
          ** inv H; exploit step_internal; eauto; ss; try (by econs 2; econs; eauto).
    - (* Callstate *)
      right. econs.
      + i. inv FINALTGT. inv FINAL.
      + i. econs. i. inv STEPTGT.
        * ss. inv AT. inv EXTERNAL. des.
          admit " by SIG && H0".
        * ss. inv STEP; ss.
          { inv H. }
          exists 0%nat, st0.
          split.
          ** left. apply plus_one. econs 2.
             inv H; try (by econs).
             { ss.  econs; eauto.
               - admit "".
               - instantiate (1 := m1). admit "".
               - admit "".
             }
             { ss. econs; admit "". }
          ** right. eapply CIH.
             econs; eauto.
        * inv FINAL.
      + (* progress *)
        i.
        specialize (SAFESRC _ (star_refl _ _ _)). des.
        * left. inv SAFESRC.
        * right.
          inv SAFESRC.
          { inv H. }
          exists t. eexists. econs. ss.
          inv H; econs 2; ss.
          { admit "prove it". }
          { admit "prove it". }
    - (* Returnstate *)
      right. econs.
      + i. inv FINALTGT. inv FINAL. ss. esplits.
        * econs.
        * rewrite INT. econs.
      + i. econs. i. inversion STEPTGT; ss.
        * inv AT.
        * inv STEP.
          { inv H. }
          inv H.
          exists 0%nat.
          esplits.
          ** left. apply plus_one. econs 2.
             econs.
          ** right. eapply CIH.
             econs; eauto.
        * subst. inv FINAL.
          
          admit "how can i prove st0 is state of C ?".
      + (* progress *)
        i.
        specialize (SAFESRC _ (star_refl _ _ _)). des.
        * destruct frs as [| fr' frs'].
          ** left. ss. inv SAFESRC. exists r0. econs; ss.
          ** right. ss. inv SAFESRC.
             exists E0.
             esplits. eapply step_return; ss.
             specialize (FRAMES fr').
             exploit FRAMES; auto. i. des. subst. ss.
             admit "not trivial. st' state?? ".
        * right.
          inv SAFESRC.
          { inv H. }
          exists t. eexists. econs. ss.
          inv H; econs 2; ss. econs.
    - (* Stuckstate *)
      right. econs.
      + i. inv FINALTGT. inv FINAL.
      + i. econs. i. inv STEPTGT; try (by (ss; des_ifs)).
        * ss. des_ifs. inv AT.
        * ss. inv STEP; ss; inv H.
        * inv FINAL.
      + (* progress *)
        i.
        specialize (SAFESRC _ (star_refl _ _ _)). inv SAFESRC.
        * des. inv H.
        * right. des; inv H; inv H0.
      Unshelve.
      auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
      destruct fr'. ss.
  Qed.

  Lemma transf_xsim_properties
    :
        xsim_properties (Csem.semantics prog) (Sem.sem tprog) nat lt.
  Proof.
    econs; [apply lt_wf| |apply symb_preserved].
    econs. i.
    exploit (transf_initial_states); eauto.
    i. des. esplits. econs; eauto.
    - i. inv INIT0. inv INIT1. clarify.
    - apply match_state_xsim; eauto.
  Qed.

  Lemma transf_program_correct:
    mixed_simulation (Csem.semantics prog) (Sem.sem tprog).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.


  End PLANB0.

End PRESERVATION.
