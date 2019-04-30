 Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.
Require Import Equality.
Require Import CtypingC.
Require Import UpperBound_A.
Require Import UpperBound_A.

Set Implicit Arguments.



Section SIM.

  Variable cp_link cp0 cp1: Csyntax.program.
  Variable ctx: Syntax.program.
  Hypothesis FOCUS: link cp0 cp1 = Some cp_link.
  (* Let prog_src := cp_link.(CsemC.module) :: ctx. *)
  (* Let prog_tgt := cp1.(CsemC.module) :: cp2.(CsemC.module) :: ctx. *)
  Let prog_src := ctx ++ [cp_link.(CsemC.module)].
  Let prog_tgt := ctx ++ [cp0.(CsemC.module) ; cp1.(CsemC.module)].
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk prog_src = Some sk_link).

  Notation " 'geof' cp" := (Build_genv (SkEnv.revive (SkEnv.project skenv_link cp.(CSk.of_program signature_of_function)) cp) cp.(prog_comp_env))
                           (at level 50, no associativity, only parsing).

  Let sum_cont := sum_cont cp0 cp1 sk_link.

  Lemma call_cont_app_cont
        k k0
        tl_tgt (SUM: sum_cont tl_tgt k0)
    (* (CASE: k0 = Kstop \/ is_call_cont_strong k0) *)
    :
      (app_cont (call_cont k) k0) = call_cont (app_cont k k0)
  .
  Proof.
    clear - SUM.
    assert(CASE: k0 = Kstop \/ is_call_cont_strong k0).
    { inv SUM; ss; et. des. clarify. ss. et. }
    clear SUM. clear_tac.
    des.
    { clarify. repeat rewrite app_cont_stop_right. ss. }
    {
      rr in CASE. des_ifs. clear_tac. clear - c.
      ginduction k; ii; ss; des; repeat rewrite app_cont_stop_right; ss; clarify.
    }
  Qed.

  Definition matched_state_source (st_tgt: Csem.state) (k0: cont): Csem.state :=
    match st_tgt with
    | Csem.State f s k1 e m => Csem.State f s (app_cont k1 k0) e m
    | Csem.ExprState f ex k1 e m => Csem.ExprState f ex (app_cont k1 k0) e m
    | Csem.Callstate fptr tyf vargs k1 m => Csem.Callstate fptr tyf vargs (app_cont k1 k0) m
    | Csem.Returnstate vres k1 m => Csem.Returnstate vres (app_cont k1 k0) m
    | Csem.Stuckstate => Csem.Stuckstate
    end
  .

  Lemma match_focus_state_iff
        st_src0 st_tgt0 k0
    :
      <<MATCH: match_focus_state st_src0 st_tgt0 k0>> <-> <<MATCH: st_src0 = matched_state_source st_tgt0 k0>>
  .
  Proof.
    split; i.
    - inv H; ss.
    - des. clarify. r. destruct st_tgt0; ss; try (by econs; eauto).
      admit "".
  Qed.

  Lemma match_focus_state_bsim
        cst_src0 cst_tgt0 cst_tgt1 k0 cp tr
        (ST: match_focus_state cst_src0 cst_tgt0 k0)
        (FOC: linkorder cp cp_link)
        (WTSRC: wt_state (geof cp_link) cst_src0)
        (WTTGT: wt_state (geof cp) cst_tgt0)
        (STEP: Csem.step skenv_link (geof cp) cst_tgt0 tr cst_tgt1)
        tl_tgt
        (SUM: sum_cont tl_tgt k0)
    :
      (* exists cst_src1, <<STEP: Csem.step skenv_link (geof cp_link) cst_src0 tr cst_src1>> *)
      <<STEP: Csem.step skenv_link (geof cp_link) cst_src0 tr (matched_state_source cst_tgt1 k0)>>
  .
  Proof.
    pose cst_tgt1 as XXX.
    assert(EXTENDS: forall id cmp (IN: (prog_comp_env cp) ! id = Some cmp),
              <<IN: (prog_comp_env cp_link) ! id = Some cmp>>).
    { admit "ez". }
    unfold NW in *. (* TODO: Hint Unfold NW does not work !!! *)
    rr in STEP. des.
    - left.
      inv STEP; inv ST; econs; eauto.
      + (* lred *)
        inv H; econs; ss; eauto.
        * admit "ez - genv".
        * hexploit (prog_comp_env_eq cp); et. intro X.
          exploit build_composite_env_consistent; et. intro Y.
          exploit co_consistent_complete; et. intro Z.
          admit "field_offset: make lemma".
      + (* rred *)
        rename C into CC.
        inv H; try (econs; ss; eauto); ss.
        * destruct op; ss.
          { admit "sem_binary_operation: make lemma". }
          { admit "sem_binary_operation: make lemma". }
        * rpapply red_sizeof; eauto. ss.
          erewrite <- sizeof_stable; eauto.
          clear - H0 WTTGT.
          admit "strengthen typechecker".
        * rpapply red_alignof; eauto. ss.
          admit "strengthen typechecker".
        * inv H2; try (by econs; eauto).
          econs 3; ss; eauto.
          admit "strengthen typechecker and make lemma".
          admit "strengthen typechecker".
          admit "strengthen typechecker".
          admit "strengthen typechecker".
      + ii. eapply H0.
        inv H1.
        * econs 1; eauto.
        * econs 2; eauto.
        * econs 3; eauto.
          admit "lred progress (make a lemma)".
        * econs 4; eauto.
          admit "rred progress (make a lemma)".
        * econs 5; eauto.
    - right.
      inv STEP; inv ST; try (by econs; eauto).
      + ss. rpapply step_return_0; eauto.
        * admit "strengthen typechecker".
        * erewrite call_cont_app_cont; et.
      + ss. rpapply step_return_2; eauto.
        * admit "strengthen typechecker".
        * erewrite call_cont_app_cont; et.
      + ss. eapply step_skip_call; eauto.
        * exploit Cstrategy.is_call_cont_call_cont; et. intro T.
          (* TODO: make lemma *)
          clear - H T SUM. unfold is_call_cont in H. des_ifs. ss. inv SUM; ss. des; clarify.
        * admit "strengthen typechecker".
      + ss. eapply step_goto; et.
        clear - SUM H.
        erewrite <- call_cont_app_cont; et.
        admit "make lemma".
      + ss. eapply step_internal_function; et.
        * admit "quantify NCALLTGT".
        * admit "strengthen typechecker".
        * admit "strengthen typechecker".
      + exfalso.
        admit "quantify NCALLSRC".
  Admitted.

End SIM. 