Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import MutrecHeader.
Require Import MutrecAspec MutrecBspec MutrecABspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SimMemId.
Require SoundTop.
Require Import Clightdefs.
Require Import CtypesC.
Require Import BehaviorsC.
Require Import Simulation Sem SemProps LinkingC.

Set Implicit Arguments.

(* Section SIMMODSEM. *)

(* Variable skenv_link: SkEnv.t. *)
(* Variable sm_link: SimMem.t. *)
(* Let md_src: Mod.t := (MutrecAspec.module). *)
(* Let md_tgt: Mod.t := (MutrecBspec.module). *)
(* Hypothesis (INCLSRC: SkEnv.includes skenv_link md_src.(Mod.sk)). *)
(* Hypothesis (INCLTGT: SkEnv.includes skenv_link md_tgt.(Mod.sk)). *)
(* Hypothesis (WF: SkEnv.wf skenv_link). *)
(* Let ge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_src.(Mod.sk)) MutrecA.prog) MutrecA.prog.(prog_comp_env). *)
(* Let tge := skenv_link.(SkEnv.revive) MutrecB.prog. *)
(* Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) tt sm_link. *)

(* End SIMMODSEM. *)

Lemma link_sk_same
      ctx
  :
    link_sk (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)])
    = link_sk (ctx ++ [module])
.
Proof.
  admit "see UpperBound_A extra".
Qed.

Lemma wf_module_Aspec: Sk.wf MutrecAspec.module.
Proof.
  admit "ez".
Qed.

Lemma wf_module_Bspec: Sk.wf MutrecBspec.module.
Proof.
  admit "ez".
Qed.

Definition is_focus (x: Mod.t) := x = MutrecAspec.module \/ x = MutrecBspec.module.

Section LXSIM.

  Variable ctx: Syntax.program.
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk (ctx ++ [module]) = Some sk_link).
  Let LINKTGT: link_sk (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)]) = Some sk_link.
  Proof. rewrite link_sk_same. ss. Qed.

  Lemma genv_sim
        fptr if_sig
    :
      (<<FINDF: Genv.find_funct (SkEnv.project skenv_link MutrecABspec.sk_link) fptr =
                Some (AST.Internal if_sig)>>)
      <->
      (<<FINDF: exists md, (<<FOCUS: is_focus md>>) /\
                           (<<FINDF: Genv.find_funct (ModSem.skenv (flip Mod.modsem skenv_link md)) fptr =
                                     Some (AST.Internal if_sig)>>)>>)
  .
  Proof.
    admit "ez".
  Qed.

  (* Axiom match_focus: Z -> Frame.t -> list Frame.t -> Prop. *)
  Inductive match_focus: mem -> Z -> Z -> list Frame.t -> Prop :=
  | match_focus_cons_A
      cur max m i tl_tgt
      (LE: (cur <= max)%Z)
      (VAL: i.(Int.intval) = cur)
      (REC: match_focus m (cur + 1)%Z max tl_tgt \/ cur = max)
    :
      match_focus m cur max ((Frame.mk (MutrecAspec.modsem skenv_link tt) (MutrecAspec.Callstate i m)) :: tl_tgt)
  | match_focus_cons_B
      cur max m i tl_tgt
      (LE: (cur <= max)%Z)
      (VAL: i.(Int.intval) = cur)
      (REC: match_focus m (cur + 1)%Z max tl_tgt \/ cur = max)
    :
      match_focus m cur max ((Frame.mk (MutrecBspec.modsem skenv_link tt) (MutrecBspec.Callstate i m)) :: tl_tgt)
  .

  Inductive match_stacks: Z -> list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_nil
    :
      match_stacks 0%Z [] []
  | match_stacks_cons_ctx
      i tail_src tail_tgt
      (TAIL: match_stacks i tail_src tail_tgt)
      hd
    :
      match_stacks 0%Z (hd :: tail_src) (hd :: tail_tgt)
  | match_stacks_focus
      j tail_src tail_tgt
      (TAIL: match_stacks j tail_src tail_tgt)
      i cur z m hd_src hds_tgt
      (SRC: hd_src = Frame.mk (MutrecABspec.modsem skenv_link tt) (MutrecABspec.Callstate i m))
      (VAL: i.(Int.intval) = z)
      (TGT: match_focus m cur z hds_tgt)
    :
      match_stacks z (hd_src :: tail_src) (hds_tgt ++ tail_tgt)
  .

  Inductive match_states (i: Z): Sem.state -> Sem.state -> Prop :=
  | match_states_normal
      frs_src frs_tgt
      (STK: match_stacks i frs_src frs_tgt)
    :
      match_states i (State frs_src) (State frs_tgt)
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks i frs_src frs_tgt)
    :
      match_states i (Callstate args frs_src) (Callstate args frs_tgt)
  .

  Lemma match_states_xsim
        i st_src0 st_tgt0
        (MATCH: match_states i st_src0 st_tgt0)
    :
      xsim (sem (ctx ++ [module])) (sem (ctx ++ [MutrecAspec.module; MutrecBspec.module]))
           Z.lt i st_src0 st_tgt0
  .
  Proof.
    revert_until LINKTGT. pcofix CIH. i.
    inv MATCH; cycle 1.
    - (* Sem.Callstate *)
      pfold. right.
      econs; et.
      { ss. i. inv FINALTGT; ss. }
      econs; et; cycle 1.
      { i; ss. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
        - left. inv SAFESRC.
        - right. des_ifs. inv SAFESRC. inv MSFIND. ss. des.
          { esplits; et. econs; et. econs; et. ss; et. }
          unfold load_modsems in *. rewrite in_map_iff in *. des. clarify.
          rewrite in_app_iff in *. des; clarify.
          { esplits; et. econs; et. econs; et. ss; et. right.
            unfold load_modsems in *. rewrite in_map_iff in *. esplits; et. rewrite in_app_iff. et.
          }
          ss. des; clarify.
          exploit genv_sim; et. i; des. exploit FINDF; et. i; des. rr in FOCUS.
          des; clarify; inv INIT; esplits; et.
          + econs.
            * instantiate (1:= MutrecAspec.modsem skenv_link tt). econs; et. ss. right.
              unfold load_modsems, flip in *; rewrite in_map_iff in *; folder; esplits; et; cycle 1.
              { rewrite in_app_iff; ss. right. left. et. }
              ss.
            * econs; ss; et.
              admit "ez - revive// TODO: make lemma".
          + econs.
            * instantiate (1:= MutrecBspec.modsem skenv_link tt). econs; et. ss. right.
              unfold load_modsems, flip in *; rewrite in_map_iff in *; folder; esplits; et; cycle 1.
              { rewrite in_app_iff; ss. right. right. et. }
              ss.
            * econs; ss; et.
              admit "ez - revive// TODO: make lemma".
      }
      i. ss. des_ifs. inv STEPTGT.
      inv MSFIND. ss. des; clarify.
      { (* system *)
        inv INIT. esplits; eauto.
        + left. apply plus_one. esplits; eauto; cycle 1.
          econs; et.
          { econs; ss; et. }
          econs; et.
        + right. eapply CIH; et. econs; et. econs; et.
      }
      unfold load_modsems in *. rewrite in_map_iff in *. des.
      clarify.
      rewrite in_app_iff in *. des; clarify.
      { (* ctx *)
        esplits; eauto.
        + left. apply plus_one. econs; et. econs; et. ss. right.
          unfold load_modsems in *. rewrite in_map_iff. esplits; et.
          rewrite in_app_iff. ss. et.
        + right. eapply CIH; et. econs; et. econs; et.
      }
      (* real *)
      folder.
      assert(exists i, <<ARGS: Args.vs args = [Vint i]>>).
      { ss. des; clarify; inv INIT; et. }
      des.
      esplits; et.
      + left. apply plus_one. econs.
        { instantiate (1:= modsem skenv_link tt). econs; ss; et.
          - right.
            unfold load_modsems in *. rewrite in_map_iff. unfold flip. esplits; et; cycle 1.
            { rewrite in_app_iff. ss. et. }
            ss.
          - instantiate (1:= if_sig).
            eapply genv_sim; et. esplits; et. rr; des; ss; et.
        }
        econs; et.
        eapply genv_sim; et. esplits; et. rr; des; ss; et. des; clarify; et.
      + right. eapply CIH. instantiate (1:= i0.(Int.intval)). econs; et. rewrite cons_app with (xtl := frs_tgt).
        econs 3; et.
        destruct args; ss. clarify.
        des; ss; clarify.
        * inv INIT; ss; clarify. econs; et. refl.
        * inv INIT; ss; clarify. econs; et. refl.
    - (* Sem.State *)
      inv STK.
      + pfold. left. right. econs; et.
        econs; et; cycle 1.
        { ss. i. inv FINALSRC; ss. }
        i. ss. des_ifs. inv STEPSRC.
      + pfold. right. econs; et.
        { ss. i. inv FINALTGT; ss. inv TAIL; ss; cycle 1.
          { destruct hds_tgt, tail_tgt; ss. inv TGT; ss. }
          esplits; et.
          { apply star_refl. }
          econs; ss; et.
        }
        i.
        econs; et; cycle 1.
        { ss. i. specialize (SAFESRC _ (star_refl _ _ _ _)). des.
          - left. inv SAFESRC. inv TAIL. esplits; et. econs; et.
          - right. des_ifs. inv SAFESRC; inv TAIL; try (by esplits; et; econs; et).
        }
        i. ss. des_ifs. inv STEPTGT; ss.
        * esplits; et.
          { left. apply plus_one. econs; et. }
          right. eapply CIH; et. econs; et. econs; et.
        * esplits; et.
          { left. apply plus_one. econs; et. }
          right. eapply CIH; et. econs; et. econs; et.
        * inv TAIL.
          -- esplits; et.
             { left. apply plus_one. econs 4; et. }
             right. eapply CIH; et. econs; et. econs; et.
          -- esplits; et.
             { left. apply plus_one. econs 4; et. ss. TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT }
             right. eapply CIH; et. econs; et. econs; et.
          econs; et.
      inv MSFIND. ss. des; clarify.
      { (* system *)
        inv INIT. esplits; eauto.
        + left. esplits; eauto; cycle 1.
          { admit "ez - semprops receptive". }
          apply plus_one.
          econs; et.
          { admit "ez - semprops determinate". }
          ss. des_ifs. econs; et.
          { econs; ss; et. }
          econs; et.
        + right. eapply CIH; et. econs; et. econs; et.
      }
      unfold load_modsems in *.
      rewrite in_map_iff in *. des. clarify. rewrite in_app_iff in *. des; clarify.
      { (* ctx *)
        esplits; eauto.
        + left. esplits; eauto; cycle 1.
          { admit "ez - semprops receptive". }
          apply plus_one.
          econs; et.
          { admit "ez - semprops determinate". }
          ss. des_ifs. econs; et.
          { econs; ss; et. }
          econs; et.
        + right. eapply CIH; et. econs; et. econs; et.
        +
      }
    -
    admit "".
  Qed.

End LXSIM.
  

Theorem mutrecABcorrect
        ctx
  :
    (* (<<REFINE: improves (Sem.sem ([(MutrecABspec.module)] ++ ctx)) *)
    (*                     (Sem.sem ([(MutrecAspec.module) ; (MutrecBspec.module)] ++ ctx)) *)
    (*                     >>) *)
    (<<REFINE: improves (Sem.sem (ctx ++ [(MutrecABspec.module)]))
                        (Sem.sem (ctx ++ [(MutrecAspec.module) ; (MutrecBspec.module)]))
                        >>)
.
Proof.
  eapply bsim_improves.
  eapply mixed_to_backward_simulation.
  econs; eauto.
  econs; swap 2 3.
  { apply lt_wf. }
  { i; des. ss. inv SAFESRC. rewrite INITSK.
    ss. rewrite link_sk_same. des_ifs.
  }
  econs; eauto.
  i. ss. inv INITSRC.
  esplits; eauto.
  { econs; ss; eauto.
    - econs; eauto.
      + rewrite link_sk_same. ss.
      + ii; ss. rewrite in_app_iff in *. des; ss.
        { eapply WF; et. rewrite in_app_iff. et. }
        des; ss; clarify.
        * eapply wf_module_Aspec; et.
        * eapply wf_module_Bspec; et.
    - i; ss. inv INIT0. inv INIT1. clarify.
  }
  eapply match_states_xsim; et.
  econs; et. econs; et.
Qed.


(* Inductive match_states_internal: MutrecABspec.state -> Clight.state -> Prop := *)
(* | match_callstate_nonzero *)
(*     i m_src m_tgt *)
(*     fptr *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_returnstate *)
(*     i m_src m_tgt *)
(*   : *)
(*     match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt) *)
(* . *)

(* Inductive match_states (sm_init: SimMem.t) *)
(*           (idx: nat) (st_src0: MutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop := *)
(* | match_states_intro *)
(*     (MATCHST: match_states_internal st_src0 st_tgt0) *)
(*     (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src)) *)
(*     (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt)) *)
(*     (MWF: SimMem.wf sm0) *)
(*     (IDX: (idx > 3)%nat) *)
(* . *)

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link md_src.(Mod.sk)) (SkEnv.project skenv_link md_tgt.(Mod.sk)) ->
  Genv.match_genvs (match_globdef (fun _ => eq) eq tt) ge tge.
Proof.
  subst_locals. ss. ii.
  eapply SimSymbId.sim_skenv_revive; eauto.
  admit "ez - reflexivity".
Qed.

Lemma g_blk_exists
  :
    exists g_blk,
      (<<FINDG: Genv.find_symbol
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_id = Some g_blk>>)
      /\
      (<<FINDG: Genv.find_funct_ptr
                  (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                  g_blk = None>>)
      /\
      (<<FINDG: exists skd, Genv.find_funct_ptr skenv_link g_blk = Some skd /\
                            signature_of_type (Tcons tint Tnil) tint cc_default = SkEnv.get_sig skd>>)
.
Proof.
  exploit (prog_defmap_norepet prog g_id); eauto.
  { unfold prog_defs_names. ss. repeat (econs; eauto). ii; ss; des; ss. }
  { ss. eauto. }
  intro T; des.
  exploit SkEnv.project_impl_spec; eauto. intro PROJ.
  assert(PREC: SkEnv.genv_precise
                 (SkEnv.revive (SkEnv.project skenv_link (CSk.of_program signature_of_function prog)) prog)
                 prog).
  { eapply CSkEnv.project_revive_precise; ss; et. }
  inv PREC.
  exploit (P2GE g_id); eauto. i; des. des_ifs.
  rename b into g_blk.
  eexists. splits; et.
  { unfold Genv.find_funct_ptr. des_ifs. }
  (* exploit (@SkEnv.project_revive_precise _ _ skenv_link); eauto. *)
  { inv INCLSRC.
    exploit (CSk.of_program_prog_defmap prog signature_of_function); et. rewrite T. intro S.

    remember ((prog_defmap (CSk.of_program signature_of_function prog)) ! g_id) as U in *.
    destruct U eqn:V; try (by ss). inv S. inv H1.

    exploit DEFS; eauto. i; des.
    assert(blk = g_blk).
    { inv PROJ. exploit SYMBKEEP; et.
      - instantiate (1:= g_id). unfold defs. des_sumbool. ss. et.
      - i. rewrite SYMB0 in *. clear - SYMB H. unfold SkEnv.revive in *. rewrite Genv_map_defs_symb in *. ss.
        rewrite SYMB in *. des. clarify.
    }
    clarify. inv MATCH.
    esplits; eauto.
    - unfold Genv.find_funct_ptr. rewrite DEF0. et.
    - ss. des_ifs. clear - H1. inv H1; ss.
  }
Qed.

Lemma match_states_lxsim
      sm_init idx st_src0 st_tgt0 sm0
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun st => exists su m_init, SoundTop.sound_state su m_init st)
                  sm_init (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until tge.
  pcofix CIH.
  i.
  pfold.
  generalize g_blk_exists; et. i; des.
  inv MATCH. ss. inv MATCHST; ss; clarify.
  - (* call *)
    destruct (classic (i = Int.zero)).
    + (* zero *)
      clarify.
      econs 1. i; des.
      econs 1; cycle 2.
      { admit "ez - spec is receptive". }
      { split; ii; rr in H; inv H; inv H0; ss. }
      i. ss. inv STEPSRC.
      esplits; eauto.
      * left.
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss.
          - ss.
        }

        apply star_refl.
      (* * refl. *)
      * right. eapply CIH. econs; ss; eauto. econs; eauto.
    + (* nonzero *)
      econs.
      i; des.
      econs 2; eauto.
      * esplits; cycle 1.
        { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). lia. }

        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify.
        }
        
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
          - repeat econs; et.
          - ss. rewrite Int.eq_false; ss.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto.
        }

        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          { eapply modsem2_determinate; eauto. }
          econs; eauto; swap 1 2.
          - econs.
            + eapply eval_Evar_global; ss. et.
            + econs 2; et.
          - unfold Cop.classify_fun. ss.
          - repeat econs; ss; et.
        }

        apply star_refl.
      * left. pfold. econs 3; et.
        { rr. esplits; eauto. ss. econs; et. ii. destruct i; ss. clarify. apply H. unfold Int.zero.
          Local Transparent Int.repr.
          unfold Int.repr.
          Local Opaque Int.repr.
          ss. apply eta; ss.
        }
        ii; des.
        inv ATSRC. ss; clarify.
        destruct sm0; ss. clarify.
        unfold Clight.fundef in *.
        rewrite FINDG in *. clarify.
        eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _), (SimMemId.mk _ _).
        esplits; ss; eauto.
        { econs; ss; eauto. }
        i. inv AFTERSRC. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. inv SIMRETV; ss; clarify.
        esplits; eauto.
        { econs; eauto. }
        instantiate (2:= (Ord.lift_idx lt_wf 15%nat)).
        left. pfold. econs; eauto. i; des. econs 2; eauto.
        {
          esplits; eauto; cycle 1.
          { instantiate (1:= (Ord.lift_idx lt_wf 14%nat)). eapply Ord.lift_idx_spec; et. }

          eapply plus_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }
          
          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; eauto.
          }

          eapply star_left with (t1 := E0) (t2 := E0); ss.
          { econs; eauto.
            { eapply modsem2_determinate; eauto. }
            econs; ss; eauto.
            - repeat (econs; ss; eauto).
              + unfold typify. des_ifs.
              + ss.
            - ss.
          }

          eapply star_refl.
        }
        
        right. eapply CIH. instantiate (1:= SimMemId.mk _ _).
        econs; ss; eauto; try lia.
        rewrite sum_recurse. des_ifs.
        { rewrite Z.eqb_eq in *. lia. }
        replace (Int.sub (Int.add (sum (Int.sub i Int.one)) i) (Int.repr 1)) with
            (Int.add (sum (Int.sub i Int.one)) (Int.sub i Int.one)); cycle 1.
        { abstr (sum (Int.sub i Int.one)) z. rewrite ! Int.sub_add_opp.
          rewrite Int.add_assoc. ss. }
        econs; eauto.
  - (* return *)
    econs 4; ss; eauto.
Unshelve.
  all: ss.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { eapply SoundTop.sound_state_local_preservation. }
  i. ss. esplits; eauto; cycle 1.
  { (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE.

    (* hexploit (@fsim_external_inject_eq); try apply FINDF; eauto. clear FPTR. intro FPTR. *)

    esplits; eauto. econs; eauto.
    + rewrite <- FPTR. eauto.
    + instantiate (1:= [Vint i]). rewrite VS in *. inv VALS. econs; ss.
      cbn. unfold typify. des_ifs; ss.
  }
  (* init bsim *)
  ii.
  destruct sm_arg; ss. clarify.
  clear MFUTURE.
  inv SIMARGS; ss. clarify.
  inv INITTGT.
  (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
  exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
  eexists. eexists (SimMemId.mk _ _).
  esplits; eauto.
  + eapply match_states_lxsim.
    econs; ss; eauto; cycle 1.
    { inv SAFESRC. ss. }

    inv SAFESRC. destruct args_src, args_tgt; ss. clarify.
    assert(tvs = [Vint i]).
    {
      unfold signature_of_function in TYP. ss.
      inv TYP. ss. cbn. unfold typify. des_ifs; ss.
    } clarify.
    econs; eauto.
Unshelve.
  all: try (ss; econs).
Qed.

End SIMMODSEM.

Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (MutrecAspec.module prog) (ClightC.module2 prog) tt)
.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. eapply sim_modsem; eauto.
Qed.

