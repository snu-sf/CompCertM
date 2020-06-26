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
Require Import Fib1.
Require Import Fib0.

Set Implicit Arguments.

Program Instance SMO: SimMemOh.class := (SimMemOh_default_aux _ (Some "fib")).
Local Arguments ModSemPair.mk [SM] [SS] _ _ _ _ [SMO].



Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (Fib1.module).
Let md_tgt: Mod.t := (Fib0.module).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
(* Let INCLTGT: SkEnv.includes skenv_link (Mod.sk md_tgt). *)
(* Proof. ss. Qed. *)
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link.

Lemma unsymb
      fid fblk
      (FID: Genv.find_symbol ge fid = Some fblk)
  :
    <<FID: fid = _fib>>
.
Proof.
  subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec in *. des_ifs.
  unfold defs in *. des_sumbool. ss. des; ss.
Qed.

Lemma symb
  :
    exists fblk, <<FID: Genv.find_symbol tge _fib = Some fblk>>
.
Proof.
  Local Opaque _fib.
  inv INCL. ss.
  exploit (DEFS _fib); et.
  { unfold prog_defmap. ss. }
  i; des. ss. folder.
  clear - SYMB.
  subst ge. ss. uge. ss. rewrite MapsC.PTree_filter_key_spec. des_ifs. et.
Qed.

Lemma symb_def
      fblk
      (SYMB: Genv.find_symbol ge _fib = Some fblk)
  :
    <<DEF: Genv.find_funct tge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal f_fib)>>
.
Proof.
  exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
  des.
  exploit SkEnv.project_revive_precise; et.
Unshelve.
  all: admit "giveup".
Qed.





Notation "'_'" := PTree.Leaf (at level 150).
Notation "a % x % b" := (PTree.Node a x b) (at level 150).
Notation "a %% b" := (PTree.Node a None b) (at level 150).

Definition te1 nn: temp_env := (@PTree.Node val
             (@PTree.Node val (@PTree.Leaf val) (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val))))
                   (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val)))) (@None val)
             (@PTree.Node val
                (@PTree.Node val (@PTree.Leaf val) (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val (Vint nn)) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val))) (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val))))
                   (@None val)
                   (@PTree.Node val
                      (@PTree.Node val (@PTree.Leaf val) (@None val)
                         (@PTree.Node val (@PTree.Leaf val) (@Some val Vundef) (@PTree.Leaf val)))
                      (@None val) (@PTree.Leaf val))))).

Definition k1 (nn: int) (k_tgt: cont): cont :=
  (Kcall (Some _t'1) f_fib empty_env (te1 nn)
          (Kseq (Sset _y1 (Etempvar _t'1 tint))
             (Kseq
                (Clight.Ssequence
                   (Clight.Ssequence
                      (Scall (Some _t'2)
                         (Clight.Evar _fib (Tfunction (Tcons tint Tnil) tint cc_default))
                         [Clight.Ebinop Cop.Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
                            tint]) (Sset _y2 (Etempvar _t'2 tint)))
                   (Clight.Sreturn
                      (Some (Clight.Ebinop Cop.Oadd (Etempvar _y1 tint) (Etempvar _y2 tint) tint))))
                k_tgt))).

Definition te2 (rv: val) (nn: int) := (@PTree.Node val
          (@PTree.Node val (@PTree.Leaf val) (@None val)
             (@PTree.Node val
                (@PTree.Node val (@PTree.Leaf val) (@None val)
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (Some rv) (@PTree.Leaf val))))
                (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (Some rv) (@PTree.Leaf val)))
                   (@None val) (@PTree.Leaf val)))) (@None val)
          (@PTree.Node val
             (@PTree.Node val (@PTree.Leaf val) (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (Some (Vint nn)) (@PTree.Leaf val)))
                   (@None val) (@PTree.Leaf val))) (@None val)
             (@PTree.Node val
                (@PTree.Node val (@PTree.Leaf val) (@None val)
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (Some Vundef) (@PTree.Leaf val))))
                (@None val)
                (@PTree.Node val
                   (@PTree.Node val (@PTree.Leaf val) (@None val)
                      (@PTree.Node val (@PTree.Leaf val) (Some Vundef) (@PTree.Leaf val)))
                   (@None val) (@PTree.Leaf val))))).

Definition k2 (rv: val) (nn: int) (k_tgt: cont): cont :=
  (Kcall (Some _t'2) f_fib empty_env
         (te2 rv nn)
         (Kseq (Sset _y2 (Etempvar _t'2 tint))
               (Kseq
                  (Clight.Sreturn
                     (Some (Clight.Ebinop Cop.Oadd (Etempvar _y1 tint) (Etempvar _y2 tint) tint)))
                  k_tgt)))
.




From ITree Require Export
     KTree
     KTreeFacts
     Basics.CategoryOps
     Basics.CategoryKleisli
.






Notation ktr :=
  (ktree (eff1 owned_heap) (owned_heap * (mem * val)) (owned_heap * (mem * val)))
.
Notation itr := (itree (eff1 owned_heap) (owned_heap * (mem * val))).

Definition is_call_cont_strong (k0: cont): Prop :=
  match k0 with
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

Inductive match_stacks (k_src: list ktr) (k_tgt: Clight.cont): Prop :=
| match_stacks_nil
    (KSRC: k_src = nil)
    (KTGT: k_tgt = Kstop)
| match_stacks_cons1
    tl_src tl_tgt
    (STKS: match_stacks tl_src tl_tgt)
    hd_src n
    (HDSRC: hd_src =
            fun '(oh0, (m0, v0)) =>
              '(oh1, (m1, v1)) <- trigger (ICall _fib oh0 m0 [Vint (Int.sub n (Int.repr 1))]) ;;
              Ret (oh1, (m1, Val.add v0 v1)))
    (KSRC: k_src = hd_src :: tl_src)
    (KTGT: k_tgt = k1 n tl_tgt)
| match_stacks_cons2
    tl_src tl_tgt
    (STKS: match_stacks tl_src tl_tgt)
    hd_src rv n
    (ISINT: exists rvi, rv = Vint rvi)
    (HDSRC: hd_src = fun '(oh1, (m1, v1)) => Ret (oh1, (m1, Val.add rv v1)))
    (KSRC: k_src = hd_src :: tl_src)
    (KTGT: k_tgt = k2 rv n tl_tgt)
.



Inductive match_states_internal: SIRStack.state owned_heap -> Clight.state -> Prop :=
| match_call
    itr0 ty m0 vs n
    fid fblk fptr_tgt k_src k_tgt
    (STKS: match_stacks k_src k_tgt)
    (ITR: itr0 = (interp_function Fib1.prog (ICall _fib tt m0 vs)))

    (VS: vs = [Vint n])
    (TY: ty = Clight.type_of_fundef (Internal f_fib))

    (SYMB: Genv.find_symbol ge fid = Some fblk)
    (FPTR: fptr_tgt = (Vptr fblk Ptrofs.zero))
  :
    match_states_internal (mk itr0 k_src)
                          (Clight.Callstate fptr_tgt ty vs k_tgt m0)
| match_return
    itr0 m0 v k_src k_tgt
    (STKS: match_stacks k_src k_tgt)
    (ITR: itr0 = Ret (tt, (m0, v)))
    (ISINT: exists vi, v = Vint vi)
  :
    match_states_internal (mk itr0 k_src)
                          (Clight.Returnstate v (call_cont k_tgt) m0)
(* | match_return *)
(*     itr0 m0 v k_src k_tgt n par *)
(*     (STKS: match_stacks n par k_src k_tgt) *)
(*     (RET: itr0 ≈ r <- Ret (tt, (m0, v)) ;; (k_src r)) *)
(*   : *)
(*     match_states_internal i (Eqv.lift itr0) (Clight.Returnstate v k_tgt m0) *)
(*                           (SimMemId.mk m0 m0) *)
.

Inductive match_states
          (i: nat) (st_src0: SIRStack.state owned_heap) (st_tgt0: Clight.state)
          (smo0: SimMemOh.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (MWF: SimMemOh.wf smo0)
    (IDX: (i >= 100)%nat)
.



(*** TODO: it is unused for now. use this later ***)
Lemma init_fsim
      args st_src0
      (INIT: ModSem.initial_frame (md_src skenv_link) tt args st_src0)
  :
    exists i st_tgt0 smo0,
      (<<INIT: ModSem.initial_frame (md_tgt skenv_link) tt args st_tgt0>>)
      /\ (<<MATCH: match_states i st_src0 st_tgt0 smo0>>)
.
Proof.
  inv INIT. ss. des_ifs_safe. folder.
  unfold interp_program in *.
  exploit unsymb; et. i; des. clarify. des_ifs.
  assert(SIG: fd = signature_of_function f_fib).
  { admit "ez - findf sig". }
  destruct args; ss. inv TYP. ss. destruct vs; ss. destruct vs; ss.
  inv DEF. clear H2. unfold typify_list, typify in *; ss. des_ifs. destruct v; ss. clear_tac. i.
  eexists _, _, (SimMemId.mk _ _). esplits; eauto.
  - econs; ss; eauto.
    { des_ifs. folder. exploit symb_def; et. }
    { ss. }
  - econs; ss; eauto. econs; ss; eauto.
    + econs; ss.
    + unfold typify_list. ss. unfold typify. des_ifs; ss.
    + cbn. unfold typify. des_ifs; ss.
Unshelve.
  all: ss.
Qed.

(* Lemma final_fsim *)
(*       i st_src0 st_tgt0 smo0 retv *)
(*       (MATCH: match_states i st_src0 st_tgt0 smo0) *)
(*       (FIN: ModSem.final_frame (md_src skenv_link) st_src0 tt retv) *)
(*   : *)
(*     exists smo_ret, *)
(*       (<<FIN: ModSem.final_frame (md_tgt skenv_link)  st_tgt0 tt retv>>) /\ *)
(*       (<<SIMRET: SimMem.sim_retv retv retv smo_ret>>) /\ *)
(*       (<<MWF: SimMem.wf smo_ret>>) *)
(* . *)
(* Proof. *)
(*   inv FIN. ss. *)
(*   inv MATCH. ss. inv MATCHST; ss. *)
(*   { rewrite RET in *. rewrite ITR in *. clear - IN. exfalso. *)
(*     rewrite mrec_as_interp in IN. irw in IN. des_ifs; vvt IN. } *)
(*   eexists (SimMemId.mk m0 m0). *)
(*   esplits; ss; eauto; cycle 1. *)
(*   { econs; eauto. ss. } *)
(*   inv STKS; cycle 1. *)
(*   { rewrite RET in *. rewrite RET0 in *. clear - IN. exfalso. *)
(*     vvt IN. *)
(* Qed. *)

Lemma match_states_lxsim
      idx st_src0 st_tgt0 sm0
      (MATCH: match_states idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsimL (md_src skenv_link) (md_tgt skenv_link)
                   (fun st => unit -> exists su m_init, SoundTop.sound_state su m_init st)
                   top3 (fun _ _ => SimMemOh.le)
                   (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  revert_until idx. revert idx. pcofix CIH.
  i.
  pfold.
  inv MATCH. subst; ss. ii. clear SUSTAR. inv MATCHST; ss; clarify.
  - econs 1; eauto. ii. clear SU.
    exploit unsymb; et. intro T. des; clarify.
    exploit symb_def; et. intro DEF; des. ss. des_ifs.
    rename Heq into V. cbn in V. des_ifs. clear_tac.



    econs 1; et; swap 2 3.
    { esplits; intro T; rr in T; des; inv T; ss. }
    { eapply modsem_receptive; et. }
    ii. ss. inv STEPSRC; ss. unfold Fib1.f_fib in TAU. clarify.
    destruct (classic (Int.eq n Int.zero)).
    { apply_all_once Int.same_if_eq. clarify.
      eexists _, _, (SimMemId.mk _ _). esplits; eauto.
      { left. eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). ii; ss; des; ss; clarify. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_refl.
      }
      { right. eapply CIH.
        econs; ss; et. econs; ss; et.
      }
    }
    rename H into NZERO.



    destruct (classic (Int.eq n Int.one)).
    { apply_all_once Int.same_if_eq. clarify.
      eexists _, _, (SimMemId.mk _ _). esplits; eauto.
      { left. eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). ii; ss; des; ss; clarify. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_refl.
      }
      { right. eapply CIH.
        econs; ss; et. econs; ss; et.
      }
    }
    rename H into NONE.



    rewrite Int.eq_false; cycle 1.
    { ii; clarify. }
    rewrite Int.eq_false; cycle 1.
    { ii; clarify. }
    eexists (Ord.lift_idx lt_wf (S idx)), _, (SimMemId.mk _ _). esplits; eauto.
    { left. eapply spread_dplus; et.
      { eapply modsem2_mi_determinate; et. }
      eapply plus_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). ii; ss; des; ss; clarify. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). ss. rewrite Int.eq_false; ss. ii; clarify. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). ss. rewrite Int.eq_false; ss. ii; clarify. }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { repeat (econs; ss; et). }
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { econsr; ss; et.
        - econsr; ss; et.
          + econsr; ss; et.
          + econs 2; ss; et.
        - repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
      eapply star_refl.
    }
    left. pfold. ii. clear SUSTAR. ss. econs 2; et. ii. clear_tac.
    econs 2; ss; et.
    { esplits; try eapply Ord.lift_idx_spec; et.
      eapply star_left with (t1 := E0) (t2 := E0); ss.
      { eapply SIRStack.step_call; ss; et. f. irw. f. ss. }
      unfold Fib1.prog. ss. des_ifs_safe.
      apply star_refl.
    }
    instantiate (1:= SimMemId.mk _ _). right. eapply CIH.
    econs; ss; et. econs; ss; et. econs 2; ss; et.
  - inv STKS.
    + ss. econs 4; ss.
      { instantiate (1:= SimMemId.mk m0 m0). et. }
      { ss. }
      rr. esplits; ss; et. econs; ss; et.
    + econs 1; eauto. ii. clear SU.
      hexploit symb; et. i; des.
      econs 1; et; swap 2 3.
      { esplits; intro T; rr in T; des; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. ss. inv STEPSRC; ss. clarify. ss.
      eexists (Ord.lift_idx lt_wf (S idx)), _, (SimMemId.mk _ _). esplits; eauto.
      { left. eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econsr; ss; et.
          - econsr; ss; et.
            + econsr; ss; et.
            + econs 2; ss; et.
          - repeat (econs; ss; et); ii; repeat (des; ss; clarify). }
        eapply star_refl.
      }
      left. pfold. ii. clear SUSTAR. ss. econs 2; et. ii. clear_tac.
      econs 2; ss; et.
      { esplits; try eapply Ord.lift_idx_spec; et.
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { eapply SIRStack.step_call; ss; et. f. irw. f. ss. }
        unfold Fib1.prog. ss. des_ifs_safe.
        apply star_refl.
      }
      instantiate (1:= SimMemId.mk _ _). right. eapply CIH.
      econs; ss; et. econs; ss; et. econs 3; ss; et.
    + econs 1; eauto. ii. clear SU.
      econs 1; et; swap 2 3.
      { esplits; intro T; rr in T; des; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. ss. inv STEPSRC; ss. clarify. ss. des; clarify.
      des; clarify.
      eexists (Ord.lift_idx lt_wf (S idx)), _, (SimMemId.mk _ _). esplits; eauto.
      { left. eapply spread_dplus; et.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_refl.
      }
      right. eapply CIH.
      econs; ss; et. econs; ss; et.
Unshelve.
  all: ss.
Qed.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply sim_mod_sem_implies.
  econstructor 1 with (sidx := unit) (sound_states := top4); eauto;
    try apply SoundTop.sound_state_local_preservation; et; try (by ii; ss).
  { ii. eapply Preservation.local_preservation_noguarantee_weak.
    apply SoundTop.sound_state_local_preservation; et.
  }
  { ii. ss. eexists (SimMemId.mk _ _); ss. esplits; eauto. destruct sm; ss. }
  ii. ss. esplits; eauto.
  - ii. des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
    rr in SIMARGS. des. ss. clarify. inv SIMARGS0; ss. clarify.
    destruct sm_arg; ss. clarify. des_ifs.
    assert(SG: sg_init_src = signature_of_function fd).
    { folder. admit "ez - FINDF". }
    clarify.
    assert(TY: Clight.type_of_function fd = Clight.type_of_function f_fib).
    { admit "ez - findf sig". }
    assert(SIG: signature_of_function fd = signature_of_function f_fib).
    { clear - TY. unfold signature_of_function, Clight.type_of_function in *.
      destruct fd, f_fib; ss. clarify. f_equal.
      clear - H2. ginduction fn_params; ii; ss.
      { destruct fn_params0; ss. des_ifs; ss. }
      des_ifs; ss. destruct fn_params0; ss. des_ifs; ss. f_equal; et.
    }
    dup TYP0.
    rewrite SIG in *. inv TYP. ss. destruct vs_tgt; ss. destruct vs_tgt; ss.
    inv DEF. inv TYP0. ss. cbn in TYP. unfold typify in *.
    revert TY. (*** TODO: FIXTHIS: des_ifs drops some information, "SIG" and "TY" hyp ***)
    des_ifs; ss. destruct v; ss. clear_tac. i.

    eexists _, (SimMemId.mk _ _), _. esplits; ss; eauto.
    { econs; ss; et. econs; ss; et. }
    eapply match_states_lxsim; eauto.
    econs; ss; et. econs; ss; et.
    { econs; ss; et. }
    { cbn. exploit unsymb; et. i; des. clarify. des_ifs. f_equal. cbv. des_ifs; ss. }
    { cbv. des_ifs; ss; et. }
  - i; des. inv SAFESRC. ss. des_ifs.
    rr in SIMARGS. des. inv SIMARGS0; ss. clarify. destruct sm_arg; ss. clarify.
    esplits; et. econs; ss; et.
    { des_ifs. folder. admit "ez - FINDF". }
    admit "ez - typecheck".
Unshelve.
  all: ss.
  all: repeat econs; et.
Qed.

End SIMMODSEM.

Definition mp: ModPair.t := SimSymbId.mk_mp (Fib1.module) (Fib0.module).
Theorem sim_mod: ModPair.sim mp.
Proof. econs; ss. - ii. inv SIMSKENVLINK. esplits; eauto. eapply sim_modsem; eauto. Qed.
