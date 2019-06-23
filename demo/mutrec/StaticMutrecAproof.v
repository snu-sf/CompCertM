Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import StaticMutrecHeader.
Require Import StaticMutrecA StaticMutrecAspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SoundTop.
Require SimMemInjInv.
Require Import Clightdefs.
Require Import CtypesC.

Set Implicit Arguments.

Print Instances SimMem.class.


Definition memoized_inv (chunk: memory_chunk) (ofs: Z) (v: option val): Prop :=
  forall
    ind
    (BOUND: 0 <= ind < 10)
    (INT: chunk = Mint64)
    (INDEX: size_chunk Mint64 * ind = ofs),
  exists i,
    (<<VAL: v = Some (Vint i)>>) /\
    forall (VPOS: 0 <= i.(Int.intval)),
      i = sum (Int.repr ind).

Local Instance SimMemMemoized: SimMem.class := SimMemInjInv.SimMemInjInv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (StaticMutrecAspec.module).
Let md_tgt: Mod.t := (ClightC.module2 prog).
Hypothesis (INCL: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link md_src.(Mod.sk)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) symbol_memoized sm_link.


Inductive match_states_internal: StaticMutrecAspec.state -> Clight.state -> Prop :=
| match_callstate_nonzero
    i m_src m_tgt
    fptr
    (* targs tres cconv *)
    (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f))
  :
    match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *)
                                                                        (Tcons tint Tnil) tint cc_default)
                                                                [Vint i] Kstop m_tgt)
| match_returnstate
    i m_src m_tgt
  :
    match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt)
.


(* Inductive match_states_internal: StaticMutrecAspec.state -> Clight.state -> Prop := *)
(* | match_callstate_nonzero_memoized *)
(*     i m_src m_tgt *)
(*     fptr blk memov *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*     (SYMB: Genv.find_symbol skenv_link _memoized = Some blk) *)
(*     (MEMOLD: Mem.loadv *)
(*                Mint64 m_tgt *)
(*                (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) = Some (Vint memov)) *)
(*     (MEMOIZED: memov = sum i) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_callstate_nonzero_nonmemoized *)
(*     i m_src m_tgt *)
(*     fptr blk memov *)
(*     (* targs tres cconv *) *)
(*     (FINDF: Genv.find_funct (Smallstep.globalenv (modsem2 skenv_link prog)) fptr = Some (Internal func_f)) *)
(*     (SYMB: Genv.find_symbol skenv_link _memoized = Some blk) *)
(*     (MEMOLD: Mem.loadv *)
(*                Mint64 m_tgt *)
(*                (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) = Some (Vint memov)) *)
(*     (NONMEMOIZED: memov.(Int.intval) < 0) *)
(*   : *)
(*     match_states_internal (Callstate i m_src) (Clight.Callstate fptr (Tfunction (* targs tres cconv) *) *)
(*                                                                         (Tcons tint Tnil) tint cc_default) *)
(*                                                                 [Vint i] Kstop m_tgt) *)
(* | match_returnstate *)
(*     i m_src m_tgt *)
(*   : *)
(*     match_states_internal (Returnstate i m_src) (Clight.Returnstate (Vint i) Kstop m_tgt) *)
(* . *)

Inductive match_states (sm_init: SimMem.t)
          (idx: nat) (st_src0: StaticMutrecAspec.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: match_states_internal st_src0 st_tgt0)
    (MCOMPATSRC: st_src0.(get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (IDX: (idx > 3)%nat)
.

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
  { unfold prog_defs_names. ss. repeat (econs; eauto).
    - ii; ss; des; ss.
    - ii; ss; des; ss. }
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
  { inv INCL.
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
      econs 2. i. esplits; cycle 3.
      { ii. esplits. econs; eauto. econs; ss; eauto.
        - econs.
        - econs; eauto. econs.
        - ii. ss. des; clarify.
        - econs. }
      { ii. inv H. inv H0. }
      { ii. inv H. inv H0. }
      econs 2.
      { split.
        - econs 2.
          + ss. econs 1.
          + econs 1.
          + ss.
        - admit "index". }
      left. pfold.
      econs 1. i; des.
      econs 2.

      (* econs 2; cycle 2. *)
      (* { admit "ez - spec is receptive". } *)
      (* { split; ii; rr in H; inv H; inv H0; ss. } *)
      (* i. ss. inv STEPSRC. *)
      (* esplits; eauto. *)

      * split; cycle 1.
        { admit "index". }

        (* left. *)
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
      * right. eapply CIH. econs; ss; eauto.
        replace (Int.repr 0) with (sum Int.zero).
        { econs; eauto. }
        { admit "". }

    + (* nonzero *)

      destruct sm0.
      destruct (Genv.find_symbol skenv_link _memoized) eqn:BLK; cycle 1.
      { exfalso. clear - INCL BLK. inv INCL.
        exploit DEFS; eauto.
        - instantiate (2:=_memoized). ss.
        - i. des. clarify. }

      inv MWF. ss. admit "".
      (* exploit SAT. *)

  - admit "".
    Unshelve. all : admit "".

(*       destruct (Mem.loadv *)
(*                   Mint64 (minj.(SimMemInj.tgt)) *)
(*                   (Vptr b (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval))))). *)

(*       Mem.loadv *)
(*                    Mint64 m_tgt *)
(*                    (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) *)


(*       (MEMOLD: Mem.loadv *)
(*                    Mint64 m_tgt *)
(*                    (Vptr blk (Ptrofs.repr (size_chunk Mint64 * i.(Int.intval)))) = Some (Vint memov)) *)
(*         (MEMOIZED: memov = sum i) *)





(*       econs. *)
(*       i; des. *)
(*       econs 2; eauto. *)
(*       * esplits; cycle 1. *)
(*         { eapply Ord.lift_idx_spec. instantiate (1:= 2%nat). lia. } *)

(*         eapply plus_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto. *)
(*           econs; ss; eauto; try (by repeat (econs; ss; eauto)). *)
(*           unfold _x. unfold _t'1. rr. ii; ss. des; ss. clarify. *)
(*         } *)

(*         eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto. *)
(*         } *)

(*         eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto. *)
(*           - repeat econs; et. *)
(*           - ss. rewrite Int.eq_false; ss. *)
(*         } *)

(*         eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto. *)
(*         } *)

(*         eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto. *)
(*         } *)

(*         eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*         { econs; eauto. *)
(*           { eapply modsem2_determinate; eauto. } *)
(*           econs; eauto; swap 1 2. *)
(*           - econs. *)
(*             + eapply eval_Evar_global; ss. et. *)
(*             + econs 2; et. *)
(*           - unfold Cop.classify_fun. ss. *)
(*           - repeat econs; ss; et. *)
(*         } *)

(*         apply star_refl. *)
(*       * left. pfold. econs 3; et. *)
(*         { rr. esplits; eauto. ss. econs; et. ii. destruct i; ss. clarify. apply H. unfold Int.zero. *)
(*           Local Transparent Int.repr. *)
(*           unfold Int.repr. *)
(*           Local Opaque Int.repr. *)
(*           ss. apply eta; ss. *)
(*         } *)
(*         ii; des. *)
(*         inv ATSRC. ss; clarify. *)
(*         destruct sm0; ss. clarify. *)
(*         unfold Clight.fundef in *. *)
(*         assert(g_fptr = g_blk). *)
(*         { unfold SkEnv.revive in FINDG. rewrite Genv_map_defs_symb in *. clarify. } *)
(*         clarify. *)
(*         eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _), (SimMemId.mk _ _). *)
(*         esplits; ss; eauto. *)
(*         { econs; ss; eauto. } *)
(*         i. inv AFTERSRC. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. inv SIMRETV; ss; clarify. *)
(*         esplits; eauto. *)
(*         { econs; eauto. } *)
(*         instantiate (2:= (Ord.lift_idx lt_wf 15%nat)). *)
(*         left. pfold. econs; eauto. i; des. econs 2; eauto. *)
(*         { *)
(*           esplits; eauto; cycle 1. *)
(*           { instantiate (1:= (Ord.lift_idx lt_wf 14%nat)). eapply Ord.lift_idx_spec; et. } *)

(*           eapply plus_left with (t1 := E0) (t2 := E0); ss. *)
(*           { econs; eauto. *)
(*             { eapply modsem2_determinate; eauto. } *)
(*             econs; eauto. *)
(*           } *)

(*           eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*           { econs; eauto. *)
(*             { eapply modsem2_determinate; eauto. } *)
(*             econs; eauto. *)
(*           } *)

(*           eapply star_left with (t1 := E0) (t2 := E0); ss. *)
(*           { econs; eauto. *)
(*             { eapply modsem2_determinate; eauto. } *)
(*             econs; ss; eauto. *)
(*             - repeat (econs; ss; eauto). *)
(*               + unfold typify. des_ifs. *)
(*             - ss. *)
(*           } *)

(*           eapply star_refl. *)
(*         } *)

(*         right. eapply CIH. instantiate (1:= SimMemId.mk _ _). *)
(*         econs; ss; eauto; try lia. *)
(*         rewrite sum_recurse. des_ifs. *)
(*         { rewrite Z.eqb_eq in *. lia. } *)
(*         replace (Int.sub (Int.add (sum (Int.sub i Int.one)) i) (Int.repr 1)) with *)
(*             (Int.add (sum (Int.sub i Int.one)) (Int.sub i Int.one)); cycle 1. *)
(*         { abstr (sum (Int.sub i Int.one)) z. rewrite ! Int.sub_add_opp. *)
(*           rewrite Int.add_assoc. ss. } *)
(*         econs; eauto. *)
(*   - (* return *) *)
(*     econs 4; ss; eauto. *)
(* Unshelve. *)
(*   all: ss. *)
Qed.

End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (StaticMutrecAspec.module) (ClightC.module2 prog) symbol_memoized)
.
Proof.
Admitted.
(*   econs; ss. *)
(*   - ii. inv SIMSKENVLINK. *)
(* Qed. *)
