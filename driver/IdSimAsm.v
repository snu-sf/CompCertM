Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import AsmregsC.
Require Import MatchSimModSem.

Set Implicit Arguments.


Local Existing Instance Val.mi_normal.
Local Opaque Z.mul Z.add Z.sub Z.div.


(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)

Lemma asm_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  { i; ss. clarify. }
  intro GENV; des.
  inv SIMSKENVLINK.

  econs; ss; eauto.
  { eapply SoundTop.sound_state_local_preservation; eauto. }
  ii; ss.

  inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  fold fundef in *.
  split; ii; cycle 1.
  { (* init progress *) des. exists st_init_src. inv SAFESRC. econs; ss; eauto. }
  rename tgt into m0.
  rename st_init_tgt into st0.
  rename skenv_link_tgt into skenv_link.
  (* init bsim *)
  esplits; eauto.
  (* lxsim *)
  instantiate (1:= (SimMemId.mk m0 m0)). instantiate (1:= Ord.lift_idx unit_ord_wf tt).
  clear - GENV.
  generalize dependent st0.
  pcofix CIH. ii. pfold.
  destruct (classic ((modsem skenv_link asm).(ModSem.is_call) st0)).
  { (* call *)
    ss. rr in H. des.
    econs 3; eauto.
    { econs; eauto. }
    ii. des. clear_tac.
    exists args_src. exists (SimMemId.mk args_src.(Args.m) args_src.(Args.m)). ss.
    esplits; eauto.
    { econs; ss; eauto. }
    ii. ss. des.
    esplits; eauto.
    inv SIMRETV. ss. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. clarify.
  }
  destruct (classic ((modsem skenv_link asm).(ModSem.is_return) st0)).
  { (* final *)
    ss. rr in H0. des.
    dup H0. set (R:= retv). inv H0.
    econs 4; eauto.
    { instantiate (1:= SimMemId.mk m2 m2). ss. }
    { econs; eauto. }
    { ss. }
  }
  econs 1; eauto.
  ii; des. clear_tac.
  esplits; eauto.
  econs; eauto; cycle 1.
  { admit "ez - receptive". }
  ii. ss. inv STEPSRC.
  esplits; eauto. left. apply plus_one. econs; eauto.
  { admit "ez - determinate". }
  econs; eauto.
Unshelve.
  all: ss.
Qed.

Lemma asm_id_trial2
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  { i; ss. clarify. }
  intro GENV; des.
  inv SIMSKENVLINK.

  eapply match_states_sim with (index := unit)
                               (sound_state := SoundTop.sound_state)
                               (match_states := fun sm_arg idx st_src0 st_tgt0 sm =>
                                                  st_src0 = st_tgt0 /\ SimMem.wf sm)
                               (match_states_at := top4); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eapply SoundTop.sound_state_local_preservation; eauto.
  - (* init bsim *)
    ii. des. exists st_init_tgt. inv SAFESRC. econs; ss; eauto.
    esplits; ss; eauto.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  - (* init progress *)
    ii. des.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
    exists st_init_src. inv SAFESRC. econs; ss; eauto.
  - (* call wf *)
    ii; des; ss.
  - (* call fsim *)
    ii; des; ss.
    destruct sm0; ss. clarify.
    eexists _, (SimMemId.mk _ _); ss. esplits; eauto.
    econs; ss; eauto.
  - (* after fsim *)
    ii; des; ss.
    destruct sm_ret; ss. clarify. clear_tac.
    destruct retv_src, retv_tgt; ss. inv SIMRET. ss. clarify.
    esplits; eauto.
  - (* final fsim *)
    ii; des; ss. clarify.
    destruct retv_src; ss.
    exists (SimMemId.mk m m).
    esplits; ss; eauto.
  - (* step fsim *)
    ii; ss. des. clarify. clear_tac.
    esplits; eauto.
    { admit "ez - receptive". }
    ii; des. esplits; eauto. left. apply plus_one. econs; eauto.
    { admit "ez - determinate". }
Unshelve.
  all: ss.
Qed.

Lemma asm_ext_top
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Inductive sound_state (skenv: SkEnv.t) (su: Sound.t) (m_init: mem): AsmC.state -> Prop :=
| sound_state_intro
    init_rs rs0 m0
    (MLE: Unreach.mle su m_init m0)
    (RS: forall pr, UnreachC.val' su (rs0#pr))
    (MEM: UnreachC.mem' su m0)
    (INIT: forall pr, UnreachC.val' su (init_rs#pr))
    (WF: forall blk (PRIV: su.(Unreach.unreach) blk) (PUB: Plt blk su.(Unreach.ge_nb)), False)
    (* (SKE: UnreachC.skenv su m0 skenv) *)
    (SKE: su.(Unreach.ge_nb) = skenv.(Genv.genv_next))
  :
    sound_state skenv su m_init (mkstate init_rs (State rs0 m0))
.

(* Lemma val_hle *)
(*       su0 su1 v *)
(*       (SU: UnreachC.val' su0 v) *)
(*       (LE: UnreachC.hle' su0 su1) *)
(*   : *)
(*     <<SU: UnreachC.val' su1 v>> *)
(* . *)
(* Proof. *)
(*   ii. clarify. exploit SU; eauto. i; des. *)
(*   rr in LE. des. *)
(*   esplits; eauto. *)
(*   xomega. *)
(* Qed. *)
(* Inductive Mem_future (P: val -> Prop) (m0 m1: Mem.mem): Prop := *)
(* | Mem_future_alloc *)
(*     lo hi blk *)
(*     (ALLOC: m0.(Mem.alloc) lo hi = (m1, blk)) *)
(*   : *)
(*     Mem_future P m0 m1 *)
(* | Mem_future_store *)
(*     ( *)
(* . *)

(* Lemma asm_unreach_local_preservation *)
(*       asm skenv_link *)
(*   : *)
(*     <<PRSV: local_preservation (modsem skenv_link asm) (sound_state skenv_link)>> *)
(* . *)
(* Proof. *)
(*   s. *)
(*   econs; ii; ss; eauto. *)
(*   - (* init *) *)
(*     inv INIT. *)
(*     r in SUARG. des. *)
(*     rename m into m2. *)
(*     assert(SURS: forall pr, UnreachC.val' su_init (Mem.nextblock m2) (rs pr)). *)
(*     { *)
(*       ii. unfold PregEq.t in *. spc PTRFREE. *)

(*       inv STORE. *)
(*       exploit Mem.alloc_result; eauto. i; clarify. *)
(*       exploit Mem.nextblock_alloc; eauto. intro SUCC. *)

(*       hexploit PTRFREE; eauto. *)
(*       { rewrite PTR. ss. } *)
(*       clear PTRFREE. *)
(*       i; des; clarify; cycle 1. *)
(*       { rewrite PTR in *. rewrite <- NB in *. erewrite Mem.nextblock_alloc; eauto. *)
(*         clear - VAL RSPC. rr in VAL. symmetry in RSPC. repeat spc VAL. des. split; ss. eauto with xomega. *)
(*       } *)
(*       { rewrite PTR in *. clarify. *)
(*         clear - MEM NB SUCC. *)
(*         inv MEM. unfold Mem.valid_block in *. *)
(*         split; ss. *)
(*         - ii. exploit BOUND; eauto. i. xomega. *)
(*         - rewrite <- NB. rewrite SUCC. xomega. *)
(*       } *)
(*       rewrite Forall_forall in *. *)
(*       (* TODO: pull out as a lemma *) *)
(*       assert(IN: In (rs pr) (Args.vs args)). *)
(*       { clear - ARG VALS0 MR. *)
(*         r in VALS0. *)
(*         generalize (loc_arguments_one (fn_sig fd)); intro ONES. *)
(*         abstr (loc_arguments (fn_sig fd)) locs. abstr (Args.vs args) vs. *)
(*         ginduction vs; ii; ss; inv VALS0; ss. *)
(*         rewrite in_app_iff in ARG. *)
(*         des; eauto. *)
(*         exploit ONES; eauto. i; des. destruct a1; ss. des; ss. *)
(*         inv H2. inv H1. left. f_equal. clear - MR. eapply to_mreg_preg_of; eauto. *)
(*       } *)
(*       Fail spc VALS. (* TODO: fix spc *) *)
(*       specialize (VALS _ IN). rewrite PTR in *. *)
(*       clear - VALS NB SUCC. *)
(*       exploit VALS; eauto. i; des. esplits; eauto. *)
(*       rewrite <- NB. *)
(*       rewrite SUCC. *)
(*       xomega. *)
(*     } *)
(*     econs; eauto; ss. *)
(*     + (* mle *) *)

(*       inv STORE. *)
(*       exploit Mem.alloc_result; eauto. i; clarify. *)
(*       exploit Mem.nextblock_alloc; eauto. intro SUCC. *)

(*       econs; eauto. *)
(*       * ii. *)
(*         eapply Mem.perm_alloc_4; eauto. *)
(*         eapply UNCH; eauto. *)
(*         { unfold Mem.valid_block in *. des_ifs. xomega. } *)
(*         { unfold Mem.valid_block in *. rewrite SUCC. xomega. } *)
(*       * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1. *)
(*         { eapply Mem.unchanged_on_implies; eauto. *)
(*           ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. } *)
(*         { eapply Mem.alloc_unchanged_on; eauto. } *)
(*       * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1. *)
(*         { eapply Mem.unchanged_on_implies; eauto. *)
(*           ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. } *)
(*         { eapply Mem.alloc_unchanged_on; eauto. } *)
(*     + (* mem *) *)

(*       inv STORE. *)
(*       exploit Mem.alloc_result; eauto. i; clarify. *)
(*       exploit Mem.nextblock_alloc; eauto. intro SUCC. *)

(*       inv MEM. *)
(*       econs; ss; eauto; cycle 1. *)
(*       { ii. exploit BOUND; eauto. i. unfold Mem.valid_block in *. rewrite <- NB. rewrite SUCC. xomega. } *)
(*       { rewrite <- NB. rewrite SUCC. xomega. } *)
(*       { admit "idk". } *)
(*       { i. admit "this should hold". } *)
(*     + (* ske *) *)
(*       inv SKENV. rewrite PUB in *. ss. *)
(*   - (* step *) *)
(*       admit "ez". *)
(*   - (* call *) *)
(*     inv AT. ss. *)
(*     exploit (Sound.greatest_ex su0 (Args.mk (Vptr blk0 Ptrofs.zero true) vs m1)); ss; eauto. *)
(*     { exists su0. esplits; eauto. *)
(*       { refl. } *)
(*       inv SUST. econs; ss; eauto. *)
(*       + ii. exploit (RS PC); eauto. i; des. clarify. esplits; eauto. admit "ez". *)
(*       + esplits; eauto. *)
(*         * rewrite Forall_forall. i. *)
(*           admit "extcall-arguments". *)
(*         * admit "this should hold". *)
(*         * admit "idk". *)
(*     } *)
(*     esplits; eauto. *)
(*     + inv SUST. *)
(*       etrans; eauto. *)
(*       exploit RS; eauto. intro SU; des. *)
(*       eapply Unreach.free_mle; eauto. *)
(*     + admit "somehow... this should have been proven in somewhere else". *)
(*     + ii. inv AFTER. ss. *)
(*       destruct retv; ss. rename m into m2. *)
(*       econs; eauto. *)
(*       { inv SUST. etrans; eauto. *)
(*         admit "free-mle-unfree dual". *)
(*       } *)
(*       { admit "this should hold". } *)
(*       { inv SUST. admit "nontrivial... free-mle-unfree". } *)
(*       { inv SUST. *)
(*         ii. exploit INIT; eauto. i; des. esplits; eauto. admit "ez". *)
(*       } *)
(*       { inv SUST. ss. } *)
(*       { inv SUST. ss. } *)
(*   - (* return *) *)
(*     inv SUST. inv FINAL. ss. clarify. *)
(*     exists su0. esplits; eauto. *)
(*     { refl. } *)
(*     { econs; ss. *)
(*       - erewrite Mem.nextblock_free; eauto. *)
(*       - admit "this should hold". *)
(*     } *)
(*     etrans; eauto. *)
(*     eapply UnreachC.free_mle; eauto. *)
(*     exploit INIT; eauto. i; des. ss. *)
(* Unshelve. *)
(*   all: ss. *)
(* Qed. *)

Module TRIAL2.
Section TRIAL2.

  Variable skenv_link: SkEnv.t.

  Inductive sound_state (su: Sound.t): AsmC.state -> Prop :=
  | sound_state_intro
      (init_rs rs0: regset) m0
      (RS: forall pr, UnreachC.val' su (rs0#pr))
      (MEM: UnreachC.mem' su m0)
      (INIT: forall pr, UnreachC.val' su (init_rs#pr))
      (WF: Sound.wf su)
      (* (WF: forall blk (PRIV: su.(Unreach.unreach) blk) (PUB: Plt blk su.(Unreach.ge_nb)), False) *)
      (* (WF: forall blk (PRIV: su.(Unreach.unreach) blk) (PUB: Ple su.(Unreach.nb) blk), False) *)
      (* (SKE: UnreachC.skenv su m0 skenv) *)
      (SKE: su.(Unreach.ge_nb) = skenv_link.(Genv.genv_next))
      (STACKPUB: su.(UnreachC.val') (rs0 RSP))
    :
      sound_state su (mkstate init_rs (State rs0 m0))
  .

  Inductive has_footprint: AsmC.state -> Sound.t -> mem -> Prop :=
  | has_footprint_intro
      su0
      blk0 blk1 ofs
      init_rs (rs0: regset) m_unused m1 sg
      (FPTR: rs0 # PC = Vptr blk0 Ptrofs.zero true)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr blk0 Ptrofs.zero true)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSP: rs0 RSP = Vptr blk1 ofs true)
      (* (FREED: Mem_range_noperm m1 blk1 ofs.(Ptrofs.unsigned) (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg))) *)
      (FREEABLE: Mem.range_perm m1 blk1 (ofs.(Ptrofs.unsigned))
                                (ofs.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                Cur Freeable)
      (VALID: Mem.valid_block m1 blk1)
      (PUB: ~ su0.(Unreach.unreach) blk1)
    :
      has_footprint (mkstate init_rs (State rs0 m_unused)) su0 m1
  .

  Inductive mle_excl: AsmC.state -> Sound.t -> mem -> mem -> Prop :=
  | mle_excl_intro
      init_rs rs0 m_unused (su0: Unreach.t) m0 m1
      blk0 blk1 sg ofs1
      (FPTR: rs0 # PC = Vptr blk0 Ptrofs.zero true)
      (SIG: exists skd, skenv_link.(Genv.find_funct) (Vptr blk0 Ptrofs.zero true)
                        = Some skd /\ SkEnv.get_sig skd = sg)
      (RSP: rs0 RSP = Vptr blk1 ofs1 true)
      UNFR
      (UNFRDEF: UNFR = (brange blk1 ofs1.(Ptrofs.unsigned)
                                           (ofs1.(Ptrofs.unsigned) + 4 * (size_arguments sg))))
      (PERM: forall
          blk ofs
          (VALID: m0.(Mem.valid_block) blk)
          (UNFREE: ~ UNFR blk ofs)
        ,
          m1.(Mem.perm) blk ofs Max <1= m0.(Mem.perm) blk ofs Max)
      (UNCH: Mem.unchanged_on (~2 UNFR) m0 m1)
      (* (RO: Mem.unchanged_on (~2 UNFR /2\ m0.(loc_not_writable)) m0 m1) *)
      (* (PRIV: Mem.unchanged_on (~2 UNFR /2\ (fun _ => su0.(UnreachC.unreach)).(Basics.flip)) m0 m1) *)
    :
      mle_excl (mkstate init_rs (State rs0 m_unused)) su0 m0 m1
  .

  (* TODO: move to proper place *)
  Lemma loc_external_result_one
        sg
    :
      is_one (loc_external_result sg)
  .
  Proof.
    unfold loc_external_result. generalize (loc_result_one sg); i.
    destruct (loc_result sg) eqn:T; ss.
  Qed.

  Lemma asm_unreach_local_preservation
        asm
    :
      exists sound_state, <<PRSV: local_preservation (modsem skenv_link asm) sound_state>>
  .
  Proof.
    esplits.
    eapply local_preservation_strong_horizontal_excl_spec with (sound_state := (sound_state)); eauto.
    instantiate (1:= AsmC.get_mem).
    ss.
    eapply local_preservation_strong_horizontal_excl_intro with
        (has_footprint := has_footprint)
        (mle_excl := mle_excl); ii; ss; eauto.
    (* - (* FOOTMLE *) *)
    (*   inv FOOT. inv MLE. econs; eauto; cycle 1. *)
    (*   { eapply Mem.valid_block_unchanged_on; eauto. } *)
    (*   (* r. i. r in FREED. hexploit FREED; eauto. i. *) *)
    (*   ii. exploit FREED; eauto. *)
    - (* FOOTEXCL *)
      inv MLE. inv FOOT. inv MLEEXCL. ss. des. rewrite FPTR in *. rewrite RSP in *. clarify. econs; et.
      + i.
        destruct (classic (brange blk3
                                  (Ptrofs.unsigned ofs1)
                                  (Ptrofs.unsigned ofs1 + 4 * size_arguments (SkEnv.get_sig skd0)) blk ofs)).
        * rr in H. des; clarify. eapply Mem.perm_cur. eapply Mem.perm_implies with Freeable; eauto with mem.
        * eapply PERM; et.
          eapply PERM0; et.
          eapply Mem.valid_block_unchanged_on; et.
      + des_ifs. clear_tac.
        eapply Mem_unchanged_on_trans_strong; et.
        eapply Mem.unchanged_on_implies; try apply RO0; et.
        i. des.
        esplits; et.
        { u. i; des; clarify. r in H. eapply H. eapply Mem.perm_implies with Freeable; eauto with mem. }
      + eapply Mem_unchanged_on_trans_strong; et.
        eapply Mem.unchanged_on_implies; try apply PRIV0; et.
        u. i; des; clarify; ss.
    - (* init *)
      inv INIT.
      r in SUARG. des.
      rename m into m2.
      set (Unreach.mk su_arg.(Unreach.unreach) su_arg.(Unreach.ge_nb) (Pos.succ su_arg.(Unreach.nb))) as su_init.
      exists su_init.
      assert(HLE: Unreach.hle su_arg su_init).
      { rr. ss. esplits; et.
        xomega.
      }
      assert(SURS: forall pr, UnreachC.val' su_init (rs pr)).
      {
        i.
        destruct (is_real_ptr (rs pr)) eqn:ISPTR; cycle 1.
        { ii; ss. rewrite PTR in *. ss. }

        inv STORE. inv H.
        exploit Mem.alloc_result; eauto. i; clarify.
        exploit Mem.nextblock_alloc; eauto. intro SUCC.

        inv MEM.

        exploit PTRFREE; et. i; des; ss; clarify; cycle 1.
        { unfold su_init. ii. ss.
          rewrite PTR in *. rewrite NB0 in *. erewrite <- Mem.nextblock_alloc; eauto.
          rr in VAL. symmetry in RSPC. repeat spc VAL. des. split; ss. rewrite NB0 in *. rewrite SUCC. eauto with xomega.
        }
        { unfold su_init. ii. ss.
          rewrite PTR in *. clarify.
          rewrite ! NB0 in *.
          esplits; et.
          - ii. inv WF. exploit WFHI; et. i. Unreach.nb_tac. xomega.
          - xomega.
        }

        eapply (@Sound.hle_val UnreachC.Unreach); et.
        (* TODO: pull out as a lemma *)
        inv TYP.

        assert(IN: In (rs pr) (Args.vs args)).
        { clear - ARG VALS0 MR ISPTR.
          r in VALS0.
          abstr (sig_args (fn_sig fd)) sargs.
          generalize (loc_arguments_one (fn_sig fd)); intro ONES.
          abstr (loc_arguments (fn_sig fd)) locs.
          abstr (Args.vs args) vs.
          ginduction vs; ii; ss; inv VALS0; ss.
          rewrite in_app_iff in ARG. destruct sargs; inv H.
          des; eauto.
          exploit ONES; eauto. i; des. destruct a1; ss. des; ss. clarify.
          inv H0. inv H3. unfold to_mregset in *.
          erewrite to_mreg_preg_of in H4; eauto. rewrite H4 in *.
          unfold typify in *; des_ifs; eauto.
        }
        Fail spc VALS. (* TODO: fix spc *)
        rr in VALS. rewrite Forall_forall in *. eapply VALS; et.
      }
      ss.
      esplits; eauto; try refl; swap 2 3.
      { (* store_arguments mle *)
        inv STORE. inv H.
        exploit Mem.alloc_result; eauto. i; clarify.
        exploit Mem.nextblock_alloc; eauto. intro SUCC.

        econs; eauto.
        * ii.
          eapply Mem.perm_alloc_4; eauto.
          eapply UNCH; eauto.
          { unfold Mem.valid_block in *. des_ifs. xomega. }
          { unfold Mem.valid_block in *. rewrite SUCC. xomega. }
        * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1.
          { eapply Mem.unchanged_on_implies; eauto.
            ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. }
          { eapply Mem.alloc_unchanged_on; eauto. }
        * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1.
          { eapply Mem.unchanged_on_implies; eauto.
            ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. }
          { eapply Mem.alloc_unchanged_on; eauto. }
      }
      econs; eauto; ss.
      + (* mem *)

        inv STORE. inv H.
        exploit Mem.alloc_result; eauto. i; clarify.
        exploit Mem.nextblock_alloc; eauto. intro SUCC.

        inv MEM.
        econs; ss; eauto; cycle 1.
        { ii. exploit BOUND; eauto. i. unfold Mem.valid_block in *. rewrite <- NB. rewrite SUCC. xomega. }
        { rewrite <- NB. rewrite SUCC. xomega. }
        { rewrite NB0. congruence. }
        i.
        admit "this should hold".
      + unfold su_init. inv WF. econs; ss; et. ii. exploit WFHI; et. i. xomega.
      + (* ske *)
        inv SKENV. rewrite PUB in *. ss.
    - (* step *)
      admit "ez".
    - (* call *)
      inv AT. ss.
      assert(SUARGS: UnreachC.args' su0 (Args.mk (Vptr blk0 Ptrofs.zero true) vs m1)).
      {
        inv SUST. r. splits; ss.
        + rewrite <- FPTR. eapply RS; et.
        + rewrite Forall_forall. i.
          admit "extcall-arguments - (MEM && UnreachC.mem'_load_val') \/ (RS)".
        + clear - FREE MEM. admit "ez - Unreach.mem - free - Unreach.mem".
      }
      exploit (@Sound.greatest_ex _ su0 (Args.mk (Vptr blk0 Ptrofs.zero true) vs m1)); ss; eauto.
      { exists su0. esplits; eauto. refl. }
      i; des.
      des_ifs. clear_tac.
      esplits; eauto.
      + (* mle *)
        inv SUST.
        exploit RS; eauto. intro SU; des.
        eapply Unreach.free_mle; eauto.
      + (* footprint *)
        des_ifs. des. clarify. econs; eauto.
        * eapply Mem.free_range_perm; et.
        * admit "ez - valid block".
        * inv SUST. eapply STACKPUB; et.
      + (* K *)
        ii. inv AFTER. ss.
        destruct retv; ss. rename m into m2.
        assert(GRARGS: Sound.args su_gr (Args.mk (Vptr blk0 Ptrofs.zero true) vs m1)).
        { rr in GR. des. ss. }
        assert(LEOLD: Unreach.hle_old su_gr su_ret).
        { eapply Unreach.hle_hle_old; et. rr in GRARGS. des. ss. }
        (* set (f := fun b => if su_ret b *)
        (*                    then BCinvalid *)
        (*                    else *)
        (*                      if plt b (Mem.nextblock m_arg) *)
        (*                      then bc b *)
        (*                      else *)
        (*                        if plt b (Mem.nextblock retv.(Retv.m)) *)
        (*                        then BCother *)
        (*                        else BCinvalid). *)
        set (su1 := Unreach.mk (fun blk =>
                                  (* if su_ret.(Unreach.unreach) blk *)
                                  (* then true *)
                                  (* else  *)
                                  (*   if plt blk (Mem.nextblock m0) *)
                                  (*   then su0.(Unreach.unreach) blk *)
                                  (*   else false *)
                                  if plt blk (Mem.nextblock m0)
                                  then su0.(Unreach.unreach) blk
                                  else su_ret.(Unreach.unreach) blk
                               )
                               su0.(Unreach.ge_nb) m2.(Mem.nextblock)).
        exists su1.
        assert(HLEA: Sound.hle su0 su1).
        (* { rr in GR. des. unfold su1. *)
        (*   rr. ss. esplits; eauto. *)
        (*   - ii. des_ifs. eapply LE; eauto. eapply LE0; eauto. *)
        (*   - ii. des. des_ifs. inv SUST. inv MEM. congruence. *)
        (*   - admit "ez". *)
        (* } *)
        { unfold su1. rr. ss.
          inv SUST. inv MEM. rewrite NB in *.
          esplits; et.
          - ii. des_ifs.
          - admit "ez".
        }
        assert(LEA: UnreachC.le' su0 su1).
        { rr in GR. des. unfold su1.
          rr. ss. esplits; eauto.
          ii. des_ifs. eapply LEOLD; eauto. eapply LE0; eauto.
        }
        assert(LEB: UnreachC.le' su1 su_ret).
        { rr in GR. des. unfold su1.
          rr. ss. esplits; eauto.
          - ii. des_ifs. eapply LEOLD; eauto. eapply LE0; eauto.
          - rr in LE. des. rr in LE0. des. congruence.
        }
        esplits; eauto; cycle 1.
        { (* unfree mle_excl *)
          des. clarify. rewrite FPTR in *. ss. des_ifs. clear_tac.
          econs; et.
          - ii. eapply Mem_unfree_unchanged_on; et.
          - eapply Mem_unfree_unchanged_on; et.
            (* u. ii; des; ss; clarify. *)
            (* rr in H. eapply H. *)
        }
        (* { inv SUST. inv MEM. rr. split; ss. ii. des_ifs. apply BOUND in PR. unfold Mem.valid_block in *. ss. } *)
        inv SUST.
        generalize (loc_external_result_one sg); intro ONE.
        destruct (loc_external_result sg) eqn:T; ss. clear_tac.
        unfold Pregmap.set.
        (* sound_state *)
        Local Opaque PregEq.eq.
        econs; ss; eauto.
        { i.
          set pr as PR.
          des_ifs.
          - (* PC *)
            eapply (@Sound.hle_val UnreachC.Unreach); ss; et.
          - (* retv *)
            move RETV at bottom. rr in RETV. des. ss.
            eapply UnreachC.val_le; eauto.
            unfold su1. ss. inv MEM0. rewrite NB. refl.
          - (* others *)
            eapply (@Sound.hle_val UnreachC.Unreach); ss; et.
            unfold regset_after_external. des_ifs.
        }
        { bar. move RETV at bottom. rr in RETV. des. ss.
          assert(UnreachC.mem' su1 m2).
          { inv MEM0. econs; ss; eauto; cycle 1.
            - ii. eapply BOUND. des_ifs. eapply LEB. eapply LEA. ss.
            - admit "ez".
            - i.
              destruct (classic (Unreach.unreach su_ret blk2)); cycle 1.
              { hexploit SOUND; eauto. i.
                eapply UnreachC.memval_le; et. unfold su1. ss. Unreach.nb_tac. xomega.
              }
              rename H into SURET.
              des_ifs.
              assert(HLE: forall
                        blk
                        (OLD: Plt blk (Mem.nextblock m0))
                        (NEW: Unreach.unreach su_ret blk)
                      ,
                        <<OLD: Unreach.unreach su_gr blk>>).
              { ii. rr in LEOLD. des. eapply OLD0. esplits; et. clear - OLD GR FREE. admit "ez". }
              exploit HLE; et. intro SUGR; des.

              assert(UNCH: (ZMap.get ofs1 (Mem.mem_contents m2) !! blk2)
                           = (ZMap.get ofs1 (Mem.mem_contents m1) !! blk2)).
              { inv MLE. eapply Mem.unchanged_on_contents; eauto.
                - eapply PRIV; et.
                  admit "ez".
              }


              move SUARGS at bottom. rr in SUARGS. des. ss. inv MEM0.
              erewrite UNCH.
              hexploit SOUND0; et.
              { inv MLE. eapply PRIV; et. admit "ez". }
              i; des.
              admit "this should hold".
          }
          admit "ez".
        }
        { i. eapply (@Sound.hle_val UnreachC.Unreach); ss; et. }
        { (* WF *)
          inv WF. unfold su1. econs; ss; et.
          - i. des_ifs; et.
            inv MEM. xomega.
          - i. des_ifs; et.
            { admit "ez". }
            rr in RETV. des. ss. inv WF. inv MEM0. Unreach.nb_tac. eapply WFHI0; et.
        }
        { unfold regset_after_external. ss.
          des_ifs_safe.
          des_ifs.
          { unfold loc_external_result in *. unfold loc_result in *. unfold loc_result_64 in *. des_ifs; ss. }
          eapply (@Sound.hle_val UnreachC.Unreach); ss; et.
        }
    - (* return *)
      inv SUST. inv FINAL. ss. clarify.
      exists su0. esplits; eauto.
      { refl. }
      { rr. ss. esplits; ss; et.
        admit "this should hold".
      }
      eapply Unreach.free_mle; eauto.
      exploit INIT; eauto. i; des. ss.
  Unshelve.
      all: ss.
  Qed.

End TRIAL2.
End TRIAL2.

Let asm_ext_unreach_lxsim: forall
    asm skenv_link
    m_src0 m_tgt0
    (GENV: Genv.match_genvs (match_globdef (fun _ : AST.program fundef unit => eq) eq asm)
                            (SkEnv.revive (SkEnv.project skenv_link (defs asm)) asm)
                            (SkEnv.revive (SkEnv.project skenv_link (defs asm)) asm))
    m_src1 m_tgt1
    st_init_src st_init_tgt
  ,
  <<LXSIM: lxsim (modsem skenv_link asm) (modsem skenv_link asm)
                 (fun st => exists su m_init, sound_state skenv_link su m_init st)
                 (SimMemExt.mk m_src0 m_tgt0) (lift_idx unit_ord_wf tt) st_init_src st_init_tgt
                 (SimMemExt.mk m_src1 m_tgt1)>>
.
Proof.
  i. revert_until m_tgt1.
  pcofix CIH. ii. pfold.
Abort.

Lemma asm_ext_unreach
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  fold SkEnv.t in skenv_link_src.
  hexploit (TRIAL2.asm_unreach_local_preservation skenv_link_src asm); eauto. i; des.
  eapply match_states_sim; ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eauto.
  - (* init bsim *)
    admit "".
  - (* init progress *)
    admit "".
  - (* call bsim *)
    admit "".
  - admit "".
  - admit "".
  - admit "".
  - admit "".
Admitted.
(*   econs; ss; eauto. *)
(*   { eapply asm_unreach_local_preservation; eauto. } *)
(*   ii; ss. *)

(*   exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto. *)
(*   { i; ss. clarify. } *)
(*   intro GENV; des. *)
(*   inv SIMSKENVLINK. inv SIMSKENV. ss. *)

(*   inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify. *)
(*   rename fptr into fptr_src. rename fptr0 into fptr_tgt. *)
(*   rename vs into vs_src. rename vs0 into vs_tgt. *)
(*   fold fundef in *. *)
(*   inv FPTR; ss. *)
(*   split; ii; cycle 1. *)
(*   { (* tgt progress *) *)
(*     des. inv SAFESRC. esplits. econs; ss; eauto. *)
(*     - rp; eauto. symmetry. eapply Mem.mext_next; eauto. *)
(*     - admit "this should hold - store_arguments_progress". *)
(*   } *)
(*   (* bsim *) *)
(*   rename src into m_src0. rename tgt into m_tgt0. *)
(*   bar. *)
(*   inv INITTGT. rename m into m_tgt1. *)
(*   assert(exists m_src1, <<STORESRC: AsmC.store_arguments m_src0 rs vs_src (fn_sig fd) m_src1>>). *)
(*   { admit "this should hold - store_arguments_progress". } *)
(*   des. *)
(*   esplits; eauto. *)
(*   ss. *)
(*   instantiate (1:= (SimMemExt.mk m_src1 m_tgt1)). instantiate (1:= Ord.lift_idx unit_ord_wf tt). *)
(*   clear - GENV. *)
(*   rename _st_init_src into st_init_src. abstr {| init_rs := rs; st := State rs m_tgt1 |} st_init_tgt. *)
(*   generalize dependent st_init_src. *)
(*   generalize dependent st_init_tgt. *)
(*   pcofix CIH. ii. pfold. *)
(*   destruct (classic ((modsem skenv_link asm).(ModSem.is_call) st0)). *)
(*   { ss. rr in H. des. *)
(*     econs 3; eauto. *)
(*     { econs; eauto. } *)
(*     ii. des. clear_tac. *)
(*     exists args_src. exists (SimMemId.mk args_src.(Args.m) args_src.(Args.m)). ss. *)
(*     esplits; eauto. *)
(*     { econs; ss; eauto. } *)
(*     ii. ss. des. *)
(*     esplits; eauto. *)
(*     inv SIMRETV. ss. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. clarify. *)
(*   } *)
(*   destruct (classic ((modsem skenv_link asm).(ModSem.is_return) st0)). *)
(*   { ss. rr in H0. des. *)
(*     dup H0. set (R:= retv). inv H0. *)
(*     econs 4; eauto. *)
(*     { instantiate (1:= SimMemId.mk m2 m2). ss. } *)
(*     { econs; eauto. } *)
(*     { ss. } *)
(*   } *)
(*   econs 1; eauto. *)
(*   ii; des. clear_tac. *)
(*   esplits; eauto. *)
(*   econs; eauto; cycle 1. *)
(*   { admit "ez". } *)
(*   ii. ss. inv STEPSRC. *)
(*   esplits; eauto. left. apply plus_one. econs; eauto. *)
(*   { admit "ez". } *)
(*   econs; eauto. *)
(* Unshelve. *)
(*   all: ss. *)
(* Qed. *)

Lemma asm_inj_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma asm_inj_drop
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.
