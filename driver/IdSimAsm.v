Require Import Program.

Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
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
Require Import StoreArguments.
Require Import AsmExtra IntegersC.
Require Import Coq.Logic.PropExtensionality.


Set Implicit Arguments.


Local Existing Instance Val.mi_normal.
Local Opaque Z.mul Z.add Z.sub Z.div.

Require Import mktac.

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
                            (SkEnv.revive (SkEnv.project skenv_link asm.(Sk.of_program fn_sig)) asm)
                            (SkEnv.revive (SkEnv.project skenv_link asm.(Sk.of_program fn_sig)) asm))
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

Inductive wf_init_rs (sg: signature) (rs: regset) : Prop :=
| wf_init_rs_intro
    (RSPDEF: rs RSP <> Vundef)
    (RAPTR: wf_RA (rs RA))
    (PTRFREE: forall mr (SAVE: Conventions1.is_callee_save mr),
        ~ is_real_ptr (rs (to_preg mr)))
.

Definition undef_bisim (rs_src rs_tgt: regset): Prop :=
  forall (r: mreg) (IN: Conventions1.is_callee_save r = true) (UNDEF: rs_src (to_preg r) = Vundef),
    rs_tgt (to_preg r) = Vundef.

Inductive match_states
          (ge_src ge_tgt: genv)
          (sm_init : @SimMem.t (@SimMemInjC.SimMemInj Val.mi_normal))
  : nat-> AsmC.state -> AsmC.state -> (@SimMem.t SimMemInjC.SimMemInj) -> Prop :=
| match_states_intro
    j init_rs_src init_rs_tgt rs_src rs_tgt m_src m_tgt
    (sm0 : @SimMem.t (@SimMemInjC.SimMemInj Val.mi_normal))
    (* (GEINJECT: skenv_inject skenv_link_src j) *)
    (AGREE: agree j rs_src rs_tgt)
    (AGREEINIT: agree j init_rs_src init_rs_tgt)
    (INJ: Mem.inject j m_src m_tgt)
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MCOMPATINJ: j = sm0.(SimMemInj.inj))
    (MWF: SimMem.wf sm0)
    (UNDEF: undef_bisim init_rs_src init_rs_tgt)

    fd
    (FINDF: Genv.find_funct ge_src (init_rs_src PC) = Some (Internal fd))
    (WFINITSRC: wf_init_rs fd.(fn_sig) init_rs_src)
    (WFINITTGT: wf_init_rs fd.(fn_sig) init_rs_tgt)
    (RSPDELTA: forall blk_src ofs b (RSPSRC: init_rs_src RSP = Vptr blk_src ofs b),
        exists blk_tgt,
          (j blk_src = Some (blk_tgt, 0)))
  :
    match_states
      ge_src ge_tgt sm_init 0
      (AsmC.mkstate init_rs_src (Asm.State rs_src m_src))
      (AsmC.mkstate init_rs_tgt (Asm.State rs_tgt m_tgt)) sm0
.

(* TODO it's from AsmgenproofC *)
Section FROMASMGEN.

  Definition set_regset (rs0 rs1: Mach.regset) (sg: signature) (mr: mreg) : val :=
    if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
    then rs1 mr
    else rs0 mr.

  Definition set_regset_undef (rs: Mach.regset) (sg: signature) (mr: mreg) : val :=
    if Loc.notin_dec (R mr) (regs_of_rpairs (loc_arguments sg))
    then Vundef
    else rs mr.

End FROMASMGEN.

(* TODO it's from LowerBoundExtra *)
Section FROMLB.

  Definition extcall_args_reg (mr: mreg) (sg: signature):
    {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
    {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
  Proof.
    generalize (regs_of_rpairs (loc_arguments sg)). induction l.
    - ss. tauto.
    - ss. inv IHl; [tauto|].
      destruct a.
      + destruct (mreg_eq r mr); [clarify; eauto|].
        right. intros []; clarify.
      + right. intros []; clarify.
  Qed.

  Definition src_init_rs sg (rs_src: regset) (rsp: val) : regset :=
    fun (pr : PregEq.t) =>
      match Asm.to_mreg pr with
      | Some mr =>
        if (extcall_args_reg mr sg)
        then (rs_src pr)
        else (to_fake (rs_src pr))
      | None =>
        match pr with
        | IR RSP => rsp
        | PC => rs_src PC
        | RA => to_fake (rs_src RA)
        | _ => to_fake (rs_src pr)
        end
      end.

End FROMLB.



Inductive has_footprint
          (skenv_link_src skenv_link_tgt: SkEnv.t)
  :
    AsmC.state -> AsmC.state -> @SimMem.t SimMemInjC.SimMemInj -> Prop :=
| has_foot_print_intro
    blk0 blk1_src blk1_tgt ofs_src ofs_tgt
    (init_rs_src init_rs_tgt rs0_src rs0_tgt: regset)
    m_src m_tgt (sm0: @SimMem.t SimMemInjC.SimMemInj) sg
    (FPTR: rs0_src # PC = Vptr blk0 Ptrofs.zero true)
    (SIG: exists skd, skenv_link_src.(Genv.find_funct) (Vptr blk0 Ptrofs.zero true)
                      = Some skd /\ SkEnv.get_sig skd = sg)
    (RSPSRC: rs0_src RSP = Vptr blk1_src ofs_src true)
    (RSPTGT: rs0_tgt RSP = Vptr blk1_tgt ofs_tgt true)
    (FREEABLESRC: Mem.range_perm (sm0.(SimMem.src)) blk1_src (ofs_src.(Ptrofs.unsigned))
                                 (ofs_src.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                 Cur Freeable)
    (FREEABLETGT: Mem.range_perm (sm0.(SimMem.tgt)) blk1_tgt (ofs_tgt.(Ptrofs.unsigned))
                                 (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                                 Cur Freeable)
    (VALIDSRC: Mem.valid_block sm0.(SimMem.src) blk1_src)
    (VALIDTGT: Mem.valid_block sm0.(SimMem.tgt) blk1_tgt)

    (MLEEXCLWF: sm0.(SimMemInj.tgt_external) <2= (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))


  :
    has_footprint skenv_link_src skenv_link_tgt
                  (mkstate init_rs_src (State rs0_src m_src))
                  (mkstate init_rs_tgt (State rs0_tgt m_tgt))
                  sm0
.

Inductive mle_excl
          (skenv_link_src skenv_link_tgt: SkEnv.t)
  : AsmC.state -> AsmC.state -> (@SimMem.t SimMemInjC.SimMemInj)
    -> (@SimMem.t SimMemInjC.SimMemInj) -> Prop :=
| mle_excl_intro
    blk0 sg
    blk1_src ofs_src
    (init_rs_src rs0_src: regset) m_unused_src
    blk1_tgt ofs_tgt
    (init_rs_tgt rs0_tgt: regset) m_unused_tgt
    (FPTR: rs0_src # PC = Vptr blk0 Ptrofs.zero true)
    (SIG: exists skd, skenv_link_src.(Genv.find_funct) (Vptr blk0 Ptrofs.zero true)
                      = Some skd /\ SkEnv.get_sig skd = sg)
    (RSPSRC: rs0_src RSP = Vptr blk1_src ofs_src true)
    (RSPTGT: rs0_tgt RSP = Vptr blk1_tgt ofs_tgt true)
    (mrel0 mrel1: @SimMem.t SimMemInjC.SimMemInj)
    (INCR: inject_incr mrel0.(SimMemInj.inj) mrel1.(SimMemInj.inj))

    (SRCUNCHANGED: Mem.unchanged_on mrel0.(SimMemInj.src_external) mrel0.(SimMem.src) mrel1.(SimMem.src))

    (TGTUNCHANGED: Mem.unchanged_on
                     ((mrel0.(SimMemInj.tgt_external))
                        /2\
                        (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))))
                     mrel0.(SimMem.tgt) mrel1.(SimMem.tgt))

    (SRCPARENTEQ: mrel0.(SimMemInj.src_external) = mrel1.(SimMemInj.src_external))
    (SRCPARENTEQNB: mrel0.(SimMemInj.src_parent_nb) = mrel1.(SimMemInj.src_parent_nb))
    (TGTPARENTEQ: mrel0.(SimMemInj.tgt_external) /2\
                                                 (~2 brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))) = mrel1.(SimMemInj.tgt_external))
    (TGTPARENTEQNB: mrel0.(SimMemInj.tgt_parent_nb) = mrel1.(SimMemInj.tgt_parent_nb))
    (FROZEN: SimMemInj.frozen mrel0.(SimMemInj.inj) mrel1.(SimMemInj.inj) (mrel0.(SimMemInj.src_parent_nb))
                                                                          (mrel0.(SimMemInj.tgt_parent_nb)))

    (MAXSRC: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(SimMem.src) b)
        (UNFREE: ~ brange blk1_src (ofs_src.(Ptrofs.unsigned)) (ofs_src.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                   b ofs)
      ,
        <<MAX: Mem.perm mrel1.(SimMem.src) b ofs Max <1= Mem.perm mrel0.(SimMem.src) b ofs Max>>)
    (MAXTGT: forall
        b ofs
        (VALID: Mem.valid_block mrel0.(SimMem.tgt) b)
        (UNFREE: ~ brange blk1_tgt (ofs_tgt.(Ptrofs.unsigned)) (ofs_tgt.(Ptrofs.unsigned) + 4 * (size_arguments sg))
                   b ofs)
      ,
        <<MAX: Mem.perm mrel1.(SimMem.tgt) b ofs Max <1= Mem.perm mrel0.(SimMem.tgt) b ofs Max>>)
  :
    mle_excl
      skenv_link_src skenv_link_tgt
      (mkstate init_rs_src (State rs0_src m_unused_src))
      (mkstate init_rs_tgt (State rs0_tgt m_unused_tgt))
      mrel0 mrel1
.


Require Import MatchSimModSemExcl.
Require Import Conventions1C.

Lemma Mem_unfree_perm m0 m1 b lo hi
      (UNFREE: Mem_unfree m0 b lo hi = Some m1)
      blk ofs k p
      (PERM: Mem.perm m0 blk ofs k p)
  :
    Mem.perm m1 blk ofs k p.
Proof.
  unfold Mem_unfree in *. des_ifs. unfold Mem.perm in *. ss.
  rewrite PMap.gsspec. unfold zle, zlt, proj_sumbool. des_ifs.
  exfalso. eapply m; eauto.
  eapply Mem.perm_max.
  eapply Mem.perm_implies; eauto. econs.
Qed.

Lemma Z2Nat_range n:
  Z.of_nat (Z.to_nat n) = if (zle 0 n) then n else 0.
Proof. Admitted.
  (* des_ifs. *)
  (* - rewrite Z2Nat.id; eauto. *)
  (* - unfold Z.of_nat. des_ifs. *)

Theorem Mem_unfree_parallel_inject
        j m1 m2 b lo hi m1' b' delta
        (INJECT: Mem.inject j m1 m2)
        (UNFREE: Mem_unfree m1 b lo hi = Some m1')
        (DELTA: j b = Some (b', delta))
        (* TODO add condition about align *)
        (NOPERM: Mem_range_noperm m2 b' (lo + delta) (hi + delta))


  :
    exists m2',
      (<<UNFREE: Mem_unfree m2 b' (lo + delta) (hi + delta) = Some m2'>>)
      /\ (<<INJECT: Mem.inject j m1' m2'>>).
Proof.
  unfold Mem_unfree in UNFREE. des_ifs.

  assert (VALID: Plt b' (Mem.nextblock m2)).
  {
    exploit Mem.valid_block_inject_2; eauto.
  }
  unfold Mem_unfree in *. des_ifs. esplits; eauto. ss.

  assert (NOOVERLAP: forall b_src delta' ofs k p (DELTA: j b_src = Some (b', delta'))
                            (OFS: lo + delta <= ofs + delta' < hi + delta)
                            (PERM: Mem.perm m1 b_src ofs k p),
             False).
  {
    i. exploit Mem.perm_inject; eauto. i. exploit NOPERM; eauto.
    eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
  }

  econs; ss; eauto; i.

  - cinv (Mem.mi_inj _ _ _ INJECT).
    econs; ss; eauto; i.
    + destruct (peq b b1); clarify.
      * unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *.
        des_ifs; clarify; try nia; exploit Mem.perm_inject; eauto.
      * assert (Mem.perm m2 b2 (ofs + delta0) k p1).
        {
          exploit Mem.perm_inject; eauto. unfold Mem.perm in *. ss.
          rewrite PMap.gso in H0; eauto.
        }
        unfold Mem.perm, proj_sumbool in *. ss. rewrite PMap.gsspec in *.
        des_ifs. exfalso. exploit NOPERM; eauto.
        eapply Mem.perm_max. eapply Mem.perm_implies; eauto. econs.
    + admit "add condition".
    + unfold Mem.perm, proj_sumbool in *. ss.
      repeat rewrite PMap.gsspec in *. des_ifs; eauto.
      * rewrite Mem_setN_in_repeat; eauto; [econs|].
        rewrite Z2Nat.id; nia.
      * repeat rewrite Mem.setN_outside; cycle 1.
        { right. rewrite length_list_repeat.
          rewrite Z2Nat_range. des_ifs; try nia. }
        { right. rewrite length_list_repeat.
          rewrite Z2Nat_range. des_ifs; try nia. }
        eauto.
      * repeat rewrite Mem.setN_outside; cycle 1.
        { left. nia. }
        repeat rewrite Mem.setN_outside; cycle 1.
        { left. nia. }
        eauto.
      * repeat rewrite Mem.setN_outside; cycle 1.
        { rewrite length_list_repeat.
          rewrite Z2Nat_range. des_ifs; try nia. }
        repeat rewrite Mem.setN_outside; cycle 1.
        { rewrite length_list_repeat.
          rewrite Z2Nat_range. des_ifs; try nia. }
        eauto.
      * repeat rewrite Mem.setN_outside; cycle 1.
        { rewrite length_list_repeat.
          rewrite Z2Nat_range. des_ifs; try nia.
          apply NNPP. ii.
          exploit NOOVERLAP; eauto. nia. }
        eauto.
  - exploit Mem.mi_freeblocks; eauto.
  - exploit Mem.mi_mappedblocks; eauto.
  - ii. unfold Mem.perm in *. ss. apply imply_to_or. i. clarify.
    rewrite PMap.gsspec in *. unfold proj_sumbool in *. des_ifs; ss.
    + ii. exploit NOOVERLAP; eauto. nia.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify.
    + ii. exploit NOOVERLAP; eauto. nia.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
    + exploit Mem.mi_no_overlap; eauto. i. des; clarify. eauto.
    + exploit Mem.mi_no_overlap; try apply H; eauto. i. des; clarify.

  - admit "add condition".

  - unfold Mem.perm, proj_sumbool in *. ss.
    rewrite PMap.gsspec in *.
    des_ifs; ss; eauto; (try by exploit Mem.mi_perm_inv; eauto); left; econs.
Qed.


Lemma store_arguments_unchanged_on m0 m1 rs args sg
      (STORE: store_arguments m0 rs args sg m1)
  :
    Mem.unchanged_on (SimMemInj.valid_blocks m0) m0 m1.
Proof.
  inv STORE. dup ALC. eapply Mem.alloc_unchanged_on in ALC0.
  eapply Mem.unchanged_on_trans; eauto.
  eapply Mem.unchanged_on_implies; eauto.
  i. ss. des_ifs. red in H.
  exfalso. eapply Mem.fresh_block_alloc; eauto.
Qed.

Lemma loc_notin_not_in mr locs
  :
      Loc.notin (R mr) locs <-> ~ In (R mr) locs.
Proof.
  induction locs; ss.
  split; ii; des; des_ifs.
  - eapply IHlocs; eauto.
  - eapply IHlocs; eauto.
  - apply not_or_and in H. des. split; auto. ii. clarify.
  - apply not_or_and in H. des. split; auto.
Qed.

Lemma lessdef_commute j src0 src1 tgt0 tgt1
      (INJ0: Val.inject j src0 tgt0)
      (INJ1: Val.inject j src1 tgt1)
      (PTRFREE: ~ is_real_ptr src0)
      (LESS: Val.lessdef src0 src1)
      (UNDEF: src0 = Vundef -> tgt0 = Vundef)
  :
    Val.lessdef tgt0 tgt1.
Proof.
  inv LESS.
  - inv INJ0; inv INJ1; ss; try econs.
    rewrite UNDEF; auto.
  - rewrite UNDEF; auto.
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
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto.
  econs; ss; i.
  { instantiate (1:=bot1). admit "add condition". }
  eapply match_states_sim with
      (match_states :=
         match_states
           (SkEnv.revive (SkEnv.project skenv_link_src (Sk.of_program _ asm)) asm)
           (SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program _ asm)) asm))
      (match_states_at := top4)
      (has_footprint := has_footprint skenv_link_src skenv_link_tgt)
      (mle_excl := mle_excl skenv_link_src skenv_link_tgt); ss; eauto; ii.
  - apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - inv MLE. inv FOOT. inv MLEEXCL.
    ss. econs; ss; eauto.
    + etrans; eauto.

    + eapply Mem.unchanged_on_trans; eauto.
      rewrite SRCPARENTEQ. eauto.
    + des. des_ifs. rewrite FPTR in *. rewrite RSPTGT in *. clarify.
      eapply Mem.unchanged_on_trans; eauto.
      rewrite TGTPARENTEQ in *.
      eapply Mem.unchanged_on_implies; eauto.
      ii. ss. splits; eauto.
    + etrans; eauto.
    + etrans; eauto.
    + etrans; eauto.
      rewrite TGTPARENTEQ in *. des. des_ifs. clarify.
      rewrite FPTR in *. clarify.
      rewrite RSPTGT in *. clarify.
      clear - TGTPARENTEQ0 MLEEXCLWF.
      extensionality blk.
      extensionality ofs.
      rewrite <- TGTPARENTEQ0.
      eapply propositional_extensionality. split; auto; tauto.

    + etrans; eauto.
    + inv FROZEN. inv FROZEN0.
      econs; ss; eauto.
      i. des.
      destruct (SimMemInj.inj sm1 b_src) eqn:EQ.
      * destruct p.
        exploit NEW_IMPLIES_OUTSIDE; eauto.
        eapply INCR0 in EQ. clarify.
      * exploit NEW_IMPLIES_OUTSIDE0; eauto.
        rewrite SRCPARENTEQNB.
        rewrite TGTPARENTEQNB.
        eauto.

    + ii. des. des_ifs. clarify.
      destruct (classic (brange blk1_src0 (Ptrofs.unsigned ofs_src0)
                                (Ptrofs.unsigned ofs_src0 + 4 * size_arguments (SkEnv.get_sig skd)) b ofs)).
      {
        unfold brange in *. des. clarify.
        eapply Mem.perm_cur. des_ifs.
        rewrite RSPSRC in *. clarify.
        rewrite FPTR in *. clarify.
        exploit FREEABLESRC; splits; eauto.
        eapply Mem.perm_implies; eauto. econs.
      }
      eapply MAXSRC; eauto.
      eapply MAXSRC0; eauto.
      inv SRCUNCHANGED.
      unfold Mem.valid_block.
      eapply Plt_Ple_trans; eauto.

    + ii. des. des_ifs. clarify.
      destruct (classic (brange blk1_tgt0 (Ptrofs.unsigned ofs_tgt0)
                                (Ptrofs.unsigned ofs_tgt0 + 4 * size_arguments (SkEnv.get_sig skd)) b ofs)).
      {
        unfold brange in *. des. clarify.
        eapply Mem.perm_cur. des_ifs.
        rewrite RSPTGT in *. clarify.
        rewrite FPTR in *. clarify.
        exploit FREEABLETGT; splits; eauto.
        eapply Mem.perm_implies; eauto. econs.
      }
      eapply MAXTGT; eauto.
      eapply MAXTGT0; eauto.
      inv TGTUNCHANGED.
      unfold Mem.valid_block.
      eapply Plt_Ple_trans; eauto.

  - inv SIMSKENV. ss.

    inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
    inv INITTGT. ss. inv TYP. inv MWF. ss.
    inv STORE. des.
    exploit store_arguments_parallel_inject; [..| eauto |]; eauto.
    + eapply typify_has_type_list; eauto.
    + eapply inject_list_typify_list; try eassumption.
      erewrite inject_list_length; eauto.
    + i. des.

      eexists (AsmC.mkstate (((to_pregset (set_regset rs_src (to_mregset rs) (fn_sig fd))) # PC <- fptr)
                               # RA <- (rs RA))
                            # RSP <- (Vptr (Mem.nextblock src) Ptrofs.zero true)
                            (Asm.State _ m_src1)). econs; ss.

      assert (INCR: inject_incr
                      inj
                      (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0)).
      { ii. unfold update_meminj. des_ifs.
        exfalso. inv PUBLIC. exploit mi_freeblocks.
        - eapply Plt_strict.
        - i. clarify.
      }
      esplits; eauto.
      {
        econs; ss; eauto.
        - instantiate (1:=fd).
          unfold Genv.find_funct in *. des_ifs_safe.
          cinv FPTR; ss; clarify; cycle 1.
          {
            exfalso. inv SAFESRC. ss.
          }

          assert (delta = 0).
          {
            unfold Genv.find_funct_ptr, SkEnv.revive in *. des_ifs.
            eapply Genv_map_defs_def in Heq0. des.
            inv SIMSKE. exploit SIMDEFINV; eauto. i. des. eauto.
          }
          clarify. psimpl. des_ifs.
          unfold Genv.find_funct_ptr in *. des_ifs_safe.
          clear - INCLSRC INCLTGT SIMSKENVLINK SIMSKE SIMSKELINK Heq0 H5.

          {
            (* genv *)
            unfold SkEnv.revive in *. ss.
            apply Genv_map_defs_def in Heq0. des.
            unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
            des_ifs_safe.
            apply Genv.invert_find_symbol in Heq0.
            inv SIMSKE. ss.
            exploit SIMDEFINV; eauto. i. des. clarify.
            exploit Genv_map_defs_def_inv; try apply DEFSRC.
            i. rewrite H. ss.
            unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
            erewrite Genv.find_invert_symbol. rewrite Heq1; eauto.
            exploit SIMSYMB3; eauto. i. des.
            assert (blk_src = b1).
            { exploit DISJ; eauto. }
            clarify.
          }

        - econs; eauto.
          erewrite inject_list_length; eauto.
        - econs; eauto.
          inv ARGTGT.
          econs; try eassumption; eauto.
          eapply extcall_arguments_same; eauto. i.
          unfold Pregmap.set, to_mregset, to_pregset, to_preg.
          erewrite to_preg_to_mreg.
          des_ifs; clarify; ss.
          * unfold preg_of in *; des_ifs.
          * unfold preg_of in *; des_ifs.
          * unfold preg_of in *; des_ifs.
          * unfold set_regset. des_ifs; clarify; eauto.
            exfalso. eapply Loc.notin_not_in in n2. eauto.
        - i.
          unfold Pregmap.set in *. des_ifs; eauto. left.
          unfold set_regset, to_pregset in *. des_ifs; inv PTR.
          + exploit PTRFREE; eauto. i. des.
            * rewrite to_preg_to_mreg in *. clarify.
              apply Loc.notin_not_in in n2. eauto.
            * clear - INPC. unfold to_preg, preg_of in *. des_ifs.
            * clear - INRSP. unfold to_preg, preg_of in *. des_ifs.
          + esplits; eauto. apply NNPP. rewrite <- loc_notin_not_in. auto.
     }

      { instantiate (1:= SimMemInj.mk
                           m_src1 m
                           (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0)
                           _ _ _ _).
        econs; ss; auto.
        - i. exploit store_arguments_unchanged_on; try apply ARGTGT; eauto. i. eapply Mem.unchanged_on_implies; eauto.
        - i. exploit store_arguments_unchanged_on; try apply H; eauto.
          i. eapply Mem.unchanged_on_implies; eauto.
        - econs; ss; eauto. i. des.
          unfold update_meminj in *. des_ifs; ss.
        - ii. eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
          eapply unchanged_on_perm in PR; eauto.
        - ii. eapply store_arguments_unchanged_on in H. inv H.
          eapply unchanged_on_perm in PR; eauto.
      }
      {
        assert (AGREE0 :
                  agree (update_meminj inj (Mem.nextblock src) (Mem.nextblock tgt) 0)
                        (((to_pregset (set_regset rs_src (to_mregset rs) (fn_sig fd))) # PC <- fptr) # RA <- (rs RA)) # RSP <-
                        (Vptr (Mem.nextblock src) Ptrofs.zero true) rs).
        {
          ii.
          unfold Pregmap.set, to_mregset, to_pregset, to_preg, update_meminj.
          des_ifs; ss; eauto.
          - rewrite H0. econs; ss.
            des_ifs. ss.
          - inv RAPTR. destruct (rs RA); try econs; ss. des_ifs. eauto.
          - unfold set_regset. des_ifs; clarify; eauto.
            + apply to_mreg_some_to_preg in Heq. unfold to_preg in *. rewrite Heq.
              apply fakeptr_inject_id. ii. exploit PTRFREE; eauto. i. des; eauto.
              rewrite <- Heq in *. rewrite to_preg_to_mreg in *. clarify.
              eapply loc_notin_not_in; eauto.
            + specialize (AGREE m0). unfold to_mregset in *.
              apply to_mreg_some_to_preg in Heq. rewrite Heq in *. eauto.
        }

        econs; ss.
        - econs; ss; auto.
          + ii. unfold SimMemInj.src_private, SimMemInj.tgt_private, update_meminj in *. ss.
            eapply SRCEXT in PR. des.
            splits; eauto.
            * unfold loc_unmapped. des_ifs; ss.
              exfalso. eapply Plt_strict. eauto.
            * exploit store_arguments_unchanged_on; try apply ARGTGT; eauto. i.
              eapply Mem.valid_block_unchanged_on; eauto.
          + ii. unfold SimMemInj.src_private, SimMemInj.tgt_private, update_meminj in *. ss.
            eapply TGTEXT in PR. des.
            splits; eauto.
            * unfold loc_out_of_reach in *.
              ii. des_ifs; ss.
              -- exfalso. eapply Plt_strict. eauto.
              -- eapply PR; eauto.
                 ii. eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT.
                 eapply unchanged_on_perm in H2; eauto.
                 ++ eapply Mem.valid_block_inject_1; eauto.
                 ++ eapply Mem.valid_block_inject_1; eauto.
            * eapply store_arguments_unchanged_on in H.
              eapply Mem.valid_block_unchanged_on; eauto.
          + etrans; eauto.
            eapply store_arguments_unchanged_on in ARGTGT. inv ARGTGT. eauto.
          + etrans; eauto.
            eapply store_arguments_unchanged_on in H. inv H. eauto.
        - unfold to_pregset, set_regset, Pregmap.set. ii.
          rewrite to_preg_to_mreg in *. des_ifs.
          + rewrite e. auto.
          + unfold to_preg, preg_of in *. des_ifs.
          + exfalso. exploit loc_args_callee_save_disjoint; eauto.
            apply NNPP. rewrite <- loc_notin_not_in. eauto.
        - instantiate (1:= fd). instantiate (1:= fn_sig).
          inv SAFESRC. ss.
          unfold to_pregset, set_regset, Pregmap.set. des_ifs.

          clear - FINDF FINDF0 FPTR SIMSKE.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. inv FPTR.
          unfold SkEnv.revive in *.
          apply Genv_map_defs_def in Heq2. des.
          apply Genv_map_defs_def in Heq0. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in *.
          des_ifs_safe. apply Genv.invert_find_symbol in Heq2.
          inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
          exploit SIMSYMB1; eauto. i. des.
          apply Genv.find_invert_symbol in BLKTGT. clarify.
        - econs; ss. i.
          unfold to_pregset, set_regset, Pregmap.set.
          rewrite to_preg_to_mreg. des_ifs; eauto.
          + unfold to_preg, preg_of in *; des_ifs.
          + unfold to_preg, preg_of in *; des_ifs.
          + unfold to_preg, preg_of in *; des_ifs.
          + ii. unfold to_mregset in *. exploit PTRFREE; eauto. i. des.
            * rewrite to_preg_to_mreg in *. clarify. eapply loc_notin_not_in; eauto.
            * unfold to_preg, preg_of in *; des_ifs.
            * unfold to_preg, preg_of in *; des_ifs.
          + exfalso. exploit loc_args_callee_save_disjoint; eauto.
            apply NNPP. rewrite <- loc_notin_not_in. eauto.
        - econs; ss.
          + ii. eq_closure_tac.
          + ii. exploit PTRFREE; eauto. i. des.
            * rewrite to_preg_to_mreg in MR. clarify.
              exploit loc_args_callee_save_disjoint; eauto.
            * unfold to_preg, preg_of in *. des_ifs.
            * unfold to_preg, preg_of in *. des_ifs.
        - ii. unfold to_pregset, set_regset, Pregmap.set in *. des_ifs.
          unfold update_meminj in *. eexists; des_ifs; eauto.
      }

  - inv SIMARGS. destruct args_src, args_tgt, sm_arg. ss. clarify.
    des. inv SAFESRC. ss.
    inv TYP.
    exploit StoreArguments.store_arguments_progress; eauto.
    { instantiate (1:=typify_list vs0 (sig_args (fn_sig fd))).
      eapply typify_has_type_list.
      erewrite <- inject_list_length; eauto.
    }
    i. des.
    eexists (AsmC.mkstate (to_pregset (set_regset_undef rs0 (fn_sig fd)))
                          #PC <- fptr0
                          #RA <- Vnullptr
                          #RSP <- (Vptr (Mem.nextblock tgt) Ptrofs.zero true)
                          (Asm.State _ m2)). econs; ss.
    + instantiate (1:=fd).
      {
        (* genv *)
        clear STR. inv SIMSKENV. ss. inv SIMSKE. ss.
        unfold Genv.find_funct in *. des_ifs_safe. inv FPTR.
        unfold Genv.find_funct_ptr in *. des_ifs_safe.
        unfold SkEnv.revive in *. ss.
        apply Genv_map_defs_def in Heq0. des.
        unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
        des_ifs_safe.
        apply Genv.invert_find_symbol in Heq1.
        exploit SIMDEF; eauto. i. des. clarify.
        des_ifs_safe.
        exploit Genv_map_defs_def_inv; try apply DEFTGT.
        i. rewrite H. ss.
        unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
        erewrite Genv.find_invert_symbol. rewrite Heq2; eauto.
        exploit SIMSYMB1; eauto. i. des. eauto.
      }
    + econs; ss; eauto.
      erewrite <- inject_list_length; eauto.
    + econs; ss; eauto. inv STR.
      econs; try eassumption; eauto.
      eapply extcall_arguments_same; eauto. i.
      unfold Pregmap.set, to_mregset, to_pregset, to_preg.
      erewrite to_preg_to_mreg.
      des_ifs; clarify; ss.
      * unfold preg_of in *; des_ifs.
      * unfold preg_of in *; des_ifs.
      * unfold preg_of in *; des_ifs.
      * unfold set_regset_undef. des_ifs; clarify; eauto.
        exfalso. eapply Loc.notin_not_in in n2. eauto.
    + i. unfold Pregmap.set in *. des_ifs; eauto. left.
      unfold set_regset_undef, to_pregset in *. des_ifs; inv PTR.
      esplits; eauto. eapply NNPP. ii.
      exploit LocationsC.Loc_not_in_notin_R; eauto.
  - inv MATCH. ss.

  - (** ******************* at external **********************************)
    inv SIMSKENV. inv CALLSRC. inv MATCH.
    des; ss; clarify. des_ifs.
    set (INJPC:= AGREE PC). rewrite FPTR in *. inv INJPC.
    assert (delta = 0).
    {
      clear EXTERNAL. unfold Genv.find_funct_ptr in *. des_ifs.
      inv SIMSKELINK.
      exploit SIMDEF; eauto.
      i. des. eauto.
    }
    clarify. psimpl. ss.
    exploit extcall_arguments_inject; eauto. i. des.
    cinv (AGREE Asm.RSP); rewrite RSP in *; clarify.
    exploit SimMemInj.free_parallel; eauto. i. des.
    assert (PEQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
                 Ptrofs.unsigned ofs + delta).
    { admit "arithmetic". }
    eexists (Args.mk (Vptr b2 _ true) _ _). exists sm1.
    esplits; eauto; ss; i.
    + econs; eauto.
      * {
          (* genv *)
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. exfalso.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq3.
          inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.

          exploit Genv_map_defs_def_inv; try apply DEFSRC.
          i. revert EXTERNAL. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq4; eauto. i. clarify.
          - exploit SIMSYMB3; eauto. i. des.
            assert (blk_src = blk0).
            { exploit DISJ; eauto. }
            clarify.
        }
      * esplits; eauto.
        unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
        inv SIMSKELINK.
        exploit SIMDEF; try apply Heq1; eauto. i. des. clarify.
        rewrite DEFTGT. eauto.
      * clear - AGREE TPTR RADEF. splits.
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
        { rename TPTR into TPTR0. unfold Tptr in *.
          des_ifs; cinv (AGREE RA); ss; rewrite <- H1 in *; ss. }
      * i.
        rewrite PEQ.
        eapply Z.divide_add_r; eauto.
        inv INJ.
        inv mi_inj. exploit mi_align; eauto.
        eapply Mem.free_range_perm in FREE.
        intros ofs0 RANGE.
        exploit FREE; eauto.
        -- instantiate (1:=ofs0).
           instantiate (1:=Ptrofs.unsigned ofs) in RANGE.
           nia.
        -- i.
           eapply Mem.perm_cur_max.
           eapply Mem.perm_implies; eauto. econs.
      * rewrite PEQ.
        replace (Ptrofs.unsigned ofs + delta + 4 * size_arguments (SkEnv.get_sig skd)) with (Ptrofs.unsigned ofs + 4 * size_arguments (SkEnv.get_sig skd) + delta); eauto.
        nia.
      * ss.
        inv SIMSKELINK.
        unfold Genv.block_is_volatile, Genv.find_var_info in *.
        des_ifs_safe.
        hexploit SIMDEFINV; eauto. i. des. clarify. des_ifs.
    + econs; s; eauto.
      * eapply val_inject_incr; cycle 1; eauto.
        inv MLE. eauto.
      * eapply val_inject_list_incr; cycle 1; eauto.
        inv MLE. eauto.
    + econs; ss; eauto.
      * eapply Mem.free_range_perm in FREE. eauto.
      * eapply Mem.free_range_perm in FREETGT.
        rewrite PEQ.
        replace (Ptrofs.unsigned ofs + delta + 4 * size_arguments (SkEnv.get_sig skd)) with (Ptrofs.unsigned ofs + 4 * size_arguments (SkEnv.get_sig skd) + delta); eauto.
        nia.
      * eapply Mem.valid_block_inject_1; eauto.
      * eapply Mem.valid_block_inject_2; eauto.
      * inv MWF.
        ii. unfold brange in *. ss. des. clarify.
        eapply TGTEXT in PR.
        unfold SimMemInj.tgt_private, loc_out_of_reach in *. ss. des.
        eapply PR; eauto.
        exploit Mem.free_range_perm; try apply FREE; eauto.
        -- instantiate (1:=x1 - delta). nia.
        -- i. eapply Mem.perm_cur_max; eauto.
           eapply Mem.perm_implies; eauto. econs.

  - (** ******************* after external **********************************)
    destruct st_tgt0. destruct st. ss.
    inv MATCH. inv AFTERSRC.
    inv SIMRET.
    cinv (AGREE RSP); rewrite RSRSP in *; ss.
    des.
    unfold Genv.find_funct in *. des_ifs. ss.

    inv MWF. rewrite MEMSRC in *.
    exploit Mem_unfree_parallel_inject; eauto.
    {
      inv MLE0. ss. eapply INCR.
      inv MLE. ss. apply INCR0; eauto.
    }
    { admit "TODO". }
    i. des. rewrite <- MEMSRC in *.

    esplits; ss.
    + instantiate (1:=SimMemInj.mk m1 m2' (SimMemInj.inj sm_ret) _ _ _ _).
      econs; ss; eauto.
      * eapply Mem.unchanged_on_implies.
        { rewrite <- MEMSRC. eapply Mem_unfree_unchanged_on; eauto. }
        ii. unfold brange in *. des. clarify.
        inv MWFAFTR. ss.
        eapply SRCEXT0 in H.
        unfold SimMemInj.src_private, loc_unmapped in *. ss. des.
        inv MLE. inv MLE0.
        eapply INCR in H2.
        eapply INCR0 in H2.
        rewrite H2 in *. clarify.
      * eapply Mem.unchanged_on_implies.
        { rewrite <- MEMTGT in *. eapply Mem_unfree_unchanged_on; eauto. }
        ii. unfold brange in *. des. clarify.
        eapply H6. split; auto.
        admit "arithmetic".
      * econs; ss; eauto. i. des. clarify.
      * ii. exploit Mem_unfree_unchanged_on; try apply UNFREE; eauto. i.
        inv H. rewrite MEMSRC in *.
        eapply unchanged_on_perm; eauto.
      * ii. exploit Mem_unfree_unchanged_on; try apply H; eauto. i.
        inv H.
        eapply unchanged_on_perm; eauto.
        clear - UNFREE1.
        ii. eapply UNFREE1. unfold brange in *. des. split; auto.
        admit "arithmetic".
    + i. ss. splits.
      {
        instantiate (1:=AsmC.mkstate _ (State _ _)). econs; ss.
        - instantiate (1:=SkEnv.get_sig skd). esplits; eauto.
          unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
          cinv (AGREE PC); rewrite Heq in *; clarify.
          inv SIMSKENV. ss. inv SIMSKELINK. exploit SIMDEF; eauto.
          i. des. clarify. des_ifs.
        - eauto.
        - rewrite MEMTGT in *. instantiate (1:=m2').
          rewrite <- UNFREE0. f_equal.
          + admit "arithmetic".
          + admit "arithmetic".
      }

      {
        econs; try assumption.
        - instantiate (1:=SimMemInj.inj sm_ret).
          ii. inv MLE. inv MLE0.
          unfold set_pair, Pregmap.set, loc_external_result, map_rpair.
          des_ifs; ss; eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
          -- eapply Val.loword_inject. eauto.
          -- eapply Val.hiword_inject. eauto.
          -- unfold regset_after_external. des_ifs; ss; eauto.
        - ii. inv MLE. inv MLE0. eauto.
        - eauto.
        - ss.
        - ss.
        - ss.
        - unfold SimMemInj.unlift' in *. ss.
          econs; ss; eauto.
          + inv MWFAFTR.
            rewrite MEMSRC in *.
            unfold SimMemInj.src_private in *. ss.
            etrans; eauto.
            ii; splits; des; eauto.
            clear - UNFREE PR0.
            eapply Mem.valid_block_unchanged_on; eauto.
            eapply Mem_unfree_unchanged_on; eauto.
          + unfold SimMemInj.lift' in *. inv HISTORY. ss.
            rewrite MEMSRC in *.
            (* clear - MLE MLE0 MLE1 MWF MWF0 MWF1 MLEAFTR MWFAFTR UNFREE H CALLSRC CALLTGT H2. *)
            ii. unfold SimMemInj.tgt_private, loc_out_of_reach. ss. splits.
            * ii. des. eapply PR0.
              inv MLE0. inv MWF. ss.
              eapply TGTEXT0 in PR.
              rewrite TGTPARENTEQ in *.
              eapply TGTEXT in PR.
              unfold SimMemInj.tgt_private in *. des.
              unfold loc_out_of_reach in *.
              hexploit PR; eauto.

              ii.
              dup UNFREE. eapply Mem_unfree_unchanged_on in UNFREE. inv UNFREE.

              apply NNPP. ii. exploit unchanged_on_perm; eauto.
              -- instantiate (1:=x1-delta0). instantiate (1:=b1).
                 ii. eapply H4.
                 unfold brange in *. des. clarify. split.
                 ++ inv MLE1. ss. exploit INCR0; eauto. i. clarify.
                 ++ admit "arithmetic".
              -- eapply Mem.valid_block_inject_1; eauto.
              -- i. des. eauto.
            * unfold SimMemInj.valid_blocks, Mem.valid_block.
              erewrite <- Mem_nextblock_unfree; eauto. des.
              inv MLE0. ss. inv TGTUNCHANGED. eapply Plt_Ple_trans; eauto.
              inv MWF. eapply TGTEXT0 in PR. unfold SimMemInj.tgt_private in *. des. eauto.
          + inv MWFAFTR. ss.
            rewrite MEMSRC in *.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
          + inv MWFAFTR. ss.
            etrans; eauto.
            erewrite Mem_nextblock_unfree; eauto. refl.
        - unfold Genv.find_funct. rewrite Heq0. des_ifs. eauto.
        - eauto.
        - eauto.
        - ii. exploit RSPDELTA; eauto. i. des.
          inv MLE1. ss. apply INCR in H. eexists; eauto.
      }

  - (** ******************* final **********************************)

    inv MATCH. inv FINALSRC.

    cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
    exploit Mem.free_parallel_inject; eauto. i. des.

    assert (delta = 0).
    { exploit RSPDELTA; eauto. i. des. clarify. }
    clarify. ss. zsimpl.

    eexists (SimMemInj.mk _ _ _ _ _ _ _). esplits; ss; eauto.
    + cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify. psimpl.
      econs; ss; ii; eauto.
      * specialize (CALLEESAVE _ H2).
        specialize (AGREEINIT (to_preg mr0)).
        specialize (AGREE (to_preg mr0)).
        clear - CALLEESAVE AGREEINIT AGREE WFINITSRC WFINITTGT H2 UNDEF.
        inv WFINITSRC.
        eapply lessdef_commute; eauto.
      * des. esplits; eauto.

        {
          (* genv *)
          unfold Genv.find_funct, Genv.find_funct_ptr in *.
          des_ifs_safe.
          cinv (AGREEINIT PC); rewrite Heq in *; clarify.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq0. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq1.
          inv SIMSKENV. inv SIMSKE. ss.
          exploit SIMDEF; try apply FIND; eauto. i. des. clarify.

          exploit Genv_map_defs_def_inv; try apply DEFTGT.
          i. rewrite H2.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq2; eauto.
          - exploit SIMSYMB2; eauto. i. des. clarify.
        }

      * unfold external_state in *.

        des_ifs_safe. exfalso.
        cinv (AGREE PC); try rewrite Heq in *; clarify; eauto.
        {
          (* genv *)
          des_ifs. unfold Genv.find_funct, Genv.find_funct_ptr in *.
          des_ifs_safe.
          unfold SkEnv.revive in *. ss.
          apply Genv_map_defs_def in Heq3. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq5.
          inv SIMSKENV. inv SIMSKE. ss.
          exploit SIMDEFINV; try apply FIND; eauto. i. des. clarify.
          exploit Genv_map_defs_def_inv; try apply DEFSRC.
          i. revert Heq2. rewrite H2.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq6; eauto. clarify.
          - exploit SIMSYMB3; eauto. i. des.
            rewrite BLKSRC. f_equal.
            exploit DISJ; eauto.
        }
        {
          inv RAPTR. rewrite RSRA in *. eauto.
        }
      * inv WFINITSRC. inv WFINITTGT. inv RAPTR0. inv RAPTR1.
        unfold Val.has_type in TPTR. des_ifs.
        -- cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
        -- ss. des_ifs.
           cinv (AGREEINIT RA); rewrite Heq in *; clarify.
           cinv (AGREE PC); rewrite RSRA in *; clarify.
      * inv WFINITTGT. eauto.
      * cinv (AGREEINIT RSP); rewrite INITRSP in *; clarify.
        cinv (AGREE RSP); rewrite RSRSP in *; clarify.
    + econs; ss.
    + inv MWF. econs; ss.
      * eapply Mem.free_unchanged_on; eauto.
        ii. eapply SRCEXT in H4. unfold SimMemInj.src_private in *. des.
        unfold loc_unmapped in *. congruence.
      * eapply Mem.free_unchanged_on; eauto.
        ii. eapply TGTEXT in H4. unfold SimMemInj.tgt_private in *. des.
        unfold loc_out_of_reach in *. red in H5.
        exploit H4; eauto. eapply Mem.perm_cur_max. eapply Mem.perm_implies.
        -- eapply Mem.free_range_perm; eauto. nia.
        -- econs.
      * econs; ss; eauto. ii. des. clarify.
      * ii. eapply Mem.perm_free_3; eauto.
      * ii. eapply Mem.perm_free_3; eauto.
    + inv MWF.
      econs; ss; unfold SimMemInj.src_private, SimMemInj.tgt_private in *; ss; eauto; i.
      * ii. eapply SRCEXT in PR. des. splits; eauto.
        eapply Mem.valid_block_free_1; eauto.
      * ii. eapply TGTEXT in PR. des.
        unfold loc_out_of_reach in *.
        splits; eauto.
        -- ii. eapply PR; eauto.
           eapply Mem.perm_free_3; eauto.
        -- eapply Mem.valid_block_free_1; eauto.
      * etrans; eauto. erewrite <- Mem.nextblock_free; eauto. refl.
      * etrans; eauto. erewrite <- Mem.nextblock_free; eauto. refl.

  - esplits; ss; i.
    + admit "receptive".
    + exists O.
      { inv STEPSRC. destruct st_src0, st_src1. inv MATCH. ss.
        destruct st0. ss. clarify.

        inv SIMSKENV. inv SIMSKE. ss.

        exploit asm_step_preserve_injection; eauto.

        {
          instantiate (1:=SkEnv.revive (SkEnv.project skenv_link_tgt (Sk.of_program fn_sig asm)) asm).
          (* genv *)
          i. unfold SkEnv.revive in *. exists d_src.
          apply Genv_map_defs_def in FINDSRC. des.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
          des_ifs_safe.
          apply Genv.invert_find_symbol in Heq0.
          exploit SIMDEF; try apply FIND; eauto. i. des. clarify.
          esplits; eauto.
          exploit Genv_map_defs_def_inv; try apply DEFTGT.
          i. rewrite H.
          unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
          erewrite Genv.find_invert_symbol.
          - rewrite Heq1; eauto.
          - exploit SIMSYMB1; eauto. i. des. eauto.
        }

        {
          i. unfold SkEnv.revive in *.
          rewrite Genv_map_defs_symb in FINDSRC.
          exploit SIMSYMB2; try apply FINDSRC; eauto.
        }

        { unfold SkEnv.revive. econs; esplits; ss; i.
          - unfold Genv.public_symbol. ss.
            repeat rewrite Genv_map_defs_symb.
            des_ifs.
            + exfalso. revert Heq0.
              exploit SIMSYMB3; try apply Heq; eauto. i. des.
              congruence.
            + exfalso. revert Heq.
              exploit SIMSYMB2; try apply Heq; eauto. i. des.
              congruence.
          - (* genv *)
            rewrite Genv_map_defs_symb in *.
            exploit SIMSYMB2; eauto. i. des. clarify.
          - des_ifs_safe.
            exploit SIMSYMB2; try apply Heq; eauto. i. des.
            esplits; eauto.
          - unfold Genv.block_is_volatile, Genv.find_var_info.

            destruct (Genv.find_def _ _) eqn:EQTGT.
            + (* genv *)
              apply Genv_map_defs_def in EQTGT. des.
              unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
              des_ifs_safe.
              apply Genv.invert_find_symbol in Heq0.
              exploit SIMDEFINV; eauto. i. des. clarify.
              exploit Genv_map_defs_def_inv; try apply DEFSRC.
              i. rewrite H0.
              unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
              erewrite Genv.find_invert_symbol. rewrite Heq1; eauto.
              exploit SIMSYMB3; eauto. i. des.
              rewrite BLKSRC. f_equal.
              exploit DISJ; eauto.
            + destruct (Genv.find_def (Genv_map_defs (SkEnv.project skenv_link_src (Sk.of_program fn_sig asm)) _)) eqn:EQSRC; auto.
              exfalso.
              apply Genv_map_defs_def in EQSRC. des.
              unfold o_bind, o_bind2, o_join, o_map, curry2, fst in MAP.
              des_ifs_safe.
              apply Genv.invert_find_symbol in Heq0.
              exploit SIMDEF; eauto. i. des. clarify.
              exploit Genv_map_defs_def_inv; try apply DEFTGT.
              i. revert EQTGT. rewrite H0.
              unfold o_bind, o_bind2, o_join, o_map, curry2, fst.
              erewrite Genv.find_invert_symbol.
              * rewrite Heq1; eauto. clarify.
              * exploit SIMSYMB2; eauto. i. des. clarify.
        }

        i. des.
        eexists (AsmC.mkstate init_rs_tgt (Asm.State _ _)).
        eexists (SimMemInj.mk _ _ _ _ _ _ _).
        esplits.
        - left. econs; cycle 1.
          + apply star_refl.
          + symmetry. apply E0_right.
          + econs.
            * admit "determ".
            * econs; ss; eauto.
        - inv MWF. instantiate (5 := j1).
          econs; ss.
          + eapply Mem.unchanged_on_implies. eauto.
            i. eapply SRCEXT; eauto.
          + eapply Mem.unchanged_on_implies; eauto.
            i. eapply TGTEXT; eauto.
          + econs. ii. des.
            exploit SEP; eauto. i. des.
            unfold Mem.valid_block in *. split.
            * eapply Ple_trans; eauto.
              apply Pos.le_nlt; eauto.
            * eapply Ple_trans; eauto.
              apply Pos.le_nlt; eauto.

          + ii. eapply asm_step_max_perm; eauto.
          + ii. eapply asm_step_max_perm; eauto.
        - econs; eauto.
          + eapply agree_incr; eauto.
          + { inv MWF. econs; ss.
              - etrans; eauto.
                unfold SimMemInj.src_private, loc_unmapped in *. ii. des; ss.
                split.
                + destruct (j1 x0) eqn:MAPPED; eauto. destruct p.
                  exfalso. exploit SEP; eauto.
                  i. des. eauto.
                + inv UNCHSRC. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                  xomega.
              - etrans; eauto.
                unfold SimMemInj.tgt_private, loc_out_of_reach in *. ii. des; ss.
                split; i.
                + destruct (SimMemInj.inj sm0 b0) eqn:MAP.
                  * destruct p.
                    dup MAP. apply INCR in MAP. clarify. ii.
                    exploit PR; eauto.
                    eapply asm_step_max_perm in STEP; eauto.
                    eapply Mem.valid_block_inject_1; eauto.
                  * exploit SEP; eauto. i. des. exfalso. eauto.
                + inv UNCHTGT. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                  xomega.
              - etrans; eauto.
                inv UNCHSRC. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                xomega.
              - etrans; eauto.
                inv UNCHTGT. unfold SimMemInj.valid_blocks, Mem.valid_block in *.
                xomega.
            }
          + i. exploit RSPDELTA; eauto. i. des. esplits; eauto.
      }

      Unshelve. all: admit "".

Qed.

(* Lemma asm_inj_drop *)
(*       (asm: Asm.program) *)
(*   : *)
(*     exists mp, *)
(*       (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>) *)
(*       /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>) *)
(*       /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>) *)
(* . *)
(* Proof. *)
(*   admit "this should hold". *)
(* Qed. *)
