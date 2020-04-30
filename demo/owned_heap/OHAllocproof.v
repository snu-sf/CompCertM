Require Import CoqlibC MapsC Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import OHAllocSource OHAllocTarget.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift AsmregsC MatchSimModSemExcl.
Require SoundTop.
Require SimMemSV.
Require Import Clightdefs.
Require Import CtypesC.
Require Import Any.

Set Implicit Arguments.



Hint Unfold privmods privmod_others.

Global Opaque string_dec. (**** TODO: Put in SimMem ****)
(**** TODO: update CoqlibC ****)
Ltac econsr :=
  first
    [ econstructor 30
     |econstructor 29
     |econstructor 28
     |econstructor 27
     |econstructor 26
     |econstructor 25
     |econstructor 24
     |econstructor 23
     |econstructor 22
     |econstructor 21
     |econstructor 20
     |econstructor 19
     |econstructor 18
     |econstructor 17
     |econstructor 16
     |econstructor 15
     |econstructor 14
     |econstructor 13
     |econstructor 12
     |econstructor 11
     |econstructor 10
     |econstructor  9
     |econstructor  8
     |econstructor  7
     |econstructor  6
     |econstructor  5
     |econstructor  4
     |econstructor  3
     |econstructor  2
     |econstructor  1].

(** TODO: put it MemoryC **)

Lemma Mem_valid_access_unchanged_on
      m0 m1 chunk b ofs perm
      (VA: Mem.valid_access m0 chunk b ofs perm)
      (UNCH: Mem.unchanged_on (brange b ofs (ofs + size_chunk chunk)) m0 m1)
  :
    (<<VA: Mem.valid_access m1 chunk b ofs perm>>)
.
Proof.
  rr in VA. des.
  rr. esplits; et.
  ii. exploit VA; et. intro T.
  eapply Mem.perm_unchanged_on; et.
Qed.

(*** TODO: move to SimMem ***)
Lemma unch_implies
      mi
  :
    <<IMPL: SimMem.unch None <2= SimMem.unch mi>>
.
Proof.
  ii. inv PR. econs; et.
  { eapply Mem.unchanged_on_implies; et. u. ii. des_ifs. }
  { eapply Mem.unchanged_on_implies; et. u. ii. des_ifs. }
  { ii. destruct mj; try (by ss). exploit LESRC; et. ss. }
  { ii. destruct mj; try (by ss). exploit LETGT; et. ss. }
Qed.



Section SMO.

  Record t: Type :=
    mk {
      sm :> SimMem.t;
      oh_src: Any;
      oh_tgt: Any;
    }
  .

  Inductive wf (smo: t): Prop :=
  | wf_intro
      (MWF: SimMem.wf smo)
      (map: block -> option int)
      (OHSRC: smo.(oh_src) = upcast map)
      (OHTGT: smo.(oh_tgt) = upcast tt)
      (SOME: forall
          k v
          (SOME: map k = Some v)
        ,
          (* (<<SRC: forall o, ZMap.get o (smo.(SimMem.src).(Mem.mem_contents) # k) = Undef>>) /\ *)
          (<<PERMSRC: Mem_range_noperm smo.(SimMem.src) k lo hi>>) /\
          (* (<<SRC: (smo.(SimMem.tgt).(Mem.mem_contents) # k) = (ZMap.init Undef)>>) /\ *)
          (<<PMSRC: brange k lo hi <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_src)>>) /\
          (<<VLSRC: Mem.valid_block smo.(SimMem.src) k>>) /\
            exists k_tgt,
              (<<SIMVAL: smo.(sm).(SimMemSV.inj) k = Some (k_tgt, 0)>>) /\
              (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint64 k_tgt (-8) Writable>>) /\
              (<<LDTGT: Mem.load Mint32 smo.(SimMem.tgt) k_tgt 0%Z = Some (Vint v)>>) /\
              (<<PMTGT: brange k_tgt lo hi <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_tgt)>>)
      )
  .

  Local Obligation Tactic := try (by ii; des; ss).

  Program Instance SimMemOh: (SimMemOh.class) :=
    {|
      SimMemOh.t := t;
      SimMemOh.sm := sm;
      SimMemOh.oh_src := oh_src;
      SimMemOh.oh_tgt := oh_tgt;
      SimMemOh.wf := wf;
      SimMemOh.le := SimMem.le;
      SimMemOh.lepriv := SimMem.lepriv;
      SimMemOh.midx := Some "OHAlloc";
      SimMemOh.set_sm := fun smo sm => mk sm smo.(oh_src) smo.(oh_tgt);
    |}
  .
  Next Obligation.
    econs; et.
    - ii. refl.
    - ii. etrans; et.
  Qed.
  Next Obligation.
    econs; et.
    - ii. refl.
    - ii. etrans; et.
  Qed.
  Next Obligation. i. eapply SimMem.pub_priv; eauto. Qed.
  Next Obligation.
    ii. eapply PR.
  Qed.
  Next Obligation.
    ii. inv WF.
    econs; ss; et.
    ii. exploit SOME; et. i; des. esplits; ss; et.
    - eapply Mem_unchanged_noperm; et.
    - eapply Mem.valid_block_unchanged_on; et.
    - eapply MLEPRIV; ss.
    - eapply Mem_valid_access_unchanged_on; et.
      eapply Mem.unchanged_on_implies; et; ss. ii.
      exploit PMTGT0; et.
      { rr in H. rr. des. esplits; et. u in *. xomega. }
    - eapply Mem.load_unchanged_on; et. ii. ss. eapply PMTGT0; et. rr. unfold lo, hi. esplits; et; xomega.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.





Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (OHAllocSource.module).
Let md_tgt: Mod.t := (OHAllocTarget.module).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link SimMemOh.

Local Existing Instance SimMemOh.

Inductive match_states: nat -> OHAllocSource.state -> Clight.state -> SimMemOh.t -> Prop :=
| match_callstate_new
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_new)))
    (TYF: tyf = (Clight.type_of_function f_new))
    (VSTGT: vs_tgt = [])
  :
    match_states 0%nat
                 (CallstateNew oh m_src)
                 (Callstate fptr_tgt tyf vs_tgt Kstop m_tgt)
                 smo0
| match_callstate_get
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    blk_src
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_get)))
    (TYF: tyf = (Clight.type_of_function f_get))
    (SIMVS: SimMem.sim_val_list smo0 [Vptr blk_src Ptrofs.zero] vs_tgt)
  :
    match_states 0%nat
                 (CallstateGet blk_src oh m_src)
                 (Callstate fptr_tgt tyf vs_tgt Kstop m_tgt)
                 smo0
| match_callstate_set
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    blk_src v_src
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_set)))
    (TYF: tyf = (Clight.type_of_function f_set))
    (SIMVS: SimMem.sim_val_list smo0 [Vptr blk_src Ptrofs.zero ; Vint v_src] vs_tgt)
  :
    match_states 0%nat
                 (CallstateSet blk_src v_src oh m_src)
                 (Callstate fptr_tgt tyf vs_tgt Kstop m_tgt)
                 smo0
| match_returnstate_new
    oh m_src m_tgt blk_src v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (SIMVAL: SimMem.sim_val smo0 (Vptr blk_src Ptrofs.zero) v_tgt)
  :
    match_states 0%nat
                 (ReturnstateNew blk_src oh m_src)
                 (Returnstate v_tgt Kstop m_tgt)
                 smo0
.

Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  eapply match_states_sim with
      (match_states := match_states) (match_states_at := bot4)
      (has_footprint := top3) (mle_excl := fun _ _ => SimMemOh.le) (sidx := unit);
    eauto; ii; ss; folder.
  - eapply lt_wf.
  - eapply SoundTop.sound_state_local_preservation; et.
  - r. etrans; et.
  - des. inv INITTGT. folder. ss.
    inv SAFESRC.
    + destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs; et. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_new)).
      { admit "FINDF". }
      ss. clarify.
      econs; et.
      inv VALS; ss. inv TYP; ss.
    + admit "NOT NOW".
    + admit "NOT NOW".
  - des. rr in SIMARGS; des. inv SAFESRC; inv SIMARGS0; ss; clarify.
    + assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_new))).
      { admit "FINDF". }
      inv VALS.
      esplits; et. econs; et. ss.
    + admit "NOT NOW".
    + admit "NOT NOW".
  - inv MATCH; ss.
  - inv FINALSRC; inv MATCH; ss.
    + esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.
  - left.
    esplits; et.
    { admit "receptive". }
    ii. inv MATCH; inv STEPSRC; ss.
    + exploit SimMemSV.alloc_parallel; try apply ALLOC; try refl.
      { eapply MWF. }
      i; des. clarify.
      exploit (SimMemSV.free_left (SimMemSV.privmod "OHAlloc")); et. i; des. clarify.

      assert(STRTGT0: exists m_tgt0,
                Mem.store Mint64 (SimMemSV.tgt sm2) blk_tgt (-8) (Vptrofs (Ptrofs.repr 4)) = Some m_tgt0).
      { edestruct Mem.valid_access_store; et.
        eapply Mem.valid_access_implies with Freeable; eauto with mem.
        rewrite MTGT.
        eapply Mem.valid_access_alloc_same; et; u; ss.
        exists (- 1). xomega.
      }
      des.

      exploit (SimMemSV.store_right_pm (Some "OHAlloc")); try apply STRTGT0; et.
      { u. ii. specialize (PM x0 x1). des; clarify. ss.
        exploit PM; et.
        { rr. esplits; et. u. xomega. }
        u. intro T. rewrite T. ss.
      }
      i; des. clarify.

      assert(STRTGT1: exists m_tgt1,
                Mem.store Mint32 (SimMemSV.tgt sm3) blk_tgt 0 (Vint (Int.repr 0)) = Some m_tgt1).
      { edestruct Mem.valid_access_store; et.
        eapply Mem.store_valid_access_1; et.
        eapply Mem.valid_access_implies with Freeable; eauto with mem.
        rewrite MTGT.
        eapply Mem.valid_access_alloc_same; et; u; ss.
        apply Z.divide_0_r.
      }
      des.

      exploit (SimMemSV.store_right_pm (Some "OHAlloc")); try apply STRTGT1; et.
      { u. ii. specialize (PM x0 x1). des; clarify. ss.
        exploit PM; et.
        { rr. esplits; et. u. xomega. }
        u. intro T. inv MLE1. exploit PMTGT; et. intro U. rewrite U. ss.
      }
      i; des. clarify.


      eexists _, _, _, (mk sm4 _ _); ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "determinate". }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et.
          (** TODO: we might need better "econs" tactic for multiple choices **)
          - econs; et.
            { repeat econsr; et. folder. admit "FINDF". }
            { econs 2; ss; et. }
          - repeat econs; et.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econsr; ss; et.
          - folder. des_ifs. instantiate (1:= EF_malloc).
            admit "FINDF".
          - rr. econs; ss; et. rewrite <- MTGT. et.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et.
          econs; ss; et.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat (econs; ss; et). }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; ss; et. }
        apply star_refl.
      }
      {
        etrans; et. etrans; et. etrans; et.
      }
      {
        etrans; et. etrans; et. etrans; et.
        { eapply unch_implies; et. }
        { eapply unch_implies; et. }
      }
      {
        econs 4; ss; et.
        - instantiate (1:= upcast tt). econs; ss; et.
          ii. unfold update in *. des_ifs.
          + admit "hard -- new".
          + inv MWF. rewrite OH in *. clarify. exploit SOME0; et. i; des.
            admit "hard -- old".
        - congruence.
        - rewrite MINJ1. rewrite MINJ0. rewrite MINJ. econs; et.
      }
    + admit "NOTNOW".
    + admit "NOTNOW".
  - eexists (mk sm0 _ _); ss. esplits; et. econs; ss; et.
Unshelve.
  all: ss.
  all: admit "NOTNOW".
Qed.

End SIMMODSEM.

