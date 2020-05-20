Require Import CoqlibC MapsC Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import BoxSource BoxTarget.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift AsmregsC MatchSimModSemExcl.
Require SoundTop.
Require SimMemSV.
Require Import Clightdefs.
Require Import CtypesC.
Require Import Any.

Set Implicit Arguments.



(***
complexity with injection:
1) inject_incr
2) frozen
3) need to strengthen meminj_no_overlap. (for from_raw. we may have workaround but anyway complex)
***)


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

Lemma Mem_load_valid_block
      chunk m b ofs v
      (LOAD: Mem.load chunk m b ofs = Some v)
  :
    <<VALID: Mem.valid_block m b>>
.
Proof.
  eapply Mem.load_valid_access in LOAD. rr in LOAD. des. specialize (LOAD ofs). exploit LOAD; eauto.
  { generalize (size_chunk_pos chunk); i. xomega. }
  intro T. eapply Mem.perm_valid_block; et.
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
          (<<PMSRC: brange k lo hi <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_src)>>) /\
          (* (<<SRC: (smo.(SimMem.tgt).(Mem.mem_contents) # k) = (ZMap.init Undef)>>) /\ *)
          (<<VLSRC: Mem.valid_block smo.(SimMem.src) k>>) /\
            exists k_tgt,
              (<<SIMVAL: smo.(sm).(SimMemSV.inj) k = Some (k_tgt, 0)>>) /\
              (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint64 k_tgt (-8) Freeable>>) /\
              (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint32 k_tgt 0 Freeable>>) /\
              (<<LDTGT: Mem.load Mint64 smo.(SimMem.tgt) k_tgt lo = Some (Vptrofs (Ptrofs.repr hi))>>) /\
              (<<LDTGT: Mem.load Mint32 smo.(SimMem.tgt) k_tgt 0%Z = Some (Vint v)>>) /\
              (<<PMTGT: brange k_tgt lo hi <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_tgt)>>)
      )
      (UNIQ: forall
          k0 k1 blk_tgt0 blk_tgt1
          (DIFF: k0 <> k1)
          (SOME0: map k0 <> None)
          (SOME1: map k1 <> None)
          (SIMVAL0: smo.(sm).(SimMemSV.inj) k0 = Some (blk_tgt0, 0))
          (SIMVAL1: smo.(sm).(SimMemSV.inj) k1 = Some (blk_tgt1, 0))
        ,
          <<DIFF: blk_tgt0 <> blk_tgt1>>)
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
    econs; [..|M]; Mskip (ss; et).
    (* TODO: COQ BUG !!!!!!!!! update to 8.11 and see if we can remove M/Mskip *)
    all: cycle 1.
    { ii. ss. clarify.
      destruct (map k0) eqn:T0; ss.
      destruct (map k1) eqn:T1; ss.
      destruct (SimMemSV.inj smo0.(sm) k0) eqn:U0; cycle 1.
      { exploit SOME; try apply T0; et. i; des. clarify. }
      destruct (SimMemSV.inj smo0.(sm) k1) eqn:U1; cycle 1.
      { exploit SOME; try apply T1; et. i; des. clarify. }
      inv MLEPRIV. inv FINCR.
      destruct p, p0; ss.
      assert(V0:= U0). assert(V1:= U1).
      eapply INCR in U0. eapply INCR in U1. clarify.
      eapply (UNIQ k0 k1); eauto with congruence.
    }
    ii. exploit SOME; et. i; des. esplits; ss; et.
    - eapply Mem_unchanged_noperm; eauto.
    - eapply Mem.valid_block_unchanged_on; et.
    - eapply MLEPRIV; ss.
    - eapply Mem_valid_access_unchanged_on; et.
      eapply Mem.unchanged_on_implies; et; ss. ii.
      exploit PMTGT0; et.
      { rr in H. rr. des. esplits; et. u in *. xomega. }
    - eapply Mem_valid_access_unchanged_on; et.
      eapply Mem.unchanged_on_implies; et; ss. ii.
      exploit PMTGT0; et.
      { rr in H. rr. des. esplits; et. u in *. xomega. }
    - eapply Mem.load_unchanged_on; et. ii. ss. eapply PMTGT0; et. rr. unfold lo, hi in *.
      esplits; et; xomega.
    - eapply Mem.load_unchanged_on; et. ii. ss. eapply PMTGT0; et. rr. unfold lo, hi. esplits; et; xomega.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.





Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (BoxSource.module).
Let md_tgt: Mod.t := (BoxTarget.module).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link SimMemOh.

Local Existing Instance SimMemOh.

Inductive match_states: nat -> BoxSource.state -> Clight.state -> SimMemOh.t -> Prop :=
| match_callstate_new
    oh m_src m_tgt fptr_tgt tyf vs_tgt v (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_new)))
    (TYF: tyf = (Clight.type_of_function f_new))
    (VSTGT: vs_tgt = [Vint v])
  :
    match_states 0%nat
                 (CallstateNew v oh m_src)
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
    (OHSOME: oh blk_src <> None)
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
| match_callstate_delete
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    blk_src
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_delete)))
    (TYF: tyf = (Clight.type_of_function f_delete))
    (SIMVS: SimMem.sim_val_list smo0 [Vptr blk_src Ptrofs.zero] vs_tgt)
  :
    match_states 0%nat
                 (CallstateDelete blk_src oh m_src)
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
| match_returnstate_get
    oh m_src m_tgt v_src v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (SIMVAL: SimMem.sim_val smo0 (Vint v_src) v_tgt)
  :
    match_states 0%nat
                 (ReturnstateGet v_src oh m_src)
                 (Returnstate v_tgt Kstop m_tgt)
                 smo0
| match_returnstate_set
    oh m_src m_tgt v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
  :
    match_states 0%nat
                 (ReturnstateSet oh m_src)
                 (Returnstate v_tgt Kstop m_tgt)
                 smo0
| match_returnstate_delete
    oh m_src m_tgt v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
  :
    match_states 0%nat
                 (ReturnstateDelete oh m_src)
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

    + (* method: new *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 1; et; ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_new)).
      { admit "ez - FINDF". }
      ss. clarify.
      econs; et.
      inv VALS; ss. inv TYP; ss. inv H3; ss. inv H1; ss. rewrite has_type_list_typify; ss.

    + (* method: get *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 2; et. ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_get)).
      { admit "ez - FINDF". }
      ss. clarify.
      econs; et. ss. inv TYP; ss. inv VALS; ss. inv H3; ss. econs; et. unfold typify. des_ifs.
      { inv H1. ss. }

    + (* method: set *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 3; et. ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_set)).
      { admit "ez - FINDF". }
      ss. clarify.
      econs; et. ss. inv TYP; ss. inv VALS; ss. inv H3; ss. inv H5. inv H2. inv H1. ss. psimpl.
      econs; et.
      { unfold typify. des_ifs. econs; et. psimpl. ss. }
      { econs; et. unfold typify. des_ifs. }

    + (* method: delete *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 4; et. ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_delete)).
      { admit "ez - FINDF". }
      ss. clarify.
      econs; et. ss. inv TYP; ss. inv VALS; ss. inv H3; ss. econs; et. unfold typify. des_ifs.
      { inv H1. ss. }


  - des. rr in SIMARGS; des. inv SAFESRC; inv SIMARGS0; ss; clarify.

    + (* method: new *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_new))).
      { admit "FINDF". }
      inv VALS. inv H3. inv H1.
      esplits; et. econs; et. ss.

    + (* method: get *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_get))).
      { admit "FINDF". }
      inv VALS.
      esplits; et. econs; et. ss.
      inv H3. econs; et.

    + (* method: set *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_set))).
      { admit "FINDF". }
      inv VALS.
      esplits; et. econs; et. ss.
      inv H3. inv H5. inv H2. inv H1. econs; et.

    + (* method: delete *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_delete))).
      { admit "FINDF". }
      inv VALS.
      esplits; et. econs; et. ss.
      inv H3. econs; et.


  - inv MATCH; ss.


  - inv FINALSRC; inv MATCH; ss.

    + (* method: new *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.

    + (* method: get *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.

    + (* method: set *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.

    + (* method: delete *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.


  - left.
    esplits; et.
    { admit "ez - receptive". }
    ii. inv MATCH; inv STEPSRC; ss.

    + (* method: new *)
      exploit SimMemSV.alloc_parallel; try apply ALLOC; try refl.
      { eapply MWF. }
      i; des. clarify.
      exploit (SimMemSV.free_left (SimMemSV.privmod "OHAlloc") (SimMemSV.privmod "OHAlloc")); et.
      i; des. clarify.

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
      { u. ii. specialize (PMTGT x0 x1). des; clarify. ss.
        exploit PMTGT; et.
        { rr. esplits; et. u. xomega. }
        u. intro T. rewrite T. ss.
      }
      i; des. clarify.

      assert(STRTGT1: exists m_tgt1,
                Mem.store Mint32 (SimMemSV.tgt sm3) blk_tgt 0 (Vint v) = Some m_tgt1).
      { edestruct Mem.valid_access_store; et.
        eapply Mem.store_valid_access_1; et.
        eapply Mem.valid_access_implies with Freeable; eauto with mem.
        rewrite MTGT.
        eapply Mem.valid_access_alloc_same; et; u; ss.
        apply Z.divide_0_r.
      }
      des.

      exploit (SimMemSV.store_right_pm (Some "OHAlloc")); try apply STRTGT1; et.
      { u. ii. specialize (PMTGT x0 x1). des; clarify. ss.
        exploit PMTGT; et.
        { rr. esplits; et. u. xomega. }
        u. intro T. inv MLE1. exploit PMTGT0; et. intro U. rewrite U. ss.
      }
      i; des. clarify.


      eexists _, _, _, (mk sm4 _ _); ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "ez - determinate". }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          unfold _v, _key, _t'1. ii; ss; des; clarify.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; ss; et.
          (** TODO: we might need better "econs" tactic for multiple choices **)
          - econs; et.
            { repeat econsr; et. folder. admit "ez - FINDF". }
            { econs 2; ss; et. }
          - repeat econs; et.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econsr; ss; et.
          - folder. des_ifs. instantiate (1:= EF_malloc).
            admit "ez - FINDF".
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
        econs 5; ss; et.
        - instantiate (1:= upcast tt). econs; ss; et; cycle 1.
          { bar.
            (*** TODO: make some good lemma ***)
            assert(MLEALL: SimMemSV.le' sm0.(sm) sm4).
            { repeat (etrans; et). }
            ii. unfold update in *. inv MWF.
            rewrite OHSRC in *. clarify.
            destruct (eq_block key k0).
            - destruct (eq_block key k1); clarify.
              assert(blk_tgt = blk_tgt1) by congruence; clarify.
              assert(NVAL: ~Mem.valid_block sm0.(sm).(SimMemSV.tgt) blk_tgt1).
              { ii. eapply Mem.fresh_block_alloc; et. }
              assert(VAL: Mem.valid_block sm0.(sm).(SimMemSV.tgt) blk_tgt1).
              { destruct (oh k1) eqn:W; ss. exploit SOME; et. i; des.
                assert(k_tgt = blk_tgt1).
                { clarify.
                  clear - SIMVAL1 SIMVAL MLEALL.
                  inv MLEALL. inv FINCR. exploit INCR; et. intro T; des. rewrite T in *. clarify.
                }
                clarify.
                eapply Mem.mi_mappedblocks; try apply MWF4; et.
              }
              ss.
            - destruct (eq_block key k1); clarify.
              {
                assert(blk_tgt = blk_tgt1) by congruence; clarify.
                assert(NVAL: ~Mem.valid_block sm0.(sm).(SimMemSV.tgt) blk_tgt1).
                { ii. eapply Mem.fresh_block_alloc; et. }
                assert(VAL: Mem.valid_block sm0.(sm).(SimMemSV.tgt) blk_tgt1).
                { destruct (oh k0) eqn:W; ss. exploit SOME; et. i; des.
                  assert(k_tgt = blk_tgt1).
                  { clarify.
                    clear - SIMVAL0 SIMVAL MLEALL.
                    inv MLEALL. inv FINCR. exploit INCR; et. intro T; des. rewrite T in *. clarify.
                  }
                  clarify.
                  eapply Mem.mi_mappedblocks; try apply MWF4; et.
                }
                ss.
              }
              {
                assert(LEMMA: forall k (SOME: oh k <> None), k <> key).
                {
                  clear - SOME ALLOC.
                  i. destruct(oh k) eqn:T; ss. clear_tac.
                  exploit SOME; et. i; des.
                  ii. hexploit Mem.fresh_block_alloc; try apply ALLOC; et. intro U. clarify.
                }
                destruct (oh k0) eqn:W0; ss.
                destruct (oh k1) eqn:W1; ss.
                hexploit (LEMMA k0); eauto with congruence. intro X0.
                hexploit (LEMMA k1); eauto with congruence. intro X1.
                exploit (SOME k0); et. i; des.
                assert(k_tgt = blk_tgt1).
                { clear - MLEALL SIMVAL SIMVAL0.
                  inv MLEALL. inv FINCR. exploit INCR; et. intro T; des. rewrite T in *. clarify.
                } clarify.
                exploit (SOME k1); et. i; des.
                assert(k_tgt = blk_tgt1).
                { clear - MLEALL SIMVAL1 SIMVAL2.
                  inv MLEALL. inv FINCR. exploit INCR; et. intro T; des. rewrite T in *. clarify.
                } clarify.
                hexploit (UNIQ k0 k1); eauto with congruence.
              }
          }
          ii. unfold update in *. des_ifs.
          + (** new **)
            esplits; et.
            * rp; et. rp; et. eapply Mem_free_noperm; et.
            * etrans; et. u. ii.
              bar.
              inv MLE2. erewrite (PMSRC0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE1. erewrite (PMSRC0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
            * admit "ez - mem".
            * rp; et. congruence.
            * eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
              rewrite MTGT.
              eapply Mem.valid_access_implies with Freeable; [|eauto with mem].
              eapply Mem.valid_access_alloc_same; et; u; try xomega.
              exists (- 1). xomega.
            * eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
              rewrite MTGT.
              eapply Mem.valid_access_implies with Freeable; [|eauto with mem].
              eapply Mem.valid_access_alloc_same; et; u; try xomega.
              eapply Z.divide_0_r.
            * erewrite Mem.load_store_other; et; cycle 1.
              { right. ss. left. ss. }
              erewrite Mem.load_store_same; et. ss.
            * erewrite Mem.load_store_same; et. ss.
            * etrans; et. u. ii.
              bar.
              inv MLE2. erewrite (PMTGT0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE1. erewrite (PMTGT0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
          + (** old **)
            inv MWF. rewrite OH in *. clarify. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC0. rewrite MSRC. clear - n PERMSRC FREE ALLOC.
              admit "ez - mem".
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE2 MLE1 MLE0 MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE2. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE1. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE0. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
            * admit "ez - mem".
            * rewrite MINJ1. rewrite MINJ0. rewrite MINJ. rewrite INJ0; et.
            * exploit Mem.valid_access_alloc_other; try apply PERMTGT; et. intro T. rewrite <- MTGT in T.
              eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
            * exploit Mem.valid_access_alloc_other; try apply PERMTGT0; et. intro T. rewrite <- MTGT in T.
              eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
            * exploit Mem.load_alloc_other; try apply LDTGT; et. intro T.
              erewrite Mem.load_store_other; try apply STRTGT1; et; cycle 1.
              { left. admit "ez - mem". }
              erewrite Mem.load_store_other; try apply STRTGT0; et; cycle 1.
              { left. admit "ez - mem". }
              congruence.
            * exploit Mem.load_alloc_other; try apply LDTGT0; et. intro T.
              erewrite Mem.load_store_other; try apply STRTGT1; et; cycle 1.
              { left. admit "ez - mem". }
              erewrite Mem.load_store_other; try apply STRTGT0; et; cycle 1.
              { left. admit "ez - mem". }
              congruence.
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE2 MLE1 MLE0 MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE2. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE1. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE0. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              inv MLE. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
        - congruence.
        - rewrite MINJ1. rewrite MINJ0. rewrite MINJ. econs; et.
      }

    + (* method: get *)
      inv SIMVS. inv H3. inv H1. rename H2 into INJ.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      exploit SOME; et. i; des. clarify.

      eexists _, _, _, sm0; ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "ez - determinate". }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; et.
          - ss.
        }
        apply star_refl.
      }
      {
        refl.
      }
      {
        refl.
      }
      {
        econs 6; ss; et.
        (* - econs; ss; et. *) (**** COQ BUG!!!! ****)
        eapply wf_intro with (map := map); ss; et.
      }

    + (* method: set *)
      inv SIMVS. inv H3. inv H1. rename H3 into INJ. inv H5. inv H2.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      destruct (map blk_src) eqn:T; ss.
      exploit SOME0; et. i; des. clarify.

      assert(STRTGT0: exists m_tgt0,
                Mem.store Mint32 (SimMem.tgt sm0) b2 0 (Vint v_src) = Some m_tgt0).
      { edestruct Mem.valid_access_store with (chunk := Mint32) (ofs := 0%Z); et.
        eauto with mem.
      }
      des.

      exploit (SimMemSV.store_right_pm (Some "OHAlloc")); try apply STRTGT0; et.
      { u. ii. specialize (PMTGT x0 x1). des; clarify. ss.
        exploit PMTGT; et.
        { rr. esplits; et. u. xomega. }
      }
      i; des. clarify.


      eexists _, _, _, (mk sm1 _ _); ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "ez - determinate". }
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          - unfold _key, _val. econs; ss; et.
            + apply and_not_or. esplits; et. ii; ss.
            + econs; et. econs; et.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; ss; et. }
        apply star_refl.
      }
      {
        econs 7; ss; et.
        - instantiate (1:= upcast tt).
          econs; ss; et; cycle 1.
          { bar.
            (*** TODO: make some good lemma ***)
            assert(MLEALL: SimMemSV.le' sm0.(sm) sm1).
            { ss. }
            ii. rewrite MINJ in *.
            unfold update in *. inv MWF.
            destruct (eq_block blk_src k0).
            - destruct (eq_block blk_src k1); clarify.
              destruct (map k1) eqn:W; ss.
              exploit (UNIQ k0 k1); eauto with congruence.
            - destruct (eq_block blk_src k1); clarify.
              + destruct (map k1) eqn:W; ss.
                exploit (UNIQ k0 k1); eauto with congruence.
              + exploit (UNIQ k0 k1); eauto with congruence.
          }
          ii. unfold update in *. des_ifs.
          + (** new **)
            esplits; et.
            * rp; et.
            * etrans; et. u. ii.
              bar.
              inv MLE. erewrite (PMSRC0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              unfold SimMemSV.ownership_to_ownership in PR. des_ifs. des_sumbool. clarify.
            * rewrite MSRC. eauto with mem.
            * rp; et. congruence.
            * eapply Mem.store_valid_access_1; et.
            * eapply Mem.store_valid_access_1; et.
            * erewrite Mem.load_store_other; et. right. ss. left; ss.
            * erewrite Mem.load_store_same; et. ss.
            * etrans; et. u. ii.
              bar.
              inv MLE. erewrite (PMTGT0 "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              unfold SimMemSV.ownership_to_ownership in PR. des_ifs. des_sumbool. clarify.
          + (** old **)
            inv MWF. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC. eauto with mem.
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
            * rewrite MSRC. eauto with mem.
            * rewrite MINJ. eauto.
            * eauto with mem.
            * eauto with mem.
            * erewrite Mem.load_store_other; et. left. ii; clarify.
              exploit (UNIQ blk_src k); ss; eauto with congruence.
            * erewrite Mem.load_store_other; et. left. ii; clarify.
              exploit (UNIQ blk_src k); ss; eauto with congruence.
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
      }

    + (* method: delete *)
      inv SIMVS. inv H3. inv H1. rename H2 into INJ.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      destruct (map blk_src) eqn:T; ss.
      exploit SOME0; et. i; des. clarify.

      assert(FREETGT0: exists m_tgt0,
                Mem.free (SimMem.tgt sm0) b2 lo hi = Some m_tgt0).
      { edestruct Mem.range_perm_free; et. clear - PERMTGT PERMTGT0.
        unfold lo, hi in *.
        ii.
        destruct (classic (ofs < 0)).
        - eapply PERMTGT. ss. xomega.
        - eapply PERMTGT0. ss. xomega.
      }
      des.

      exploit (@SimMemSV.free_right_pm "OHAlloc"); try apply FREETGT0; et.
      { u. ii. specialize (PMTGT x0 x1). des; clarify. ss.
        exploit PMTGT; et.
        { unfold SimMemSV.ownership_to_ownership.
          des_ifs. ii. des_sumbool. clarify. }
      }
      i; des. clarify.


      eexists _, _, _, (mk sm1 _ _); ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "ez - determinate". }
        assert(FINDF0: exists loc,
                  (<<SYMB: Genv.find_symbol (SkEnv.revive ge prog) _free = Some loc>>) /\
                  (<<DEF: Genv.find_funct_ptr (SkEnv.revive ge prog) loc =
                          Some (External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)>>)).
        { admit "FINDF". }
        des.
        eapply plus_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          econs; ss; eauto; try (by repeat (econs; ss; eauto)).
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { econs; eauto.
          - econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          - econs; ss; eauto; try (by repeat (econs; ss; eauto)).
          - repeat (econs; ss; eauto).
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econsr; ss; et.
          rr. econs; eauto. ss.
        }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; ss; et. }
        eapply star_left with (t1 := E0) (t2 := E0); ss.
        { repeat econs; ss; et. }
        apply star_refl.
      }
      {
        econs 8; ss; et.
        - instantiate (1:= upcast tt).
          econs; ss; et; cycle 1.
          { bar.
            (*** TODO: make some good lemma ***)
            assert(MLEALL: SimMemSV.le' sm0.(sm) sm1).
            { ss. }
            ii. rewrite MINJ in *.
            unfold update in *. inv MWF. des_ifs. exploit (UNIQ k0 k1); et.
          }
          ii. unfold update in *. des_ifs.
          + (** old **)
            inv MWF. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC. eauto with mem.
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE. erewrite (PMSRC "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
            * rewrite MSRC. eauto with mem.
            * rewrite MINJ. eauto.
            * destruct (eq_block b2 k_tgt).
              { exploit (UNIQ blk_src k); eauto with congruence. ii; ss. }
              eapply Mem.valid_access_free_1; eauto.
            * destruct (eq_block b2 k_tgt).
              { exploit (UNIQ blk_src k); eauto with congruence. ii; ss. }
              eapply Mem.valid_access_free_1; eauto.
            * erewrite Mem.load_free; et. left. ii; clarify.
              exploit (UNIQ blk_src k); ss; eauto with congruence.
            * erewrite Mem.load_free; et. left. ii; clarify.
              exploit (UNIQ blk_src k); ss; eauto with congruence.
            * etrans; et. ii. ss. des_ifs_safe. des_sumbool. clarify. clear - Heq MLE.
              unfold SimMemSV.ownership_to_ownership in *. des_ifs_safe.
              bar.
              inv MLE. erewrite (PMTGT "OHAlloc"). { des_sumbool; ss. } u. clear_until_bar.
              ss.
      }


  - eexists (mk sm0 _ _); ss. esplits; et. econs; ss; et.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.



Section SIMMOD.

Definition mp: ModPair.t := SimSymbId.mk_mp (BoxSource.module) (BoxTarget.module).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. inv SIMSKENV. esplits; eauto. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
