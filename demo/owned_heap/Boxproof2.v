Require Import CoqlibC MapsC Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import BoxSource2 BoxTarget.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift AsmregsC MatchSimModSemExcl.
Require SoundTop.
Require SimMemExtSep.
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

Lemma Mem_range_noperm_split
      m b lo mid hi
      (PERM: Mem_range_noperm m b lo hi)
      (LO: lo <= mid)
      (HI: mid <= hi)
  :
    (<<PERM: Mem_range_noperm m b lo mid>>) /\
    (<<PERM: Mem_range_noperm m b mid hi>>)
.
Proof.
  esplits; et.
  - ii. eapply (PERM ofs); et. xomega.
  - ii. eapply (PERM ofs); et. xomega.
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
      (map: BoxSource2.owned_heap)
      (OHSRC: smo.(oh_src) = upcast map)
      (OHTGT: smo.(oh_tgt) = upcast tt)
      (SOME: forall
          k v is_raw
          (SOME: map k = Some (v, is_raw))
        ,
          (<<PERMSRC: Mem_range_noperm smo.(SimMem.src) k 0 hi>>) /\
          (** TODO: can remove above. See SimMemExtSep.wf' /\ below ("PM") **)
          (<<PM: brange k 0 hi <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_src)>>) /\
          (<<VLSRC: Mem.valid_block smo.(SimMem.src) k>>) /\

          (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint32 k 0 Freeable>>) /\
          (<<LDTGT: Mem.load Mint32 smo.(SimMem.tgt) k 0%Z = Some (Vint v)>>) /\

          (<<NEW:
             is_raw = false ->
             (<<PMNEW: brange k lo 0 <2= privmods (Some "OHAlloc") smo.(sm).(SimMem.ptt_src)>>) /\
             (<<PERMTGT: Mem.valid_access smo.(SimMem.tgt) Mint64 k lo Freeable>>) /\
             (<<LDTGT: Mem.load Mint64 smo.(SimMem.tgt) k lo = Some (Vptrofs (Ptrofs.repr hi))>>)
               >>)
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
    ii. eapply PR.
  Qed.
  Next Obligation.
    ii. inv WF.
    econs; ss; et.
    ii. exploit SOME; et. i; des. esplits; ss; et.
    - eapply Mem_unchanged_noperm; eauto.
    - eapply Mem.valid_block_unchanged_on; et.
    - eapply Mem_valid_access_unchanged_on; et.
      eapply Mem.unchanged_on_implies; et; ss. ii.
      exploit PMTGT; et.
    - eapply Mem.load_unchanged_on; et. ii. ss. eapply PM; et.
    - ii.
      destruct is_raw; ss.
      exploit NEW; eauto. i; des. esplits; eauto.
      + eapply Mem_valid_access_unchanged_on; et.
        eapply Mem.unchanged_on_implies; et; ss. ii.
        exploit PMTGT; et.
      + eapply Mem.load_unchanged_on; et. ii. ss. eapply PMNEW; et.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SMO.





Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (BoxSource2.module).
Let md_tgt: Mod.t := (BoxTarget.module).
Hypothesis (INCL: SkEnv.includes skenv_link (Mod.sk md_src)).
Hypothesis (WF: SkEnv.wf skenv_link).
Let ge := (SkEnv.project skenv_link (Mod.sk md_src)).
Let tge := Build_genv (SkEnv.revive (SkEnv.project skenv_link (Mod.sk md_tgt)) prog) prog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) (SimSymbId.mk md_src md_tgt) sm_link SimMemOh.

Local Existing Instance SimMemOh.

Inductive match_states: nat -> BoxSource2.state -> Clight.state -> SimMemOh.t -> Prop :=
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
| match_callstate_from_raw
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    blk_src
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_from_raw)))
    (TYF: tyf = (Clight.type_of_function f_from_raw))
    (SIMVS: SimMem.sim_val_list smo0 [Vptr blk_src Ptrofs.zero] vs_tgt)
  :
    match_states 0%nat
                 (CallstateFromRaw blk_src oh m_src)
                 (Callstate fptr_tgt tyf vs_tgt Kstop m_tgt)
                 smo0
| match_callstate_into_raw
    oh m_src m_tgt fptr_tgt tyf vs_tgt (smo0: SimMemOh.t)
    blk_src
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (FINDF: Genv.find_funct tge fptr_tgt = Some (Internal (f_into_raw)))
    (TYF: tyf = (Clight.type_of_function f_into_raw))
    (SIMVS: SimMem.sim_val_list smo0 [Vptr blk_src Ptrofs.zero] vs_tgt)
  :
    match_states 1%nat
                 (CallstateIntoRaw blk_src oh m_src)
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
| match_returnstate_from_raw
    oh m_src m_tgt blk_src v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (SIMVAL: SimMem.sim_val smo0 (Vptr blk_src Ptrofs.zero) v_tgt)
  :
    match_states 0%nat
                 (ReturnstateFromRaw blk_src oh m_src)
                 (Returnstate v_tgt Kstop m_tgt)
                 smo0
| match_returnstate_into_raw
    oh m_src m_tgt blk_src v_tgt (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (SIMVAL: SimMem.sim_val smo0 (Vptr blk_src Ptrofs.zero) v_tgt)
  :
    match_states 0%nat
                 (ReturnstateIntoRaw blk_src oh m_src)
                 (Returnstate v_tgt Kstop m_tgt)
                 smo0
| match_into_raw_intermediate
    oh m_src m_tgt blk_src le (smo0: SimMemOh.t)
    (MWF: SimMemOh.wf smo0)
    (OH: smo0.(oh_src) = upcast oh)
    (MSRC: m_src = smo0.(SimMem.src))
    (MTGT: m_tgt = smo0.(SimMem.tgt))
    (LENV: bind_parameter_temps (Clight.fn_params f_into_raw) [Vptr blk_src Ptrofs.zero]
                                (create_undef_temps (fn_temps f_into_raw)) = Some le)
  :
    match_states 0%nat
                 (CallstateIntoRaw blk_src oh m_src)
                 (State f_into_raw (Clight.Sreturn
                                      (Some (Etempvar _key (tptr tvoid)))) Kstop empty_env le m_tgt)
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
      { unfold typify. des_ifs. }
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

    + (* method: from_raw *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 5; et. ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_from_raw)).
      { admit "ez - FINDF". }
      ss. clarify.
      econs; et. ss. inv TYP; ss. inv VALS; ss. inv H3; ss. econs; et. unfold typify. des_ifs.
      { inv H1. ss. }

    + (* method: into_raw *)
      destruct args_src; ss. clarify.
      rr in SIMARGS; des. inv SIMARGS0; ss. clarify. folder.
      esplits; try refl.
      { econs 6; et. ss. }
      assert(T: Genv.find_funct tge fptr_tgt = Some (Internal f_into_raw)).
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

    + (* method: from_raw *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_from_raw))).
      { admit "FINDF". }
      inv VALS.
      esplits; et. econs; et. ss.
      inv H3. econs; et.

    + (* method: into_raw *)
      assert(T: Genv.find_funct (SkEnv.revive ge prog) fptr_tgt = Some (Internal (f_into_raw))).
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

    + (* method: from_raw *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.

    + (* method: into_raw *)
      esplits; et.
      * econs; et.
      * rr. esplits; ss; et.
        { econs; et; ss. }
        instantiate (1:= tt). inv MWF. ss.
      * refl.
      * refl.


  -
    inv MATCH; try (contradict NOTRET; rr; esplits; et; econs; et).
    + (* method: new *)
      left.
      esplits; et.
      { admit "ez - receptive". }
      ii. inv STEPSRC; ss.

      exploit SimMemExtSep.alloc_parallel; try apply ALLOC; try refl.
      { eapply MWF. }
      i; des. clarify.
      exploit (SimMemExtSep.free_left (privmod "OHAlloc")); et.
      i; des. clarify.

      assert(STRTGT0: exists m_tgt0,
                Mem.store Mint64 (SimMemExtSep.tgt sm2) key lo (Vptrofs (Ptrofs.repr 4)) = Some m_tgt0).
      { edestruct Mem.valid_access_store; et.
        eapply Mem.valid_access_implies with Freeable; eauto with mem.
        rewrite MTGT.
        eapply Mem.valid_access_alloc_same; et; u; ss.
        exists (- 1). xomega.
      }
      des.

      exploit (SimMemExtSep.store_right_pm (Some "OHAlloc")); try apply STRTGT0; et.
      { u. ii. des. clarify.
        exploit (PMSRC key x1).
        { u. esplits; eauto with xomega. }
        intro T; des. rr in T. rewrite T. ss.
      }
      i; des. clarify.

      assert(STRTGT1: exists m_tgt1,
                Mem.store Mint32 (SimMemExtSep.tgt sm3) key 0 (Vint v) = Some m_tgt1).
      { edestruct Mem.valid_access_store; et.
        eapply Mem.store_valid_access_1; et.
        eapply Mem.valid_access_implies with Freeable; eauto with mem.
        rewrite MTGT.
        eapply Mem.valid_access_alloc_same; et; u; ss.
        apply Z.divide_0_r.
      }
      des.

      exploit (SimMemExtSep.store_right_pm (Some "OHAlloc")); try apply STRTGT1; et.
      { u. ii. des. clarify.
        exploit (PMSRC key x1).
        { u. esplits; eauto with xomega. }
        intro T; des. rr in T. inv MLE1. exploit (PMLE (Some "OHAlloc")); et. u. des_ifs.
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
        { eapply unch_implies; et. }
        { eapply unch_implies; et. }
      }
      {
        econs 7; ss; et.
        - instantiate (1:= upcast tt). econs; ss; et; cycle 1.
          ii. unfold update in *. des_ifs.
          + (** new **)
            esplits; et.
            * rp; et. rp; et. eapply Mem_range_noperm_split with (lo := lo); et.
              { eapply Mem_free_noperm; et. }
              { unfold lo. xomega. }
              { unfold hi. xomega. }
            * etrans; et.
              bar.
              assert(T: brange k 0 hi <2= brange k lo hi).
              { u. ii. des. clarify. eauto with xomega. }
              etrans; et.
              etrans; et.
              rewrite SimMemExtSep.ons_mem_privmods.
              specialize (PMLE (Some "OHAlloc")). etrans; et.
              specialize (PMLE0 (Some "OHAlloc")). etrans; et.
            * admit "ez - mem".
            * eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
              rewrite MTGT.
              eapply Mem.valid_access_implies with Freeable; [|eauto with mem].
              eapply Mem.valid_access_alloc_same; et; u; try xomega.
              exists 0. xomega.
            * erewrite Mem.load_store_same; et. ss.
            * ii.
              esplits; eauto.
              { etrans; et.
                bar.
                assert(T: brange k lo 0 <2= brange k lo hi).
                { u. ii. des. clarify. eauto with xomega. }
                etrans; et.
                etrans; et.
                rewrite SimMemExtSep.ons_mem_privmods.
                specialize (PMLE (Some "OHAlloc")). etrans; et.
                specialize (PMLE0 (Some "OHAlloc")). etrans; et.
              }
              { eapply Mem.store_valid_access_1; et.
                eapply Mem.store_valid_access_1; et.
                rewrite MTGT.
                eapply Mem.valid_access_implies with Freeable; [|eauto with mem].
                eapply Mem.valid_access_alloc_same; et; u; try xomega.
                exists (- 1)%Z. xomega.
              }
              { erewrite Mem.load_store_other; et; cycle 1.
                { right. ss. left. ss. }
                erewrite Mem.load_store_same; et. ss.
              }
          + (** old **)
            inv MWF. rewrite OH in *. clarify. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC0. rewrite MSRC. clear - n PERMSRC FREE ALLOC.
              admit "ez - mem".
            * clear - PM UNCH UNCH0 PMLE PMLE0.
              etrans; et.
              specialize (PMLE0 (Some "OHAlloc")). ss. etrans; et.
              specialize (PMLE (Some "OHAlloc")). ss. etrans; et.
              bar.
              inv UNCH0. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
              clear_until_bar.
              inv UNCH. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
            * admit "ez - mem".
            * exploit Mem.valid_access_alloc_other; try apply PERMTGT; et. intro T. rewrite <- MTGT in T.
              eapply Mem.store_valid_access_1; et.
              eapply Mem.store_valid_access_1; et.
            * exploit Mem.load_alloc_other; try apply LDTGT; et. intro T.
              erewrite Mem.load_store_other; try apply STRTGT1; et; cycle 1.
              erewrite Mem.load_store_other; try apply STRTGT0; et; cycle 1.
              congruence.
            * ii. destruct is_raw; ss. exploit NEW; eauto. bar. intro T; des.
              esplits; eauto.
              { clear - PMNEW UNCH UNCH0 PMLE PMLE0.
                etrans; et.
                specialize (PMLE0 (Some "OHAlloc")). ss. etrans; et.
                specialize (PMLE (Some "OHAlloc")). ss. etrans; et.
                bar.
                inv UNCH0. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
                clear_until_bar.
                inv UNCH. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
              }
              { exploit Mem.valid_access_alloc_other; try apply PERMTGT0; et. intro T. rewrite <- MTGT in T.
                eapply Mem.store_valid_access_1; et.
                eapply Mem.store_valid_access_1; et.
              }
              { exploit Mem.load_alloc_other; try apply LDTGT0; et. intro T.
                erewrite Mem.load_store_other; try apply STRTGT1; et; cycle 1.
                erewrite Mem.load_store_other; try apply STRTGT0; et; cycle 1.
                congruence.
              }
        - congruence.
      }

    + (* method: get *)
      left.
      esplits; et.
      { admit "ez - receptive". }
      ii. inv STEPSRC; ss.

      inv SIMVS. inv H3. inv H1.
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
        econs 8; ss; et.
        (* - econs; ss; et. *) (**** COQ BUG!!!! ****)
        eapply wf_intro with (map := map); ss; et.
      }

    + (* method: set *)
      left.
      esplits; et.
      { admit "ez - receptive". }
      ii. inv STEPSRC; ss.

      inv SIMVS. inv H3. inv H1. inv H5. inv H2.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      destruct (map blk_src) eqn:T; ss. clarify.
      exploit SOME0; et. i; des. clarify.

      assert(STRTGT0: exists m_tgt0,
                Mem.store Mint32 (SimMem.tgt sm0) blk_src 0 (Vint v_src) = Some m_tgt0).
      { edestruct Mem.valid_access_store with (chunk := Mint32) (ofs := 0%Z); et.
        eauto with mem.
      }
      des.

      exploit (SimMemExtSep.store_right_pm (Some "OHAlloc")); try apply STRTGT0; et.
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
        econs 9; ss; et.
        - instantiate (1:= upcast tt).
          econs; ss; et; cycle 1.
          ii. unfold update in *. des_ifs.
          + (** new **)
            esplits; et.
            * rp; et.
            * etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et.
            * rewrite MSRC. eauto with mem.
            * eapply Mem.store_valid_access_1; et.
            * erewrite Mem.load_store_same; et. ss.
            * ii. destruct is_raw0; ss.
              exploit NEW; et. i; des.
              esplits; et.
              { etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et. }
              { eapply Mem.store_valid_access_1; et. }
              { erewrite Mem.load_store_other; et. right. ss. left; ss. }
          + (** old **)
            inv MWF. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC. eauto with mem.
            * clear - PM0 PMLE.
              etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et.
            * rewrite MSRC. eauto with mem.
            * eauto with mem.
            * erewrite Mem.load_store_other; et.
            * ii. destruct is_raw0; ss.
              exploit NEW0; et. i; des.
              esplits; et.
              { clear - PMNEW PMLE.
                etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et. }
              { eauto with mem. }
              { erewrite Mem.load_store_other; et. }
      }

    + (* method: delete *)
      left.
      esplits; et.
      { admit "ez - receptive". }
      ii. inv STEPSRC; ss.

      inv SIMVS. inv H3. inv H1.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      destruct (map blk_src) eqn:T; ss. clarify.
      exploit SOME0; et. i; des. clarify.
      exploit NEW; eauto. i; des. clarify.

      assert(FREETGT0: exists m_tgt0,
                Mem.free (SimMem.tgt sm0) blk_src lo hi = Some m_tgt0).
      { edestruct Mem.range_perm_free; et. clear - PERMTGT PERMTGT0.
        unfold lo, hi in *.
        ii.
        destruct (classic (ofs < 0)).
        - eapply PERMTGT0. ss. xomega.
        - eapply PERMTGT. ss. xomega.
      }
      des.

      exploit (@SimMemExtSep.free_right_pm (Some "OHAlloc")); try apply FREETGT0; et.
      { rewrite brange_split with (mid := 0); ss. ii. des.
        - specialize (PMNEW x0 x1). ss. erewrite PMNEW; ss.
        - specialize (PM x0 x1). ss. erewrite PM; ss.
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
        econs 10; ss; et.
        - instantiate (1:= upcast tt).
          econs; ss; et; cycle 1.
          ii. unfold update in *. des_ifs.
          + (** old **)
            inv MWF. exploit SOME0; et. i; des.
            esplits; et.
            * rewrite MSRC. eauto with mem.
            * etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et.
            * rewrite MSRC. eauto with mem.
            * eapply Mem.valid_access_free_1; eauto.
            * erewrite Mem.load_free; et.
            * destruct is_raw; ss. exploit NEW0; et. i; des.
              esplits; et.
              { etrans; et. specialize (PMLE (Some "OHAlloc")). etrans; et. }
              { eapply Mem.valid_access_free_1; eauto. }
              { erewrite Mem.load_free; et. }
      }

    + (* method: from_raw *)
      left.
      esplits; et.
      { admit "ez - receptive". }
      ii. inv STEPSRC; ss.

      inv SIMVS. inv H3. inv H1.
      inv MWF.
      rewrite OH in *. clarify. (** TODO: make clarify smarter **)
      destruct (map blk_src) eqn:T; ss.

      exploit (@SimMemExtSep.free_left (privmod "OHAlloc")); try apply FREETGT0; et.
      i; des. clarify.

      eexists _, _, _, (mk sm1 _ _); ss. esplits; et.
      { apply star_refl. }
      { left.
        eapply ModSemProps.spread_dplus; et.
        { admit "ez - determinate". }
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
        psimpl.
        apply star_refl.
      }
      { eapply unch_implies; eauto. }
      {
        econs 11; ss; et; cycle 1.
        - instantiate (1:= upcast tt).
          econs; ss; et; cycle 1.
          ii. unfold update in *. des_ifs.
          + (** new **)
            esplits; et.
            * rp; et. rp; et. eapply Mem_free_noperm; et.
            * etrans; et.
              bar.
              rewrite SimMemExtSep.ons_mem_privmods. ss.
            * admit "ez - mem".
            * rewrite MTGT. eapply Mem.valid_access_extends; try apply MWF0.
              { rr. esplits; eauto with mem. ss. exists 0. xomega. }
            * rewrite MTGT. exploit Mem.load_extends; try apply MWF0; et. intro U; des.
              inv U0. ss.
            * ss.
          + (** old **)
            inv MWF. exploit SOME; et. i; des.
            esplits; et.
            * clear - n PERMSRC FREE.
              admit "ez - mem".
            * etrans; et.
              clear - UNCH.
              bar.
              inv UNCH. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
            * admit "ez - mem".
            * rewrite MTGT. eauto.
            * rewrite MTGT. eauto.
            * ii. destruct is_raw; ss. exploit NEW; eauto. bar. intro U; des.
              esplits; eauto.
              { etrans; et.
                bar.
                inv UNCH. specialize (LESRC (Some "OHAlloc")). ss. etrans; try apply LESRC; ss; et.
              }
              { rewrite MTGT. eauto. }
              { rewrite MTGT. eauto. }
      }

    + (* method: into_raw - 1 *)
      right.
      esplits; et.
      { (* safe *)
        intro S. exploit S; et. { apply star_refl. } i; des; ss.
        rr. inv SIMVS. inv H3. inv H1. esplits; et. repeat (econs; ss; et).
      }
      ii. inv STEPTGT; clarify; ss.
      esplits; et.
      { right. esplits; et. apply star_refl. }
      { refl. }
      { refl. }
      { inv H6. inv H2. inv SIMVS. inv H5. inv H7. econs 13; et. }
    + (* method: into_raw - 2 *)
      right.
      esplits; et.
      { (* safe *)
        intro S. exploit S; et. { apply star_refl. } i; des; ss.
        rr. clarify. esplits; et. repeat (econs; ss; et).
      }
      ii. inv STEPTGT; clarify; ss.

      exploit SAFESRC; et. { apply star_refl. } i; des; ss.
      inv EVSTEP. clear STORE m2.
      inv MWF. ss. rewrite OHSRC in *. clarify.
      exploit SOME0; et. intro T; des.

      exploit (@SimMemExtSep.unfree_left (Some "OHAlloc")); try apply FREETGT0; et.
      { rr in PERMTGT. des. ss. }
      i; des. clarify.

      exploit (@SimMemExtSep.load_right_stored_left sm1); ss; et.
      { rewrite MTGT. eauto. }
      { rr. rr in PERMTGT. des. esplits; et. eapply Mem_unfree_perm; et. }
      i; des.

      eexists _, _, (mk sm2 _ _); ss.
      esplits; et.
      { left. eapply plus_one. econs; et. }
      { etrans; et. eapply unch_implies; et. }
      econs 12; ss; et.
      * econs; ss; et.
        ii. unfold update in *. des_ifs.
        exploit SOME0; eauto. i; des.
        esplits; eauto.
        { assert(Mem_range_noperm (SimMemExtSep.src sm1) k 0 hi).
          {
            clear - PERMSRC0 VLSRC0 UNFREE n.
            eapply Mem_unchanged_noperm; eauto.
            eapply Mem.unchanged_on_implies.
            { apply Mem_unfree_unchanged_on; et. }
            u. ii. des. clarify.
          }
          ii. inv STRSRC. eapply PERM in H0. eapply H; et.
        }
        {
          clear - n PM0 UNCH0 PMEXACT.
          ii.
          bar.
          inv UNCH0. specialize (LESRC (Some "OHAlloc")). ss. exploit LESRC; ss; et.
          clear_until_bar.
          rewrite PMEXACT. exploit PM0; et. i. des_ifs; ss. bsimpl; des; des_sumbool. clarify.
          rr in PR. des. clarify.
        }
        { erewrite Mem_valid_block_unfree in VLSRC0; [|et]. clear - STRSRC VLSRC0. inv STRSRC.
          unfold Mem.valid_block in *. congruence. }
        { congruence. }
        { congruence. }
        { i. exploit NEW0; et. i; des. esplits; et.
          {
            clear - n PMNEW UNCH0 PMEXACT.
            ii.
            bar.
            inv UNCH0. specialize (LESRC (Some "OHAlloc")). ss. exploit LESRC; ss; et.
            clear_until_bar.
            rewrite PMEXACT. exploit PMNEW; et. i. des_ifs; ss. bsimpl; des; des_sumbool. clarify.
            rr in PR. des. clarify.
          }
          { congruence. }
          { congruence. }
        }
      * congruence.
      * clear - H8 H7. inv H7; ss; clarify.
        { unfold Cop.sem_cast in *. des_ifs. }
        { inv H. }

  - eexists (mk sm0 _ _); ss. esplits; et. econs; ss; et.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.



Section SIMMOD.

Definition mp: ModPair.t := SimSymbId.mk_mp (BoxSource2.module) (BoxTarget.module).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. esplits; eauto. eapply sim_modsem; eauto.
Qed.

End SIMMOD.
