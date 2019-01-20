Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Smallstep.
Require Import Integers.
Require Import EventsC.
Require Import MapsC.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem.

Set Implicit Arguments.



(* TODO: better namespace? *)
Lemma includes_refl
      sk
  :
    <<INCL: SkEnv.includes (Sk.load_skenv sk) sk>>
.
Proof.
  econs; eauto.
  - ii. eapply Genv.find_def_symbol in DEF. des. esplits; eauto. apply linkorder_refl.
  - rewrite Genv.globalenv_public. ss.
Qed.




Lemma link_includes
      p sk_link_src
      (LINK: link_sk p = Some sk_link_src)
      md
      (IN: In md p)
  :
    SkEnv.includes (Sk.load_skenv sk_link_src) md.(Mod.sk)
.
Proof.
  unfold link_sk in *.
  (* TODO: can we remove `_ LINK` ? *)
  (* Arguments link_list_linkorder [_]. *)
  (* Arguments link_list_linkorder: default implicits. *)
  hexploit (link_list_linkorder _ LINK); et. intro LOS; des.
  rewrite Forall_forall in *.
  exploit (LOS md); et.
  { rewrite in_map_iff. esplits; et. }
  intro LO.
  Local Transparent Linker_prog.
  ss. des.
  Local Opaque Linker_prog.
  econs; et.
  - i. exploit LO1; et. i; des. eapply Genv.find_def_symbol in H. des. esplits; et.
  - rewrite Genv.globalenv_public. ss.
Qed.






Section INITDTM.

  Print fsim_properties.
  Print determinate.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable p: program.
  Let sem := Sem.sem p.

  Lemma skenv_fill_internals_preserves_wf
        skenv0 skenv1
        (WF: SkEnv.wf skenv0)
        (FILL: skenv0.(skenv_fill_internals) = skenv1)
    :
      <<WF: SkEnv.wf skenv1>>
  .
  Proof.
    inv WF. unfold skenv_fill_internals.
    econs; ii; ss; eauto.
    - rewrite Genv_map_defs_symb in *. exploit SYMBDEF; eauto. i; des.
      hexploit Genv_map_defs_def_inv; eauto. i; des. esplits; eauto.
      rewrite H0; ss.
    - eapply Genv_map_defs_def in DEF; eauto. des. des_ifs.
      exploit DEFSYMB; eauto.
  Qed.

  Lemma system_disjoint
        skenv_link
        (WFBIG: SkEnv.wf skenv_link)
        sys_def
        fptr
        (SYSTEM: Genv.find_funct (System.skenv skenv_link) fptr = Some (Internal sys_def))
        md md_def
        (MOD: In md p)
        (MODSEM: Genv.find_funct (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) fptr =
                 Some (Internal md_def))
        (INCL: SkEnv.includes skenv_link md.(Mod.sk))
    :
      False
  .
  Proof.
    hexploit (@Mod.get_modsem_projected_sk md skenv_link); eauto. intro SPEC; des.
    remember (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) as skenv_proj eqn:T in *.
    assert(WFSMALL: skenv_proj.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; eauto. }
    clarify. des. inv SPEC.
    exploit Genv.find_funct_inv; eauto. i; des. clarify. ss. des_ifs.
    unfold Genv.find_funct_ptr in *. des_ifs.
    inv WFSMALL. exploit DEFSYMB; eauto. intro SYMBSMALL; des.
    assert((defs (Mod.get_sk md (Mod.data md))) id).
    { apply NNPP. ii.
      exploit SYMBDROP; eauto. i; des. clarify.
    }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des.
    rewrite SYMB in *. symmetry in SYMBBIG.
    exploit DEFKEPT; eauto.
    { apply Genv.find_invert_symbol; eauto. }
    i; des.
    exploit DEFKEEP; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    intro DEFSMALL; des. rewrite Heq in *. symmetry in DEFSMALL0.
    unfold System.skenv in *. ss.
    exploit Genv_map_defs_def; eauto. i; des. des_ifs. inv LO. inv H3.
  Qed.

  (* Lemma link_sk_disjoint_aux *)
  (*       (sks: list Sk.t) *)
  (*       sk0 sk1 *)
  (*       (IN0: In sk0 sks) *)
  (*       (IN1: In sk1 sks) *)
  (*       sk_link *)
  (*       (LINKSK: link_list sks = Some sk_link) *)
  (*       (NEQ: sk0 <> sk1) *)
  (*   : *)
  (*     sk0.(defs) /1\ sk1.(defs) <1= bot1 *)
  (* . *)
  (* Proof. *)
  (*   admit "". *)
  (* Qed. *)

  (* Lemma link_sk_disjoint *)
  (*       md0 md1 *)
  (*       (IN0: In md0 p) *)
  (*       (IN1: In md1 p) *)
  (*       sk_link *)
  (*       (LINKSK: link_sk p = Some sk_link) *)
  (*       (NEQ: md0.(Mod.sk) <> md1.(Mod.sk)) *)
  (*   : *)
  (*     md0.(Mod.sk).(defs) /1\ md1.(Mod.sk).(defs) <1= bot1 *)
  (* . *)
  (* Proof. *)
  (*   unfold link_sk in *. *)
  (*   hexploit link_sk_disjoint_aux; eauto. *)
  (*   { rewrite in_map_iff. esplits; eauto. } *)
  (*   { rewrite in_map_iff. esplits; eauto. } *)
  (* Qed. *)

  Lemma link_sk_disjoint
        md0 md1
        (IN0: In md0 p)
        (IN1: In md1 p)
        sk_link
        (LINKSK: link_sk p = Some sk_link)
        (NEQ: md0 <> md1)
    :
      md0.(Mod.sk).(defs) /1\ md1.(Mod.sk).(defs) <1= bot1
  .
  Proof.
    clear_tac. clear sem.
    unfold link_sk in *.
    unfold Mod.sk in *.
    ginduction p; i; ss.
    eapply link_list_cons_inv in LINKSK. des_safe.
    hexploit (link_list_linkorder _ TL); eauto. intro TLORD; des_safe.
    hexploit (link_linkorder _ _ _ HD); eauto. intro HDORD; des_safe.

    destruct IN0; ss.
    { clarify. des; ss.
Local Transparent Linker_prog.
      simpl in HD. simpl in TL.
      ss.
(* Local Opaque Linker_prog. *)
(*       exploit link_prog_inv; eauto. *)
(*       unfold Linker_prog in *. *)
(*     } *)
  Abort.

  Theorem genv_disjoint
    :
      <<DISJ: sem.(globalenv).(Ge.disjoint)>>
  .
  Proof.
    ss. des_ifs; cycle 1.
    { econs; eauto. ii; ss. inv FIND0. ss. }
    assert(WFBIG: t.(Sk.load_skenv).(SkEnv.wf)).
    { eapply SkEnv.load_skenv_wf. }
    econs; eauto.
    ii; ss.
    inv FIND0; inv FIND1.
    generalize (link_includes p Heq). intro INCLS.
    unfold Sk.load_skenv in *. unfold load_genv in *. unfold load_modsems in *. ss.
    abstr (Genv.globalenv t) skenv_link. rename t into sk_link.  rename Heq into SKLINK.
    rewrite in_map_iff in *.
    u in *.
    destruct MODSEM.
    { clarify. des; ss. exfalso. clarify. eapply system_disjoint; eauto. }
    des; ss.
    { clarify. ss. exfalso. eapply system_disjoint; eauto. }

    rename x into md0. rename x0 into md1.
    clarify.
    destruct fptr; ss. des_ifs. unfold Genv.find_funct_ptr in *. des_ifs.
    rename Heq0 into DEF0. rename Heq into DEF1.

    hexploit (@Mod.get_modsem_projected_sk md0 skenv_link); eauto. intro SPEC0; des.
    hexploit (@Mod.get_modsem_projected_sk md1 skenv_link); eauto. intro SPEC1; des.
    remember (ModSem.skenv (Mod.get_modsem md0 skenv_link (Mod.data md0))) as skenv_proj0 eqn:T0 in *.
    remember (ModSem.skenv (Mod.get_modsem md1 skenv_link (Mod.data md1))) as skenv_proj1 eqn:T1 in *.

    assert(WFSMALL0: skenv_proj0.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC0; eauto. }
    assert(WFSMALL1: skenv_proj1.(SkEnv.wf_proj)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC1; eauto. }

    bar.
    inv WFSMALL0. exploit DEFSYMB; eauto. i; des.
    inv WFSMALL1. exploit DEFSYMB0; eauto. i; des.
    rename SYMB0 into SYMB1. rename SYMB into SYMB0. rename id0 into id1. rename id into id0.
    move SYMB0 at top. move SYMB1 at top. clear_until_bar.

    inv SPEC0.
    assert(DEFS0: defs (Mod.get_sk md0 (Mod.data md0)) id0).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG0; des. rewrite SYMB0 in *. symmetry in SYMBBIG0.
    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    move SYMBBIG0 at top.
    move DEFBIG at top.
    move DEFS0 at top.
    clear_until_bar.

    inv SPEC1.
    assert(DEFS1: defs (Mod.get_sk md1 (Mod.data md1)) id1).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG1; des. rewrite SYMB1 in *. symmetry in SYMBBIG1.
    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    move SYMBBIG1 at top.
    move DEFBIG0 at top.
    move DEFS1 at top.
    clear_until_bar.

    assert(id0 = id1).
    { eapply Genv.genv_vars_inj.
      { apply SYMBBIG0. }
      { apply SYMBBIG1. }
    } clarify.
    rename id1 into id.

    clear - DEF0 DEF1 DEFBIG DEFS0 DEFS1 SKLINK H0 MODSEM1.
    destruct (classic (md0 = md1)); ss.
    { clarify. }
    admit "this should hold. state some lemma like: link_sk_disjoint".
  Qed.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner sem.(globalenv) fptr ms0)
        (FIND1: Ge.find_fptr_owner sem.(globalenv) fptr ms1)
    :
      ms0 = ms1
  .
  Proof.
    inv FIND0; inv FIND1. ss. des_ifs.
    unfold load_genv in *. ss.
    generalize genv_disjoint; i. inv H.
    eapply DISJOINT; eauto.
    - econs; eauto. ss. des_ifs.
    - econs; eauto. ss. des_ifs.
  Qed.

  Theorem initial_state_determ
          st_init0 st_init1
          (INIT0: sem.(Smallstep.initial_state) st_init0)
          (INIT1: sem.(Smallstep.initial_state) st_init1)
    :
      st_init0 = st_init1
  .
  Proof.
    ss.
    inv INIT0; inv INIT1; ss.
    clarify.
  Qed.

End INITDTM.




Lemma lift_step
      (ms: ModSem.t) st0 tr st1
      (STEP: Step ms st0 tr st1)
  :
    forall prog tail,
    <<STEP: Step (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. econs 3; eauto.
Qed.

Lemma lift_star
      (ms: ModSem.t) st0 tr st1
      (STAR: Star ms st0 tr st1)
  :
    forall prog tail,
    <<STAR: Star (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. ginduction STAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_step; eauto.
    + eapply IHSTAR; eauto.
Qed.

Lemma lift_plus
      (ms: ModSem.t) st0 tr st1
      (PLUS: Plus ms st0 tr st1)
  :
    forall prog tail,
    <<PLUS: Plus (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv PLUS; ii; ss.
  econs; eauto.
  - eapply lift_step; eauto.
  - eapply lift_star; eauto.
Qed.

Lemma lift_sdstep
      (ms: ModSem.t) st0 tr st1
      (SDSTEP: SDStep ms st0 tr st1)
  :
    forall prog tail,
    <<SDSTEP: SDStep (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. destruct SDSTEP as [DTM STEP].
  econs; eauto; cycle 1.
  - econs; ss; eauto.
  - inv DTM.
    econs; eauto.
    + ii. ss.
      inv STEP0; ss; ModSem.tac.
      inv STEP1; ss; ModSem.tac.
      clear STEP.
      determ_tac ssd_determ_at.
    + ii. ss.
      inv STEP0; ss; ModSem.tac.
      inv FINAL; ss; ModSem.tac.
    + ii. inv H; ss; ModSem.tac.
      exploit ssd_traces_at; eauto.
Qed.

Lemma lift_sdstar
      (ms: ModSem.t) st0 tr st1
      (SDSTAR: SDStar ms st0 tr st1)
  :
    forall prog tail,
    <<SDSTAR: SDStar (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. ginduction SDSTAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_sdstep; eauto.
    + eapply IHSDSTAR; eauto.
Qed.

Lemma lift_sdplus
      (ms: ModSem.t) st0 tr st1
      (SDPLUS: SDPlus ms st0 tr st1)
  :
    forall prog tail,
    <<SDPLUS: SDPlus (Sem.sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv SDPLUS; ii; ss.
  econs; eauto.
  - eapply lift_sdstep; eauto.
  - eapply lift_sdstar; eauto.
Qed.

Lemma lift_single_events_at
      (ms: ModSem.t) st0
      (SINGLE: single_events_at ms st0)
  :
    forall prog tail,
    <<SINGLE: single_events_at (Sem.sem prog)
                              (State ((Frame.mk ms st0) :: tail))>>
.
Proof.
  ii. ss.
  - inv H; s; try omega.
    exploit SINGLE; eauto.
Qed.

Lemma lift_strict_determinate_at
      (ms: ModSem.t) st0
      (DTM: strict_determinate_at ms st0)
  :
    forall prog tail,
    <<DTM: strict_determinate_at (Sem.sem prog)
                                 (State ((Frame.mk ms st0) :: tail))>>
.
Proof.
  ii. inv DTM. ss.
  econs; eauto; ii.
  - inv STEP0; inv STEP1; ModSem.tac.
    + esplits; et. f_equal. eapply ModSem.at_external_dtm; et.
    + ss. determ_tac ssd_determ_at.
    + ss. esplits; et.
      i. repeat f_equal.
      determ_tac ModSem.final_frame_dtm. eapply ModSem.after_external_dtm; et.
  - ss. inv FINAL. ss. inv STEP; ss; ModSem.tac.
  - inv H; s; try omega.
    exploit ssd_traces_at; eauto.
Qed.

(* Lemma callstate_receptive_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: receptive_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. econs; eauto. *)
(*     + inv H. inv MSFIND. ss. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

(* Lemma callstate_determinate_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: determinate_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. *)
(*       * econs; eauto. *)
(*       * i. repeat f_equal. clear_tac. *)
(*         exploit find_fptr_owner_determ; eauto. *)
(*         { ss. rewrite Heq. eapply MSFIND. } *)
(*         { ss. rewrite Heq. eapply MSFIND0. } *)
(*         i; clarify. *)
(*         determ_tac ModSem.initial_frame_dtm. *)
(*     + exfalso. inv H. inv MSFIND. ss. *)
(*   - ii. ss. des_ifs. *)
(*     + inv FINAL. *)
(*     + inv FINAL. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

Require Import MemoryC.

Let link_load_skenv_wf_sem_aux: forall
    md sk_link
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    m0 m1
  ,
    let skenv_link := (Sk.load_skenv sk_link) in
    forall
      idg
      (IN: In idg sk_link.(prog_defs))
      (LOADM: Genv.alloc_global skenv_link m0 idg = Some m1)
      (WFM: SkEnv.wf_mem skenv_link md m0)
      (* (WFMA: Genv.globals_initialized skenv_link skenv_link m0) *)
    ,
      <<WFM: SkEnv.wf_mem skenv_link md m1>>
             (* /\ <<WFMA: Genv.globals_initialized skenv_link skenv_link m0>> *)
.
Proof.
  i. unfold Genv.alloc_global in *. des_ifs.
  { (* func *)
    econs; et. i. inv WFM. exploit WFPTR; et.
    assert(VALID: Mem.valid_block m0 blk_fr).
    { assert(NEQ: blk_fr <> b).
      { ii. clarify. clear - LOAD LOADM Heq. admit "ez". }
      assert(VAL: Mem.valid_block m1 blk_fr).
      { clear - LOAD. admit "ez". }
      clear - Heq LOADM NEQ VAL. admit "ez".
    }
    erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
    { etrans.
      - eapply Mem.alloc_unchanged_on; et.
      - eapply Mem.drop_perm_unchanged_on; et. ii. admit "ez".
    }
  }
  { (* gvar *)
    bar.
    econs; et. i. inv WFM.
    rename b into blk.
    destruct (eq_block blk_fr blk).
    - clarify. clear WFPTR.
Abort.

Lemma NoDup_norepet
      X (xs: list X)
  :
    NoDup xs <-> list_norepet xs
.
Proof.
  admit "ez - TODO: move to CoqlibC".
Qed.

(* TODO: move to proper place *)
Lemma Genv_bytes_of_init_data_length
      F V (ge: Genv.t F V) a
  :
    Datatypes.length (Genv.bytes_of_init_data ge a) = nat_of_Z (init_data_size a)
.
Proof.
  { clear - a .
    destruct a; ss.
    - rewrite length_list_repeat. rewrite Z2Nat.inj_max. ss. xomega.
    - des_ifs.
  }
Qed.

Let link_load_skenv_wf_sem_one: forall
    md sk_link
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    m0 m1
    id gd
    (* (IN: sk_link.(prog_defmap) ! id = Some gd) *)
    (IN: In (id, gd) sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (LOADM: Genv.alloc_global (Sk.load_skenv sk_link) m0 (id, gd) = Some m1)
    ge0
    (NOTIN: Genv.find_symbol ge0 id = None)
    (WFM: SkEnv.wf_mem ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0)
  ,
    <<WFM: SkEnv.wf_mem (Genv.add_global ge0 (id, gd)) md m1>>
           /\ <<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) (Genv.add_global ge0 (id, gd)) m1>>
                                               /\ <<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>
.
Proof.
  i.
  exploit Genv.alloc_global_initialized; et. intro FREETHM; des.
  esplits; et.
  econs; et. i. ss.
  des_ifs.
  - (* func *)
    assert(VALID: Mem.valid_block m0 blk_fr).
    { assert(NEQ: blk_fr <> b).
      { ii. clarify. clear - LOAD LOADM Heq. admit "ez". }
      assert(VAL: Mem.valid_block m1 blk_fr).
      { clear - LOAD. admit "ez". }
      clear - Heq LOADM NEQ VAL. admit "ez".
    }
    uge. unfold Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs.
    + Local Transparent Linker_prog.
      ss.
      Local Opaque Linker_prog.
      des.
      exploit prog_defmap_norepet; try apply IN; et.
      { apply NoDup_norepet. ss. }
      intro MAP; des.
      exploit prog_defmap_norepet; try apply IN0; et.
      { apply NoDup_norepet. ss. }
      intro MAP0; des.
      exploit LO1; et. i; des. clarify. inv H0.
    + inv WFM.
      assert(VAL: Mem.valid_block m0 blk_fr).
      { assert(NEQ: blk_fr <> b).
        { ii. clarify. clear - LOAD LOADM Heq. admit "ez". }
        assert(VAL: Mem.valid_block m1 blk_fr).
        { clear - LOAD. admit "ez". }
        clear - Heq LOADM NEQ VAL. admit "ez".
      }
      exploit WFPTR; et.
      erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
      { etrans.
        - eapply Mem.alloc_unchanged_on; et.
        - eapply Mem.drop_perm_unchanged_on; et. intros ? ? TTT. clear - Heq TTT. admit "ez".
      }
      i; des.
      esplits; et.
      apply Genv.find_invert_symbol.
      apply Genv.invert_find_symbol in SYMB0.
      uge. ss. rewrite PTree.gsspec. des_ifs.
  - (* gvar *)
    rename b into blk.
    unfold Genv.find_symbol, Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs; cycle 1.
    + assert(blk <> blk_fr).
      { ii; clarify. clear - WFMB Heq SYMB. admit "ez". }
      inv WFM. exploit WFPTR; et.
      assert(VAL: Mem.valid_block m0 blk_fr).
      { admit "ez - similar with above". }
      assert(NVAL: ~ Mem.valid_block m0 blk).
      { clear - Heq. eauto with mem. }
      erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
      { etrans.
        { eapply Mem.alloc_unchanged_on; et. }
        etrans.
        { eapply Genv.store_zeros_unchanged; et. }
        etrans.
        { eapply Genv.store_init_data_list_unchanged; et. }
        { eapply Mem.drop_perm_unchanged_on; et. }
      }
      i; des. esplits; et.
      apply Genv.find_invert_symbol.
      apply Genv.invert_find_symbol in SYMB0; et.
      uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs.
    + r in FREETHM.
      exploit (FREETHM (Genv.genv_next ge0)); et.
      { unfold Genv.find_def, Genv.add_global. s. rewrite PTree.gsspec. des_ifs. }
      clear FREETHM. intro FREETHM; des. ss. des.
      (* assert(gv.(gvar_init) = v.(gvar_init)). *)
      assert(LOA: linkorder gv v /\ gvar_volatile v = false).
      {
        Local Transparent Linker_prog.
        ss.
        Local Opaque Linker_prog.
        des.
        exploit LO1; et.
        { apply prog_defmap_norepet; et. apply NoDup_norepet; et. }
        i; des.
        apply prog_defmap_norepet in IN; cycle 1. { apply NoDup_norepet; et. }
        clarify.
        inv H0. inv H4. ss.
      }
      des.
      exploit FREETHM3; et. intro LOADA; des.
      assert(DAT: exists id_to _ofs, <<IN: In (Init_addrof id_to _ofs) (gvar_init gv)>>
                                    /\ <<SYMB: Genv.find_symbol (Sk.load_skenv sk_link) id_to = Some blk_to>>
            ).
      { assert(EQ: gv.(gvar_init) = v.(gvar_init)).
        { inv LOA. ss. inv H0; ss. }
        rewrite EQ in *.
        abstr (gvar_init v) dts.
        clear - LOAD LOADA FREETHM1.
        abstr (Genv.genv_next ge0) blk. clear_tac.
        abstr ((Sk.load_skenv sk_link)) skenv_link. clear_tac.
        (* destruct (classic (0 < init_data_list_size dts)); cycle 1. *)
        (* { hexploit Mem.loadbytes_range_perm; try apply LOAD; et. intro PERM. *)
        (*   exploit FREETHM1; et. *)
        (*   { r in PERM. eapply PERM; et. instantiate (1:= _ofs_fr). xomega. } *)
        (*   i; des. xomega. *)
        (* } *)
        (* destruct (classic (dts = [])). *)
        (* { clarify. ss. *)
        (*   exfalso. clear - LOAD FREETHM1. hexploit Mem.loadbytes_range_perm; et. intro PERM. *)
        (*   specialize (FREETHM1 _ofs_fr Cur Readable). *)
        (*   exploit FREETHM1; et. *)
        (*   { r in PERM. eapply PERM; et. xomega. } *)
        (*   i; des. xomega. *)
        (* } *)
        destruct (classic (0 <= _ofs_fr < init_data_list_size dts)); cycle 1.
        {
          hexploit Mem.loadbytes_range_perm; try apply LOAD; et. intro PERM.
          exploit FREETHM1; et.
          { r in PERM. eapply PERM; et. instantiate (1:= _ofs_fr). xomega. }
          i; des. xomega.
        }
        rename H into RANGE.
        clear FREETHM1.
        assert(POS: 0 <= 0) by xomega.
        change (init_data_list_size dts) with (0 + init_data_list_size dts) in RANGE.
        revert_until skenv_link.
        generalize 0 at 1 2 3 5 as ofs. i.
        (* generalize 0 at 1 2 4 as ofs. i. *)
        ginduction dts; ii; ss.
        { xomega. }
        try rewrite Z.add_assoc in *.
        assert(LOADB: Mem.loadbytes m1 blk (ofs + init_data_size a) (init_data_list_size dts) =
                      Some (Genv.bytes_of_init_data_list skenv_link dts) /\
                      <<LOADC: Mem.loadbytes m1 blk ofs (init_data_size a) =
                               Some (Genv.bytes_of_init_data skenv_link a)>>).
        { exploit Mem.loadbytes_split; et; try xomega.
          { admit "ez - init_data_size_pos". }
          { admit "ez - init_data_list_size_pos". }
          i; des.
          exploit Mem.loadbytes_length; try apply H; et. intro LEN0.
          exploit Mem.loadbytes_length; try apply H0; et. intro LEN1.
          rewrite H. rewrite H0. clear - LEN0 LEN1 H1.
          generalize (Genv_bytes_of_init_data_length skenv_link a); intro LEN2.
          admit "ez".
        }
        des.
        destruct (classic ((ofs + init_data_size a) <= _ofs_fr)).
        - exploit IHdts; et; try xomega.
          { admit "ez - init_data_size_pos". }
          i; des. esplits; et.
        - clear IHdts LOADB LOADA.
          rename a into aa.
          Local Opaque Z.add.
          destruct aa; ss.
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - encode_int vs fragment of ptr".
          + admit "ez - byte vs fragment of ptr".
          + des_ifs_safe. des_ifs; cycle 1.
            { admit "ez - Undef vs fragment of ptr". }
            esplits; et.
            admit "ez - Vptr blk_to vs Vptr b".
      }
      des.
      bar. inv WF. exploit WFPTR; et. i ;des. esplits; et.
      apply Genv.find_invert_symbol.
      assert(Genv.find_symbol ge0 id_to = Some blk_to).
      { inv WFM. admit "". (* exploit WFPTR0; et. *) }
      uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs.
      admit "Add gvar_volatile condition.
Get gvar_init has Init_addrof
use Sk.wf".
Qed.


Let link_load_skenv_wf_sem_mult: forall
    md sk_link
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    idgs
    (INCL: incl idgs sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (NODUP: NoDup (map fst idgs))
    m0 m1
    (LOADM: Genv.alloc_globals (Sk.load_skenv sk_link) m0 idgs = Some m1)
    ge0
    (* (FRESH: ident -> Prop) *)
    (* (NOTIN: forall id (IN: In id (map fst idgs)), FRESH id) *)
    (* (NOTIN: forall id (IN: FRESH id), Genv.find_symbol ge0 id = None) *)
    (NOTIN: forall id (IN: In id (map fst idgs)), Genv.find_symbol ge0 id = None)
    (WFM: SkEnv.wf_mem ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0)
  ,
    <<WFM: SkEnv.wf_mem (Genv.add_globals ge0 idgs) md m1>>
           /\ <<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link)
                                               (Genv.add_globals ge0 idgs) m1>>
                                               /\ <<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>
.
Proof.
  i.
  generalize dependent ge0.
  generalize dependent m0.
  generalize dependent m1.
  (* generalize dependent FRESH. *)
  induction idgs; ii; ss.
  { clarify. }
  des_ifs.
  destruct a.
  exploit link_load_skenv_wf_sem_one; et.
  { eapply INCL; et. s. et. }
  i; des.
  exploit IHidgs; try apply WFM0; et.
  { ii. eapply INCL; et. s. et. }
  (* { instantiate (1:= fun id => FRESH id \/ i = id). s. et. } *)
  (* { s. i. uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs. *)
  (*   - *)
  (*   - eapply NOTIN0. *)
  (*   s in IN.  des. r in IN. *)
  (*   - des; ss. *)
  { ss. inv NODUP1. ss. }
  { i. uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs.
    - inv NODUP1. ss.
    - apply NOTIN. right. ss. }
  { s. clear - WFMB0 Heq. admit "ez". }
  i; des.
  esplits; et.
Qed.

Lemma link_load_skenv_wf_mem
      p sk_link m_init
      (LINK: link_sk p = Some sk_link)
      (WF: forall md (IN: In md p), Sk.wf md)
      (LOADM: Sk.load_mem sk_link = Some m_init)
  :
    let skenv_link := Sk.load_skenv sk_link in
    <<WFM: forall md (IN: In md p), SkEnv.wf_mem skenv_link md m_init>>
.
Proof.
  econs. i.
  unfold link_sk in *.
  hexploit (link_list_linkorder _ LINK); et. intro LO. des.
  rewrite Forall_forall in *.
  exploit LO; et.
  { rewrite in_map_iff. esplits; et. }
  clear LO.
  intro LO.
  exploit WF; et. clear WF. intro WF; des.
  assert(NODUP: NoDup (prog_defs_names sk_link)).
  { clear - LINK IN WF. destruct p; ss. destruct p; ss.
    - des; ss. clarify. unfold link_list in *. des_ifs. ss. clarify. apply WF.
    - clear IN WF.
      exploit (link_list_cons_inv _ LINK); et.
      { ss. }
      i; des.
      clear - HD.
      Local Transparent Linker_prog.
      ss.
      Local Opaque Linker_prog.
      unfold link_prog in *. des_ifs.
      apply NoDup_norepet.
      unfold prog_defs_names.
      apply PTree.elements_keys_norepet.
  }
  clear LINK IN.


  {
    eapply link_load_skenv_wf_sem_mult; et.
    { refl. }
    { apply WF. }
    { i. uge. ss. rewrite PTree.gempty. ss. }
    { econs; et. i. exfalso. clear - LOAD0. admit "ez". }
    { rr. ii. exfalso. clear - H. admit "ez". }
  }
Qed.

