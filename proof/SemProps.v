Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Asmregs.
Require Import Smallstep.
Require Import Integers.
Require Import Events.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem.

Set Implicit Arguments.




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
        (MODSEM: Genv.find_funct (ModSem.skenv (Mod.get_modsem md (skenv_fill_internals skenv_link)
                                                               (Mod.data md))) fptr =
                 Some (Internal md_def))
        (INCL: includes skenv_link md.(Mod.sk))
    :
      False
  .
  Proof.
  Admitted.
  (*   set (skenv_fill_internals skenv_link) as skenv_link2 in *. *)
  (*   hexploit (@Mod.get_modsem_projected_sk md skenv_link2); eauto. intro SPEC; des. *)
  (*   remember (ModSem.skenv (Mod.get_modsem md skenv_link2 (Mod.data md))) as skenv_proj eqn:T in *. *)
  (*   assert(WFBIG2: SkEnv.wf skenv_link2). *)
  (*   { eapply skenv_fill_internals_preserves_wf; eauto. } *)
  (*   assert(WFSMALL: skenv_proj.(SkEnv.wf)). *)
  (*   { eapply SkEnv.project_spec_preserves_wf; eauto. } *)
  (*   clarify. des. inv SPEC. *)
  (*   exploit Genv.find_funct_inv; eauto. i; des. clarify. ss. des_ifs. *)
  (*   unfold Genv.find_funct_ptr in *. des_ifs. *)
  (*   inv WFSMALL. exploit DEFSYMB; eauto. intro SYMBSMALL; des. *)
  (*   assert((defs (Mod.get_sk md (Mod.data md))) id). *)
  (*   { apply NNPP. ii. *)
  (*     exploit SYMBDROP; eauto. i; des. clarify. *)
  (*   } *)
  (*   exploit SYMBKEEP; eauto. intro SYMBBIG; des. *)
  (*   rewrite SYMBSMALL in *. symmetry in SYMBBIG. *)
  (*   exploit DEFKEEP; eauto. *)
  (*   { eapply Genv.find_invert_symbol; eauto. } *)
  (*   intro DEFSMALL; des. rewrite Heq in *. symmetry in DEFSMALL. *)
  (*   inv INCL. specialize (INCL0 id (Gfun (Internal md_def))). exploit INCL0; eauto. *)
  (*   { unfold Mod.sk in *. clear - Heq SYMBSMALL. *)
  (*   } *)
  (*   i; des_ifs. *)
  (*   assert(b = b0). *)
  (*   { admit "ez". } *)
  (*   clarify. *)
  (*   inv WFBIG. *)
  (*   exploit SYMBDEF0; eauto. i; des. clarify. *)
  (*   clear - Heq0 Heq1 WFBIG. *)
  (*   clear - Heq0 DEFSMALL. *)
  (*   unfold System.skenv in *. ss. *)
  (*   subst_locals. *)
  (*   apply_all_once Genv_map_defs_def. des. des_ifs_safe. *)
  (*   unfold System.gd_to_skd in *. unfold System.globalenv in *. *)
  (*   apply_all_once Genv_map_defs_def. des. des_ifs_safe. clear_tac. *)
  (*   destruct f; ss; des_ifs; clear_tac. des_ifs; ss. *)
  (*   clear Heq0. *)
  (*   exploit Genv_map_defs_def; eauto. i; des. des_ifs. *)
  (* Qed. *)

  Lemma system_disjoint_old
        skenv_link
        (WFBIG: SkEnv.wf skenv_link)
        sys_def
        fptr
        (SYSTEM: Genv.find_funct (System.skenv skenv_link) fptr = Some (Internal sys_def))
        md md_def
        (MOD: In md p)
        (MODSEM: Genv.find_funct (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) fptr =
                 Some (Internal md_def))
    :
      False
  .
  Proof.
    hexploit (@Mod.get_modsem_projected_sk md skenv_link); eauto. intro SPEC; des.
    remember (ModSem.skenv (Mod.get_modsem md skenv_link (Mod.data md))) as skenv_proj eqn:T in *.
    assert(WFSMALL: skenv_proj.(SkEnv.wf)).
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
    rewrite SYMBSMALL in *. symmetry in SYMBBIG.
    exploit DEFKEEP; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    intro DEFSMALL; des. rewrite Heq in *. symmetry in DEFSMALL.
    clear - Heq0 DEFSMALL.
    unfold System.skenv in *. ss.
    exploit Genv_map_defs_def; eauto. i; des. unfold System.gd_to_skd in MAP. des_ifs.
    clear Heq0.
    exploit Genv_map_defs_def; eauto. i; des. des_ifs.
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
    { eapply Sk.load_skenv_wf. }
    econs; eauto.
    ii; ss.
    inv FIND0; inv FIND1.
    unfold Sk.load_skenv in *. unfold load_genv in *. unfold load_modsems in *. ss.
    rename t into sk_link. rename Heq into SKLINK.
    u in SKLINK.
    hexploit (link_list_linkorder _ SKLINK). intro LORD.
    set (Genv.globalenv sk_link) as skenv_link in *.
    set (skenv_fill_internals skenv_link) as skenv_filled in *.
    assert(WFFILLED: SkEnv.wf skenv_filled).
    { eapply skenv_fill_internals_preserves_wf; eauto. }
    move WFFILLED at top.
    rewrite in_map_iff in *. des_safe. rewrite Forall_forall in *. fold Mod.sk in *.
    u in *.
    destruct MODSEM.
    { clarify. des; ss. exfalso. clarify.

      (* system has internal. skenv_link should have external. *)
      (* WTS: module x should have external *)
      (* ETS: skenv_link includes module x *)

      hexploit LORD; eauto.
      { apply in_map_iff. esplits; eauto. }
      i; des.

      set (ModSem.skenv (Mod.get_modsem x skenv_filled (Mod.data x))) as skenv_small in *.
      assert(WFSMALL: SkEnv.wf skenv_small).
      { admit "add on mod.v". }
      inv WFSMALL.
      unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
      exploit DEFSYMB; eauto. i; des.

      hexploit (@Mod.get_modsem_projected_sk x skenv_filled); eauto. intro SPEC; des.
      inv SPEC.
      exploit H1; eauto.
      { eapply Genv.find_def_symbol; eauto. esplits; eauto. }

      eapply system_disjoint; eauto.

      econs; eauto. u. i.
      des_sumbool. rewrite prog_defmap_spec in *. des.
      exploit H1; try eassumption. i; des.
      rewrite Genv.find_def_symbol in *. des.
      subst_locals.
      des_ifs.
    }
    des; ss.
    { clarify. ss. exfalso. eapply system_disjoint; eauto.

      hexploit LORD; eauto.
      { apply in_map_iff. esplits; eauto. }
      i; des.

      econs; eauto. u. i. des_sumbool. rewrite prog_defmap_spec in *. des.
      exploit H2; try eassumption. i; des.
      rewrite Genv.find_def_symbol in *. des.
      subst_locals.
      des_ifs.
    }

    rename x into md0. rename x0 into md1.
    clarify.
    destruct fptr; ss. des_ifs. unfold Genv.find_funct_ptr in *. des_ifs.
    rename Heq0 into DEF0. rename Heq into DEF1.

    hexploit (@Mod.get_modsem_projected_sk md0 skenv_filled); eauto. intro SPEC0; des.
    hexploit (@Mod.get_modsem_projected_sk md1 skenv_filled); eauto. intro SPEC1; des.
    remember (ModSem.skenv (Mod.get_modsem md0 skenv_filled (Mod.data md0))) as skenv_proj0 eqn:T0 in *.
    remember (ModSem.skenv (Mod.get_modsem md1 skenv_filled (Mod.data md1))) as skenv_proj1 eqn:T1 in *.

    assert(WFSMALL0: skenv_proj0.(SkEnv.wf)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC0; eauto. }
    assert(WFSMALL1: skenv_proj1.(SkEnv.wf)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC1; eauto. }

    bar.
    inv WFSMALL0. exploit DEFSYMB; eauto. i; des.
    inv WFSMALL1. exploit DEFSYMB0; eauto. i; des.
    rename H into SYMB0. rename H1 into SYMB1. rename id0 into id1. rename id into id0.
    move SYMB0 at top. move SYMB1 at top. clear_until_bar.

    inv SPEC0.
    assert(DEFS0: defs (Mod.get_sk md0 (Mod.data md0)) id0).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG0; des. rewrite SYMB0 in *. symmetry in SYMBBIG0.
    exploit DEFKEEP; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    intro DEFBIG0; des. rewrite DEF0 in *. symmetry in DEFBIG0.
    move SYMBBIG0 at top.
    move DEFBIG0 at top.
    move DEFS0 at top.
    clear_until_bar.

    inv SPEC1.
    assert(DEFS1: defs (Mod.get_sk md1 (Mod.data md1)) id1).
    { apply NNPP. ii. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG1; des. rewrite SYMB1 in *. symmetry in SYMBBIG1.
    exploit DEFKEEP; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    intro DEFBIG1; des. rewrite DEF1 in *. symmetry in DEFBIG1.
    move SYMBBIG1 at top.
    move DEFBIG1 at top.
    move DEFS1 at top.
    clear_until_bar.

    assert(id0 = id1).
    { eapply Genv.genv_vars_inj.
      { apply SYMBBIG0. }
      { apply SYMBBIG1. }
    } clarify.
    rename id1 into id.

    clear - DEF0 DEF1 DEFBIG0 DEFS0 DEFS1 SKLINK H0 MODSEM1.
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
    admit "use Mod.get_modsem_projected_sk".
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




(* TODO: Move to EventsC *)
Lemma eventval_valid_le
      se_small ev se_big
      (VALID: eventval_valid se_small ev)
      (LE: se_small.(Senv.public_symbol) <1= se_big.(Senv.public_symbol))
  :
    <<VALID: eventval_valid se_big ev>>
.
Proof.
  u in *.
  unfold eventval_valid in *. des_ifs. erewrite LE; eauto.
Qed.

Lemma match_traces_le
      se_small tr0 tr1 se_big
      (MATCH: match_traces se_small tr0 tr1)
      (LE: se_small.(Senv.public_symbol) <1= se_big.(Senv.public_symbol))
  :
    <<MATCH: match_traces se_big tr0 tr1>>
.
Proof.
  u in *.
  inv MATCH; econs; eauto; eapply eventval_valid_le; eauto.
Qed.

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
    <<STAR: Star (sem prog)
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
    <<PLUS: Plus (sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv PLUS; ii; ss.
  econs; eauto.
  - eapply lift_step; eauto.
  - eapply lift_star; eauto.
Qed.

Lemma lift_dstep
      (ms: ModSem.t) st0 tr st1
      (DSTEP: DStep ms st0 tr st1)
  :
    forall prog tail,
    <<DSTEP: DStep (sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  ii. destruct DSTEP as [DTM STEP].
  econs; eauto; cycle 1.
  - econs; ss; eauto.
  - inv DTM.
    econs; eauto.
    + ii. ss.
      inv H; ss; ModSem.tac.
      inv H0; ss; ModSem.tac.
      clear STEP.
      determ_tac sd_determ_at.
      esplits; auto.
      * eapply match_traces_le; eauto.
        admit "this should hold".
      * ii. clarify. special H0; ss. clarify.
    + ii. ss.
      inv STEP0; ss; ModSem.tac.
      inv FINAL; ss; ModSem.tac.
    + ii. inv H; ss; ModSem.tac.
      exploit sd_traces_at; eauto.
Qed.

Lemma lift_dstar
      (ms: ModSem.t) st0 tr st1
      (DSTAR: DStar ms st0 tr st1)
  :
    forall prog tail,
    <<DSTAR: DStar (sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. ginduction DSTAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_dstep; eauto.
    + eapply IHDSTAR; eauto.
Qed.

Lemma lift_dplus
      (ms: ModSem.t) st0 tr st1
      (DPLUS: DPlus ms st0 tr st1)
  :
    forall prog tail,
    <<DPLUS: DPlus (sem prog)
                   (State ((Frame.mk ms st0) :: tail)) tr
                   (State ((Frame.mk ms st1) :: tail))>>
.
Proof.
  i. inv DPLUS; ii; ss.
  econs; eauto.
  - eapply lift_dstep; eauto.
  - eapply lift_dstar; eauto.
Qed.

Lemma lift_receptive_at
      (ms: ModSem.t) st0
      (RECEP: receptive_at ms st0)
  :
    forall prog tail,
    <<RECEP: receptive_at (sem prog)
                          (State ((Frame.mk ms st0) :: tail))>>
.
Proof.
  ii. inv RECEP. ss.
  econs; eauto; ii.
  - inv H.
    + inv H0. esplits; eauto. econs 1; eauto.
    + ss.
      exploit sr_receptive_at; eauto.
      { eapply match_traces_le; eauto. admit "this should hold". }
      i; des.
      esplits; eauto.
      econs; eauto.
    + inv H0. esplits; eauto. econs 4; eauto.
  - inv H; s; try omega.
    exploit sr_traces_at; eauto.
Qed.

(* Lemma callstate_receptive_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: receptive_at (sem prog) (Callstate args frs)>> *)
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
(*     <<RECEP: determinate_at (sem prog) (Callstate args frs)>> *)
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

