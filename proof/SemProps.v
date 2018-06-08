Require Import CoqlibC.
Require Import Simulation.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Asmregs.
Require Import Smallstep.
Require Import Integers.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem.

Set Implicit Arguments.




Section INITDTM.

  Print fsim_properties.
  Print determinate.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable p: program.
  Let sem := Sem.semantics p.

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
    :
      False
  .
  Proof.
    erewrite <- Mod.get_modsem_projected_sk in *.
    hexploit (SkEnv.project_impl_spec skenv_link (defs (Mod.get_sk md (Mod.data md)))); eauto. intro SPEC.
    remember (SkEnv.project skenv_link (defs (Mod.get_sk md (Mod.data md)))) as skenv_proj eqn:T in *.
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
    exploit Genv_map_defs_spec; eauto. i; des. unfold System.gd_to_skd in MAP. des_ifs.
    clear Heq0.
    exploit Genv_map_defs_spec; eauto. i; des. des_ifs.
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
    rewrite <- Mod.get_modsem_projected_sk in *.
    hexploit (SkEnv.project_impl_spec skenv_link (defs (Mod.get_sk md0 (Mod.data md0)))); eauto. intro SPEC0.
    hexploit (SkEnv.project_impl_spec skenv_link (defs (Mod.get_sk md1 (Mod.data md1)))); eauto. intro SPEC1.
    des.

    assert(WFSMALL0: (SkEnv.project skenv_link (defs (Mod.get_sk md0 (Mod.data md0)))).(SkEnv.wf)).
    { eapply SkEnv.project_spec_preserves_wf; try apply SPEC0; eauto. }
    assert(WFSMALL1: (SkEnv.project skenv_link (defs (Mod.get_sk md1 (Mod.data md1)))).(SkEnv.wf)).
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
    exploit find_fptr_owner_determ; ss; des_ifs.
    { eapply MSFIND. }
    { eapply MSFIND0. }
    i; des. clarify.
    determ_tac ModSem.initial_frame_dtm.
  Qed.

End INITDTM.




