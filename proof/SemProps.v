Require Import CoqlibC.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.
Require Import Smallstep.
Require Import Simulation.
Require Import Integers.
Require Import EventsC.
Require Import MapsC.
Require Import BehaviorsC.

Require Import Skeleton ModSem Mod Sem.
Require Import SimSymb SimMem.

Require Import ModSemProps.
Require Import Program.
Require Import Any.

Set Implicit Arguments.






(* TODO: better namespace? *)
Lemma includes_refl
      sk:
    <<INCL: SkEnv.includes (Sk.load_skenv sk) sk>>.
Proof.
  econs; eauto.
  - ii. eapply Genv.find_def_symbol in DEF. des. esplits; eauto. apply linkorder_refl.
  - rewrite Genv.globalenv_public. ss.
Qed.




Lemma link_includes
      p sk_link_src
      (LINK: link_sk p = Some sk_link_src)
      md
      (IN: In md p):
    SkEnv.includes (Sk.load_skenv sk_link_src) (Mod.sk md).
Proof.
  unfold link_sk in *.
  (* TODO: can we remove `_ LINK` ? *)
  (* Arguments link_list_linkorder [_]. *)
  (* Arguments link_list_linkorder: default implicits. *)
  hexploit (link_list_linkorder _ LINK); et. intro LOS; des.
  rewrite Forall_forall in *. exploit (LOS md); et.
  { rewrite in_map_iff. esplits; et. }
  intro LO.
  Local Transparent Linker_prog. ss. des. Local Opaque Linker_prog.
  econs; et.
  - i. exploit LO1; et. i; des. eapply Genv.find_def_symbol in H. des. esplits; et.
  - rewrite Genv.globalenv_public. ss.
Qed.

(* Remove redundancy with CompCert/ValueAnalysis.v && UnreachC.v *)
Definition definitive_initializer (init: list init_data) : bool :=
  match init with
  | nil => false
  | Init_space _ :: nil => false
  | _ => true
  end.

Local Transparent Linker_def Linker_vardef Linker_varinit Linker_unit.
Lemma definitive_initializer_is_definitive_left
      gv1 gv0
      (sk0 sk1: Sk.t) id_fr
      (LINK: link_prog_merge (prog_defmap sk0) ! id_fr (prog_defmap sk1) ! id_fr = Some (Gvar gv1))
      (IN: (prog_defmap sk0) ! id_fr = Some (Gvar gv0))
      (DEF: definitive_initializer (gvar_init gv0)):
    gv0 = gv1.
Proof.
  unfold link_prog_merge in *. des_ifs_safe. ss. des_ifs_safe.
  unfold link_vardef in *. des_ifs_safe. ss. destruct gv0; ss. unfold link_varinit in *. des_ifs_safe.
  bsimpl. des. rewrite eqb_true_iff in *. f_equal.
  { destruct gvar_info; ss. }
  des_ifs.
Qed.

Lemma definitive_initializer_is_definitive_right
      gv1 gv0
      (sk0 sk1: Sk.t) id_fr
      (LINK: link_prog_merge (prog_defmap sk0) ! id_fr (prog_defmap sk1) ! id_fr = Some (Gvar gv1))
      (IN: (prog_defmap sk1) ! id_fr = Some (Gvar gv0))
      (DEF: definitive_initializer (gvar_init gv0)):
    gv0 = gv1.
Proof.
  unfold link_prog_merge in *. des_ifs_safe. ss. unfold link_def in *. des_ifs. ss.
  unfold link_vardef in *. des_ifs_safe. ss. clarify. destruct gv0; ss. unfold link_varinit in *. des_ifs_safe.
  bsimpl. des. rewrite eqb_true_iff in *. f_equal; ss.
  { destruct gvar_info; ss. }
  des_ifs.
Qed.

Lemma definitive_initializer_split
      (g0 g1 g: globvar unit)
      (DEF: definitive_initializer g.(gvar_init))
      (LINK: link g0 g1 = Some g):
    <<DEF: definitive_initializer g0.(gvar_init) \/ definitive_initializer g1.(gvar_init)>>.
Proof.
  ss. unfold link_vardef in *. des_ifs. ss. clarify. unfold link_varinit in *. des_ifs; ss; et.
Qed.
Local Opaque Linker_def Linker_vardef Linker_varinit Linker_unit.

Theorem link_preserves_wf_sk
        sk0 sk1 sk_link
        (WFSK0: Sk.wf sk0)
        (WFSK1: Sk.wf sk1)
        (LINK: link sk0 sk1 = Some sk_link):
    <<WF: Sk.wf sk_link>>.
Proof.
  Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
  hexploit (link_prog_inv _ _ _ LINK); et. intro INV; des. clarify. clear LINK. econs; et; ss.
  - unfold prog_defs_names. ss. eapply NoDup_norepet. eapply PTree.elements_keys_norepet; et.
  - i. unfold prog_defs_names. ss. apply PTree.elements_complete in IN.
    rewrite PTree.gcombine in *; ss. apply in_map_iff.
    assert((exists x, (prog_defmap sk0) ! id_to = Some x)
           \/ (exists x, (prog_defmap sk1) ! id_to = Some x)); cycle 1.
    { des.
      - destruct ((prog_defmap sk1) ! id_to) eqn:T.
        + exploit (INV0 id_to); eauto. intro X; des.
          eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
        + eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
      - destruct ((prog_defmap sk0) ! id_to) eqn:T.
        + exploit (INV0 id_to); eauto. intro X; des.
          eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
        + eexists (_, _). ss. esplits; eauto. apply PTree.elements_correct. rewrite PTree.gcombine; ss.
          unfold link_prog_merge. rewrite H. rewrite T. et.
    }
    assert((exists gv, (prog_defmap sk0) ! id_fr = Some (Gvar gv) /\ definitive_initializer gv.(gvar_init))
           \/ (exists gv, (prog_defmap sk1) ! id_fr = Some (Gvar gv) /\ definitive_initializer gv.(gvar_init))).
    { unfold link_prog_merge in *. des_ifs.
      - exploit (INV0 id_fr); et. intro X; des.
        Local Transparent Linker_def. ss. Local Opaque Linker_def.
        destruct g, g0; ss; des_ifs.
        exploit (@definitive_initializer_split v v0 gv); et.
        { unfold definitive_initializer. des_ifs; ss; des; clarify. }
        i; des; et.
      - left. esplits; et. unfold definitive_initializer. des_ifs; ss; des; clarify.
      - right. esplits; et. unfold definitive_initializer. des_ifs; ss; des; clarify.
    }
    des.
    + assert(gv0 = gv).
      { eapply (definitive_initializer_is_definitive_left); eauto. }
      clarify. left. inv WFSK0. exploit (WFPTR id_fr); et.
      { apply in_prog_defmap; et. }
      intro X; des. eapply prog_defmap_dom; et.
    + assert(gv0 = gv).
      { eapply (definitive_initializer_is_definitive_right); eauto. }
      clarify. right. inv WFSK1. exploit (WFPTR id_fr); et.
      { apply in_prog_defmap; et. }
      intro X; des. eapply prog_defmap_dom; et.
  - ii.
    assert(exists gd, link_prog_merge (prog_defmap sk0) ! a (prog_defmap sk1) ! a = Some gd).
    { unfold link_prog_merge. des_ifs; eauto.
      - exploit INV0; eauto. i; des. esplits; et.
      - rewrite in_app_iff in *. des.
        + inv WFSK0. exploit PUBINCL; eauto. intro T. exploit prog_defmap_dom; et. i; des. clarify.
        + inv WFSK1. exploit PUBINCL; eauto. intro T. exploit prog_defmap_dom; et.
    }
    unfold prog_defs_names. ss. rewrite in_map_iff. des. eexists (_, _). s. esplits; eauto.
    eapply PTree.elements_correct. rewrite PTree.gcombine; ss.
    unfold link_prog_merge. des_ifs; eauto.
  - i. eapply PTree.elements_complete in IN.
    rewrite PTree.gcombine in IN; ss.
    unfold link_prog_merge in IN. des_ifs.
    + Local Transparent Linker_def. ss. unfold link_def in IN. des_ifs.
      Local Transparent Linker_skfundef. ss.
      inv WFSK0; inv WFSK1.
      unfold link_skfundef in Heq1. des_ifs; eauto using in_prog_defmap.
    + inv WFSK0.
      eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
    + inv WFSK1.
      eapply WFPARAM; eauto. eapply in_prog_defmap; eauto.
Qed.

Theorem link_list_preserves_wf_sk
        (sks: list Sk.t) sk_link
        (LINK: link_list sks = Some sk_link)
        (WFSK: forall sk, In sk sks -> <<WF: Sk.wf sk>>):
    <<WF: Sk.wf sk_link>>.
Proof.
  unfold link_sk in *. ginduction sks; ii; ss. unfold link_list in LINK. des_ifs_safe. ss.
  destruct (link_list_aux sks) eqn:T; ss.
  { clarify. destruct sks; ss; des_ifs. eapply WFSK. eauto. }
  des_ifs. rename t into tl. rename a into hd. specialize (IHsks tl). exploit IHsks; eauto.
  { unfold link_list. des_ifs. }
  i; des. eapply (@link_preserves_wf_sk hd tl); et. eapply WFSK; et.
Qed.

Theorem link_sk_preserves_wf_sk
        p sk_link
        (LINK: link_sk p = Some sk_link)
        (WFSK: forall md, In md p -> <<WF: Sk.wf md >>):
    <<WF: Sk.wf sk_link>>.
Proof.
  eapply link_list_preserves_wf_sk; et. ii. rewrite in_map_iff in *. des; clarify. eapply WFSK; et.
Qed.


(*** TODO: Put in SkEnv. ***)
(*** TODO: fill_internals is not used in CoreRUSC. Update "Sem.v" properly. ***)
Lemma skenv_fill_internals_preserves_wf
      skenv0 skenv1
      (WF: SkEnv.wf skenv0)
      (FILL: (skenv_fill_internals skenv0) = skenv1):
  <<WF: SkEnv.wf skenv1>>.
Proof.
  inv WF. unfold skenv_fill_internals. econs; i; ss; eauto.
  - rewrite Genv_map_defs_symb in *. exploit SYMBDEF; eauto. i; des.
    hexploit Genv_map_defs_def_inv; eauto. i; des. esplits; eauto. rewrite H0; ss.
  - eapply Genv_map_defs_def in DEF; eauto. des. des_ifs. exploit DEFSYMB; eauto.
  - unfold Genv_map_defs, Genv.find_def in *; ss. rewrite PTree_filter_map_spec in DEF.
    destruct ((Genv.genv_defs skenv0) ! blk) eqn:DMAP; ss. unfold o_bind in DEF; ss. des_ifs; eapply WFPARAM in DMAP; eauto.
Qed.



Module DtmAux.

  Lemma find_fptr_owner_determ
        mss fptr ms0 ms1
        (DISJ: SkEnv.disj ms0.(ModSem.skenv) ms1.(ModSem.skenv))
        (FIND0: Ge.find_fptr_owner mss fptr ms0)
        (FIND1: Ge.find_fptr_owner mss fptr ms1):
      ms0 = ms1.
  Proof.
    inv FIND0. inv FIND1. inv DISJ. exploit DISJ0; et. i; des. clarify.
  Qed.

  Require Import RelationClasses Morphisms.
  Require Import Relation_Operators.
  Require Import Relations.
  Local Open Scope signature_scope.

  Lemma ForallOrdPairs_map
        X Y (f: X -> Y) rx ry xs
        (DISJ: ForallOrdPairs rx xs)
        (RESPECTFUL: (rx ==> ry) f f)
    :
      <<DISJ: ForallOrdPairs ry (map f xs)>>
  .
  Proof.
    ginduction xs; ii; ss.
    { econs; et. }
    inv DISJ.
    econs; et.
    - rewrite Forall_forall in *. ii. rewrite in_map_iff in *. des. clarify. et.
    - eapply IHxs; et.
  Qed.

  Definition mod_disj (md0 md1: Mod.t): Prop := Sk.disj (Mod.sk md0) (Mod.sk md1).
  Definition modsem_disj (ms0 ms1: ModSem.t): Prop := SkEnv.disj (ModSem.skenv ms0) (ModSem.skenv ms1).
  Lemma modsem_respects_disj: forall skenv,
      (mod_disj ==> modsem_disj) (flip Mod.modsem skenv) (flip Mod.modsem skenv).
  Proof.
    econs; ii. des. unfold Mod.modsem, flip in *. rewrite <- ! Mod.get_modsem_skenv_spec in *.
    eapply SkEnv.project_respects_disj; et.
  Qed.

  Lemma link_sk_disjoint
        p sk_link
        (LINK: link_sk p = Some sk_link)
    :
      <<DISJ: ForallOrdPairs mod_disj p>>
  .
  Proof.
    ginduction p; ii; ss.
    unfold link_sk in *. ss.
    destruct (classic (p = [])).
    { clarify; ss. econs; et. econs; et. }
    exploit (link_list_cons_inv _ LINK); et.
    { destruct p; ss. }
    i; des.
    exploit IHp; et. intro T; des.
    econs 2; et.
    rewrite Forall_forall. i. r.
    eapply Sk.link_disj in HD.
    eapply Sk.disj_linkorder; et. hexploit (link_list_linkorder _ TL); et. intro U; des.
    rewrite Forall_forall in *. eapply U. rewrite in_map_iff; et.
  Qed.

  Lemma find_fptr_owner_determ_link
        p sk_link skenv_link fptr ms0 ms1
        (LINK: link_sk p = Some sk_link)
        (LOAD: Sk.load_skenv sk_link = skenv_link)
        (FIND0: Ge.find_fptr_owner (load_genv p skenv_link) fptr ms0)
        (FIND1: Ge.find_fptr_owner (load_genv p skenv_link) fptr ms1)
    :
      ms0 = ms1.
  Proof.
    inv FIND0. inv FIND1.
    exploit link_sk_disjoint; et. intro T; des.
    set (skenv_link := (Sk.load_skenv sk_link)) in *.
    eapply (@ForallOrdPairs_map Mod.t ModSem.t (fun md => Mod.modsem md skenv_link)) in T; cycle 1.
    { eapply modsem_respects_disj; et. }
    assert(U: ForallOrdPairs modsem_disj (load_genv p skenv_link)).
    { econs; et. rewrite Forall_forall.
      econs; ii. ss. des_safe.
      unfold Genv.find_funct, Genv.find_funct_ptr in FINDF.
      des_ifs_safe. apply_all_once Genv_map_defs_def. des_safe. des_ifs.
      unfold load_modsems, flip, Mod.modsem in *. rewrite in_map_iff in *. des_safe. ss.
      rewrite <- Mod.get_modsem_skenv_spec in FINDF0. unfold Genv.find_funct_ptr in FINDF0. des_ifs.
      exploit (@SkEnv.project_linkorder skenv_link (Vptr b Ptrofs.zero)); et.
      { eapply link_includes; et. }
      { ss. des_ifs. unfold Genv.find_funct_ptr. des_ifs. }
      { ss. des_ifs. unfold Genv.find_funct_ptr. unfold Mod.sk. des_ifs. }
    }
    clear T.
    exploit ForallOrdPairs_In; [|apply MODSEM|apply MODSEM0|..]; et. ii; des; clarify.
    - inv H. exploit DISJ; et. i; clarify.
    - inv H. exploit DISJ; et. i; clarify.
  Qed.

End DtmAux.

Section INITDTM.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable p: program.
  Hypothesis (WFSK: forall md (IN: In md p), <<WF: Sk.wf md>>).
  Let sem := Sem.sem p.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner sem.(globalenv) fptr ms0)
        (FIND1: Ge.find_fptr_owner sem.(globalenv) fptr ms1):
      ms0 = ms1.
  Proof.
    ss. des_ifs; cycle 1.
    { inv FIND0; ss. }
    eapply DtmAux.find_fptr_owner_determ_link; et.
  Qed.

  Theorem initial_state_determ
          st_init0 st_init1
          (INIT0: sem.(Smallstep.initial_state) st_init0)
          (INIT1: sem.(Smallstep.initial_state) st_init1):
      st_init0 = st_init1.
  Proof.
    ss. inv INIT0; inv INIT1; ss. clarify.
  Qed.

  Theorem genv_disjoint: <<DISJ: sem.(globalenv).(Ge.disjoint)>>.
  Proof.
    econs; et. ii. eapply find_fptr_owner_determ; et.
  Qed.

End INITDTM.






Lemma lift_step
      (ms: ModSem.t) st0 tr st1
      (STEP: Step ms st0 tr st1):
    forall prog msohs tail,
    <<STEP: Step (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail) msohs) tr
                 (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof. ii. econs 3; eauto. Qed.

Lemma lift_star
      (ms: ModSem.t) st0 tr st1
      (STAR: Star ms st0 tr st1):
    forall prog msohs tail,
    <<STAR: Star (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)
                 tr (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof.
  ii. ginduction STAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_step; eauto.
    + eapply IHSTAR; eauto.
Qed.

Lemma lift_plus
      (ms: ModSem.t) st0 tr st1
      (PLUS: Plus ms st0 tr st1):
    forall prog msohs tail,
    <<PLUS: Plus (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)
                 tr (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof.
  i. inv PLUS; ii; ss. econs; eauto.
  - eapply lift_step; eauto.
  - eapply lift_star; eauto.
Qed.

Lemma lift_dstep
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTEP: DStep ms st0 tr st1):
    forall msohs tail,
    <<DSTEP: DStep (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)
                   tr (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof.
  ii. destruct DSTEP as [DTM STEP]. econs; eauto; cycle 1.
  - econs; ss; eauto.
  - inv DTM. econs; eauto.
    + ii. ss. inv H; ss; ModSem.tac. inv H0; ss; ModSem.tac. clear STEP.
      determ_tac sd_determ_at. esplits; auto.
      * eapply match_traces_preserved; try apply H. i. s. congruence.
      * ii. clarify. special H0; ss. clarify.
    + ii. ss. inv STEP0; ss; ModSem.tac. inv FINAL; ss; ModSem.tac.
    + ii. inv H; ss; ModSem.tac. exploit sd_traces_at; eauto.
Qed.

Lemma lift_dstar
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTAR: DStar ms st0 tr st1):
    forall msohs tail,
    <<DSTAR: DStar (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)
                   tr (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof.
  i. ginduction DSTAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_dstep; eauto.
    + eapply IHDSTAR; eauto.
Qed.

Lemma lift_dplus
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DPLUS: DPlus ms st0 tr st1):
    forall msohs tail,
    <<DPLUS: DPlus (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)
                   tr (State ((Frame.mk ms st1) :: tail) msohs)>>.
Proof.
  i. inv DPLUS; ii; ss. econs; eauto.
  - eapply lift_dstep; eauto.
  - eapply lift_dstar; eauto.
Qed.

Lemma lift_receptive_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (RECEP: receptive_at ms st0):
    forall msohs tail, <<RECEP: receptive_at (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)>>.
Proof.
  ii. inv RECEP. ss. econs; eauto; ii.
  - inv H.
    + inv H0. esplits; eauto. econs 1; eauto.
    + ss. exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try apply H0. i. s. congruence. }
      i; des. esplits; eauto. econs; eauto.
    + inv H0. esplits; eauto. econs 4; eauto.
  - inv H; s; try omega. exploit sr_traces_at; eauto.
Qed.

Lemma lift_determinate_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DTM: determinate_at ms st0):
    forall msohs tail,
    <<DTM: determinate_at (Sem.sem prog) (State ((Frame.mk ms st0) :: tail) msohs)>>.
Proof.
  ii. inv DTM. ss. econs; eauto; ii.
  - inv H; inv H0; ModSem.tac.
    + esplits; et.
      { econs; et. }
      i. repeat f_equal; ss; eapply ModSem.at_external_dtm; et.
    + ss. determ_tac sd_determ_at. esplits; et.
      { eapply match_traces_preserved; try apply H. i. s. congruence. }
      i. clarify. repeat f_equal. eauto.
    + ss. esplits; et.
      { econs; et. }
      i. determ_tac ModSem.final_frame_dtm.
      repeat f_equal. eapply ModSem.after_external_dtm; et.
      rp; eauto. rewrite OH in *. eapply upcast_inj in OH0. des. clarify.
  - ss. inv FINAL. ss. inv STEP; ss; ModSem.tac.
  - inv H; s; try omega. exploit sd_traces_at; eauto.
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

Section WFMEM.

(* TODO: move to proper place *)
Lemma Genv_bytes_of_init_data_length
      F V (ge: Genv.t F V) a:
    Datatypes.length (Genv.bytes_of_init_data ge a) = Z.to_nat (init_data_size a).
Proof.
  clear - a. destruct a; ss; des_ifs. rewrite length_list_repeat. rewrite Z2Nat.inj_max. ss. xomega.
Qed.

Inductive wf_mem_weak (skenv ge0: SkEnv.t) (sk: Sk.t) (m0: mem): Prop :=
| wf_mem_weak_intro
    (WFPTR: forall blk_fr _ofs_fr blk_to _ofs_to id_fr _q _n gv
        (SYMB: (Genv.find_symbol ge0) id_fr = Some blk_fr)
        (* (IN: In id_fr sk.(prog_defs_names)) *)
        (IN: In (id_fr, (Gvar gv)) sk.(prog_defs))
        (NONVOL: gv.(gvar_volatile) = false)
        (DEFINITIVE: classify_init gv.(gvar_init) = Init_definitive gv.(gvar_init))
        (* (IN: sk.(prog_defmap) ! id_fr = Some (Gvar gv)) *)
        (LOAD: Mem.loadbytes m0 blk_fr _ofs_fr 1 = Some [Fragment (Vptr blk_to _ofs_to) _q _n]),
        exists id_to, (<<SYMB: (Genv.invert_symbol skenv) blk_to = Some id_to>>)
                      /\ (<<IN: In id_to (prog_defs_names sk)>>)).

Let link_load_skenv_wf_sem_one: forall md sk_link m0 m1 id gd ge0
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    (* (IN: sk_link.(prog_defmap) ! id = Some gd) *)
    (IN: In (id, gd) sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (LOADM: Genv.alloc_global (Sk.load_skenv sk_link) m0 (id, gd) = Some m1)
    (NOTIN: Genv.find_symbol ge0 id = None)
    (WFM: wf_mem_weak (Sk.load_skenv sk_link) ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0),
    (<<WFM: wf_mem_weak (Sk.load_skenv sk_link) (Genv.add_global ge0 (id, gd)) md m1>>)
    /\ (<<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) (Genv.add_global ge0 (id, gd)) m1>>)
    /\ (<<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>).
Proof.
  i. exploit Genv.alloc_global_initialized; et. intro FREETHM; des.
  esplits; et. econs; et. i. ss. des_ifs.
  - (* func *)
    assert(VALID: Mem.valid_block m0 blk_fr).
    { assert(NEQ: blk_fr <> b).
      { ii. clarify. clear - LOAD LOADM Heq. eapply Mem_alloc_fresh_perm in Heq. des.
        eapply Mem.loadbytes_range_perm in LOAD. unfold Mem.range_perm in LOAD. exploit (LOAD _ofs_fr). omega. i.
        destruct (zeq _ofs_fr 0).
        - subst. exploit Mem.perm_drop_2. eauto. instantiate (1 := 0). omega. eauto. i. inv H0.
        - eapply NOPERM0. instantiate (1 := _ofs_fr). omega. eapply Mem.perm_drop_4; eauto.
      }
      assert(VAL: Mem.valid_block m1 blk_fr).
      { clear - LOAD. exploit (Mem.loadbytes_range_perm); eauto. split. eapply Z.le_refl. omega. eapply Mem.perm_valid_block. }
      clear - Heq LOADM NEQ VAL. exploit Mem.drop_perm_valid_block_2; eauto. i.
      exploit Mem.valid_block_alloc_inv; eauto. i; des; des_ifs.
    }
    uge. unfold Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs.
    + Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
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
        { ii. clarify. clear - LOAD LOADM Heq. eapply Mem_alloc_fresh_perm in Heq. des.
        eapply Mem.loadbytes_range_perm in LOAD. unfold Mem.range_perm in LOAD. exploit (LOAD _ofs_fr). omega. i.
        destruct (zeq _ofs_fr 0).
        - subst. exploit Mem.perm_drop_2. eauto. instantiate (1 := 0). omega. eauto. i. inv H0.
        - eapply NOPERM0. instantiate (1 := _ofs_fr). omega. eapply Mem.perm_drop_4; eauto. }
        assert(VAL: Mem.valid_block m1 blk_fr).
        { clear - LOAD. exploit (Mem.loadbytes_range_perm); eauto. split. eapply Z.le_refl. omega. eapply Mem.perm_valid_block. }
        clear - Heq LOADM NEQ VAL. exploit Mem.drop_perm_valid_block_2; eauto. i.
        exploit Mem.valid_block_alloc_inv; eauto. i; des; des_ifs.
      }
      exploit WFPTR; et. erewrite <- Mem.loadbytes_unchanged_on_1 with (P := fun blk _ => Mem.valid_block m0 blk); et.
      { etrans.
        - eapply Mem.alloc_unchanged_on; et.
        - eapply Mem.drop_perm_unchanged_on; et. intros ? ? TTT. clear - Heq TTT. eapply Mem.fresh_block_alloc; eauto.
      }
  - (* gvar *)
    rename b into blk. unfold Genv.find_symbol, Genv.add_global in SYMB. ss. rewrite PTree.gsspec in *. des_ifs; cycle 1.
    + assert(blk <> blk_fr).
      { ii; clarify. clear - WFMB Heq SYMB. exploit GlobalenvsC.Genv_update_publics_obligation_1; eauto. i.
        eapply Mem.alloc_result in Heq. subst. rewrite WFMB in H. xomega. }
      inv WFM. exploit WFPTR; et.
      assert(VAL: Mem.valid_block m0 blk_fr).
      { clear - Heq WFMB FREETHM0 H LOAD. rewrite WFMB in FREETHM0. exploit Mem.alloc_result; eauto. i. subst blk.
        eapply Mem.loadbytes_range_perm in LOAD. exploit Mem.perm_valid_block. eapply LOAD. instantiate (1 := _ofs_fr). omega. i.
        unfold Mem.valid_block in *. rewrite <- FREETHM0 in H0. exploit Plt_succ_inv; eauto. i. des; des_ifs. }
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
    + r in FREETHM.
      exploit (FREETHM (Genv.genv_next ge0)); et.
      { unfold Genv.find_def, Genv.add_global. s. rewrite PTree.gsspec. des_ifs. }
      clear FREETHM. intro FREETHM; des. ss. des.
      (* assert(gv.(gvar_init) = v.(gvar_init)). *)
      assert(LOA: linkorder gv v /\ gvar_volatile v = false).
      { Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
        des. exploit LO1; et.
        { apply prog_defmap_norepet; et. apply NoDup_norepet; et. }
        i; des. apply prog_defmap_norepet in IN; cycle 1. { apply NoDup_norepet; et. }
        clarify. inv H0. inv H4. ss.
      }
      des. exploit FREETHM3; et. intro LOADA; des.
      assert(DAT: exists id_to _ofs,
                (<<IN: In (Init_addrof id_to _ofs) (gvar_init gv)>>)
                /\ (<<SYMB: Genv.find_symbol (Sk.load_skenv sk_link) id_to = Some blk_to>>)).
                (* /\ (<<PLT :Plt blk_to (Genv.genv_next ge0)>>) *)
      { assert(EQ: gv.(gvar_init) = v.(gvar_init)).
        { inv LOA. ss. inv H0; ss. }
        rewrite EQ in *.
        abstr (gvar_init v) dts. clear - LOAD LOADA FREETHM1. abstr (Genv.genv_next ge0) blk. clear_tac.
        abstr ((Sk.load_skenv sk_link)) skenv_link. clear_tac.
        destruct (classic (0 <= _ofs_fr < init_data_list_size dts)); cycle 1.
        { hexploit Mem.loadbytes_range_perm; try apply LOAD; et. intro PERM.
          exploit FREETHM1; et.
          { r in PERM. eapply PERM; et. instantiate (1:= _ofs_fr). xomega. }
          i; des. xomega.
        }
        rename H into RANGE. clear FREETHM1.
        assert(POS: 0 <= 0) by xomega.
        change (init_data_list_size dts) with (0 + init_data_list_size dts) in RANGE.
        revert_until skenv_link. generalize 0 at 1 2 3 5 as ofs. i.
        (* generalize 0 at 1 2 4 as ofs. i. *)
        ginduction dts; ii; ss; try xomega. try rewrite Z.add_assoc in *.
        assert(LOADB: Mem.loadbytes m1 blk (ofs + init_data_size a) (init_data_list_size dts) =
                      Some (Genv.bytes_of_init_data_list skenv_link dts) /\
                      <<LOADC: Mem.loadbytes m1 blk ofs (init_data_size a) =
                               Some (Genv.bytes_of_init_data skenv_link a)>>).
        { exploit Mem.loadbytes_split; et; try xomega.
          { eapply init_data_size_pos. }
          { eapply init_data_list_size_pos. }
          i; des.
          exploit Mem.loadbytes_length; try apply H; et. intro LEN0.
          exploit Mem.loadbytes_length; try apply H0; et. intro LEN1.
          rewrite H. rewrite H0. clear - LEN0 LEN1 H1.
          generalize (Genv_bytes_of_init_data_length skenv_link a); intro LEN2.
          assert(Genv.bytes_of_init_data skenv_link a = bytes1).
          { do 2 (rewrite <- app_nil_r; erewrite <- firstn_O; sym; rewrite <- firstn_app_2).
            rewrite H1. rewrite LEN0. rewrite LEN2. eauto.
          }
          split; des_ifs. eapply app_inv_head in H1. des_ifs.
        }
        des.

        Ltac break_Z :=
          try replace 2 with (1 + 1) in * by omega;
          try replace 3 with (1 + 1 + 1) in * by omega;
          try replace 4 with (1 + 1 + 1 + 1) in * by omega;
          try replace 5 with (1 + 1 + 1 + 1 + 1) in * by omega;
          try replace 6 with (1 + 1 + 1 + 1 + 1 + 1) in * by omega;
          try replace 7 with (1 + 1 + 1 + 1 + 1 + 1 + 1) in * by omega.

        destruct (classic ((ofs + init_data_size a) <= _ofs_fr)).
        - exploit IHdts; et; try xomega.
          { eapply OMEGA2; eauto. eapply Z.ge_le. eapply init_data_size_pos. }
          i; des. esplits; et.
        - clear IHdts LOADB LOADA. rename a into aa. clear RANGE0.
          Local Opaque Z.add. Local Transparent Mem.loadbytes.
          rename ofs into ofs_bound. rename _ofs_fr into ofs_mid.
          assert(T: ofs_mid < ofs_bound + init_data_size aa) by omega. clear H.

          destruct aa; ss;
            try (by exfalso; unfold Mem.loadbytes in *; des_ifs;
                 assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                        \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                        \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7) by omega;
                 des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H0 in *; ss).

          + exfalso. unfold Mem.loadbytes in *. des_ifs. rename H0 into P. rename H1 into Q. clear - P Q T RANGE POS.
            abstr ((Mem.mem_contents m1) !! blk) MC. clear_tac.
            assert(POS0: 0 <= Z.max z 0) by xomega.
            exploit (@Mem.getN_in MC ofs_mid (Z.to_nat (Z.max z 0)) ofs_bound); eauto.
            { split; try xomega. rewrite Z2Nat.id; ss. }
            intro R. rewrite Q in *. unfold Z.to_nat in *. rewrite P in *. clear - R. apply in_list_repeat in R. ss.

          + des_ifs; cycle 1.
            { exfalso. unfold Mem.loadbytes in *. des_ifs.
              assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                     \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                     \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7) by omega.
              des; subst; try xomega; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H8 in *; ss.
            }
            esplits; et. unfold inj_value in *. ss. unfold Mem.loadbytes in *. des_ifs.
            assert(ofs_mid = ofs_bound \/ ofs_mid = ofs_bound + 1 \/ ofs_mid = ofs_bound + 2
                   \/ ofs_mid = ofs_bound + 3 \/ ofs_mid = ofs_bound + 4 \/ ofs_mid = ofs_bound + 5
                   \/ ofs_mid = ofs_bound + 6 \/ ofs_mid = ofs_bound + 7) by omega.
            des; subst; break_Z; try rewrite ! Z.add_assoc in *; try rewrite H8 in *; congruence.
          Local Opaque Mem.loadbytes.
      }
      des. bar. inv WF. exploit WFPTR; et. i ;des. esplits; et. apply Genv.find_invert_symbol. ss.
Qed.


Let link_load_skenv_wf_sem_mult: forall md sk_link idgs m0 m1 ge0
    (WF: Sk.wf md)
    (LO: linkorder md sk_link)
    (INCL: incl idgs sk_link.(prog_defs))
    (NODUP: NoDup (prog_defs_names md))
    (NODUP: NoDup (prog_defs_names sk_link))
    (NODUP: NoDup (map fst idgs))
    (LOADM: Genv.alloc_globals (Sk.load_skenv sk_link) m0 idgs = Some m1)
    (NOTIN: forall id (IN: In id (map fst idgs)), Genv.find_symbol ge0 id = None)
    (WFM: wf_mem_weak (Sk.load_skenv sk_link) ge0 md m0)
    (WFMA: Genv.globals_initialized (Sk.load_skenv sk_link) ge0 m0)
    (WFMB: Genv.genv_next ge0 = Mem.nextblock m0),
    <<WFM: wf_mem_weak (Sk.load_skenv sk_link) (Genv.add_globals ge0 idgs) md m1>>
           /\ <<WFMA: Genv.globals_initialized (Sk.load_skenv sk_link)
                                              (Genv.add_globals ge0 idgs) m1>>
                     /\ <<WFMB: Genv.genv_next ge0 = Mem.nextblock m0>>.
Proof.
  i. generalize dependent ge0. generalize dependent m0. generalize dependent m1.
  (* generalize dependent FRESH. *)
  induction idgs; ii; ss.
  { clarify. }
  des_ifs. destruct a.
  exploit link_load_skenv_wf_sem_one; et.
  { eapply INCL; et. s. et. }
  i; des.
  exploit IHidgs; try apply WFM0; et.
  { ii. eapply INCL; et. s. et. }
  { ss. inv NODUP1. ss. }
  { i. uge. unfold Genv.add_global. s. rewrite PTree.gsspec. des_ifs.
    - inv NODUP1. ss.
    - apply NOTIN. right. ss. }
  { s. clear - WFMB0 Heq. exploit Genv.alloc_global_nextblock; eauto. congruence. }
  i; des. esplits; et.
Qed.

Lemma link_load_skenv_wf_mem
      p sk_link m_init
      (LINK: link_sk p = Some sk_link)
      (WF: forall md (IN: In md p), Sk.wf md)
      (LOADM: Sk.load_mem sk_link = Some m_init):
    let skenv_link := Sk.load_skenv sk_link in
    <<WFM: forall md (IN: In md p), SkEnv.wf_mem skenv_link md m_init>>.
Proof.
  econs. i. unfold link_sk in *.
  hexploit (link_list_linkorder _ LINK); et. intro LO. des.
  rewrite Forall_forall in *. exploit LO; et.
  { rewrite in_map_iff. esplits; et. }
  clear LO. intro LO.
  exploit WF; et. clear WF. intro WF; des.
  assert(NODUP: NoDup (prog_defs_names sk_link)).
  { clear - LINK IN WF. destruct p; ss. destruct p; ss.
    - des; ss. clarify. unfold link_list in *. des_ifs. ss. clarify. apply WF.
    - clear IN WF.
      exploit (link_list_cons_inv _ LINK); et.
      { ss. }
      i; des. clear - HD.
      Local Transparent Linker_prog. ss. Local Opaque Linker_prog.
      unfold link_prog in *. des_ifs. apply NoDup_norepet. unfold prog_defs_names. apply PTree.elements_keys_norepet.
  }
  clear LINK IN.


  { eapply link_load_skenv_wf_sem_mult; et; try eapply WF; try refl.
    { i. uge. ss. rewrite PTree.gempty. ss. }
    { econs; et. i. exfalso. clear - LOAD0. eapply Mem.loadbytes_range_perm in LOAD0.
      exploit (LOAD0 _ofs_fr0). omega. eapply Mem.perm_empty.
    }
    { rr. ii. exfalso. clear - H. unfold Genv.find_def in H. rewrite PTree.gempty in H. des_ifs. }
  }
Qed.

End WFMEM.


Require Import Sem SimModSem.
Theorem safe_implies_safe_modsem
        p sk ms lst msohs tail
        (LINK: link_sk p = Some sk)
        (SAFE: safe (sem p) (State ((Frame.mk ms lst) :: tail) msohs)):
    <<SAFE: safe_modsem ms lst>>.
Proof.
  ii. ss. exploit SAFE.
  { instantiate (1:= (State ((Frame.mk ms st1) :: tail) msohs)). eapply lift_star; eauto. }
  i; des.
  - ss. inv H. ss. right. left. eauto.
  - ss. des_ifs. inv H; ss.
    + left. eauto.
    + right. right. eauto.
    + right. left. eauto.
Qed.


Lemma backward_simulation_refl: forall SEM, backward_simulation SEM SEM.
Proof.
  i. eapply (@Backward_simulation _ _ unit bot2). econs; eauto.
  { apply unit_ord_wf. }
  ii. ss. exists tt. esplits; eauto.
  clear st_init_src_ INITSRC INITTGT. rename st_init_tgt into st. revert st.
  pcofix CIH. i. pfold. econs; eauto.
  ii. econs; eauto.
  { ii. esplits; eauto. left. apply plus_one. ss. }
  { i. r in SAFESRC. specialize (SAFESRC st (star_refl _ _ _ _)). ss. }
  { ii. esplits; eauto. econs; eauto. }
Qed.

Lemma sk_nwf_improves (mds_src mds_tgt: program)
      (NWF: ~ (forall x (IN: In x mds_src), Sk.wf x)):
      improves (sem mds_src) (sem mds_tgt).
Proof.
  eapply bsim_improves. econs. econs; try (i; inv INITSRC; clarify). eapply unit_ord_wf.
Qed.

Lemma load_owned_heaps_diff
      ms mss mi
      (DIFF: mi <> ms.(ModSem.midx))
  :
    load_owned_heaps (mss) mi = load_owned_heaps (ms :: mss) mi
.
Proof.
  unfold load_owned_heaps.
  unfold Midx.list_to_set.
  rewrite <- ! fold_left_rev_right. rewrite <- ! map_rev. ss.
  abstr (rev mss) mss0. clear_tac.
  ginduction mss0; ii; ss.
  { unfold Midx.update. des_ifs. }
  unfold Midx.update. des_ifs. erewrite IHmss0; eauto.
Qed.

Lemma load_modsems_midx
      p skenv
  :
    <<EQ: map ModSem.midx (load_modsems p skenv) = map Mod.midx p>>
.
Proof.
  ginduction p; ii; ss.
  rewrite IHp; et. unfold flip. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. ss.
Qed.

Lemma load_owned_heaps_same
      mss0 mss1
      (NODUP0: Midx.NoDup (map (fun ms => ModSem.midx ms) mss0))
      (NODUP1: Midx.NoDup (map (fun ms => ModSem.midx ms) mss1))
      (INITSAME: forall k v,
          In (k, v) (map (fun ms => (ModSem.midx ms, Any.upcast (ModSem.initial_owned_heap ms))) mss0)
          <->
          In (k, v) (map (fun ms => (ModSem.midx ms, Any.upcast (ModSem.initial_owned_heap ms))) mss1))
  :
    load_owned_heaps mss0 = load_owned_heaps mss1
.
Proof.
  clear - NODUP0 NODUP1 INITSAME.
  unfold load_owned_heaps.
  apply func_ext1.
  intro mi.
  destruct (classic (exists v, <<IN: In (mi, v) (map (fun ms => (ModSem.midx ms, Any.upcast (ModSem.initial_owned_heap ms))) mss0)>>)).
  { des. dup IN.
    eapply INITSAME in IN0. destruct mi.
    - exploit Midx.list_to_set_spec1; try apply IN; eauto.
      { rewrite map_map in *. ss. }
      intro T.
      exploit Midx.list_to_set_spec1; try apply IN0; eauto.
      { rewrite map_map in *. ss. }
      intro U.
      rewrite T. rewrite U. ss.
    - exploit Midx.list_to_set_spec2; try apply IN; eauto.
      { rewrite map_map in *. ss. }
      { instantiate (1:= Any.upcast tt). ii. rewrite in_map_iff in *. des. inv IN1.
        exploit ModSem.midx_none; et. intro U. clear - U.
        remember (ModSem.initial_owned_heap x) as X. clear HeqX. revert X. rewrite U in *.
        ii; des_u; ss.
      }
      intro T.
      exploit Midx.list_to_set_spec2; try apply IN0; eauto.
      { rewrite map_map in *. ss. }
      { instantiate (1:= Any.upcast tt). ii. rewrite in_map_iff in *. des. inv IN1.
        exploit ModSem.midx_none; et. intro U. clear - U.
        remember (ModSem.initial_owned_heap x) as X. clear HeqX. revert X. rewrite U in *.
        ii; des_u; ss.
      }
      intro U.
      rewrite T. rewrite U. ss.
  }
  { apply not_ex_all_not in H.
    erewrite Midx.list_to_set_spec3; et; cycle 1.
    { rewrite map_map in *. ss. }
    erewrite Midx.list_to_set_spec3; et; cycle 1.
    { intros ? T. eapply INITSAME in T. eapply H; et. }
    { rewrite map_map in *. ss. }
  }
Qed.
