Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import CsemC ClightC.
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

Local Opaque Z.mul Z.add Z.sub Z.div.



Lemma ccc_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  rewrite SIMSKENVLINK in *.
  eapply match_states_sim; ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - instantiate (1:= fun sm_arg _ st_src st_tgt sm0 =>
                       (<<EQ: st_src = st_tgt>>) /\
                       (<<MWF: sm0.(SimMemId.src) = sm0.(SimMemId.tgt)>>) /\
                       (<<STMWF: match st_src.(CsemC.get_mem) with
                                 | Some m => sm0.(SimMemId.src) = m
                                 | _ => True
                                 end>>)).
    ss. i.
    destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
    clear SAFESRC. dup INITTGT. inv INITTGT. ss.
    eexists. eexists (SimMemId.mk tgt tgt). esplits; eauto; ss.
  - ii. destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
  - ii. ss. des. clarify.
  - i. ss. des. clarify. esplits; eauto.
    + inv CALLSRC. ss. clarify.
    + instantiate (1:=top4). ss.
  - i. clear HISTORY. ss. destruct sm_ret, retv_src, retv_tgt.
    inv SIMRET. des. ss. clarify. eexists (SimMemId.mk _ _). esplits; eauto.
    inv AFTERSRC. ss.
  - i. ss. des. destruct sm0. ss. clarify. eexists (SimMemId.mk tgt tgt).
    esplits; eauto.
    inv FINALSRC. ss.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1.
      exists (match st_tgt1.(CsemC.get_mem) with
              | Some m => SimMemId.mk m m
              | _ => SimMemId.mk tgt tgt
              end).
      esplits; eauto.
      * left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
      * des_ifs.
      * des_ifs.
Qed.

Lemma clight1_inj_id
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module1)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module1)>>)
.
Proof.
  admit "this should hold".
Qed.

Definition match_env (j: meminj) (env_src env_tgt: env) :=
  forall id,
    (<<MAPPED: exists blk_src blk_tgt ty,
        (<<INJ: j blk_src = Some (blk_tgt, 0)>>) /\
        (<<BLKSRC: env_src ! id = Some (blk_src, ty)>>) /\
        (<<BLKTGT: env_tgt ! id = Some (blk_tgt, ty)>>)>>) \/
    (<<NOTMAPPED:
       (<<BLKSRC: env_src ! id = None>>) /\
       (<<BLKTGT: env_tgt ! id = None>>)>>)
.

Definition match_temp_env (j: meminj) (tenv_src tenv_tgt: temp_env) :=
  forall id,
    option_rel (Val.inject j) (tenv_src ! id) (tenv_tgt ! id).

Inductive match_cont (j: meminj): cont -> cont -> Prop :=
| match_Kstop:
    match_cont j Kstop Kstop
| match_Kseq
    stmt K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kseq stmt K_src) (Kseq stmt K_tgt)
| match_Kloop1
    stmt0 stmt1 K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kloop1 stmt0 stmt1 K_src) (Kloop1 stmt0 stmt1 K_tgt)
| match_Kloop2
    stmt0 stmt1 K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kloop2 stmt0 stmt1 K_src) (Kloop2 stmt0 stmt1 K_tgt)
| match_Kswitch
    K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kswitch K_src) (Kswitch K_tgt)
| match_Kcall
    id fn
    env_src env_tgt
    tenv_src tenv_tgt
    K_src K_tgt
    (ENV: match_env j env_src env_tgt)
    (TENV: match_temp_env j tenv_src tenv_tgt)
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kcall id fn env_src tenv_src K_src) (Kcall id fn env_tgt tenv_tgt K_tgt)
.

Inductive match_states_clight (sm_arg: SimMemInj.t')
  : unit -> state -> state -> SimMemInj.t' -> Prop :=
| match_State
    fn stmt K_src K_tgt env_src env_tgt tenv_src tenv_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWF: SimMemInj.wf' sm0)
    (ENV: match_env sm0.(SimMemInj.inj) env_src env_tgt)
    (TENV: match_temp_env sm0.(SimMemInj.inj) tenv_src tenv_tgt)
    (CONT: match_cont sm0.(SimMemInj.inj) K_src K_tgt)
  :
    match_states_clight
      sm_arg tt
      (State fn stmt K_src env_src tenv_src m_src)
      (State fn stmt K_tgt env_tgt tenv_tgt m_tgt)
      sm0
| match_Callstate
    fptr_src fptr_tgt ty args_src args_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWF: SimMemInj.wf' sm0)
    (INJ: Val.inject sm0.(SimMemInj.inj) fptr_src fptr_tgt)
    (VALS: Val.inject_list sm0.(SimMemInj.inj) args_src args_tgt)
    (CONT: match_cont sm0.(SimMemInj.inj) K_src K_tgt)
  :
    match_states_clight
      sm_arg tt
      (Callstate fptr_src ty args_src K_src m_src)
      (Callstate fptr_tgt ty args_tgt K_tgt m_tgt)
      sm0
| match_Returnstate
    retv_src retv_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWF: SimMemInj.wf' sm0)
    (INJ: Val.inject sm0.(SimMemInj.inj) retv_src retv_tgt)
    (CONT: match_cont sm0.(SimMemInj.inj) K_src K_tgt)
  :
    match_states_clight
      sm_arg tt
      (Returnstate retv_src K_src m_src)
      (Returnstate retv_tgt K_tgt m_tgt)
      sm0
.

Inductive match_states_ext_clight (sm_arg: SimMemExt.t')
  : unit -> state -> state -> SimMemExt.t' -> Prop :=
| match_ext_State
    fn stmt K_src K_tgt env_src env_tgt tenv_src tenv_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (ENV: env_src = env_tgt)
    (TENV: tenv_src = tenv_tgt)
    (CONT: match_cont inject_id K_src K_tgt)
  :
    match_states_ext_clight
      sm_arg tt
      (State fn stmt K_src env_src tenv_src m_src)
      (State fn stmt K_tgt env_tgt tenv_tgt m_tgt)
      sm0
| match_ext_Callstate
    fptr_src fptr_tgt ty args_src args_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (INJ: Val.lessdef fptr_src fptr_tgt)
    (VALS: Val.lessdef_list args_src args_tgt)
    (CONT: match_cont inject_id K_src K_tgt)
  :
    match_states_ext_clight
      sm_arg tt
      (Callstate fptr_src ty args_src K_src m_src)
      (Callstate fptr_tgt ty args_tgt K_tgt m_tgt)
      sm0
| match_ext_Returnstate
    retv_src retv_tgt K_src K_tgt m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemExt.src))
    (MWFTGT: m_tgt = sm0.(SimMemExt.tgt))
    (MWF: Mem.extends m_src m_tgt)
    (INJ: Val.lessdef retv_src retv_tgt)
    (CONT: match_cont inject_id K_src K_tgt)
  :
    match_states_ext_clight
      sm_arg tt
      (Returnstate retv_src K_src m_src)
      (Returnstate retv_tgt K_tgt m_tgt)
      sm0
.

Lemma clight2_id
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  rewrite SIMSKENVLINK in *.
  eapply match_states_sim; ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - instantiate (1:= fun sm_arg _ st_src st_tgt sm0 =>
                       (<<EQ: st_src = st_tgt>>) /\
                       (<<MWF: sm0.(SimMemId.src) = sm0.(SimMemId.tgt)>>) /\
                       (<<STMWF: st_src.(ClightC.get_mem) =
                                 sm0.(SimMemId.src)>>)).
    ss. i.
    destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
    clear SAFESRC. dup INITTGT. inv INITTGT. ss.
    eexists. eexists (SimMemId.mk tgt tgt). esplits; eauto; ss.
  - ii. destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
  - ii. ss. des. clarify.
  - i. ss. des. clarify. esplits; eauto.
    + inv CALLSRC. ss. clarify.
    + instantiate (1:=top4). ss.
  - i. clear HISTORY. ss. destruct sm_ret, retv_src, retv_tgt.
    inv SIMRET. des. ss. clarify. eexists (SimMemId.mk _ _). esplits; eauto.
    inv AFTERSRC. ss.
  - i. ss. des. destruct sm0. ss. clarify.
    eexists (SimMemId.mk (get_mem st_tgt0) (get_mem st_tgt0)).
    esplits; eauto.
    inv FINALSRC. ss.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1.
      eexists (SimMemId.mk (get_mem st_tgt1) (get_mem st_tgt1)).
      esplits; eauto.
      left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
Qed.

Lemma clight2_ext_top
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma clight2_ext_unreach
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma clight2_inj_id
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma clight2_inj_drop
      (clight: Clight.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = clight.(module2)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = clight.(module2)>>)
.
Proof.
  admit "this should hold".
Qed.


Require Import mktac.
Require Import IntegersC.
(* Require Import SimplLocalsproof. *)

Section CLIGHTINJ.

  Variable se_src se_tgt: Senv.t.
  Variable ge_src ge_tgt: genv.
  Hypothesis CENV: genv_cenv ge_src = genv_cenv ge_tgt.
  (* TODO: injection condition of env *)

  Definition function_entry_inject
             (function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    :=
      forall
        fn vs_src vs_tgt sm0 env_src tenv_src m_src1
        (MWF: SimMemInj.wf' sm0)
        (VALS: Val.inject_list sm0.(SimMemInj.inj) vs_src vs_tgt)
        (ENTRY: function_entry ge_src fn vs_src sm0.(SimMemInj.src) env_src tenv_src m_src1),
      exists env_tgt tenv_tgt sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<ENV: match_env sm1.(SimMemInj.inj) env_src env_tgt>>) /\
        (<<TENV: match_temp_env sm1.(SimMemInj.inj) tenv_src tenv_tgt>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<ENTRY: function_entry ge_tgt fn vs_tgt sm0.(SimMemInj.tgt) env_tgt tenv_tgt sm1.(SimMemInj.tgt)>>).

  Lemma alloc_variables_inject sm0 idl e_src0 e_tgt0 e_src1 m_src1
        (ALLOC: alloc_variables ge_src e_src0 (SimMemInj.src sm0) idl e_src1 m_src1)
        (ENV: match_env (SimMemInj.inj sm0) e_src0 e_tgt0)
        (MWF: SimMemInj.wf' sm0)
    :
      exists e_tgt1 sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<ENV: match_env (SimMemInj.inj sm1) e_src1 e_tgt1>>) /\
        (<<ALLOC: alloc_variables ge_tgt e_tgt0 (SimMemInj.tgt sm0) idl e_tgt1 (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 MWF e_src0 e_tgt0 e_src1 m_src1 ENV ALLOC. induction idl.
    - i. inv ALLOC. esplits; eauto.
      + refl.
      + econs.
    - i. inv ALLOC.
      exploit SimMemInj.alloc_parallel; eauto; try refl. i. des. clarify.
      exploit IHidl; eauto.
      { instantiate (1:=PTree.set id (blk_tgt, ty) e_tgt0).
        ii. repeat rewrite PTree.gsspec. des_ifs.
        - left. esplits; eauto.
        - destruct (ENV id0).
          + des. left. inv MLE. esplits; cycle 1; eauto.
          + right. eauto. }
      i. des. clarify.
      esplits; eauto.
      + etrans; eauto.
      + econs; eauto.
        rewrite <- CENV. auto.
  Qed.

  Lemma storebytes_mapped
        sm0 b tb ofs bytes1 bytes2 m_src delta
        (MWF : SimMemInj.wf' sm0)
        (STRSRC: Mem.storebytes (SimMemInj.src sm0) b ofs bytes1 = Some m_src)
        (SIMBLK: (SimMemInj.inj sm0) b = Some (tb, delta))
        (BYTESINJ: list_forall2 (memval_inject (SimMemInj.inj sm0)) bytes1 bytes2)
    (* (SIMADDR: Val.inject (SimMemInj.inj sm0) (Vptr b ofs) (Vptr tb tofs)) *)
    :
      exists sm1,
        (<<MSRC: (SimMemInj.src sm1) = m_src>>)
        /\ (<<MINJ: (SimMemInj.inj sm1) = (SimMemInj.inj sm0)>>)
        /\ (<<STRTGT: Mem.storebytes (SimMemInj.tgt sm0) tb (ofs + delta) bytes2 = Some (SimMemInj.tgt sm1)>>)
        /\ (<<MWF: SimMemInj.wf' sm1>>)
        /\ (<<MLE: SimMemInj.le' sm0 sm1>>)
  .
  Proof.
    (* inv SIMADDR. *)
    exploit Mem.storebytes_mapped_inject; eauto.
    { inv MWF. eauto. }
    i. des.
    inv MWF.
    eexists (SimMemInj.mk _ _ _ _ _ _ _).
    esplits; ss; eauto; cycle 1.
    - econs; ss; eauto.
      + eapply Mem.storebytes_unchanged_on; eauto.
        ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
      + eapply Mem.storebytes_unchanged_on; eauto.
        ii. apply TGTEXT in H2. red in H2. des. red in H2.
        eapply H2; eauto. clear - BYTESINJ STRSRC H1 H4.
        eapply Mem.storebytes_range_perm in STRSRC.
        assert (Datatypes.length bytes2 = Datatypes.length bytes1).
        { exploit list_forall2_length; eauto. }
        rewrite H in *.
        assert (ofs <= i - delta) by nia.
        assert (i - delta < ofs + Z.of_nat (Datatypes.length bytes1)) by nia.
        unfold Mem.range_perm in STRSRC.
        specialize (STRSRC (i - delta)). exploit STRSRC. nia.
        i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto.
        eapply perm_any_N.
      + eapply SimMemInj.frozen_refl.
      + ii. eapply Mem.perm_storebytes_2; eauto.
      + ii. eapply Mem.perm_storebytes_2; eauto.
    - econs; ss; eauto.
      + etransitivity; eauto. unfold SimMemInj.src_private. ss. ii; des. esplits; eauto.
        unfold SimMemInj.valid_blocks in *. eauto with mem.
      + etransitivity; eauto. unfold SimMemInj.tgt_private. ss. ii; des. esplits; eauto.
        { ii. eapply PR. eauto with mem. eauto with mem. }
        unfold SimMemInj.valid_blocks in *. eauto with mem.
      + etransitivity; eauto. erewrite <- Mem.nextblock_storebytes; eauto. xomega.
      + etransitivity; eauto. erewrite <- Mem.nextblock_storebytes; eauto. xomega.
  Qed.

  Lemma assign_loc_inject ce ty sm0 blk_src blk_tgt ofs_src ofs_tgt v_src v_tgt m_src1
        (ASSIGN: assign_loc ce ty sm0.(SimMemInj.src) blk_src ofs_src v_src m_src1)
        (INJ: Val.inject sm0.(SimMemInj.inj) (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
        (VAL: Val.inject sm0.(SimMemInj.inj) v_src v_tgt)
        (MWF: SimMemInj.wf' sm0)
    :
      exists sm1,
        (<<ASSIGN: assign_loc ce ty sm0.(SimMemInj.tgt) blk_tgt ofs_tgt v_tgt sm1.(SimMemInj.tgt)>>) /\
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>).
  Proof.
    inv ASSIGN.
    - exploit SimMemInj.storev_mapped; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    - cinv MWF. cinv VAL. cinv INJ.
      exploit Mem.loadbytes_inject; eauto. i. des_safe.
      exploit storebytes_mapped; eauto. i. des_safe.
      esplits; eauto. admit "TODO".
  Qed.

  Lemma call_cont_match j K_src K_tgt
        (MATCH: match_cont j K_src K_tgt)
    :
      match_cont j (call_cont K_src) (call_cont K_tgt).
  Proof.
    revert K_tgt MATCH. induction K_src; ss; i; inv MATCH; ss; eauto.
    - econs.
    - econs; eauto.
  Qed.

  Lemma match_env_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_env j0 <2= match_env j1.
  Proof.
    ii. destruct (PR id).
    - des. left. esplits; eauto.
    - des. right. esplits; eauto.
  Qed.

  Lemma match_temp_env_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_temp_env j0 <2= match_temp_env j1.
  Proof.
    ii. destruct (PR id); econs. eapply val_inject_incr; eauto.
  Qed.

  Lemma match_cont_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_cont j0 <2= match_cont j1.
  Proof.
    ii. revert INCR.
    induction PR; i; econs; eauto; try by (eapply match_expr_incr; eauto).
    - eapply match_env_incr; eauto.
    - eapply match_temp_env_incr; eauto.
  Qed.

  Lemma bind_parameters_inject e_src e_tgt sm0 idl vargs_src vargs_tgt m_src1
        (BIND: bind_parameters ge_src e_src (SimMemInj.src sm0) idl vargs_src m_src1)
        (ENV: match_env (SimMemInj.inj sm0) e_src e_tgt)
        (MWF: SimMemInj.wf' sm0)
        (VALS: Val.inject_list (SimMemInj.inj sm0) vargs_src vargs_tgt)
    :
      exists sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<BIND: bind_parameters ge_tgt e_tgt (SimMemInj.tgt sm0) idl vargs_tgt (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 ENV vargs_src vargs_tgt m_src1 MWF VALS BIND. induction idl.
    - i. inv BIND. inv VALS. esplits; eauto.
      + refl.
      + econs.
    - i. inv BIND. inv VALS.
      destruct (ENV id); des; clarify.
      exploit assign_loc_inject; eauto. i. des. clarify.
      exploit IHidl; try apply H6; eauto.
      { inv MLE. eapply match_env_incr; eauto. }
      { inv MLE. eapply val_inject_list_incr; eauto. }
      i. des. esplits; eauto.
      + etrans; eauto.
      + econs; eauto. rewrite CENV in *. auto.
  Qed.

  Lemma set_match_temp_env j id v_src v_tgt tenv_src tenv_tgt
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (VAL: Val.inject j v_src v_tgt)
    :
      match_temp_env j (PTree.set id v_src tenv_src) (PTree.set id v_tgt tenv_tgt).
  Proof.
    ii. repeat rewrite PTree.gsspec. des_ifs.
    econs; eauto.
  Qed.

  Lemma bind_parameter_temps_inject tenv_src0 tenv_tgt0 tenv_src1
        j idl vargs_src vargs_tgt
        (BIND: bind_parameter_temps idl vargs_src tenv_src0 = Some tenv_src1)
        (TENV: match_temp_env j tenv_src0 tenv_tgt0)
        (VALS: Val.inject_list j vargs_src vargs_tgt)
    :
      exists tenv_tgt1,
        (<<BIND: bind_parameter_temps idl vargs_tgt tenv_tgt0 = Some tenv_tgt1>>) /\
        (<<TENV: match_temp_env j tenv_src1 tenv_tgt1>>).
  Proof.
    revert tenv_src0 tenv_tgt0 tenv_src1 vargs_src BIND TENV vargs_tgt VALS.
    induction idl; i; ss; des_ifs_safe.
    - inv VALS. esplits; eauto.
    - inv VALS. exploit IHidl; eauto.
      eapply set_match_temp_env; eauto.
  Qed.

  Lemma create_undef_temps_match j l
    :
      match_temp_env j (create_undef_temps l) (create_undef_temps l).
  Proof.
    induction l; ss.
    - ii. repeat rewrite PTree.gempty. econs.
    - ii. des_ifs. rewrite PTree.gsspec.
      des_ifs. econs. eauto.
  Qed.

  Lemma function_entry1_inject
    :
      function_entry_inject function_entry1.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_inject; eauto.
    { instantiate (1:=empty_env). ii. right.
      unfold empty_env. repeat rewrite PTree.gempty. auto. }
    i. des. clarify.
    exploit bind_parameters_inject; eauto.
    { cinv MLE. eapply val_inject_list_incr; eauto. } i. des.
    esplits; eauto.
    - cinv MLE. cinv MLE0. eapply match_env_incr; eauto.
    - eapply create_undef_temps_match.
    - etrans; eauto.
    - econs; eauto.
  Qed.

  Lemma function_entry2_inject
    :
      function_entry_inject function_entry2.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_inject; eauto.
    { instantiate (1:=empty_env). ii. right.
      unfold empty_env. repeat rewrite PTree.gempty. auto. }
    i. des. clarify.
    exploit bind_parameter_temps_inject; eauto.
    { eapply create_undef_temps_match. } i. des.
    esplits; eauto.
    - cinv MLE. eapply match_temp_env_incr; eauto.
    - econs; eauto.
  Qed.

  Variable function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
  Hypothesis FUNCTIONENTRY: function_entry_inject function_entry.

  Lemma deref_loc_inject j ty m_src m_tgt blk_src blk_tgt ofs_src ofs_tgt v_src
        (DEREF: deref_loc ty m_src blk_src ofs_src v_src)
        (INJECT: Mem.inject j m_src m_tgt)
        (VAL: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
    :
      exists v_tgt,
        (<<DEREF: deref_loc ty m_tgt blk_tgt ofs_tgt v_tgt>>) /\
        (<<VAL: Val.inject j v_src v_tgt>>).
  Proof.
    inv DEREF.
    - exploit Mem.loadv_inject; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    - esplits; eauto. econs 2; eauto.
    - esplits; eauto. econs 3; eauto.
  Qed.

  Lemma eval_expr_lvalue_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
    :
      (forall
          exp v_src
          (EVAL: eval_expr ge_src env_src tenv_src m_src exp v_src),
          forall
            (ENV: match_env j env_src env_tgt)
            (TENV: match_temp_env j tenv_src tenv_tgt)
            (INJECT: Mem.inject j m_src m_tgt),
          exists v_tgt,
            (<<EVAL: eval_expr ge_tgt env_tgt tenv_tgt m_tgt exp v_tgt>>) /\
            (<<INJ: Val.inject j v_src v_tgt>>)) /\
      (forall
          exp blk_src ofs_src
          (EVAL: eval_lvalue ge_src env_src tenv_src m_src exp blk_src ofs_src),
          forall
            (ENV: match_env j env_src env_tgt)
            (TENV: match_temp_env j tenv_src tenv_tgt)
            (INJECT: Mem.inject j m_src m_tgt),
          exists blk_tgt ofs_tgt,
            (<<EVAL: eval_lvalue ge_tgt env_tgt tenv_tgt m_tgt exp blk_tgt ofs_tgt>>) /\
            (<<INJ: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt)>>)).
  Proof.
    apply eval_expr_lvalue_ind; i.
    - esplits; eauto. econs 1; eauto.
    - esplits; eauto. econs 2; eauto.
    - esplits; eauto. econs 3; eauto.
    - esplits; eauto. econs 4; eauto.
    - cinv (TENV id); rewrite H in *; clarify.
      esplits; eauto. econs 5; eauto.
    - exploit H0; eauto. i. des.
      esplits; eauto. econs 6; eauto.
    - exploit H0; eauto. i. des.
      exploit sem_unary_operation_inject; eauto. i. des.
      esplits; eauto. econs 7; eauto.
    - exploit H0; eauto. i. des.
      exploit H2; eauto. i. des.
      exploit sem_binary_operation_inject; eauto. i. des.
      esplits; eauto. econs 8; eauto.
      rewrite <- CENV. auto.
    - exploit H0; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      esplits; eauto. econs 9; eauto.
    - esplits; eauto. rewrite CENV. econs 10; eauto.
    - esplits; eauto. rewrite CENV. econs 11; eauto.
    - exploit H0; eauto. i. des.
      exploit deref_loc_inject; eauto. i. des.
      esplits; eauto. econs 12; eauto.
    - cinv (ENV id); des; rewrite H in *; clarify.
      esplits; eauto. econs 1; eauto.
    - cinv (ENV id); des; rewrite H in *; clarify.
      admit "genv".
    - exploit H0; eauto. i. des. cinv INJ.
      esplits; eauto. econs 3; eauto.
    - exploit H0; eauto. i. des. cinv INJ. rewrite CENV in *.
      esplits.
      + econs 4; eauto.
      + econs; eauto.
        repeat rewrite Ptrofs.add_assoc. f_equal.
        apply Ptrofs.add_commut.
    - exploit H0; eauto. i. des. cinv INJ. rewrite CENV in *.
      esplits; eauto. econs 5; eauto.
  Qed.

  Lemma eval_expr_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
        exp v_src
        (EVAL: eval_expr ge_src env_src tenv_src m_src exp v_src)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists v_tgt,
        (<<EVAL: eval_expr ge_tgt env_tgt tenv_tgt m_tgt exp v_tgt>>) /\
        (<<INJ: Val.inject j v_src v_tgt>>).
  Proof.
    exploit eval_expr_lvalue_inject; eauto. i. des. eauto.
  Qed.

  Lemma eval_exprlist_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt tys
        exps vs_src
        (EVALS: eval_exprlist ge_src env_src tenv_src m_src exps tys vs_src)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists vs_tgt,
        (<<EVALS: eval_exprlist ge_tgt env_tgt tenv_tgt m_tgt exps tys vs_tgt>>) /\
        (<<INJ: Val.inject_list j vs_src vs_tgt>>).
  Proof.
    revert tys vs_src EVALS ENV TENV INJECT. induction exps; i.
    - inv EVALS. exists []. esplits; eauto. econs; eauto.
    - inv EVALS. exploit IHexps; eauto. i. des.
      exploit eval_expr_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exists (tv :: vs_tgt). esplits; eauto.
      econs; eauto.
  Qed.

  Lemma eval_lvalue_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
        exp blk_src ofs_src
        (EVAL: eval_lvalue ge_src env_src tenv_src m_src exp blk_src ofs_src)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists blk_tgt ofs_tgt,
        (<<EVAL: eval_lvalue ge_tgt env_tgt tenv_tgt m_tgt exp blk_tgt ofs_tgt>>) /\
        (<<INJ: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt)>>).
  Proof.
    exploit eval_expr_lvalue_inject; eauto. i. des. eauto.
  Qed.

  Definition match_loc j (loc_src loc_tgt: block * Z * Z): Prop :=
    match loc_src with
    | (blk_src, lo_src, hi_src) =>
      match loc_tgt with
      | (blk_tgt, lo_tgt, hi_tgt) =>
        exists delta,
        (<<DELTA: j blk_src = Some (blk_tgt, delta)>>) /\
        (<<LO: lo_src + delta = lo_tgt>>) /\
        (<<HI: hi_src + delta = hi_tgt>>)
      end
    end.

  Lemma free_list_parallel
        sm0 locs_src locs_tgt m_src1
        (MWF: SimMemInj.wf' sm0)
        (LOCS: list_forall2 (match_loc (SimMemInj.inj sm0)) locs_src locs_tgt)
        (FREE: Mem.free_list (SimMemInj.src sm0) locs_src = Some m_src1)
    :
      exists sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<FREE: Mem.free_list (SimMemInj.tgt sm0) locs_tgt = Some (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 locs_tgt m_src1 MWF LOCS FREE. induction locs_src; ss.
    - i. clarify. inv LOCS. esplits; eauto. refl.
    - i. inv LOCS. unfold match_loc in H1. des_ifs. des. clarify. ss.
      exploit SimMemInj.free_parallel; eauto. i. des. clarify.
      exploit IHlocs_src; eauto.
      { eapply list_forall2_imply; eauto. i. unfold match_loc in *. des_ifs.
        des. inv MLE. esplits; eauto. }
      i. des. clarify.
      esplits; eauto.
      + etrans; eauto.
      + ss. rewrite FREETGT. eauto.
  Qed.

  Lemma blocks_of_env_match j e_src e_tgt
        (ENV: match_env j e_src e_tgt)
    :
      list_forall2 (match_loc j) (blocks_of_env ge_src e_src) (blocks_of_env ge_tgt e_tgt).
  Proof.
    set (R:=(fun (d_src d_tgt: block * type) =>
               let (b_src, t_src) := d_src in
               let (b_tgt, t_tgt) := d_tgt in
               (<<INJ: j b_src = Some (b_tgt, 0)>>) /\
               (<<TYSAME: t_src = t_tgt>>))).
    exploit PTree.elements_canonical_order.
    - instantiate (1:=R).
      instantiate (1:=e_tgt).
      instantiate (1:=e_src).
      i. destruct (ENV i); des; clarify.
      esplits; eauto. ss.
    - i. destruct (ENV i); des; clarify.
      esplits; eauto. ss.
    - intros ALL.
      unfold blocks_of_env. revert ALL.
      generalize (PTree.elements e_tgt).
      generalize (PTree.elements e_src).
      induction l; ss; i.
      + inv ALL. econs.
      + inv ALL. ss. econs; eauto.
        unfold block_of_binding. des_ifs; ss; des; clarify.
        esplits; eauto.
        rewrite CENV. zsimpl. auto.
  Qed.

  Lemma find_label_match_none j lbl stmt K_src0 K_tgt0
        (LABEL: find_label lbl stmt K_src0 = None)
        (CONT: match_cont j K_src0 K_tgt0)
    :
      find_label lbl stmt K_tgt0 = None.
  Proof.
    revert K_src0 K_tgt0 LABEL CONT. induction stmt; ss; i.
    - des_ifs_safe. exploit IHstmt1; eauto.
      { econs; eauto. } intros LABEL0.
      rewrite LABEL0. eauto.
    - des_ifs_safe. exploit IHstmt1; eauto. intros LABEL0.
      exploit IHstmt2; eauto. intros LABEL1.
      rewrite LABEL0. eauto.
    - des_ifs_safe. exploit IHstmt1; eauto.
      { econs; eauto. } intros LABEL0.
      exploit IHstmt2; eauto.
      { econs; eauto. } intros LABEL1.
      rewrite LABEL0. eauto.
    - admit "mutual induction".
    - des_ifs. exploit IHstmt; eauto.
  Qed.

  Lemma find_label_match j lbl stmt K_src0 K_tgt0 stmt' K_src1
        (LABEL: find_label lbl stmt K_src0 = Some (stmt', K_src1))
        (CONT: match_cont j K_src0 K_tgt0)
    :
      exists K_tgt1,
        (<<LABEL: find_label lbl stmt K_tgt0 = Some (stmt', K_tgt1)>>) /\
        (<<CONT: match_cont j K_src1 K_tgt1>>)
  .
  Proof.
    revert K_src0 K_tgt0 stmt' K_src1 LABEL CONT. induction stmt; ss; i.
    - destruct (find_label lbl stmt1 (Kseq stmt2 K_src0)) eqn:LABEL0.
      + clarify. exploit IHstmt1; eauto.
        { econs; eauto. } i. des.
        rewrite LABEL. esplits; eauto.
      + exploit IHstmt2; eauto. i. des.
        exploit find_label_match_none; eauto.
        { econs; eauto. } intros LABEL2.
        rewrite LABEL1. rewrite LABEL2. esplits; eauto.
    - destruct (find_label lbl stmt1 (Kseq stmt2 K_src0)) eqn:LABEL0.
      + destruct p. exploit IHstmt1; eauto.
        { econs; eauto. } i. des.
  Admitted.

  Lemma clight_step_preserve_injection
        sm_arg u st_src0 st_tgt0 st_src1 sm0 tr
        (MATCH: match_states_clight sm_arg u st_src0 st_tgt0 sm0)
        (STEP: step se_src ge_src (function_entry ge_src) st_src0 tr st_src1)
    :
      exists st_tgt1 sm1,
        (<<STEP: step se_tgt ge_tgt (function_entry ge_tgt) st_tgt0 tr st_tgt1>>) /\
        (<<MATCH: match_states_clight sm_arg u st_src1 st_tgt1 sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>).
  Proof.
    inv STEP; inv MATCH.
    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit eval_lvalue_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exploit assign_loc_inject; eauto. i. des.
      rewrite CENV in *.
      esplits.
      + econs 1; eauto.
      + cinv MLE. econs; eauto.
        * eapply match_env_incr; eauto.
        * eapply match_temp_env_incr; eauto.
        * eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des. esplits.
      + econs 2; eauto.
      + econs; eauto.
        eapply set_match_temp_env; eauto.
      + refl.

    - cinv MWF. exploit eval_exprlist_inject; eauto. i. des.
      exploit eval_expr_inject; eauto. i. des. esplits.
      + econs 3; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - cinv MWF. exploit eval_exprlist_inject; eauto. i. des.
      admit "external call".

    - esplits.
      + econs 5; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 6; eauto.
      + econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 7; eauto.
      + econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 8; eauto.
      + econs; eauto.
      + refl.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit bool_val_inject; eauto. i. esplits.
      + econs 9; eauto.
      + econs; eauto.
      + refl.

    - esplits.
      + econs 10; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 11; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 12; eauto.
      + econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 13; eauto.
      + econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 14; eauto.
      + econs; eauto.
      + refl.

    - exploit free_list_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 15; eauto.
      + econs; eauto. eapply call_cont_match; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exploit free_list_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 16; eauto.
      + econs; eauto.
        * cinv MLE. eapply val_inject_incr; eauto.
        * eapply call_cont_match; eauto.
          cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit free_list_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 17; eauto.
        unfold is_call_cont in *. destruct CONT; clarify.
      + econs; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      assert (SWITCH: sem_switch_arg v_tgt (typeof a) = Some n).
      { unfold sem_switch_arg in *. inv INJ; ss; clarify; des_ifs. }
      esplits.
      + econs 18; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 19; eauto.
      + econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 20; eauto.
      + econs; eauto.
      + refl.

    - esplits.
      + econs 21; eauto.
      + econs; eauto.
      + refl.

    - exploit find_label_match; eauto.
      { eapply call_cont_match; eauto. } i. des.
      esplits.
      + econs 22; eauto.
      + econs; eauto.
      + refl.

    - assert (FPTRTGT: Genv.find_funct ge_tgt fptr_tgt = Some (Internal f)).
      { admit "genv". }
      exploit FUNCTIONENTRY; eauto. i. des.
      esplits.
      + econs 23; eauto.
      + econs; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - assert (FPTRTGT: Genv.find_funct ge_tgt fptr_tgt = Some (External ef targs tres cconv)).
      { admit "genv". }
      admit "external_call".

    - inv CONT. esplits.
      + econs 25; eauto.
      + econs; eauto. destruct optid; ss.
        eapply set_match_temp_env; eauto.
      + refl.
  Qed.
