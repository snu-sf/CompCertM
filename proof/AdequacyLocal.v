Require Import CoqlibC.
Require Import Simulation.
Require Import Skeleton.
Require Import Sem.
Require Import ModSem.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.
Require Import JMeq.

Require Import SimDef SimSymb SimMem SimMod SimModSem SimProg SimLoad.
Require Import Smallstep.

Set Implicit Arguments.


Section ADEQUACYSTEP.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).
  Variable rp: RTL.program.
  Let rsem := (RTL.semantics rp).
  Compute rsem.(state).
  Let sem_src := Sem.semantics p_src.
  Let sem_tgt := Sem.semantics p_tgt.
  Compute sem_src.(state).
  Variable index: Type.
  Variable ord: index -> index -> Prop.

  Print Frame.t.
  (* Record t : Type := mk *)
  (* { ms : ModSem.t;  st : ModSem.state ms;  sg_init : option signature;  rs_init : Asmregs.regset } *)

  Inductive lxsim_tail: sem_src.(state) -> sem_tgt.(state) -> SimMem.t -> Prop :=
  | lxsim_stack_nil
      i0 sm0
    :
      lxsim_stack i0 [] [] sm0
  | lxsim_stack_cons
      tail_st_src0 tail_st_tgt0 tail_sm_init
      (STACK: lfsim_tail tail_st_src0 tail_st_tgt0 tail_sm_init)
      ms_src ms_tgt
      (K: forall
          ms_src ms_tgt lst_src lst_tgt sm1 retv0 retv1
          rs_ret_src rs_ret_tgt m_ret_src m_ret_tgt
          (MEMLE: SimMem.le (SimMem.lift) sm1)
          (MEMWF: SimMem.wf sm1)
          (RETSRC: ms_src.(ModSem.final_frame) sg_init_src rs_init_src lst_src rs_ret_src m_ret_src)
          (RETTGT: ms_tgt.(ModSem.final_frame) sg_init_tgt rs_init_tgt lst_tgt rs_ret_tgt m_ret_tgt)
          (RETRSREL: sm1.(SimMem.sim_regset) rs_ret_src rs_ret_tgt)
        ,
          exists i0, lxsim _ _ _ _ )
  .



Inductive lfsim_stack (s1: L1@lang_state) (s2: L2@lang_state): t -> Prop :=
| lfsim_stack_nil: forall mrel0
    (SRCINIT: L1.(initial_state) (ProgramState s1 mrel0.(src_mem)))
    (TGTINIT: L2.(initial_state) (ProgramState s2 mrel0.(tgt_mem))),
    lfsim_stack s1 s2 mrel0
| lfsim_stack_cons: forall s10 s20 mrel0_init mrel0
    (STACK: lfsim_stack s10 s20 mrel0_init)
    (LOCAL: forall mrel1 v1 v2 s1' s2'
              (MEMINV: le (lift mrel0) mrel1)
              (VALID: valid mrel1)
              (SRCRET: L1@final_state_local
                         (ProgramState s1 (lift mrel0).(src_mem))
                         (ProgramState s1' mrel1.(src_mem)) v1)
              (TGTRET: L2@final_state_local
                         (ProgramState s2 (lift mrel0).(tgt_mem))
                         (ProgramState s2' mrel1.(tgt_mem)) v2)
              (RETVALREL: val_rel mrel1 v1 v2),
        forall i', _lfsim_step L1 L2 order
                               (local_forward_sim L1 L2 order mrel0_init s10 s20)
                               (unlift mrel0 mrel1) i' s1' s2'),
    lfsim_stack s1 s2 (lift mrel0)
.

Inductive lfsim_lift (mrel: t) (i: index) (s1: L1@lang_state) (s2: L2@lang_state): Prop :=
| lfsim_lift_intro s1_init s2_init mrel_init
    (STACK: lfsim_stack s1_init s2_init mrel_init)
    (LOCAL: local_forward_sim L1 L2 order mrel_init s1_init s2_init mrel i s1 s2)
.


  Inductive match_states: index -> sem_src.(state) -> sem_tgt.(state) -> SimMem.t -> Prop :=
  | match_states_nil
      i0 sm0
    :
      match_states i0 [] [] sm0
  | match_states_cons
      i_tl st_tl_src st_tl_tgt sm_tl
      (TLMATCH: match_states i_tl st_tl_src st_tl_tgt sm_tl)
      ms_src ms_tgt ss
      (SIM: ModSemPair.sim (ModSemPair.mk ms_src ms_tgt ss ord))
      st_hd_src st_hd_tgt
      sg_init_src sg_init_tgt rs_init_src rs_init_tgt
      i0 sm0 sm_init
      (HDMATCH: lxsim ms_src ms_tgt ord sg_init_src sg_init_tgt rs_init_src rs_init_tgt
                      sm_init i0 st_hd_src st_hd_tgt sm0)
      (LE: SimMem.le sm_tl sm_init
    :
      match_states i_tl st_tl_src st_tl_tgt sm_tl
  .

End ADEQUACYSTEP.


Section ADEQUACY.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).

  Theorem adequacy_local
          sem_src
          (LOADSRC: load p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: load p_tgt = Some sem_tgt>> /\ <<SIM: mixed_simulation sem_src sem_tgt>>
  .
  Proof.
    (* exploit sim_load; eauto. i; des. *)
    subst_locals. unfold load in *. des_ifs_safe.
    exploit sim_link_sk; eauto. i; des. des_ifs_safe. clarify.
    rename t into sk_src. rename sk_link_tgt into sk_tgt.
    esplits; eauto.


    exploit sim_progpair_sim_loadpair; eauto. i; des.
    assert(LPSIM := SIM).
    inv SIM.
    econs; eauto.
    econs; eauto.

    eapply xsim_init_forward; ss.
    ii. inv INITSRC. clarify.
    exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. clarify.
    exploit find_fptr_owner_bsim; eauto.
    { instantiate (2:= (Genv.symbol_address (Sk.load_skenv sk_src) (prog_main sk_src) Integers.Ptrofs.zero)).
      instantiate (1:= (Genv.symbol_address (Sk.load_skenv sk_tgt) (prog_main sk_tgt) Integers.Ptrofs.zero)).
      admit "main ptr should be related. obligate this to sim_skenv". }
    { admit "???". }
    { unfold LoadPair.ge_src. unfold load_genv, load_modsems in MSFIND.
      admit "???".
    }
    i; des.

    esplits; eauto.
    - econs; ss; eauto.
      + admit "".
      + admit "determinacy".
    -

    ii.
    inv ujjj
    eapply xsim_init_backward; ss.
    {
      ii. inv INITSRC. clarify.
      exploit SimSymb.sim_sk_load_sim_skenv; eauto. i; des. clarify.
      exploit find_fptr_owner_bsim; eauto.
      { instantiate (2:= (Genv.symbol_address (Sk.load_skenv sk_src) (prog_main sk_src) Integers.Ptrofs.zero)).
        instantiate (1:= (Genv.symbol_address (Sk.load_skenv sk_tgt) (prog_main sk_tgt) Integers.Ptrofs.zero)).
        admit "main ptr should be related. obligate this to sim_skenv". }
      { }
      esplits; eauto. econs; ss; eauto.
      -
      admit "progress".
    }


    exploit sim_progpair_sim_gepair; eauto. i; des. ss.
    esplits; eauto. clarify.
    inv SIM; ss.
    econstructor 1 with (order := gep.(GePair.ord)); eauto.
    econs; eauto.
    eapply xsim_init_backward; ss.
    { (* progress *)
      i. inv INITSRC. ss.
      inv MSFIND. ss.
      unfold Genv.symbol_address in *. des_ifs.
      Print SimSymb.sim_sk_weak.
      apply SimSymb.sim_sk_sim_sk_weak in SIMSK.
      admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!".
    }
    { (* init *)
      i. inv INITTGT.
      rename ms into ms_tgt.
      assert(exists ms_src, <<SIMMS: sim_modsem order ms_src ms_tgt>>).
      { admit "". } i; des.
      inv SIMMS.
      inv MSFIND.
      unfold Genv.symbol_address in *. des_ifs.
      rename Heq0 into MAINTGT. rename blk into blk_tgt. rename m into m_tgt. rename INITMEM into MEMTGT.
      (* assert(exists blk_tgt m_tgt sm0, *)
      (*           <<WF: SimMem.wf sm0>> *)
      (*           /\ <<MEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt>> *)
      (*           /\ <<MAINTGT: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_tgt>> *)
      (*           /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>> *)
      (*           /\ <<MCOMPAT: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>). *)
      assert(exists blk_src m_src sm0,
                <<WF: SimMem.wf sm0>>
                /\ <<MEMSRC: sk_src.(Sk.load_mem) = Some m_src>>
                /\ <<MAINSRC: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_src>>
                /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>>
                /\ <<MCOMPAT: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>).
      { admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!". }
      i; des.

      hexploit SIM; eauto.
      { instantiate (1:= None). instantiate (1:= None). econs 2; eauto. }
      { instantiate (1:= (Asmregs.Pregmap.init Vundef)). instantiate (1:= (Asmregs.Pregmap.init Vundef)).
        admit "undef sim_val".
      }
      i; des.
      exploit STEP; eauto.
      { rewrite MCOMPAT0. eauto. }
      i; des.
      esplits; eauto.
      esplits; eauto.
      rename m into m_tgt.
      rename st_init into st_init_tgt.
      rename ms into ms_tgt.
      rename INITSK into INITSKTGT.
      rename INITMEM into INITMEMTGT.
      inv MSFIND. ss. clarify.
      rename MODSEM into MODSEMTGT.
      rename 
    }
    { (* init *)
      i. inv INITSRC. inv MSFIND. ss. clarify.
      unfold Genv.symbol_address in *. des_ifs.
      rename Heq into MAINSRC. rename blk into blk_src. rename m into m_src. rename INITMEM into MEMSRC.
      assert(exists blk_tgt m_tgt sm0,
                <<MEMTGT: sk_tgt.(Sk.load_mem) = Some m_tgt>>
                /\ <<MAINTGT: Genv.find_symbol (Sk.load_skenv sk_src) (prog_main sk_src) = Some blk_tgt>>
                /\ <<SIMFPTR: SimMem.sim_block sm0 blk_src blk_tgt>>
                /\ <<SIMMS: sm0.(SimMem.src_mem) = m_src /\ sm0.(SimMem.tgt_mem) = m_tgt>>).
      { admit "sim_skenv should have some info################!!!!!!!!!!!!!!!!!!!!". }
      des.
      esplits; eauto.
    }
    i. ss.
    tttttttttttttttttttttttt
    exploit sim_load; eauto. i; des.
    esplits; eauto.

    unfold sem in *. des_ifs. rename t into init_sk_tgt. rename t0 into init_sk_src.
    inv SIMPROG.
    inv SIMMOD. admit "".
    assert(Forall2 sim_modsem
    assert(exists wfo, 
    econs; eauto.
    econs; eauto.
    (* Each modsem has mixed sim *)

    assert(Forall3 sim_modsem p_src p_tgt).
    eapply Forall3_impl with (Q:= const sim_modsem) in SIMMOD.
    
  Qed.


End ADEQUACY.


Context `{Linker symbinj}.
Context `{SM: SimMem}.

(* Inductive sim_mod `{SM: SimMem} (si: symbinj) (m_src m_tgt: Mod.t): Prop := *)
(* | sim_mod_intro *)
(*     (SIMSK: sim_sk si m_src.(Mod.sk) m_tgt.(Mod.sk)) *)
(* . *)

Axiom sim_skenv: list symbinj -> SkEnv.t -> SkEnv.t -> Prop.
Axiom sim_modsem: symbinj -> ModSem.t -> ModSem.t -> Prop.



Inductive sim_prog (p_src p_tgt: program): Prop :=
| sim_prog_intro
    sis
    (SIMMOD: Forall3 sim_mod sis p_src p_tgt)
    si_prog
    (LINKSI: link_list sis = Some si_prog)
    (SIMMS: forall
        skenv_src skenv_tgt
        (SIMSKENV: sim_skenv sis skenv_src skenv_tgt)
      ,
        Forall2 (fun m_src m_tgt => sim_modsem (m_src.(Mod.get_modsem) skenv_src m_src.(Mod.data))
                                               (m_tgt.(Mod.get_modsem) skenv_tgt m_tgt.(Mod.data))) p_src p_tgt)
.

Section TRANSF.

  Variable p: program.

End TRANSF.

Section ADEQUACY.

  Variable p_src p_tgt: program.
  Hypothesis SIMPROG: sim_prog p_src p_tgt.

    Theorem xsim_properties_embedded
            L1 L2
            (EMBEDDED: embedded ord0 ord1)
            (XSIM: xsim_properties L1 L2 idx0 ord0)
      :
        <<XSIM: xsim_properties L1 L2 idx1 ord1>>
    .
    Proof.
      admit "easy".
    Qed.

  End LINK_WFO.

  Lemma sim_load
        sem_src
        (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold sem in *.
    des_ifs.
    { esplits; eauto. }
    exfalso.
    unfold init_sk in *.
    admit "".
  Qed.

  Theorem adequacy_machine
          sem_src
          (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>> /\ <<SIM: mixed_simulation sem_src sem_tgt>>
  .
  Proof.
    exploit sim_load; eauto. i; des.
    esplits; eauto.

    unfold sem in *. des_ifs. rename t into init_sk_tgt. rename t0 into init_sk_src.
    inv SIMPROG.
    inv SIMMOD. admit "".
    assert(Forall2 sim_modsem
    assert(exists wfo, 
    econs; eauto.
    econs; eauto.
    (* Each modsem has mixed sim *)

    assert(Forall3 sim_modsem p_src p_tgt).
    eapply Forall3_impl with (Q:= const sim_modsem) in SIMMOD.
    
  Qed.

End ADEQUACY.
