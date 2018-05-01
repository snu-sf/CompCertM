Require Import CoqlibC.
Require Import Simulation.
Require Import Skeleton.
Require Import Sem.
Require Import ModSem.
Require Import LinkingC.
Require Import Skeleton.
Require Import Values.

Require Import SimDef SimSymb SimMem SimMod SimModSem SimProg SimGe.

Set Implicit Arguments.



Section ADEQUACY.

  Context `{SS: SimSymb.class}.
  Context `{SM: SimMem.class}.

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
    exploit sim_progpair_sim_gepair; eauto. i; des. ss.
    esplits; eauto. clarify.
    inv SIM; ss.
    econstructor 1 with (order := order); eauto.
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
