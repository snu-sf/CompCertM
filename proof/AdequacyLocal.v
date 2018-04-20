Require Import CoqlibC.
Require Import Simulation.
Require Import Skeleton.
Require Import Sem.
Require Import ModSem.
Require Import LinkingC.
Require Import Skeleton.
From Paco Require Import paco.
Require Import sflib.
Require Import SymbInj.

Require Import SimMem.
Require Import SimModSem.

Set Implicit Arguments.



Inductive sim_sk (si: symbinj) (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (CLOSED: symbinj_closed si sk_src sk_tgt)
    (PRIVATE: symbinj_private si sk_src sk_tgt)
.

Inductive Forall3 X Y Z (R: X -> Y -> Z -> Prop): list X -> list Y -> list Z -> Prop :=
| Forall3_nil: Forall3 R [] [] []
| Forall3_cons
    x y z
    xs ys zs
    (TAIL: Forall3 R xs ys zs)
  :
    Forall3 R (x :: xs) (y :: ys) (z :: zs)
.

Lemma Forall3_impl
      X Y Z
      (xs: list X) (ys: list Y) (zs: list Z)
      P Q
      (IMPL: P <3= Q)
      (FORALL: Forall3 P xs ys zs)
  :
    <<FORALL: Forall3 Q xs ys zs>>
.
Proof.
  admit "easy".
Qed.

Context `{Linker symbinj}.
Context `{SM: SimMem}.

(* Inductive sim_mod `{SM: SimMem} (si: symbinj) (m_src m_tgt: Mod.t): Prop := *)
(* | sim_mod_intro *)
(*     (SIMSK: sim_sk si m_src.(Mod.sk) m_tgt.(Mod.sk)) *)
(* . *)

Axiom sim_skenv: list symbinj -> SkEnv.t -> SkEnv.t -> Prop.
Axiom sim_modsem: symbinj -> ModSem.t -> ModSem.t -> Prop.


Inductive sim_modpair (mp: ModPair.t): Prop :=
| sim_intro
    (SIMSK: sim_sk mp.(si) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk))
    (WF: True) (* si is well-formed according to src/tgt. So that it can link with others *)
    (SIMMS: forall
        skenv_src skenv_tgt
        (SIMSKENV: respects mp.(si) skenv_src skenv_tgt)
      ,
        sim_modsem (mp.(si))
                   (mp.(src).(Mod.get_modsem) skenv_src mp.(src).(Mod.data))
                   (mp.(tgt).(Mod.get_modsem) skenv_tgt mp.(tgt).(Mod.data)))
.


Module ModSemPair.

  Record t: Type := {
    src: ModSem.t;
    tgt: ModSem.t;
    si: symbinj;
  }
  .

End ModSemPair.

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

  Section LINK_WFO.

    Variable (idx0 idx1: Type) (ord0: idx0 -> idx0 -> Prop) (ord1: idx1 -> idx1 -> Prop).

    Inductive embedded A B (ordA: A -> A -> Prop) (ordB: B -> B -> Prop): Prop :=
    | embedded_intro
        f
        (PRESERVING: forall
            a0 a1
            (ORDA: ordA a0 a1)
          ,
            <<ORDB: ordB (f a0) (f a1)>>)
    .

    Let idx := (idx0 + idx1)%type.

    Inductive ord: idx -> idx -> Prop :=
    | ord_introl
        idx0a idx0b
        (ORD0: ord0 idx0a idx0b)
      :
        ord (inl idx0a) (inl idx0b)
    | ord_intror
        idx1a idx1b
        (ORD1: ord1 idx1a idx1b)
      :
        ord (inr idx1a) (inr idx1b)
    .

    Theorem link_wfo
            
            (WF0: well_founded ord0)
            (WF1: well_founded ord1)
      :
        exists (idx: Type) (ord: idx -> idx -> Prop),
          <<EMBED0: embedded ord0 ord>> /\ <<EMBED1: embedded ord1 ord>> /\ <<WF: well_founded ord>>
    .
    Proof.
      exists idx, ord.
      esplits; eauto.
      - eapply embedded_intro with (f := inl). econs; eauto.
      - eapply embedded_intro with (f := inr). econs; eauto.
      - econs; eauto. i. inv H0.
        + generalize dependent idx0a. pattern idx0b. eapply well_founded_ind; eauto. clear idx0b. i.
          econs; eauto. i. inv H1.
          eapply H0; eauto.
        + generalize dependent idx1a. pattern idx1b. eapply well_founded_ind; eauto. clear idx1b. i.
          econs; eauto. i. inv H1.
          eapply H0; eauto.
    Qed.

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
