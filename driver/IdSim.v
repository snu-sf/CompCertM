Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import Csem AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import Linking.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.

Set Implicit Arguments.


Lemma match_program_refl
      F V
      `{Linker F} `{Linker V}
      (prog: AST.program F V)
  :
    match_program (fun _ => eq) eq prog prog
.
Proof.
  econs; eauto.
  destruct prog; ss.
  ginduction prog_defs; ii; ss.
  { econs; eauto. }
  destruct a; ss.
  econs; eauto.
  - econs; eauto. ss. destruct g; ss.
    + econs; eauto. eapply linkorder_refl.
    + econs; eauto. destruct v; ss.
  - rpapply IHprog_defs; eauto.
    apply Axioms.functional_extensionality. i.
    destruct x; ss.
    apply Axioms.functional_extensionality. i.
    destruct x; ss.
    apply prop_ext. split; ii.
    + inv H1. ss. clarify. inv H3; econs; ss; eauto; econs; ss; eauto.
      apply linkorder_refl.
    + inv H1. ss. clarify. inv H3; econs; ss; eauto; econs; ss; eauto.
      apply linkorder_refl.
Unshelve.
  all: ss.
Qed.

Local Existing Instance Val.mi_normal.
Local Opaque Z.mul Z.add Z.sub Z.div.

Parameter C_module: Csyntax.program -> Mod.t.

Lemma genv_eq
      F V
      (ge1 ge2: Genv.t F V)
      (PUB: ge1.(Genv.genv_public) = ge2.(Genv.genv_public))
      (NEXT: ge1.(Genv.genv_next) = ge2.(Genv.genv_next))
      (SYMB: ge1.(Genv.genv_symb) = ge2.(Genv.genv_symb))
      (DEFS: ge1.(Genv.genv_defs) = ge2.(Genv.genv_defs))
  :
    ge1 = ge2
.
Proof.
  destruct ge1, ge2; ss. clarify.
  f_equal.
  - apply proof_irr.
  - apply proof_irr.
  - apply proof_irr.
Qed.

Lemma sim_skenv_eq
      skenv_link_src skenv_link_tgt
      (SKE: SimSymbId.sim_skenv skenv_link_src skenv_link_tgt)
  :
    skenv_link_src = skenv_link_tgt
.
Proof.
  inv SKE; ss.
  apply genv_eq; ss.
  -
Abort.



Local Existing Instance SimMemId.SimMemId | 0.
Local Existing Instance SimMemId.SimSymbId | 0.
Local Existing Instance SoundTop.Top | 0.

Lemma asm_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  econs; ss; eauto.
  { eapply SoundTop.sound_state_local_preservation; eauto. }
  ii; ss.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  (* hexploit (SimSymbId.sim_skenv_revive PROG). *)
  { i; ss. clarify. }
  (* { instantiate (1:= (SkEnv.project skenv_link_src (defs asm))). eauto. } *)
  (* { instantiate (1:= (SkEnv.project skenv_link_tgt (defs asm))). eauto. } *)
  (* { ss. } *)
  intro GENV; des.

  inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  fold fundef in *.
  split; ii; cycle 1.
  { des. exists st_init_src. inv SAFESRC. econs; ss; eauto.
    - unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. inv GENV.
      specialize (mge_defs b).
      Local Opaque SkEnv.revive SkEnv.project.
      unfold Genv.find_def in *. ss. rewrite Heq2 in *.
      inv mge_defs; ss; clarify.
      inv H1. ss.
    - etrans; eauto.
      admit "ez".
  }
  rename tgt into m0.
  rename st_init_tgt into st0.
  esplits; eauto.
  { instantiate (1:= st0). clear SAFESRC.
    inv INITTGT. econs; ss; eauto.
    + unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe. inv GENV.
      specialize (mge_defs b).
      Local Opaque SkEnv.revive SkEnv.project.
      unfold Genv.find_def in *. ss. rewrite Heq2 in *.
      inv mge_defs; ss; clarify.
      inv H1. ss.
    + etrans; eauto. admit "ez".
  }
  instantiate (1:= (SimMemId.mk m0 m0)). instantiate (1:= Ord.lift_idx unit_ord_wf tt).
  clear - GENV.
  generalize dependent st0.
  pcofix CIH. ii. pfold.
  destruct (classic ((modsem skenv_link_src asm).(ModSem.is_call) st0)).
  { ss. rr in H. des.
    econs 3; eauto.
    { econs; eauto. }
    ii. des. clear_tac.
    exists args_src. exists (SimMemId.mk args_src.(Args.m) args_src.(Args.m)). ss.
    esplits; eauto.
    { econs; ss; eauto. }
    { admit "ez". }
    ii. ss. des.
    esplits; eauto.
    admit "ez".
  }
  destruct (classic ((modsem skenv_link_src asm).(ModSem.is_return) st0)).
  { ss. rr in H0. des.
    dup H0. set (R:= retv). inv H0.
    econs 4; eauto.
    { instantiate (1:= SimMemId.mk m2 m2). ss. }
    { econs; eauto. }
    { ss. instantiate (1:= R). admit "ez". }
    { ss. }
  }
  econs 1; eauto.
  ii; des. clear_tac.
  esplits; eauto.
  econs; eauto; cycle 1.
  { admit "ez". }
  ii. ss. inv STEPSRC.
  esplits; eauto. left. apply plus_one. econs; eauto.
  { admit "ez". }
  econs; eauto. ss. admit "ez".
Unshelve.
  all: ss.
Qed.

Lemma asm_ext_top
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma asm_ext_unreach
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma asm_inj_id
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimMemInj.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma asm_inj_drop
      (tgt: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.






Lemma src_id
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_ext_top
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_ext_unreach
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_inj_id
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimMemInj.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma src_inj_drop
      (src: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInj.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = src.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = src.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.



Lemma lift
      `{SM: SimMem.class} `{@SimSymb.class SM} `{Sound.class}
      X (to_mod: X -> Mod.t)
      (MOD: forall x, exists mp,
            ModPair.sim mp /\ mp.(ModPair.src) = x.(to_mod) /\ mp.(ModPair.tgt) = x.(to_mod))
  :
    <<PROG: forall xs, exists pp,
        ProgPair.sim pp /\ ProgPair.src pp = map to_mod xs /\ ProgPair.tgt pp = map to_mod xs
                                                                                    >>
.
Proof.
  ii.
  induction xs; ii; ss.
  { esplits; eauto. }
  des.
  specialize (MOD a). des.
  exists (mp :: pp). esplits; ss; eauto with congruence.
Qed.

