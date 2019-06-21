Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem.
Require Import Sound.
Require Import SimSymb SimMem SimModSem.

Set Implicit Arguments.







Module ModPair.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    SM:> SimMem.class;
    SS:> SimSymb.class SM;
    ss: SimSymb.t;
    wf:= SimSymb.sim_sk ss src.(Mod.sk) tgt.(Mod.sk)
  }
  .

  Reset t. (* Need to state SS = SS in SimMem... JMEQ THINGS !!!!!!!!!!!!! *)

Section MODPAIR.
Context `{SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    ss: SimSymb.t;
  }
  .

  Definition to_msp (mp: t) (skenv_link_src skenv_link_tgt: SkEnv.t) (sm: SimMem.t)
             (sidx: Type)
             (sound_states: sidx -> Sound.t -> mem -> (Mod.modsem (mp.(src)) skenv_link_src).(ModSem.state) -> Prop)
    : ModSemPair.t :=
    ModSemPair.mk (Mod.modsem (mp.(src)) skenv_link_src) (Mod.modsem (mp.(tgt)) skenv_link_tgt) mp.(ss)
                                            sm sound_states
  .

  (* TODO: Actually, ModPair can have idx/ord and transfer it to ModSemPair. *)
  (* Advantage: We can unify ord at Mod state. *)
  Inductive sim (mp: t): Prop :=
  | sim_intro
      (SIMSK: SimSymb.sim_sk mp.(ss) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk))
      (SIMMS: forall
          skenv_link_src skenv_link_tgt
          (INCLSRC: SkEnv.includes skenv_link_src mp.(src).(Mod.sk))
          (INCLTGT: SkEnv.includes skenv_link_tgt mp.(tgt).(Mod.sk))
          (WFSRC: SkEnv.wf skenv_link_src)
          (WFTGT: SkEnv.wf skenv_link_tgt)
          ss_link
          (SSLE: SimSymb.le mp.(ss) mp.(src) mp.(tgt) ss_link)
          sm_init_link
          (SIMSKENVLINK: SimSymb.sim_skenv sm_init_link ss_link skenv_link_src skenv_link_tgt)
        ,
          exists sidx (sound_states: sidx -> Sound.t -> mem -> (Mod.modsem (mp.(src)) skenv_link_src).(ModSem.state) -> Prop),
            <<SIMMSP: ModSemPair.sim (to_msp mp skenv_link_src skenv_link_tgt sm_init_link sound_states)>>)
  .

  (* Design: ModPair only has data, properties are stated in sim *)

End MODPAIR.
End ModPair.

Hint Unfold ModPair.to_msp.


