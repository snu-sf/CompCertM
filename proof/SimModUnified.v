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
Require Import SimSymb SimMem SimModSemUnified.

Set Implicit Arguments.







Module ModPair.

Section MODPAIR.
Context `{SMOS: SimMemOhs.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    ss: SimSymb.t;
  }.

  Definition to_msp (midx: Midx.t)
             (skenv_link_src skenv_link_tgt: SkEnv.t) (sm: SimMem.t) (mp: t)
    : ModSemPair.t
    := ModSemPair.mk (Mod.modsem (mp.(src)) midx skenv_link_src)
                     (Mod.modsem (mp.(tgt)) midx skenv_link_tgt) mp.(ss) sm.

  (* TODO: Actually, ModPair can have idx/ord and transfer it to ModSemPair. *)
  (* Advantage: We can unify ord at Mod state. *)
  Inductive sim (mp: t): Prop :=
  | sim_intro
      (SIMSK: SimSymb.wf mp.(ss))
      (SKSRC: mp.(ss).(SimSymb.src) = (Mod.sk mp.(src)))
      (SKTGT: mp.(ss).(SimSymb.tgt) = (Mod.sk mp.(tgt)))
      (SIMMS: forall midx skenv_link_src skenv_link_tgt ss_link sm_init_link
          (INCLSRC: SkEnv.includes skenv_link_src (Mod.sk mp.(src)))
          (INCLTGT: SkEnv.includes skenv_link_tgt (Mod.sk mp.(tgt)))
          (WFSRC: SkEnv.wf skenv_link_src)
          (WFTGT: SkEnv.wf skenv_link_tgt)
          (SSLE: SimSymb.le mp.(ss) ss_link)
          (SIMSKENVLINK: SimSymb.sim_skenv sm_init_link ss_link skenv_link_src skenv_link_tgt),
          <<SIMMSP: ModSemPair.sim (to_msp midx skenv_link_src skenv_link_tgt
                                           sm_init_link mp)>>).
  (* TODO: quantifying "exists SMO" here looks somewhat dirty... *)
  (* I would like to quantify it directly inside "sim_intro", but I need to put it here because *)
  (* I need to know "owned_heap" type which needs to know "skenv_link_src,tgt". *)
  (* It gives me feeling like "owned_heap" type differs as "skenv_link_src,tgt" changes. *)
  (* We can fix this by putting "owned_heap" in Mod.t, not ModSem.t. *)
  (* TODO: the same goes for "state" too. *)

  (* Design: ModPair only has data, properties are stated in sim *)

End MODPAIR.
End ModPair.

Hint Unfold ModPair.to_msp.