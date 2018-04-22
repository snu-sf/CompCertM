Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import SimSymb.
Require Import Integers.
Require Import ASTC.
Require Import Maps.

Require Import Syntax Sem Mod Pair ModSem SimMem SimModSem.

Set Implicit Arguments.






Section SIM.

  Context `{SS: SimSymb.class} `{SM: SimMem.class}.

  Inductive sim_modpair (mp: ModPair.t): Prop :=
  | intro_sim_modpair
      (WF: ModPair.wf mp)
      (SIMMS: forall
          skenv_src skenv_tgt
          (SIMSKENV: SimSymb.sim_skenv mp.(ModPair.ss) skenv_src skenv_tgt)
        ,
          sim_modsem
            (mp.(ModPair.src).(Mod.get_modsem) skenv_src mp.(ModPair.src).(Mod.data))
            (mp.(ModPair.tgt).(Mod.get_modsem) skenv_tgt mp.(ModPair.tgt).(Mod.data)))
  .

  Inductive sim_progpair (pp: ProgPair.t): Prop :=
  | intro_sim_modpairs
      (SIMMP: List.Forall sim_modpair pp)
  .

End SIM.





(* Inductive sim_sk (si: symbinj) (sk_src sk_tgt: Sk.t): Prop := *)
(* | sim_sk_intro *)
(*     (CLOSED: symbinj_closed si sk_src sk_tgt) *)
(*     (PRIVATE: symbinj_private si sk_src sk_tgt) *)
(* . *)


(*   Inductive sim_modpair (mp: ModPair.t): Prop := *)
(* | sim_intro *)
(*     (SIMSK: sim_sk mp.(si) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk)) *)
(*     (WF: True) (* si is well-formed according to src/tgt. So that it can link with others *) *)
(*     (SIMMS: forall *)
(*         skenv_src skenv_tgt *)
(*         (SIMSKENV: respects mp.(si) skenv_src skenv_tgt) *)
(*       , *)
(*         sim_modsem (mp.(si)) *)
(*                    (mp.(src).(Mod.get_modsem) skenv_src mp.(src).(Mod.data)) *)
(*                    (mp.(tgt).(Mod.get_modsem) skenv_tgt mp.(tgt).(Mod.data))) *)
(* . *)

 