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
Require Import LinkingC.

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

  Lemma sim_load_mod
        mp0 mp1
        (SIM0: sim_modpair mp0)
        (SIM1: sim_modpair mp1)
        sk_src
        (LINKSRC: link mp0.(ModPair.src).(Mod.sk) mp1.(ModPair.src).(Mod.sk) = Some sk_src)
    :
      exists sk_tgt,
        <<LINKTGT: link mp0.(ModPair.tgt).(Mod.sk) mp1.(ModPair.tgt).(Mod.sk) = Some sk_tgt>>
  .
  Proof.
    Local Transparent Linker_prog.
    ss.
    Local Opaque Linker_prog.
    unfold Sk.t in *.
    exploit (@link_prog_inv (fundef (option signature)) unit); eauto. intro SPEC.
    inv SIM0. inv SIM1. clear SIMMS SIMMS0. inv WF. inv WF0.

    {
      exploit (link_prog_succeeds mp0.(ModPair.tgt).(Mod.sk) mp1.(ModPair.tgt).(Mod.sk)); eauto.
        inv SPEC. des. congruence.
      - intros ? ? ? TGT0 TGT1.
        exploit closed_def_bsim; try apply TGT0; eauto. intro SRC0.
        exploit closed_def_bsim; try apply TGT1; eauto. intro SRC1.
        inv SPEC.
        exploit BOTHHIT; eauto. i; des.
        esplits; eauto; try congruence.
    }

    Print link_prog_check.
  Qed.

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

 