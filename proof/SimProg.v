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

Require Import Syntax Sem Mod ModSem.
Require Import SimMem SimModSem SimMod.

Set Implicit Arguments.





Module ProgPair.
Section PROGPAIR.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.

  Definition t := list ModPair.t.
  (* Record t := mk { *)
  (*   src: list Mod.t; *)
  (*   tgt: list Mod.t; *)
  (*   sss: list SimSymb.t; *)
  (* } *)
  (* . *)

  Definition sim (pp: t) := List.Forall ModPair.sim pp.

  Definition src (pp: t): program := List.map ModPair.src pp.
  Definition tgt (pp: t): program := List.map ModPair.tgt pp.

  Definition ss_link (pp: t): option SimSymb.t := link_list (List.map ModPair.ss pp).
  (* ############ TODO: *)
  (* ModPair.wf mp0 /\ ModPair.wf mp1 /\ link mp0.(src) mp1.(src) = Some /\ link mp1.(tgt) mp1.(tgt) = Some *)
  (* =================> link mp0.(ss) mp1.(ss) suceeds. *)
  (* Move ModPair.wf into SimSymb and obligate its proof? *)

End PROGPAIR.
End ProgPair.

Hint Unfold ProgPair.sim ProgPair.src ProgPair.tgt ProgPair.ss_link.



(* Section SIMSK. *)

(*   Context `{SS: SimSymb.class} `{SM: @SimMem.class SS}. *)

(*   Inductive sim_sk (ss_link: SimSymb.t) (sk_src sk_tgt: Sk.t): Prop := *)
(*   | sim_sk_intro *)
(*   . *)

(* End SIMSK. *)



Section SIM.
Context `{SM: SimMem.class} {SS: SimSymb.class SM}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).



  Theorem sim_link_sk
          sk_link_src
          (LOADSRC: p_src.(link_sk) = Some sk_link_src)
    :
      exists ss_link sk_link_tgt,
        <<LOADTGT: p_tgt.(link_sk) = Some sk_link_tgt>>
        /\ <<LINKSS: pp.(ProgPair.ss_link) = Some ss_link>> 
        /\ <<SIMSK: SimSymb.sim_sk ss_link sk_link_src sk_link_tgt>>
  .
  Proof.
    u. subst_locals.
    ginduction pp; ii; ss.
    eapply link_list_cons_inv in LOADSRC. des.
    inv SIMPROG.
    exploit IHt; eauto. intro IH; des.
    inv H1.
    rename sk_link_src into sk_link_link_src.
    rename restl into sk_link_src.
    exploit SimSymb.sim_sk_weak_enables_link; eauto.
    { eapply SimSymb.sim_sk_sim_sk_weak; eauto. }
    { eapply SimSymb.sim_sk_sim_sk_weak; eauto. }
    i; des.
    exploit SimSymb.link_preserves_sim_sk; [exact SIMSK|exact IH1|..]; eauto. i; des.
    esplits; eauto.
    - eapply link_list_cons; eauto.
    - eapply link_list_cons; eauto.
  Qed.

  Corollary sim_load
        sem_src
        (LOADSRC: load p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: load p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold load in *.
    des_ifs_safe.
    exploit sim_link_sk; eauto. i; des.
    esplits; eauto. des_ifs.
  Qed.


End SIM.












