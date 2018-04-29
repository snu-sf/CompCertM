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




Section TMP.

  Context `{SS: SimSymb.class} `{SM: SimMem.class}.

  Goal True. Abort.
  (* TODO: SS and SS0. I want to avoid this, without adding "@" on SM. *)
  (* I think making SimMem.class' argument explicit should be easy, but I don't know how to do that *)

End TMP.





Module ProgPair.
Section PROGPAIR.
Context `{SS: SimSymb.class} `{SM: @SimMem.class SS}.

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




Section SIM.

  Context `{SS: SimSymb.class} `{SM: @SimMem.class SS}.

  Variable pp: ProgPair.t.
  Hypothesis SIMPROG: ProgPair.sim pp.
  Let p_src := pp.(ProgPair.src).
  Let p_tgt := pp.(ProgPair.tgt).



  Theorem sim_link_sk
          sk_link_src
          (LOADSRC: p_src.(link_sk) = Some sk_link_src)
    :
      exists sk_link_tgt, <<LOADTGT: p_tgt.(link_sk) = Some sk_link_tgt>>
  .
  Proof.
    u. subst_locals.
    ginduction pp; ii; ss.
    eapply link_list_cons_inv in LOADSRC. des.
    inv SIMPROG.
    exploit IHt; eauto.
    i; des.
    esplits; eauto.
    eapply link_list_cons; eauto.
    admit "TODO: Strengthen conclusion so that IH becomes stronger too. Somehow sk_src ~ sk_tgt".
  Unshelve.
    all: ss.
  Qed.

  Theorem sim_load
        sem_src
        (LOADSRC: sem p_src = Some sem_src)
    :
      exists sem_tgt, <<LOADTGT: sem p_tgt = Some sem_tgt>>
  .
  Proof.
    unfold sem in *.
    des_ifs_safe.
    exploit sim_link_sk; eauto. i; des.
    esplits; eauto. des_ifs.
  Qed.


End SIM.












