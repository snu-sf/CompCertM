Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem SimMem SimSymb.

Set Implicit Arguments.





Lemma closed_def_bsim
      `{SimSymb.class}
      ss sk_src sk_tgt
      (CLOSED: closed ss sk_src sk_tgt)
      id gd
      (DEFTGT: sk_tgt.(prog_defmap) ! id = Some gd)
  :
    <<DEFSRC: sk_src.(prog_defmap) ! id = Some gd>>
.
Proof.
  inv CLOSED.
  destruct (classic (ss.(SimSymb.coverage) id)).
  - destruct (classic (ss.(SimSymb.kept) id)).
    + exploit KEPT; eauto. intro EQ. rewrite EQ. ss.
    + exploit NOKEPT; eauto. i. congruence.
  - exploit NOCOVER; eauto. i. congruence.
Qed.



Module ModPair.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    SS:> SimSymb.class;
    ss: SimSymb.t;
    wf:= closed ss src.(Mod.sk) tgt.(Mod.sk)
  }
  .

  Reset t. (* Need to state SS = SS in SimMem... JMEQ THINGS !!!!!!!!!!!!! *)

Section MODPAIR.
Context `{SS: SimSymb.class}.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    ss: SimSymb.t;
  }
  .

  Inductive wf `{SimSymb.class} (mp: t): Prop :=
  | wf_intro
      (CLOSED: closed mp.(ss) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk))
      (PUB: mp.(src).(Mod.sk).(prog_public) = mp.(tgt).(Mod.sk).(prog_public))
      (MAIN: mp.(src).(Mod.sk).(prog_main) = mp.(tgt).(Mod.sk).(prog_main))
  .
  (* Design: ModPair only has data, properties are stated in sim_modpair *)

  (* Change sim_modsem to be sensitive to si. *)
  (* Only when initial memory is respecting si, it can guarantee something. *)
  (* Q: Can we encode it inside SM? *)

End MODPAIR.
End ModPair.


(* Module ModPair. *)

(*   Record t: Type := { *)
(*     src: Mod.t; *)
(*     tgt: Mod.t; *)
(*     si: symbinj; *)
(*     (* TODO: unify closed & private *) *)
(*     closed: symbinj_closed si src tgt; *)
(*     private: symbinj_private si src tgt; *)
(*     (* TODO: which unary/binary property it expects *) *)
(*     (* TODO: analysis *) *)
(*   } *)
(*   . *)

(*   (* Change sim_modsem to be sensitive to si. *) *)
(*   (* Only when initial memory is respecting si, it can guarantee something. *) *)
(*   (* Q: Can we encode it inside SM? *) *)

(* End ModPair. *)


























Module ProgPair.
Section PROGPAIR.
Context `{SS: SimSymb.class}.

  Definition t := list ModPair.t.

  Definition wf (pp: t) := List.Forall ModPair.wf pp.

  Definition src (pp: t): program := List.map ModPair.src pp.
  Definition tgt (pp: t): program := List.map ModPair.tgt pp.

  Definition ss_link (pp: t): option SimSymb.t := link_list (List.map ModPair.ss pp).
  (* ############ TODO: *)
  (* ModPair.wf mp0 /\ ModPair.wf mp1 /\ link mp0.(src) mp1.(src) = Some /\ link mp1.(tgt) mp1.(tgt) = Some *)
  (* =================> link mp0.(ss) mp1.(ss) suceeds. *)
  (* Move ModPair.wf into SimSymb and obligate its proof? *)

End PROGPAIR.
End ProgPair.





































Module ModSemPair.
Section MODSEMPAIR.

(* Context `{SS: SimSymb.class} `{SM: SimMem.class}. *)
  Record t : Type := mk {
    src: ModSem.t;
    tgt: ModSem.t;
    idx: Type;
    order: idx -> idx -> Prop;
    (* TODO: which unary/binary property it expects *)
    (* TODO: analysis *)
  }
  .

End MODSEMPAIR.
End ModSemPair.















Module GePair.
Section GEPAIR.

Context `{SS: SimSymb.class} `{SM: SimMem.class}.
  Record t: Type := mk {
    skenv_src: SkEnv.t;
    skenv_tgt: SkEnv.t;
    ss: SimSymb.t;
    msps: list ModSemPair.t;
  }
  .

  Definition src (gep: t): Ge.t := (Ge.mk gep.(skenv_src) (List.map (ModSemPair.src) gep.(msps))).
  Definition tgt (gep: t): Ge.t := (Ge.mk gep.(skenv_tgt) (List.map (ModSemPair.tgt) gep.(msps))).

End GEPAIR.
End GePair.

