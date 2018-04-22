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

Require Import Syntax Mod ModSem SimSymb.

Set Implicit Arguments.


(* TODO: name? *)
Inductive closed `{SimSymb.class} (ss: SimSymb.t) (sk_src sk_tgt: Sk.t): Prop :=
| closed_intro
    (WF: SimSymb.wf ss)
    (INSRC: ss.(SimSymb.privs) <1= sk_src.(defs))
    (INTGT: ss.(SimSymb.privs) <1= sk_tgt.(defs))
    (PUBS: forall
        id
        (PUBS: ~ ss.(SimSymb.privs) id)
      ,
        <<EQ: PTree.get id sk_src.(prog_defmap) = PTree.get id sk_tgt.(prog_defmap)>>)
.


Module ModPair.

  Record t: Type := {
    src: Mod.t;
    tgt: Mod.t;
    SS:> SimSymb.class;
    ss: SimSymb.t;
    wf:= closed ss src.(Mod.sk) tgt.(Mod.sk)
  }
  .

  Reset t. (* Need to state SS = SS in SimMem... JMEQ THINGS !!!!!!!!!!!!! *)

  Record t `{SimSymb.class}: Type := {
    src: Mod.t;
    tgt: Mod.t;
    ss: SimSymb.t;
    wf:= closed ss src.(Mod.sk) tgt.(Mod.sk)
  }
  .

  (* Change sim_modsem to be sensitive to si. *)
  (* Only when initial memory is respecting si, it can guarantee something. *)
  (* Q: Can we encode it inside SM? *)

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

























(* Module ModSemPair. *)

(*   Record t: Type := { *)
(*     src: ModSem.t; *)
(*     tgt: ModSem.t; *)
(*     si: symbinj; *)
(*     (* TODO: unify closed & private *) *)
(*     closed: symbinj_closed si src tgt; *)
(*     private: symbinj_private si src tgt; *)
(*     (* TODO: which unary/binary property it expects *) *)
(*     (* TODO: analysis *) *)
(*   } *)
(*   . *)

(* End ModSemPair. *)


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

