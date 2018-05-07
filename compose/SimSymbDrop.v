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
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimDef SimSymb.
Require Import SimMem.
Require Import SimMemInj.


(* TODO: move to CoqlibC. *)
Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Tactic Notation "u" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Tactic Notation "u" := repeat (autounfold with *; cbn).
Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in *).




(* Definition t': Type := ident -> bool. *)
Definition t': Type := ident -> Prop.

Inductive sim_sk (ss: t') (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (KEPT: forall
        id
        (KEPT: ~ ss id)
      ,
       sk_tgt.(prog_defmap) ! id = sk_src.(prog_defmap) ! id)
    (DROP: forall
        id
        (DROP: ss id)
      ,
        sk_tgt.(prog_defmap) ! id = None)
    (* (SIMSK: forall *)
    (*     id *)
    (*   , *)
    (*    sk_tgt.(prog_defmap) ! id = if ss id then None else sk_src.(prog_defmap) ! id) *)
    (CLOSED: ss <1= sk_src.(privs))
    (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
    (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
.

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          /\ <<KEPT: ~ ss id>>
    )
    (SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\
           <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>)
    (SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>
           /\ <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>
             (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    )
    (SIMDEF: forall
          blk_src blk_tgt delta def_tgt
          (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
          (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
        ,
          exists def_src, <<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>> /\
                          <<DELTA: delta = Ptrofs.zero>> /\
                          <<SIM: sim_def def_src def_tgt>>)
.

Inductive le (ss0: t') (sk_src sk_tgt: Sk.t) (ss1: t'): Prop :=
| le_intro
    (LE: ss0 <1= ss1)
    (OUTSIDE: forall
        id
        (IN: (ss1 -1 ss0) id)
      ,
        <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
.

Global Program Definition link_ss (ss0 ss1: t'): option t' :=
  (* Some (fun id => orb (ss0 id) (ss1 id)) *)
  Some (ss0 \1/ ss1)
.

Global Program Instance Linker_t: Linker t' := {|
  link := link_ss;
  linkorder (ss0 ss1: t') := ss0 <1= ss1;
|}.

Global Program Instance sim_def_PreOrder: RelationClasses.PreOrder sim_def.
Next Obligation.
  admit "easy".
Qed.
Next Obligation.
  admit "easy".
Qed.



Global Program Instance SimSymbDrop: SimSymb.class SimMemInj := {
  t := t';
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}
.
(* Next Obligation. *)
(*   inv SIMSK. *)
(*   econs; eauto. *)
(*   ii. *)
(*   destruct (classic (ss id)). *)
(*   - erewrite DROP in *; eauto. ss. *)
(*   - erewrite <- KEPT; ss. *)
(*     esplits; eauto. *)
(*     reflexivity. *)
(* Qed. *)
Next Obligation.
  admit "See 'link_match_program' in Unusedglobproof.v.
Note that we have one more goal (exists ss) but it is OK, as the 'link_match_program' proof already proves it.".
Qed.
Next Obligation.
  admit "See 'init_meminj_preserves_globals' in Unusedglobproof.v".
Qed.
Next Obligation.
  admit "The proof must exist in Unusedglobproof.v. See match_stacks_preserves_globals, match_stacks_incr".
Qed.
Next Obligation.
(* THIS IS TOP *)
  inv SIMSKENV. ss.
  econs; eauto; ii; ss.
  -
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    exploit SIMSYMB1; eauto. { rewrite <- KEEP. ss. } i; des.

    inv LETGT.
    destruct (classic (defs sk_tgt id)); cycle 1.
    { erewrite SYMBDROP0; ss.
      exfalso.
      clear - LE KEPT H H0 SIMSK.
      inv SIMSK.
      apply H0.
      u.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss.
      - exfalso. apply KEPT. inv LE. eauto.
    }
    erewrite SYMBKEEP0; ss.
    esplits; eauto.
    {
      clear - LE H0 KEPT.
      inv LE.
      ii. apply KEPT.
      apply NNPP. ii.
      exploit OUTSIDE; eauto. { split; eauto. }
    }
  -
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    exploit SIMSYMB2; eauto.
    { ************ Somehow we need to know: ss_link - ss are all outside of sk_src. }
    esplits; eauto.
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
Qed.

