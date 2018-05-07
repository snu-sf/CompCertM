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

Record t': Type := mk {
  kept: ident -> Prop;
  coverage: ident -> Prop;
  wf: kept <1= coverage;
}
.

Arguments mk kept coverage : clear implicits.

Inductive sim_sk (ss: t') (sk_src sk_tgt: Sk.t): Prop :=
| closed_intro
    (COVERAGE: (ss.(coverage) <1= sk_tgt.(privs)))
    (PRIVS: sk_tgt.(privs) <1= sk_src.(privs))
    (NOCOVER: forall
        id
        (PUBS: ~ ss.(coverage) id)
      ,
        <<SIM: sim_odef (sk_src.(prog_defmap) ! id) (sk_tgt.(prog_defmap) ! id)>>)
    (KEPT: forall
        id
        (KEPT: ss.(kept) id)
      ,
        <<EQ: sk_src.(prog_defmap) ! id = sk_tgt.(prog_defmap) ! id>>)
    (DROPPED: forall
        id
        (DROPPED: ~ ss.(kept) id)
      ,
        <<NONE: sk_tgt.(prog_defmap) ! id = None>>)
    (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
    (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
.

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (COVERAGE: ss.(coverage) <1= skenv_tgt.(skenv_privs))
    (PRIVS: skenv_tgt.(skenv_privs) <1= skenv_src.(skenv_privs))
    (SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          (* /\ <<KEPT: ss.(kept) id>> *)
    )
    (SIMSYMB2: forall
        id
        (KEPT: ss.(kept) id)
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
             (* /\ <<KEPT: ss.(kept) id>> *)
    )
.

Global Program Definition link_ss (ss0 ss1: t'): option t' :=
  Some (mk (ss0.(kept) \1/ ss1.(kept)) (ss0.(coverage) \1/ ss1.(coverage)) _)
.
Next Obligation.
  u; ii; ss.
  destruct ss0, ss1; ss.
  des; eauto.
Qed.

Global Program Instance Linker_t: Linker t' := {|
  link := link_ss;
  linkorder (ss0 ss1: t') := ss0.(kept) <1= ss1.(kept) /\ ss0.(coverage) <1= ss1.(coverage);
|}.
Next Obligation.
  ss. split; ss.
  - split; u; ii; ss; left; ss.
  - split; u; ii; ss; right; ss.
Qed.

Global Program Instance SimSymbKept: SimSymb.class SimMemInj := {
  t := t';
  coverage := coverage;
  (* kept := bot2; *)
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}
.
Next Obligation.
  admit "".
Qed.
Next Obligation.
  inv SIMSK.
  econs; eauto.
  - i.
    destruct ss; ss.
    destruct (classic (kept0 id)).
    + erewrite KEPT; eauto.
    + erewrite DROPPED in *; ss.
Qed.
Next Obligation.
  admit "".
Qed.
Next Obligation.
  admit "".
Qed.
Next Obligation.
  admit "".
Qed.
(* Next Obligation. *)
(*   inv SIMSKENV. *)
(*   econs; eauto. *)
(*   - i; ss. *)
(*     exploit SIMSYMB1; eauto. i; des. esplits; eauto. *)
(* Qed. *)
Next Obligation.
  inv SIMSKENV.
  inv LESRC. inv LETGT.
  econs; eauto.
  -
  - i. destruct ss; ss.
    inv SIMSK; ss.
    destruct (classic (defs sk_src id)); cycle 1.
    { erewrite NPROJ in *; ss. }
    exploit PROJ; eauto. i; des. rewrite BLKSRC in *.
    exploit SIMSYMB1; eauto. i; des.
    esplits; eauto.
    destruct (classic (kept0 id)).
    + erewrite <- PROJ0; eauto.
      { hnf in H. des. erewrite KEPT in *; ss. hnf. esplits; eauto. }
    + erewrite <- PROJ0; eauto.
      esplits; eauto.
    +
      exploit KEPT; eauto. i ;des.
      destruct sk_tgt.(prog_defmap) ! id eqn:T; cycle 1.
      { exfalso. destruct ss; ss.
      }
      exploit PROJ; eauto. i; des_safe.
      exploit PROJ0; eauto. i; des_safe.
      rewrite <- H1. eapply SIMSYMB1; eauto.
      rewrite BLKSRC in *. ss.
    + exploit NPROJ; eauto. i; des_safe. rewrite BLKSRC in *. ss.
  - i.
    destruct ss; ss.
    exploit PROJ; eauto.
    exploit SIMSYMB2; eauto.
Qed.
  inv SIMSKENV.
  econs; eauto.
  - i. eapply SIMSYMB1; eauto. ss. inv 
Qed.
Next Obligation.
  admit "".
Qed.

  inv SIMSK.
  econs; eauto.
  esplits; eauto. ss.
Qed.
Next Obligation.
  inv SIMSK.
  econs; ss; eauto.
  - admit "easy. pull out as lemma".
  - ii; ss.
    unfold match_program in *.
    generalize (Genv.globalenvs_match SIM); intro SIMGE.
    inv SIMGE.
    admit "this should hold.".
  - inv SIM. des. ss.
  - inv SIM. des. ss.
Qed.
Next Obligation.
  exists tt.
  split.
  - ss.
  - econs; eauto. inv CLOSED0. inv CLOSED1.
  admit "This should hold".
  Print TransfLink.
  (* exploit link_match_program; eauto. *)
Qed.
(* Next Obligation. *)
(*   inv CLOSED. clear_tac. *)
(*   assert(SIMID: forall id, (prog_defmap sk_src) ! id = (prog_defmap sk_tgt) ! id). *)
(*   { i. eapply NOCOVER; eauto. } clear NOCOVER. *)
(*   u. ss. *)
(*   econs; eauto. *)
(*   - admit "this should hold, if not, 1) add uniqueness condition on good_prog to make it hold. *)
(* 2) Replace Genv.globalenv with my_globalenv, which makes it unique". *)
(*   - intro id. *)
(*     specialize (SIMID id). *)
(*     generalize Genv.find_def_symbol. intro LEMMA. *)
(*     destruct ((prog_defmap sk_src) ! id) eqn:T. *)
(*     + eapply LEMMA in T. symmetry in SIMID. eapply LEMMA in SIMID. des. *)
(*       rewrite T. rewrite SIMID. ss. *)
(*     + *)
(*     admit "this should hold, if not, add uniqueness condition on good_prog to make it hold.". *)
(*     ss. *)
(* Qed. *)




Next Obligation.
  eexists (SimMemId.mk _ _).
  esplits; ss; eauto.
  u. inv SIMSK.
  Print Genv.init_mem_transf.
  Print Genv.init_mem_transf_partial.
  About Genv.init_mem_match.
  exploit (Genv.init_mem_match SIM); eauto. i. clarify.
  econs; eauto.
  - admit "easy; Genv.init_mem_genv_next".
  - i. admit "this should hold... Genv.find_symbol_match".
Qed.
(* Next Obligation. *)
(*   inv CLOSED. *)
(*   unfold match_program in *. *)
(*   generalize (Genv.globalenvs_match SIM); intro SIMGE. *)
(*   inv SIMGE. *)
(*   econs; eauto. *)
(* Qed. *)
Next Obligation.
  inv LESRC.
  inv LETGT.
  inv SIMSKENV.
  econs; eauto.
  - eq_closure_tac.
  - intro id.
    destruct (Classical_Prop.classic (pubs id)); cycle 1.
    + exploit NPROJ; eauto. { ii; des; eauto. } i; des.
      exploit NPROJ0; eauto. { ii; des; eauto. } i; des.
      eq_closure_tac. (* TODO: debug this *)
      rewrite H0. rewrite H1. ss.
    + exploit PROJ; eauto. i; des.
      exploit PROJ0; eauto. i; des.
      eq_closure_tac. (* TODO: debug this *)
      rewrite <- H0. rewrite <- H1.
      ss.
Qed.

