From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require SimMemId SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon SIR SimSIR.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.

Local Open Scope signature_scope.



Inductive taus E R: itree E R -> nat -> Prop :=
| taus_tau
    itr0 n
    (TL: taus itr0 n)
  :
    taus (Tau itr0) (1 + n)
| taus_ret
    r
  :
    taus (Ret r) 0
| taus_vis
    X (e: E X) k
  :
    taus (Vis e k) 0
.

(* Definition mtaus E R (itr: itree E R) (n: nat): Prop := *)
(*   taus itr n /\ ~taus itr (S n) *)
(* . *)

(* Theorem case_analysis0 *)
(*         E R *)
(*         (itr: itree E R) *)
(*   : *)
(*     (<<CONVERGE: exists (m: nat), mtaus itr m>>) *)
(*     \/ (<<DIVERGE: forall m, ~mtaus itr m>>) *)
(* . *)
(* Proof. *)
(*   destruct (classic (exists m, mtaus itr m)); et. *)
(*   right. *)
(*   ii. *)
(*   eapply Classical_Pred_Type.not_ex_all_not with (n:=m) in H. Psimpl. *)
(*   des; et. *)
(* Qed. *)

(* Lemma taus_antitone *)
(*       E R *)
(*       (itr: itree E R) *)
(*       n m *)
(*       (LE: (n <= m)%nat) *)
(*   : *)
(*     <<TAUS: taus itr m -> taus itr n>> *)
(* . *)
(* Proof. *)
(*   ginduction LE; ii; ss. *)
(*   inv H. *)
(*   exploit IHLE; et. ii. *)
(*   ii. *)
(* Qed. *)

Lemma unfold_spin
      E R
  :
    (@ITree.spin E R) = tau;; ITree.spin
.
Proof.
  rewrite itree_eta_ at 1. cbn. refl.
Qed.

Lemma spin_no_ret
      E R
      r
      (SIM: @ITree.spin E R ≈ Ret r)
  :
    False
.
Proof.
  punfold SIM.
  r in SIM. cbn in *.
  dependent induction SIM; ii; clarify.
  - eapply IHSIM; ss.
Qed.

Lemma spin_no_vis
      E R
      X (e: E X) k
      (SIM: @ITree.spin E R ≈ Vis e k)
  :
    False
.
Proof.
  punfold SIM.
  r in SIM. cbn in *.
  dependent induction SIM; ii; clarify.
  - eapply IHSIM; ss.
Qed.





Theorem diverge_spin
        E R
        (itr: itree E R)
        (DIVERGE: forall m, ~taus itr m)
  :
    <<SPIN: itr = ITree.spin>>
.
Proof.
  r. f.
  revert_until R.
  ginit.
  gcofix CIH. i. gstep.
  rewrite unfold_spin.
  ides itr; swap 2 3.
  { contradict DIVERGE. ii. eapply H. econs; et. }
  { contradict DIVERGE. ii. eapply H. econs; et. }
  econs; eauto.
  gbase. eapply CIH. ii. eapply DIVERGE. econs; eauto.
Qed.

Theorem spin_diverge
        E R
        (itr: itree E R)
        (SPIN: itr = ITree.spin)
  :
    <<DIVERGE: forall m, ~taus itr m>>
.
Proof.
  ii. clarify.
  ginduction m; ii; ss.
  { inv H.
    - rewrite unfold_spin in *. ss.
    - rewrite unfold_spin in *. ss.
  }
  inv H.
  rewrite unfold_spin in *. ss. clarify. eauto.
Qed.

Theorem case_analysis
        E R
        (itr: itree E R)
  :
    (<<CONVERGE: exists (m: nat), taus itr m>>)
    \/ (<<DIVERGE: itr = ITree.spin>>)
.
Proof.
  destruct (classic (exists m, taus itr m)); et.
  right.
  eapply diverge_spin.
  ii.
  eapply Classical_Pred_Type.not_ex_all_not with (n:=m) in H. Psimpl.
  des; et.
Qed.



Theorem spin_spin
        E R
        (i_src i_tgt: itree E R)
        (SPIN: i_src = ITree.spin)
        (SIM: i_src ≈ i_tgt)
  :
    <<SPIN: i_tgt = ITree.spin>>
.
Proof.
  clarify.
  r. f.
  revert_until R.
  ginit.
  gcofix CIH. i. gstep.
  rewrite unfold_spin.
  ides i_tgt; swap 2 3.
  { apply spin_no_ret in SIM. ss. }
  { apply spin_no_vis in SIM. ss. }
  econs; eauto.
  gbase. eapply CIH. rewrite tau_eutt in SIM. ss.
Qed.



(*** TODO: Move to Ord.v ***)
Section LEXICO.

  Variable (idxh idxl: Type) (ordh: idxh -> idxh -> Prop) (ordl: idxl -> idxl -> Prop).

  Definition idx_lex := (idxh * idxl)%type.

  Inductive ord_lex: idx_lex -> idx_lex -> Prop :=
  | ord_lex_high
      idxh0 idxh1 idxl0 idxl1
      (ORDH: ordh idxh0 idxh1):
      ord_lex (idxh0, idxl0) (idxh1, idxl1)
  | ord_lex_low
      idxh idxl0 idxl1
      (ORDL: ordl idxl0 idxl1):
      ord_lex (idxh, idxl0) (idxh, idxl1).

  Theorem ord_lex_wf
          (WF0: well_founded ordl)
          (WF1: well_founded ordh):
      <<WF: well_founded ord_lex>>.
  Proof.
    assert(ACC: forall h, Acc ordh h -> forall l, Acc ordl l -> Acc ord_lex (h, l)).
    {
      induction 1.
      induction 1.
      econs. i. inv H3.
      - eauto.
      - eauto.
    }
    rr. i. destruct a. eapply ACC; eauto.
  Qed.

End LEXICO.




(* Lemma sim_st_ord_mon *)
(*       owned_heap_src owned_heap_tgt R *)
(*       (SO: owned_heap_src -> owned_heap_tgt -> Prop) *)
(*       idx (ord: idx -> idx -> Prop) *)
(*       clo g r *)
(*       i0 i1 *)
(*       (itr_src: itree (eff0 owned_heap_src) R) *)
(*       (itr_tgt: itree (eff0 owned_heap_tgt) R) *)
(*       (ORD: ord i0 i1) *)
(*   : *)
(*     gpaco3 (_sim_st SO ord) clo g r i0 <2= gpaco3 (_sim_st SO ord) clo g r i0 *)
(* . *)
(* Proof. *)
(*   revert_until i0. revert i0. *)
(*   gcofix CIH. i. *)
(*   gunfold PR. *)
(*   induction PR; ii; ss. *)
(*   - des. *)
(*     + gstep. inv IN. econs; eauto. *)
(* Qed. *)










Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let itr := itree (E owned_heap) (owned_heap * (mem * val)).

Definition match_itr: relation itr := fun i_src i_tgt => i_src ≈ i_tgt.

Let fn := function owned_heap.

Definition match_fn: relation (function owned_heap) := (eq ==> eq ==> eq ==> match_itr).

Definition match_prog: relation (program owned_heap) := (eq ==> option_rel match_fn).

End SYNTAX.
Hint Unfold match_itr match_fn match_prog.









Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
  Hypothesis (SIMP: match_prog p_src p_tgt).

  Lemma match_itr_glue
        i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      (interp_mrec (interp_function p_src) i_src) ≈ (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    eapply Proper_interp_mrec; eauto.
    ii.
    destruct a. cbn. rr in SIMP. exploit (@SIMP name); et. intro R. inv R.
    - refl.
    - eapply H1; ss.
  Qed.

  Lemma glued_sim_st
        (i_src i_tgt: itree (eff0 owned_heap) (owned_heap * (mem * val)))
        (SIM: i_src ≈ i_tgt)
    :
      sim_st eq (ord_lex lt lt) (2%nat, 0%nat) i_src i_tgt
  .
  Proof.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    revert_until SIMP.
    gcofix CIH. i.

    generalize (case_analysis i_src); intro T0.
    generalize (case_analysis i_tgt); intro T1.
    des; swap 1 3.
    { sym in SIM. eapply spin_spin in SIM; ss. des.
      exploit spin_diverge; try apply CONVERGE; et. i; ss. }
    { eapply spin_spin in SIM; ss. des.
      exploit spin_diverge; try apply CONVERGE; et. i; ss. }
    - (* both finite taus *)
      generalize (@bot3 (idx_lex nat nat) (fun _ : idx_lex nat nat => SIR.state owned_heap)
       (fun (_ : idx_lex nat nat) (_ : SIR.state owned_heap) => SIR.state owned_heap)) as q.
      i.

      gstep. econsr; cycle 1.
      { instantiate (1:= (1%nat, m)). econs; et. }
      move m at top.
      revert_until CIH.
      induction m; i.
      +
        gstep. econsr; cycle 1.
        { instantiate (1:= (0%nat, m0)). econs; et. }
        move m0 at top.
        revert_until CIH.
        induction m0; i.
        * inv CONVERGE; inv CONVERGE0.
          { punfold SIM; inv SIM; ss. gstep. destruct r0 as [oh [m vs]]. econs; eauto. }
          { punfold SIM; inv SIM; ss. }
          { punfold SIM; inv SIM; ss. }
          { punfold SIM.
            remember (Vis e0 k0) as itr0 in *.
            remember (Vis e k) as itr1 in *.
            inv SIM; ss. simpl_depind. clarify.
            r in e. destruct e.
            - destruct e; ss. gstep. econs; eauto. ii. rr in H. des_ifs. des; clarify.
              gbase. eapply CIH. pclearbot. eapply REL.
            - destruct e; ss.
              + gstep. econs; eauto.
              + gstep. econs; eauto.
              + gstep. eapply sim_st_choose.
                { right. ss. }
                ii. hexploit (REL x_tgt); et. i. pclearbot.
                esplits; eauto with paco.
          }
        * inv CONVERGE0.
          rewrite tau_eutt in SIM.
          exploit IHm0; eauto. i.
          gstep. econs; eauto.
          { econs 2; eauto. }
      + inv CONVERGE.
        rewrite tau_eutt in SIM.
        exploit IHm; eauto. i.
        gstep. econs; eauto.
        { econs 2; eauto. }
    - (* both infinite taus *)
      clarify.
      rewrite unfold_spin. gstep. econs; eauto. gbase. eauto.
  Qed.

  Lemma match_prog_sim_st
        i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st eq (ord_lex lt lt) (2%nat, 0%nat)
             (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    eapply match_itr_glue in SIM.
    eapply glued_sim_st in SIM.
    eauto.
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh
    ,
      (<<SIM: sim_st eq (ord_lex lt lt) (2%nat, 0%nat)
                     (interp_program p_src (ICall fname oh m vs))
                     (interp_program p_tgt (ICall fname oh m vs))
                     >>)
  .
  Proof.
    {
      ii.
      eapply match_prog_sim_st; ss.
      hexploit (@SIMP fname); et. intro T. inv T; ss.
      { r. refl. }
      repeat (spc H1). exploit H1; ss; et.
    }
  Qed.

  Variable ioh: SkEnv.t -> owned_heap.
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh).

  Theorem sim_mod: ModPair.sim (SimSymbId.mk_mp (SIR.module sk p_src mi ioh)
                                                (SIR.module sk p_tgt mi ioh)).
  Proof.
    ii. econs; ss; eauto.
    ii. rr in SIMSKENVLINK. clarify. esplits. eapply sim_modsem with (SO:=eq); et.
    { eapply ord_lex_wf; eapply lt_wf. }
    ii. clarify. esplits. eapply adequacy_local_local; et.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold match_itr match_fn match_prog.
