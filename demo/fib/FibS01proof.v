Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSemExcl.
Require SoundTop.
Require SimMemId.
Require Import Any.
Require Import SIR.
Require Import FibHeader.
Require Import FibS0.
Require Import FibS1.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.


(* Axiom sim_st_trans: forall *)
(*     owned_heap *)
(*     st0 st1 st2 (i0 i1 i2: unit) *)
(*     (SIM: sim_st (@eq owned_heap) bot2 i0 st0 st1) *)
(*     (SIM: sim_st (@eq owned_heap) bot2 i1 st1 st2) *)
(*   , *)
(*     <<SIM: sim_st (@eq owned_heap) bot2 i2 st1 st2>> *)
(* . *)
Let sim_st: nat -> state owned_heap -> state owned_heap -> Prop := (sim_st (@eq owned_heap) lt).
Axiom sim_st_trans: Transitive (sim_st 0%nat).
Local Existing Instance sim_st_trans.
Require Import Morphisms.
Local Open Scope signature_scope.

Inductive bindC (r: nat -> state owned_heap -> state owned_heap -> Prop):
  nat-> state owned_heap -> state owned_heap -> Prop :=
| bindC_intro
    i_src i_tgt
    n m
    (SIM: sim_st n i_src i_tgt)
    k_src k_tgt
    (SIMK: (eq ==> (r m%nat)) k_src k_tgt)
  :
    bindC r (n + m)%nat (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindC: core.

Lemma bindC_spec
      simC
  :
    bindC <4= gupaco3 (_sim_st (@eq owned_heap) lt) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold SIM. inv SIM.
  - rewrite ! bind_ret_l. gfinal. right. pclearbot. admit "add index drop".
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    gfinal. left. eapply CIH. econs; eauto.
  - rewrite ! bind_vis. gstep. econs; eauto. ii.
    exploit SIM0; et. i; des. pclearbot.
    rr in H. des_ifs. des. clarify. eauto with paco.
  - irw. gfinal. right. pfold. econs; et.
  - irw. gfinal. right. pfold. econs; et.
  - irw. gfinal. right.
    pfold. econs; et. ii. exploit SIM0; et. i; des_safe. pclearbot. esplits; et.
  - irw. gfinal. right. des. pclearbot.
    pfold. econs; et. esplits; et.
  - irw. gfinal. right. pclearbot.
    pfold. econs; et. ii. exploit SIM0; et.
  - irw. gfinal. right. pclearbot.
    pfold. econs; et; try xomega.
  - irw. gfinal. right. pclearbot.
    pfold. econs; et; try xomega.
  - irw. gfinal. right. pclearbot.
    pfold. econs; et; try xomega.
Qed.

Global Instance sim_st_bind: Proper ((eq ==> sim_st 0%nat) ==> (sim_st 0%nat) ==> (sim_st 0%nat))
                                    (ITree.bind').
Proof.
  red. ginit.
  { intros. eapply cpn3_wcompat; eauto with paco. }
  guclo bindC_spec. ii. change 0%nat with (0 + 0)%nat. econs; et.
  u. ii.
  exploit H0; et. i. eauto with paco.
Qed.

Ltac my_tac := 
  repeat match goal with
         | [ |- context[interp_function ?H] ] =>
           let name := fresh "x" in set (name := (interp_function H)) in *
         end
.

Lemma interp_bind: forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> itree F T) 
                          (t : itree E R) (k : R -> itree E S),
    interp f (` x : _ <- t;; k x) = ` r : R <- interp f t;; interp f (k r)
.
Proof.
  ii. f. apply interp_bind.
Qed.

Lemma interp_mrec_bind: forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
                               (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof.
  ii. f. eapply interp_mrec_bind.
Qed.



Lemma unfold_fib: forall oh0 m0 vs0,
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
      ≈
      (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      guarantee (parse_arg oh0 m0 vs0) ;;
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      guarantee (parse_arg oh1 m1 vs1) ;;
      '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh1 m1 vs1)) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
    end
      )
.
Proof.
  {
    i. irw.
    unfold FibS0.f_fib at 2. irw.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. irw. ITreelib.f_equiv. ii. ss. }
    irw. destruct n.
    { irw. refl. }
    destruct n.
    { irw. refl. }
    destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1.
    { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw. ITreelib.f_equiv. ii; ss. }
    unfold guarantee. des_ifs_safe. irw. rewrite tau_eutt.
    des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    (*** TODO: I just want to use "f_equiv". The problem here is that I added
`Require Import Morphisms.` after importing `ITreelib`.
Solution is to import `Morphisms` inside ITreelib.
***)
    { refl. }
    ii. des_ifs; cycle 1.
    { irw. unfold triggerNB. irw. ITreelib.f_equiv. ii; ss. }
    rewrite ! bind_ret_l.
    rewrite interp_mrec_bind. ITreelib.f_equiv.
    { irw. rewrite tau_eutt. des_ifs. refl. }
    { ii. des_ifs. irw. refl. }
  }
Qed.



Goal forall oh0 m0 vs0,
    (interp_mrec (interp_function prog) (f_fib oh0 m0 vs0)) ≈
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
.
Proof.
  ii.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS0.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.
  destruct n; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  rewrite unfold_fib. unfold unwrapU, parse_arg. rewrite T. ss. rewrite bind_ret_l.
  assert(U: to_nat_opt (of_nat n) = Some n).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. rewrite U. ss. des_ifs_safe. rewrite bind_ret_l.
  assert(V: to_nat_opt (of_nat (S n)) = Some (S n)).
  { admit "should be derived from guarantee". }
  des_ifs. unfold guarantee. rewrite V. ss. des_ifs.
  setoid_rewrite <- H; cycle 1.
  { instantiate (1:= n). eauto. }
  { ss. }
  unfold f_fib. unfold unwrapU. rewrite unfold_interp_mrec. ss. des_ifs.
  rewrite ! bind_ret_l. ss.
  rewrite unfold_interp_mrec. ss. rewrite ! bind_ret_l.
  rewrite <- H; cycle 1.
  { instantiate (1:= S n). eauto. }
  { ss. }
  unfold f_fib. ss. rewrite V. ss. rewrite bind_ret_l.
  rewrite unfold_interp_mrec. ss. rewrite bind_ret_l. refl.
Qed.

(* Lemma unfold_fib: forall oh0 m0 vs0, *)
(*     (mrec (interp_function FibS0.prog) (ICall Fib0._fib oh0 m0 vs0)) *)
(*       ≈ *)
(*       (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;; *)
(*     match n with *)
(*     | O => Ret (oh0, (m0, (Vint Int.zero))) *)
(*     | S O => Ret (oh0, (m0, (Vint Int.one))) *)
(*     | S (S m) => *)
(*       let vs0 := [Vint (of_nat m)] in *)
(*       guarantee (parse_arg oh0 m0 vs0) ;; *)
(*       '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;; *)

(*       let vs1 := [Vint (of_nat (S m))] in *)
(*       guarantee (parse_arg oh1 m1 vs1) ;; *)
(*       '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;; *)

(*       Ret (oh2, (m2, Vint (of_nat (fib_nat n)))) *)
(*     end *)
(*       ) *)
(* . *)
(* Proof. *)
(*   { *)
(*     i. rewrite mrec_as_interp. irw. *)
(*     unfold FibS0.f_fib at 2. irw. *)
(*     unfold unwrapU. des_ifs; cycle 1. *)
(*     { unfold triggerUB. irw. f_equiv. ii. ss. } *)
(*     irw. destruct n. *)
(*     { irw. refl. } *)
(*     destruct n. *)
(*     { irw. refl. } *)
(*     destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1. *)
(*     { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw. f_equiv. ii; ss. } *)
(*     unfold guarantee. des_ifs_safe. irw. rewrite tau_eutt. *)
(*     des_ifs_safe. *)
(*     rewrite <- unfold_interp_mrec. *)
(*     Fail rewrite interp_bind. *)
(*   } *)
(* Qed. *)

Goal forall oh0 m0 vs0,
    (interp_mrec (interp_function prog) (f_fib oh0 m0 vs0)) ≈
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
.
Proof.
  ii.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS0.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  ginduction n; ii; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  unfold f_fib, FibS0.f_fib. ss. rewrite T. ss. irw.
  assert(U: to_nat_opt (of_nat n)).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. des_ifs_safe. irw.
  rewrite tau_eutt. des_ifs.
  exploit (IHn oh0 m0 [Vint (of_nat n)]); eauto.
  { admit "should be derived from guarantee". }
  intro IH0. unfold f_fib in IH0. irw in IH0. unfold unwrapU in IH0. des_ifs. irw in IH0. clear_tac.
Abort.





















Lemma unfold_fib2: forall oh0 m0 vs0,
    sim_st 0%nat (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
      (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      guarantee (parse_arg oh0 m0 vs0) ;;
      tau;;
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      guarantee (parse_arg oh1 m1 vs1) ;;
      tau;;
      '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh1 m1 vs1)) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
    end
      )
.
Proof.
  {
    i. irw.
    unfold FibS0.f_fib at 2. irw.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. irw. pfold. econs; et. }
    irw. destruct n.
    { irw. pfold. econs; et. }
    destruct n.
    { irw. pfold. econs; et. }
    destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1.
    { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw. pfold. econs; et. }
    unfold guarantee. des_ifs_safe. irw. pfold. econs; et. left.
    des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. f_equiv; cycle 1.
    { (*** TODO: prove reflexive, or we may just use rtc of sim_st ***)
      admit "refl".
    }
    ii. des_ifs; cycle 1.
    { irw. unfold triggerNB. irw. pfold. econs; et. }
    rewrite ! bind_ret_l.
    rewrite interp_mrec_bind. irw. pfold. econs; et. left. f_equiv.
    { ii. clarify. irw. des_ifs. ss. pfold. econs; et. }
    { des_ifs. irw. admit "refl". }
  }
Qed.

Lemma unfold_fib3: forall oh0 m0 vs0,
    (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0))
    =
    (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;;
    match n with
    | O => Ret (oh0, (m0, (Vint Int.zero)))
    | S O => Ret (oh0, (m0, (Vint Int.one)))
    | S (S m) =>
      let vs0 := [Vint (of_nat m)] in
      guarantee (parse_arg oh0 m0 vs0) ;;
      tau;;
      '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;;

      let vs1 := [Vint (of_nat (S m))] in
      guarantee (parse_arg oh1 m1 vs1) ;;
      tau;;
      '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh1 m1 vs1)) ;;

      Ret (oh2, (m2, Vint (of_nat (fib_nat n))))
    end
      )
.
Proof.
  {
    i. irw.
    unfold FibS0.f_fib at 2. irw.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. irw. f_equiv. f_equiv. apply func_ext1. ii; ss. }
    irw. destruct n.
    { irw. refl. }
    destruct n.
    { irw. refl. }
    destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1.
    { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw.
      f_equiv. f_equiv. apply func_ext1. ii; ss. }
    unfold guarantee. des_ifs_safe. irw.
    f_equiv. f_equiv. des_ifs_safe.
    rewrite <- ! unfold_interp_mrec.
    rewrite interp_mrec_bind. f_equiv. apply func_ext1.
    ii. des_ifs; cycle 1.
    { irw. unfold triggerNB. irw. f_equiv. f_equiv. apply func_ext1. ii; ss. }
    rewrite ! bind_ret_l.
    rewrite interp_mrec_bind. irw. f_equiv. f_equiv. f_equiv. apply func_ext1. ii. des_ifs. irw. refl.
  }
Qed.

Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SIREutt.correct; ss.
  ii. clarify. rr.
  unfold FibS0.prog in *. ss. des_ifs.
  ii. clarify.
  rename y into oh0. rename y0 into m0. rename y1 into vs0.
  destruct (parse_arg oh0 m0 vs0) eqn:T; cycle 1.
  { unfold f_fib, FibS0.f_fib. ss.
    unfold unwrapU. des_ifs. unfold triggerUB. irw. r.
    ITreelib.f_equiv. ii. ss. (*** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! nice ***)
  }
  ginduction n; ii; ss.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  destruct n.
  { unfold parse_arg in *. des_ifs. unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw. refl. }
  unfold parse_arg in T. des_ifs.
  unfold f_fib, FibS0.f_fib. ss. r. rewrite T. ss. irw.
  assert(U: to_nat_opt (of_nat n)).
  { admit "should be derived from guarantee". }
  unfoldr guarantee. des_ifs_safe. irw.
Abort.



Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SimSIR.correct; ss.
  econs; try apply unit_ord_wf; ss.
  ii. clarify. exists tt.
  r.
  destruct (ident_eq fname Fib0._fib); cycle 1.
  { unfold interp_program, mrec. irw. des_ifs. irw. pfold. econs; et. }
  clarify.
  destruct (parse_arg oh_tgt m vs) eqn:T; cycle 1.
  { unfold interp_program, mrec. irw. des_ifs.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    unfold unwrapU. des_ifs. irw. pfold; econs; et.
  }
  clear_tac.
  ginduction n; ii; ss.
  { unfold parse_arg in *. des_ifs. irw.
    unfold interp_program, mrec. irw. des_ifs.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    irw. unfold to_nat_opt in *. des_ifs. irw. des_ifs. irw. pfold. econs; et. }
  unfold parse_arg in T. des_ifs_safe.
  unfold interp_program, mrec. irw. des_ifs.
  unfold f_fib at 2. unfold FibS0.f_fib at 2. irw.
  my_tac. unfold unwrapU. des_ifs. irw.
  des_ifs.
  { pfold. econs; et. }
  rewrite ! range_to_nat; cycle 1.
  { admit "int reasoning". }
  { admit "int reasoning". }
  unfold guarantee. des_ifs; cycle 1. clear_tac.
  irw.
  assert(BDOOR: forall E R (it: itree E R), (tau;; it) = it).
  { admit "". }
  rewrite BDOOR.
  des_ifs.
  rewrite <- unfold_interp_mrec.
Abort.



Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SimSIR.correct; ss.
  econs; try apply unit_ord_wf; ss.
  ii. clarify. exists tt.
  r. unfold interp_program, mrec. irw.
  destruct (ident_eq fname Fib0._fib); cycle 1.
  { des_ifs. irw. pfold. econs; et. }
  clarify. des_ifs. clear_tac.
  repeat match goal with
  | [ |- context[interp_function ?H] ] =>
    let name := fresh "x" in set (name := (interp_function H)) in *
  end
  .
  unfold f_fib. irw.
  unfold FibS0.f_fib. irw.
  unfold unwrapU. des_ifs; cycle 1.
  { irw. pfold. econs; et. }
  rename Heq into T.
  irw.
  revert T.
  revert oh_tgt.
  revert vs.
  revert m.
  induction n; ii; ss.
  { unfold parse_arg in *. des_ifs. irw. pfold. econs; et. }
  unfold parse_arg in *. des_ifs_safe.
  destruct n.
  { irw. pfold. econs; et. }
  eapply sim_st_trans; cycle 1.
  {
Abort.
