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




(*** TODO: remove redundancy with Fib56proof ***)
(* Section WFOPTION. *)

(*   Variable idx: Type. *)
(*   Variable ord: idx -> idx -> Prop. *)
(*   Hypothesis WF: well_founded ord. *)

(*   Let idx_option: Type := option idx. *)
(*   Inductive ord_option: idx_option -> idx_option -> Prop := *)
(*   | ord_option_some *)
(*       i0 i1 *)
(*       (ORD: ord i0 i1) *)
(*     : *)
(*       ord_option (Some i0) (Some i1) *)
(*   . *)

(*   Theorem wf_option: well_founded ord_option. *)
(*   Proof. *)
(*     ii. *)
(*     induction a; ii; ss. *)
(*     { pattern a. eapply well_founded_ind; et. clear a; i. *)
(*       econs; et. ii. inv H0. eapply H; et. } *)
(*     { econs. ii. inv H. } *)
(*   Qed. *)

(* End WFOPTION. *)








(* Axiom sim_st_trans: forall *)
(*     owned_heap *)
(*     st0 st1 st2 (i0 i1 i2: unit) *)
(*     (SIM: sim_st (@eq owned_heap) bot2 i0 st0 st1) *)
(*     (SIM: sim_st (@eq owned_heap) bot2 i1 st1 st2) *)
(*   , *)
(*     <<SIM: sim_st (@eq owned_heap) bot2 i2 st1 st2>> *)
(* . *)
(* Local Existing Instance sim_st_trans. *)

(* Let sim_st: option nat -> state owned_heap -> state owned_heap -> Prop := *)
(*   (sim_st (@eq owned_heap) (option_rel lt)). *)

Let sim_st: nat -> state owned_heap -> state owned_heap -> Prop := (sim_st (@eq owned_heap) lt).


(* Axiom sim_st_trans: Transitive (sim_st 0%nat). *)
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

Global Instance sim_st_Reflexive n: Reflexive (sim_st n).
Proof.
  rr. revert n.
  ginit.
  { intros. eapply cpn3_wcompat; eauto with paco. }
  gcofix CIH. ii. gstep.
  ides x.
  - destruct r0 as [oh [m vs]]. econs; et.
  - econs; et. eauto with paco.
  - destruct e.
    + destruct e. econs; et. ii. rr in H. des_ifs. des; clarify. eauto with paco.
    + destruct e.
      * econs.
      * econs.
      * econs; et. ii. esplits; et. eauto with paco.
Unshelve.
  all: ss.
Qed.

Definition rclo: (state owned_heap) -> (state owned_heap) -> Prop :=
  rtc ((sim_st 0%nat) \2/ eutt eq).

Inductive rtcn A (R: A -> A -> Prop): forall (n:nat) (a1 a2:A), Prop :=
| rtcn_nil
    a:
    rtcn R 0 a a
| rtcn_cons
    a1 a2 a3 n
    (A12: R a1 a2)
    (A23: rtcn R n a2 a3):
    rtcn R (S n) a1 a3
.
Hint Constructors rtcn.

Lemma rtcn_rtc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtc R a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma rtc_rtcn A (R: A -> A -> Prop) a1 a2
      (RTC: rtc R a1 a2):
  exists n, rtcn R n a1 a2.
Proof.
  induction RTC; eauto. i. des.
  esplits; eauto.
Qed.

Definition rcloN: nat -> (state owned_heap) -> (state owned_heap) -> Prop :=
  fun n => rtcn ((sim_st 0%nat) \2/ eutt eq) n.

(* Axiom A B: Type. *)
(* Axiom P: A -> (nat -> B) -> Prop. *)
(* Goal (forall a: A, exists b: (nat -> B), P a b) -> (exists b: (nat -> B), forall a, P a b). *)
(* Proof. *)
(*   i. *)
(* Qed. *)

Lemma rclo_bind_aux_aux
      n m
      k0 k1
      (K: (eq ==> rcloN n) k0 k1)
      i0 i1
      (H: rcloN m i0 i1)
  :
    rcloN (n + m)%nat (t <- i0;; k0 t) (t <- i1;; k1 t)
.
Proof.
  ginduction n; ii; ss.
  - assert(k0 = k1).
    { apply func_ext1. intro. exploit (K x0); et. intro T. inv T. ss. }
    subst. clear K.
    ginduction m; ii; ss.
    + inv H. econs; et.
    + inv H. des.
      { econs; et.
        - left. eapply sim_st_bind; et. ii. clarify. refl.
        - eapply IHm; et. }
      { econs; et.
        - right. eapply eutt_eq_bind; et. ii. clarify. refl.
        - eapply IHm; et. }
  -
    (* assert(exists km, <<A: forall x, rclo (k0 x) (km x)>> *)
    (*                                  /\ <<B: forall x, rcloN n (km x) (k1 x)>>). *)
    (* { clear - K. r in K. *)
    (*   exists (fun _ => _). *)
    (*   admit "". } *)
    econs; et; cycle 1.
    + eapply IHn; et.
Abort.

Lemma rclo_bind_aux_aux
      n m
      k0 k1
      (K: rtcn (fun f0 f1 => (forall x, sim_st 0 (f0 x) (f1 x)) \/
                             (forall x, eutt eq (f0 x) (f1 x))) n k0 k1)
      i0 i1
      (H: rcloN m i0 i1)
  :
    rcloN (n + m)%nat (t <- i0;; k0 t) (t <- i1;; k1 t)
.
Proof.
  ginduction n; ii; ss.
  - inv K.
    ginduction m; ii; ss.
    + inv H. econs; et.
    + inv H. des.
      { econs; et.
        - left. eapply sim_st_bind; et. ii. clarify. refl.
        - eapply IHm; et. }
      { econs; et.
        - right. eapply eutt_eq_bind; et. ii. clarify. refl.
        - eapply IHm; et. }
  - inv K.
    econs; et; cycle 1.
    + eapply IHn; et.
    + des.
      { left. eapply sim_st_bind; et.
        - ii. clarify.
        - refl.
      }
      { right. eapply eutt_eq_bind; et. refl. }
Qed.



Lemma rclo_bind_aux
      k0 k1
      (K: (eq ==> rclo) k0 k1)
      i0 i1
      (H: rclo i0 i1)
  :
    rclo (t <- i0;; k0 t) (t <- i1;; k1 t)
.
Proof.
  eapply rtc_rtcn in H. des.
  assert(T: exists max, forall ohmv, rcloN max (k0 ohmv) (k1 ohmv)).
  { admit "". }
  des.
  eapply rtcn_rtc.
  eapply rclo_bind_aux_aux; et.
  instantiate (1:= max).
  clear - T.
  ginduction max; ii; ss.
  { assert(k0 = k1).
    { eapply func_ext1. ii. exploit T; et. intro U. inv U. et. }
    subst. econs; et.
  }
  econs; et.
Abort.

Global Instance rclo_bind: Proper ((eq ==> rclo) ==> rclo ==> rclo) (ITree.bind').
Proof.
  ii.
  rename x0 into i0. rename y0 into i1.
  rename x into k0. rename y into k1.
  induction H0; ii; ss; et.
  - assert(exists max, forall x, rcloN max (k0 x) (k1 x)).
    { admit "". }
    des. clear H.
    ginduction max; ii; ss.
    + assert(k0 = k1).
      { apply func_ext1. ii. exploit H0; et. intro T. inv T; et. }
      subst. refl.
    + admit "".
  - etrans; cycle 1.
    { eapply IHclos_refl_trans_1n; eauto. }
    des.
    + eapply rtc_n1; et.
      { left. eapply sim_st_bind; et. ii. clarify. refl. }
    + eapply rtc_n1; et.
      { right. eapply eutt_eq_bind; et. ii. clarify. refl. }
Abort.



Ltac my_tac := 
  repeat match goal with
         | [ |- context[interp_function ?H] ] =>
           let name := fresh "x" in set (name := (interp_function H)) in *
         end
.

Lemma interp_mrec_bind: forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
                               (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof.
  ii. f. eapply interp_mrec_bind.
Qed.
























(* Lemma unfold_fib2: forall oh0 m0 vs0, *)
(*     sim_st 0%nat (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) *)
(*       (`n: nat <- (unwrapU (parse_arg oh0 m0 vs0)) ;; *)
(*     match n with *)
(*     | O => Ret (oh0, (m0, (Vint Int.zero))) *)
(*     | S O => Ret (oh0, (m0, (Vint Int.one))) *)
(*     | S (S m) => *)
(*       let vs0 := [Vint (of_nat m)] in *)
(*       guarantee (parse_arg oh0 m0 vs0) ;; *)
(*       tau;; *)
(*       '(oh1, (m1, y1)) <- (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh0 m0 vs0)) ;; *)

(*       let vs1 := [Vint (of_nat (S m))] in *)
(*       guarantee (parse_arg oh1 m1 vs1) ;; *)
(*       tau;; *)
(*       '(oh2, (m2, y2)) <-  (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh1 m1 vs1)) ;; *)

(*       Ret (oh2, (m2, Vint (of_nat (fib_nat n)))) *)
(*     end *)
(*       ) *)
(* . *)
(* Proof. *)
(*   { *)
(*     i. irw. *)
(*     unfold FibS0.f_fib at 2. irw. *)
(*     unfold unwrapU. des_ifs; cycle 1. *)
(*     { unfold triggerUB. irw. pfold. econs; et. } *)
(*     irw. destruct n. *)
(*     { irw. pfold. econs; et. } *)
(*     destruct n. *)
(*     { irw. pfold. econs; et. } *)
(*     destruct (to_nat_opt (of_nat n)) eqn:T; ss; cycle 1. *)
(*     { unfold guarantee. des_ifs_safe. irw. unfold triggerNB. irw. pfold. econs; et. } *)
(*     unfold guarantee. des_ifs_safe. irw. pfold. econs; et. left. *)
(*     des_ifs_safe. *)
(*     rewrite <- ! unfold_interp_mrec. *)
(*     rewrite interp_mrec_bind. f_equiv; cycle 1. *)
(*     { (*** TODO: prove reflexive, or we may just use rtc of sim_st ***) *)
(*       admit "refl". *)
(*     } *)
(*     ii. des_ifs; cycle 1. *)
(*     { irw. unfold triggerNB. irw. pfold. econs; et. } *)
(*     rewrite ! bind_ret_l. *)
(*     rewrite interp_mrec_bind. irw. pfold. econs; et. left. f_equiv. *)
(*     { ii. clarify. irw. des_ifs. ss. pfold. econs; et. } *)
(*     { des_ifs. irw. admit "refl". } *)
(*   } *)
(* Qed. *)

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




Lemma to_nat_opt_id: forall n, to_nat_opt (of_nat n) = Some n.
Proof.
  i. unfold to_nat_opt, of_nat. des_ifs.
  - rewrite Int.signed_repr; cycle 1.
    { generalize Int.min_signed_neg; i. split; try xomega.
      abstr (Z.of_nat n) x.
      admit "Need more condition".
    }
    rewrite Nat2Z.id. ss.
  - admit "Need more condition".
Abort.






Theorem lemma_aux
        m vs oh n
        (T: parse_arg oh m vs = Some n)
  :
    sim_st 0%nat (interp_mrec (interp_function prog) (f_fib oh m vs))
           (interp_mrec (interp_function FibS0.prog) (FibS0.f_fib oh m vs))
.
Proof.
  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  rewrite unfold_fib3.
  unfold f_fib. ss.

  Local Opaque prog FibS0.prog.
  assert(BDOOR: forall E R (it: itree E R), (tau;; it) = it).
  { admit "". }

  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss.  irw. pfold.
    rewrite <- BDOOR.
    eapply sim_st_choose_src. exists 0%nat. ss. left. pfold. econs; et.
    irw. Fail refl. left. pfold. econs; et. }
  destruct n.
  { unfold parse_arg in *. des_ifs.
    rewrite T. ss.  irw. pfold.
    rewrite <- BDOOR.
    eapply sim_st_choose_src. exists 0%nat. ss. left. pfold. econs; et.
    irw. Fail refl. left. pfold. econs; et. }

  unfold parse_arg in T. des_ifs.
  ss. rewrite ! T. ss. irw.
  unfold guarantee.
  destruct (to_nat_opt (of_nat n)) eqn:U; cycle 1.
  { des_ifs_safe. unfold triggerNB. irw. pfold. econs; et. }
  ss. des_ifs_safe. irw.
  admit "----------------------------------------------------------------------".
Unshelve.
  all: try econs.
Qed.
Local Transparent prog FibS0.prog.

Theorem lemma
        m vs oh
  :
    sim_st 0%nat
           (* (match parse_arg oh m vs with *)
           (*  | Some n => fib_nat n *)
           (*  | _ => 0%nat *)
           (*  end) *)
           (interp_program prog (ICall Fib0._fib oh m vs))
           (interp_program FibS0.prog (ICall Fib0._fib oh m vs))
.
Proof.
  destruct (parse_arg oh m vs) eqn:T; cycle 1.
  { unfold interp_program, mrec. irw. des_ifs.
    cbn in *.
    unfold f_fib at 2. unfold FibS0.f_fib at 2.
    unfold unwrapU. des_ifs. irw. pfold; econs; et.
  }
  clear_tac.
  eapply lemma_aux; et.
Qed.

Theorem correct: rusc defaultR [FibS1.module: Mod.t] [FibS0.module: Mod.t].
Proof.
  eapply SimSIR.correct; ss.
  econs; try apply lt_wf; ss.
  ii. clarify. exists O.
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

  move n at top. revert_until n.
  pattern n. eapply well_founded_ind.
  { eapply lt_wf. }
  clear n. intros.
  rename x into n.

  eapply lemma.
Qed.
