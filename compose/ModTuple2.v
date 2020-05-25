Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import AxiomsC.

Require Import Mod Sem ModSem.
Require Import Any.

Set Implicit Arguments.












(* Section ANY. *)

(* Polymorphic Inductive Any: Type := *)
(*   Any_intro : forall {A:Type} {x:A}, Any. *)

(* (* Arguments Any [A P]. *) *)


(* Section UNIV. *)
(* Polymorphic Universe i. *)
(* Polymorphic Definition upcast {T: Type@{i}} (a: T): Any := @Any_intro _ a. *)
(* End UNIV. *)

(* Section UNIV. *)
  
(* Polymorphic Universe i j. *)
(* Polymorphic Definition downcast (T: Type@{j}) (a: Any@{i}): option T. *)
(* (* Polymorphic Definition downcast (a: Any) (T: Type): option T. *) *)
(* destruct a. *)
(* destruct (ClassicalDescription.excluded_middle_informative (A = T)). *)
(* - subst. apply Some. assumption. *)
(* - apply None. *)
(* Defined. *)

(* Require Import Program. *)

(* Polymorphic Lemma upcast_downcast *)
(*       T (a: T) *)
(*   : *)
(*     downcast T (upcast a) = Some a *)
(* . *)
(* Proof. *)
(*   ss. des_ifs. dependent destruction e. ss. *)
(* Qed. *)

(* End UNIV. *)


(* End ANY. *)

(* Arguments Any_intro {A} x. *)
(* Global Opaque downcast upcast. *)
(* Print downcast. *)
(* Print upcast. *)
(* Print Any. *)













Lemma nth_error_nth
      X
      (xs: list X) n x
      (NTH: nth_error xs n = Some x)
  :
    forall d, nth n xs d = x
.
Proof.
  ginduction xs; ii; ss; des_ifs; ss; clarify.
  exploit IHxs; eauto.
Qed.

Local Obligation Tactic := idtac.

Variable ms_bot: ModSem.t.

Module ModSem2.

  Variable ms0 ms1: ModSem.t.

  Definition owned_heap: Type := (ms0.(ModSem.owned_heap) * ms1.(ModSem.owned_heap)).
  
  Definition initial_owned_heap: owned_heap :=
    (ms0.(ModSem.initial_owned_heap), ms1.(ModSem.initial_owned_heap)).

  Definition genvtype: Type := (ms0.(ModSem.genvtype) * ms1.(ModSem.genvtype)).

  Set Printing Universes.

  Inductive stack: Type :=
  | StackNil
      (oh: owned_heap)
  | StackCons
      (b: bool)
      (st0: (if b then ms0 else ms1).(ModSem.state))
      (tl: stack)
  .

  Definition state: Type := (stack * owned_heap).

  (* Definition ms (b: bool): ModSem.t := (if b then ms0 else ms1). *)
  Notation ms := (fun (b: bool) => (if b then ms0 else ms1)).

  Definition update A B (b: bool) (x: if b then A else B) (ab: A * B): A * B :=
    (if b as b0 return ((if b0 then A else B) -> A * B)
     then fun x => (x, (snd ab))
     else fun x => ((fst ab), x)) x
  .

  (***
Don't want to split call/init step, because we have to define Callstate separately.
To do this, I will require initial_state to be deterministic.
   ***)

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  | step_call
      (b: bool) st0 st1 tl oh ohs0 ohs1 args
      (AT: (ms b).(ModSem.at_external) st0 oh args)
      (OHS: update b oh ohs0 = ohs1)
    :
    step se ge ((StackCons b st0 tl), ohs0)
         E0 ((StackCons b st1 (StackCons b st0 tl)), ohs1)
  | step_internal
      (b: bool) st0 tr st1 tl ohs
      (STEP: ModSem.step (ms b) ((ms b).(ModSem.skenv_link)) ((ms b).(ModSem.globalenv)) st0 tr st1)
    :
      step se ge ((StackCons b st0 tl), ohs)
           tr ((StackCons b st1 tl), ohs)
  .





  Inductive state: Type :=
  | StateNil
  | StateCons
      (* (b: bool) *)
      (* (st0: (if b then ms0 else ms1).(ModSem.state)) *)
      (st0: ms0.(ModSem.state) + ms1.(ModSem.state))
      (tl: state)
  .

  Inductive find_fptr_owner (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms [ms0 ; ms1])
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  (* | step_internal *)
  (*     (b: bool) (st0 st1: ModSem.state (if b then ms0 else ms1)) tr tl *)
  (*     (STEP: Smallstep.step (if b then ms0 else ms1) st0 tr st1) *)
  (*   : *)
  (*     step se ge (StateCons b st0 tl) *)
  (*          tr (StateCons b st1 tl) *)


  (* | step_internal *)
  (*     (b: bool) (st0 st1: (if b then ms0.(ModSem.state) else ms1.(ModSem.state))) tr tl *)
  (*     (STEP: if b then Step ms0 st0 tr st1 else Step ms1 st0 tr st1) *)
  (*   : *)
  (*     step se ge (StateCons b st0 tl) *)
  (*          tr (StateCons b st1 tl) *)


  | step_internal_l
      st0 tr st1 tl
      (STEP: Step ms0 st0 tr st1)
    :
      step se ge (StateCons (inl st0) tl)
           tr (StateCons (inl st1) tl)
  | step_internal_r
      st0 tr st1 tl
      (STEP: Step ms1 st0 tr st1)
    :
      step se ge (StateCons (inr st0) tl)
           tr (StateCons (inr st1) tl)
  .

  (* Inductive step' (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop := *)
  (* | step'_internal *)
  (*     n *)
  (*     (NTH: match (nth_error mss n) with *)
  (*           | Some ms => *)
  (*             exists (hd0 hd1: ms.(ModSem.state)), *)
  (*               <<STK0: hd_error (get_stk st0) = Some (upcast (n, hd0))>> /\ *)
  (*               (* <<STK0: hd_error (get_stk st0) = Some (upcast (n, hd0))>> /\ *) *)
  (*               (* <<STK1: hd_error (get_stk st1) = Some (upcast (n, hd1))>> /\ *) *)
  (*               <<OH: get_ohs st0 = get_ohs st1>> /\ *)
  (*               <<STEP: Step ms hd0 tr hd1>> *)
  (*           | _ => False *)
  (*           end *)
  (*     ) *)
  (* . *)
  (* Reset step'. *)

  (* Print Universes. *)

  Variable skenv_link: SkEnv.t.

  Variable link_skenv: SkEnv.t -> SkEnv.t -> SkEnv.t.

  Set Printing Universes.
  Print Universes.

  Program Definition t': ModSem.t :=
    {|
      ModSem.state := state;
      ModSem.owned_heap := owned_heap;
      ModSem.genvtype := genvtype;
      (* ModSem.step := step; *)
      (* ModSem.at_external := coerce at_external; *)
      (* ModSem.initial_frame := coerce initial_frame; *)
      (* ModSem.final_frame := coerce final_frame; *)
      (* ModSem.after_external := ms0.(ModSem.after_external); *)
      (* ModSem.globalenv := ge; *)
      (* ModSem.skenv := link_skenv ms0.(ModSem.skenv) ms1.(ModSem.skenv); *)
      (* ModSem.skenv_link := skenv_link; *)
      (* ModSem.midx := None; *)
    |}
  .

End ModSem2.
