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

Set Printing Universes.

(* From ExtLib Require Import Data.PPair. *)
(* pprod@{i j} : Type@{i} -> Type@{j} -> Type@{max(i,j)} *)
(* prod : Type@{prod.u0} -> Type@{prod.u1} -> Type@{max(prod.u0,prod.u1)} *)


Section CHECK.
  Require Ord.
  Fail Check (@Ord.mk Ord.idx Ord.ord Ord.wf_ord Ord.idx_bot).
End CHECK.



Section ANY.

(* Variable T : Type@{i}. *)
Polymorphic Inductive Any: Type :=
  Any_intro : forall {A:Type} {x:A}, Any.

(* Arguments Any [A P]. *)

Section UNIV.
  
Polymorphic Universe i j.
Polymorphic Definition downcast (a: Any@{i}) (T: Type@{j}): option T.
(* Polymorphic Definition downcast (a: Any) (T: Type): option T. *)
destruct a.
destruct (ClassicalDescription.excluded_middle_informative (A = T)).
- subst. apply Some. assumption.
- apply None.
Defined.

End UNIV.

Polymorphic Definition upcast {T} (a: T): Any := @Any_intro _ a.

End ANY.

Arguments Any_intro {A} x.
Print downcast.
Print upcast.
Print Any.



Module PLAYGROUND.
  Record ModSem: Type := mk {
    state: Type;
    genv: Type;
  }
  .
  Program Definition link_ModSem (ms0 ms1: ModSem): ModSem :=
    {|
      state := ms0.(state) * ms1.(state);
    |}
  .
  Reset link_ModSem.

  Section TMP.

    Variable mss: list ModSem.

    Inductive stack: Type :=
    | state_one
        ms
        (IN: In ms mss)
        (st: ms.(state))
    | state_cons
        ms
        (IN: In ms mss)
        (st: ms.(state))
        (tl: stack)
    .

    Fail Program Definition link_ModSem2: ModSem :=
      {|
        state := stack;
      |}
    .
  End TMP.

End PLAYGROUND.

Module PLAYGROUND0.
  Polymorphic Record ModSem: Type := mk {
    state: Type;
    genv: Type;
  }
  .
  Program Definition link_ModSem (ms0 ms1: ModSem): ModSem :=
    {|
      state := ms0.(state) * ms1.(state);
    |}
  .
  Reset link_ModSem.

  Section TMP.

    Variable mss: list ModSem.

    Inductive stack: Type :=
    | state_one
        ms
        (IN: In ms mss)
        (st: ms.(state))
    | state_cons
        ms
        (IN: In ms mss)
        (st: ms.(state))
        (tl: stack)
    .

    Program Definition link_ModSem2: ModSem :=
      {|
        state := stack;
      |}
    .
    Reset link_ModSem2.
  End TMP.

End PLAYGROUND0.
(* Program Definition link_ModSem_original (ms0 ms1: ModSem.t): ModSem.t := *)
(*   {| *)
(*     ModSem.state := ms0.(ModSem.state) * ms1.(ModSem.state); *)
(*   |} *)
(* . *)
(* Back 1. *)




Module ModSem2.

  Variable mss: list ModSem.t.

  Record state: Type := {
    cur: Any;
    stk: list (Any: Type);
    (*   list (Any: Type@{ModSem.t.u0}); *)
    WTYFST:
      exists ms st, <<IN: In ms mss>> /\ <<CAST: @downcast cur ms.(ModSem.state) = Some st>>;
    WTYSND: forall
        any
        (IN: In any stk)
      ,
        exists ms st, <<IN: In ms mss>> /\ <<CAST: @downcast any ms.(ModSem.state) = Some st>>;
  }
  .

  Inductive state2: Type :=
  | state_one
      ms
      (IN: In ms mss)
      (st: ms.(ModSem.state))
  | state_cons
      ms
      (IN: In ms mss)
      (st: ms.(ModSem.state))
      (tl: state2)
  .

  Variable skenv_link: SkEnv.t.

  Variable link_skenv: SkEnv.t -> SkEnv.t -> SkEnv.t.

  Program Definition t': ModSem.t :=
    {|
      (* ModSem.state := state; *)
      ModSem.state := state2;
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
    
