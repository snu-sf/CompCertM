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












Section ANY.

Polymorphic Inductive Any: Type :=
  Any_intro : forall {A:Type} {x:A}, Any.

(* Arguments Any [A P]. *)


Section UNIV.
Polymorphic Universe i.
Polymorphic Definition upcast {T: Type@{i}} (a: T): Any := @Any_intro _ a.
End UNIV.

Section UNIV.
  
Polymorphic Universe i j.
Polymorphic Definition downcast (T: Type@{j}) (a: Any@{i}): option T.
(* Polymorphic Definition downcast (a: Any) (T: Type): option T. *)
destruct a.
destruct (ClassicalDescription.excluded_middle_informative (A = T)).
- subst. apply Some. assumption.
- apply None.
Defined.

Require Import Program.

Polymorphic Lemma upcast_downcast
      T (a: T)
  :
    downcast T (upcast a) = Some a
.
Proof.
  ss. des_ifs. dependent destruction e. ss.
Qed.

End UNIV.


End ANY.

Arguments Any_intro {A} x.
Global Opaque downcast upcast.
Print downcast.
Print upcast.
Print Any.













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

  Variable mss: list ModSem.t.

  Record owned_heap: Type := mk_oh3 {
    anys: list Any;
    (* OHWTY: forall *)
    (*     n any *)
    (*     (NTHA: nth_error anys n = Some any) *)
    (*   , *)
    (*     exists elem, (<<CAST: @downcast (nth n mss ms_bot).(ModSem.owned_heap) any = Some elem>>) *)
    (* ; *)
  }
  .
  Print Universes.
  (* ModSem.t.u1 <= owned_heap.u0). *)
  
  Program Definition initial_owned_heap: owned_heap :=
    @mk_oh3
      (map (fun ms => upcast (ModSem.initial_owned_heap ms)) mss)
      (* _ *)
  .
  Print Universes.
  (* Next Obligation. *)
  (*   i. rewrite list_map_nth in *. unfold option_map in *. des_ifs. *)
  (*   erewrite nth_error_nth; eauto. *)
  (*   esplits; eauto. *)
  (*   rewrite upcast_downcast. et. *)
  (* Qed. *)

  Definition genvtype: Type := unit.

  Set Printing Universes.

  Inductive state: Type :=
  | StateNil
  | StateCons
      n
      (* (st0: (nth n (map (ModSem.state) mss) Empty_set)) *)
      (st0: (nth n mss ms_bot).(ModSem.state))
      (tl: state)
  .

  Inductive find_fptr_owner (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms mss)
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  | step_internal
      n st0 tr st1 tl
      (STEP: Step (nth n mss ms_bot) st0 tr st1)
    :
      step se ge (StateCons n st0 tl)
           tr (StateCons n st1 tl)
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
