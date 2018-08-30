Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

Require Import ModSem.
Require Import Skeleton.
Require Import System.

Set Implicit Arguments.












(* TODO: move to CoqlibC *)
Section FLIPS.

Definition flip2 A B C D: (A -> B -> C -> D) -> A -> C -> B -> D. intros; eauto. Defined.
Definition flip3 A B C D E: (A -> B -> C -> D -> E) -> A -> B -> D -> C -> E. intros; eauto. Defined.
Definition flip4 A B C D E F: (A -> B -> C -> D -> E -> F) -> A -> B -> C -> E -> D -> F. intros; eauto. Defined.

Variable A B C D: Type.
Variable f: A -> B -> C -> D.
Check f.
(* ABCD *)
Check f.(flip).
(* BACD *)
Check f.(flip2).
(* ACBD *)
Check f.(flip2).(flip).
(* CABD *)
Check f.(flip).(flip2).
(* BCAD *)
Check f.(flip2).(flip).(flip2).
(* CBAD *)

Let put_dummy_arg_without_filp A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (fun a _ => f a).
Let put_dummy_arg1 A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (fun _ => f).(flip).
Let put_dummy_arg21 A DUMMY B C: (A -> B -> C) -> (A -> DUMMY -> B -> C) := fun f => (fun _ => f).(flip).
Let put_dummy_arg22 A B DUMMY C: (A -> B -> C) -> (A -> B -> DUMMY -> C) :=
  fun f => (fun _ => f).(flip).(flip2).

End FLIPS.
Hint Unfold flip2 flip3 flip4.






Module Sound.

  Class class :=
  {
    t: Type;
    wf: t -> Prop;
    mem: t -> mem -> Prop;
    val: t -> val -> Prop;
    mle: t -> Memory.mem -> Memory.mem -> Prop;
    mle_PreOrder su0 :> PreOrder (mle su0);

    le: t -> t -> Prop;
    le_PreOrder :> PreOrder le;
    (* le_val: forall *)
    (*     su0 su1 *)
    (*     (LE: le su0 su1) *)
    (*   , *)
    (*     <<LE: su1.(val) <1= su0.(val)>> *)
    (* ; *)

    le_spec: forall
        su0 su1 m0 m1
        (MLE: mle su1 m0 m1)
        (LE: le su0 su1)
      ,
        <<MLE: mle su0 m0 m1>>
    ;

    lub: t -> t -> t;
    lub_le: forall x y, <<LE: le x (lub x y)>> /\ <<LE: le y (lub x y)>>;
    (* lub_val: forall x y, (lub x y).(val) <1= x.(val); *)
    (* lub_mem: forall x y, (lub x y).(mem) <1= x.(mem); *)
    lub_val: forall x y, x.(val) /1\ y.(val) <1= (lub x y).(val);
    lub_mem: forall x y, x.(mem) /1\ y.(mem) <1= (lub x y).(mem);
    (* liftdata: Type; *)
    (* lift: t -> liftdata -> t; *)
    (* unlift: t -> t -> t; *)
    val_list: t -> list Values.val -> Prop;
    val_list_spec: forall su0, (List.Forall su0.(val) = su0.(val_list));

    (* (* refined type *) *)
    (* refined (m0: Memory.mem) :=  { su: t | su.(mem) m0 }; *)
    (* refined_finite: forall m0, Finite (refined m0); *)
    system_axiom: forall
        ef senv su vs_arg m_arg
        tr v_ret m_ret
        (SUVS: su.(val_list) vs_arg)
        (SUM: su.(mem) m_arg)
        (EXT: (external_call ef) senv vs_arg m_arg tr v_ret m_ret)
      ,
        <<SURETV: su.(val) v_ret>> /\ <<SUM: su.(mem) m_ret>> /\ <<MLE: su.(mle) m_arg m_ret>>;

    top: t;
    top_spec: top1 <1= top.(val) /\ top1 <1= top.(mem);
  }
  .

  Section SOUND.
  Context {SU: class}.


  Inductive args (su: t) (args0: Args.t): Prop :=
  | args_intro
      (VAL: su.(val) args0.(Args.fptr))
      (VALS: su.(val_list) args0.(Args.vs))
      (MEM: su.(mem) args0.(Args.m))
  .

  Inductive retv (su: t) (retv0: Retv.t): Prop :=
  | retv_intro
      (VAL: su.(val) retv0.(Retv.v))
      (MEM: su.(mem) retv0.(Retv.m))
  .

  Lemma top_args
        args0
    :
      top.(args) args0
  .
  Proof.
    econs; eauto; try eapply top_spec; ss.
    rewrite <- val_list_spec.
    rewrite Forall_forall. ii. apply top_spec; ss.
  Qed.

  End SOUND.

End Sound.













