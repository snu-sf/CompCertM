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
    (* wf: t -> Prop; *)

    mle: t -> Memory.mem -> Memory.mem -> Prop;
    mle_PreOrder su0 :> PreOrder (mle su0);

    le: t -> t -> Prop;
    le_PreOrder :> PreOrder le;
    hle: t -> t -> Prop;
    hle_PreOrder :> PreOrder hle;
    (* le_val: forall *)
    (*     su0 su1 *)
    (*     (LE: le su0 su1) *)
    (*   , *)
    (*     <<LE: su1.(val) <1= su0.(val)>> *)
    (* ; *)

    (* TODO: rename it into le_monotone *)
    wf: t -> Prop;
    hle_le: forall
        su0 su1
        (HLE: hle su0 su1)
        (WF: wf su0)
      ,
        <<LE: le su0 su1>>
    ;
    le_spec: forall
        su0 su1 m0 m1
        (MLE: mle su1 m0 m1)
        (LE: le su0 su1)
      ,
        <<MLE: mle su0 m0 m1>>
    ;

    val: t -> Values.val -> Prop;
    vals: t -> list Values.val -> Prop := fun su vs => Forall su.(val) vs;
    mem: t -> mem -> Prop;
    args: t -> Args.t -> Prop :=
      fun su args =>
        (<<VAL: val su args.(Args.fptr)>>) /\
        (<<VALS: vals su args.(Args.vs)>>) /\
        (<<MEM: mem su args.(Args.m)>>) /\
        (<<WF: wf su>>)
    ;
    retv: t -> Retv.t -> Prop :=
      fun su retv =>
        (<<VAL: val su retv.(Retv.v)>>) /\
        (<<MEM: mem su retv.(Retv.m)>>) /\
        (<<WF: wf su>>)
    ;

    hle_val: forall
        su0 su1 v
        (VAL: val su0 v)
        (HLE: hle su0 su1)
      ,
        <<VAL: val su1 v>>
    ;
    (* retv_le: forall *)
    (*     su0 su1 *)
    (*     (LE: le su0 su1) *)
    (*   , *)
    (*     su1.(retv) <1= su0.(retv) *)
    (* ; *)
    get_greatest: t -> Args.t -> t -> Prop;
    greatest_dtm: forall
        args0
        su0 su_gr0 su_gr1
        (GR0: get_greatest su0 args0 su_gr0)
        (GR1: get_greatest su0 args0 su_gr1)
      ,
        su_gr0 = su_gr1
    ;
    (* greatest_le: forall *)
    (*     args0 su0 su_gr *)
    (*     (ARGS: su0.(args) args0) *)
    (*     (GR: get_greatest args0 su_gr) *)
    (*   , *)
    (*     le su0 su_gr *)
    (* ; *)
    greatest_ex: forall
        su0 args0
        (INHAB: exists inhab, <<LE: le su0 inhab>> /\ <<ARGS: inhab.(args) args0>>)
      ,
        exists su_gr, <<GR: get_greatest su0 args0 su_gr>>
    ;
    greatest_adq: forall
        su0 args0 su_gr
        (GR: get_greatest su0 args0 su_gr)
      ,
        <<SUARGS: args su_gr args0>> /\ <<LE: le su0 su_gr>>
    ;
    (* get_greatest_irr: forall *)
    (*     su0 su1 args0 su_gr0 su_gr1 *)
    (*     (GR0: get_greatest su0 args0 su_gr0) *)
    (*     (GR1: get_greatest su1 args0 su_gr1) *)
    (*     (SUARG: args su1 args0) *)
    (*     (LE: le su0 su1) *)
    (*   , *)
    (*     <<EQ: su_gr0 = su_gr1>> *)
    (* ; *)
    get_greatest_le: forall
        su0 su1 args0 su_gr
        (GR: get_greatest su1 args0 su_gr)
        (SUARG: args su1 args0)
        (LE: le su0 su1)
      ,
        <<GR: get_greatest su0 args0 su_gr>>
    ;

    (* lub: t -> t -> t; *)
    (* lub_le: forall x y, <<LE: le x (lub x y)>> /\ <<LE: le y (lub x y)>>; *)
    (* (* lub_val: forall x y, (lub x y).(val) <1= x.(val); *) *)
    (* (* lub_mem: forall x y, (lub x y).(mem) <1= x.(mem); *) *)
    (* lub_val: forall x y, x.(val) /1\ y.(val) <1= (lub x y).(val); *)
    (* lub_mem: forall x y, x.(mem) /1\ y.(mem) <1= (lub x y).(mem); *)


    (* liftdata: Type; *)
    (* lift: t -> liftdata -> t; *)
    (* unlift: t -> t -> t; *)

    (* (* refined type *) *)
    (* refined (m0: Memory.mem) :=  { su: t | su.(mem) m0 }; *)
    (* refined_finite: forall m0, Finite (refined m0); *)

    (* top: t; *)
    (* top_spec: top1 <1= top.(val) /\ top1 <1= top.(mem); *)
    skenv: t -> Memory.mem -> SkEnv.t -> Prop;
    init_spec: forall
        sk_link skenv_link m_init
        (MEM: Sk.load_mem sk_link = Some m_init)
        (SKE: Sk.load_skenv sk_link = skenv_link)
      ,
        exists su_init,
          (<<SUARGS: su_init.(args) (Args.mk (Genv.symbol_address skenv_link (prog_main sk_link) Ptrofs.zero) [] m_init)>>) /\
          (<<SUSKE: su_init.(skenv) m_init skenv_link>>)
    ;

    skenv_le: forall
        m0 su0 su1 ske
        (SKE: su0.(skenv) m0 ske)
        (LE: le su0 su1)
      ,
        <<SKE: su1.(skenv) m0 ske>>
    ;

    skenv_mle: forall
        m0 m1 su0 ske
        (SKE: su0.(skenv) m0 ske)
        (MLE: su0.(mle) m0 m1)
      ,
        <<SKE: su0.(skenv) m1 ske>>
    ;

    skenv_project: forall
        su m0 skenv_link
        (WF: SkEnv.wf skenv_link)
        (SKE: su.(skenv) m0 skenv_link)
        defs0 skenv0
        (LE: SkEnv.project_spec skenv_link defs0 skenv0)
      ,
        <<SKE: su.(skenv) m0 skenv0>>
    ;

    (* system_skenv: forall *)
    (*     su skenv_link *)
    (*     (SKE: su.(skenv) skenv_link) *)
    (*   , *)
    (*     <<SKE: su.(skenv) skenv_link.(System.skenv)>> *)
    (* ; *)

    system_skenv: forall
        su m0 skenv_link
      ,
        (* <<SKE: su.(skenv) skenv_link <-> su.(skenv) skenv_link.(System.skenv)>> *)
        su.(skenv) m0 skenv_link <-> su.(skenv) m0 skenv_link.(System.skenv)
    ;

    system_axiom: forall
        ef skenv0 su0 args0
        tr v_ret m_ret
        (ARGS: su0.(args) args0)
        (SKE: skenv su0 args0.(Args.m) skenv0)
        (EXT: (external_call ef) skenv0 args0.(Args.vs) args0.(Args.m) tr v_ret m_ret)
      ,
        exists su1, <<LE: hle su0 su1>> /\ <<RETV: su1.(retv) (Retv.mk v_ret m_ret)>> /\ <<MLE: su0.(mle) args0.(Args.m) m_ret>>
    ;
  }
  .

  Section SOUND.
  Context {SU: class}.

  Lemma hle_spec: forall
        su0 su1 m0 m1
        (MLE: mle su1 m0 m1)
        (LE: hle su0 su1)
        (WF: wf su0)
      ,
        <<MLE: mle su0 m0 m1>>
  .
  Proof.
    i. eapply Sound.le_spec; et. eapply Sound.hle_le; et.
  Qed.

  Lemma get_greatest_hle: forall
      su0 su1 args0 su_gr
      (GR: get_greatest su1 args0 su_gr)
      (SUARG: args su1 args0)
      (HLE: hle su0 su1)
      (WF: wf su0)
    ,
      <<GR: get_greatest su0 args0 su_gr>>
  .
  Proof.
    i. eapply Sound.get_greatest_le; eauto. eapply Sound.hle_le; eauto.
  Qed.

  (* Lemma get_greatest_le *)
  (*       su0 su1 args0 su_gr *)
  (*       (GR: get_greatest su1 args0 su_gr) *)
  (*       (LE: le su0 su1) *)
  (*   : *)
  (*     <<GR: get_greatest su0 args0 su_gr>> *)
  (* . *)
  (* Proof. *)
  (*    exploit Sound.greatest_adq; eauto. i; des. *)
  (*    exploit (Sound.greatest_ex su0); eauto. *)
  (*    { esplits; try apply SUARGS; eauto. etrans; eauto. } *)
  (*    i; des. *)
  (*    rp; eauto. symmetry. *)
  (*    eapply Sound.get_greatest_irr; eauto. *)
  (* Qed. *)

  (* Inductive args (su: t) (args0: Args.t): Prop := *)
  (* | args_intro *)
  (*     (VAL: su.(val) args0.(Args.fptr)) *)
  (*     (VALS: su.(val_list) args0.(Args.vs)) *)
  (*     (MEM: su.(mem) args0.(Args.m)) *)
  (* . *)

  End SOUND.

End Sound.












