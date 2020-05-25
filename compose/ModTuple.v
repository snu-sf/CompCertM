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

(* Set Printing Universes. *)

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
Polymorphic Definition downcast (T: Type@{j}) (a: Any@{i}): option T.
(* Polymorphic Definition downcast (a: Any) (T: Type): option T. *)
destruct a.
destruct (ClassicalDescription.excluded_middle_informative (A = T)).
- subst. apply Some. assumption.
- apply None.
Defined.

End UNIV.

Polymorphic Definition upcast {T} (a: T): Any := @Any_intro _ a.

Require Import Program.

Lemma upcast_downcast
      T (a: T)
  :
    downcast T (upcast a) = Some a
.
Proof.
  ss. des_ifs. dependent destruction e. ss.
Qed.

End ANY.

Arguments Any_intro {A} x.
Global Opaque downcast upcast.
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



Record alist (tys: forall (n: nat), Type): Type := mk_alist {
  anys: list Any;
  WTY: forall
      n any
      (NTHA: nth_error anys n = Some any)
    ,
      exists elem, (<<CAST: @downcast (tys n) any = Some elem>>)
  ;
}
.

Module ModSem2.

  Variable mss: list ModSem.t.

  (* Record state: Type := { *)
  (*   stk: list Any; *)
  (*   WTY: forall *)
  (*       any *)
  (*       (IN: In any stk) *)
  (*     , *)
  (*       exists n ms st, (<<NTH: nth_error mss n = Some ms>>) /\ *)
  (*                       (<<CAST: @downcast (nat * ms.(ModSem.state)) any = Some (n, st)>>); *)
  (*   NNIL: stk <> nil; *)
  (* } *)
  (* . *)

  (* Record owned_heap: Type := { *)
  (*   anys: list Any; *)
  (*   WTY: forall *)
  (*       n ms *)
  (*       (NTH: nth_error mss n = Some ms) *)
  (*     , *)
  (*       exists any oh, (<<NTHA: nth_error anys n = Some any>>) /\ *)
  (*                      (<<CAST: @downcast any ms.(ModSem.owned_heap) = Some oh>>) *)
  (*   ; *)
  (* } *)
  (* . *)

  Definition owned_heap: Type := alist (fun n => match nth_error mss n with
                                                 | Some ms => ms.(ModSem.owned_heap)
                                                 | _ => Empty_set
                                                 end)
  .

  Fail Program Definition initial_owned_heap: owned_heap :=
    @mk_alist (fun n => match nth_error mss n with
                        | Some ms => ms.(ModSem.owned_heap)
                        | _ => Empty_set
                        end)
              (map (fun ms => upcast (ModSem.initial_owned_heap ms)) mss)
              _
  .

  Definition owned_heap2: Type := list Any.
  Definition initial_owned_heap2: owned_heap2 :=
    map (fun ms => upcast (ModSem.initial_owned_heap ms)) mss.

  Record owned_heap3: Type := mk_oh3 {
    anys: list Any;
    OHWTY: forall
        n any
        (NTHA: nth_error anys n = Some any)
      ,
        exists elem, (<<CAST: @downcast (match nth_error mss n with
                                         | Some ms => ms.(ModSem.owned_heap)
                                         | _ => Empty_set
                                         end) any = Some elem>>)
    ;
  }
  .
  Program Definition initial_owned_heap3: owned_heap3 :=
    @mk_oh3
      (map (fun ms => upcast (ModSem.initial_owned_heap ms)) mss)
      _
  .
  Next Obligation.
    rewrite list_map_nth in *. unfold option_map in *. des_ifs.
    esplits; eauto.
    rewrite upcast_downcast. et.
  Qed.

  Definition genvtype: Type := alist (fun n => match nth_error mss n with
                                               | Some ms => ms.(ModSem.genvtype)
                                               | _ => Empty_set
                                               end)
  .

  Inductive state: Type :=
  | Callstate
      (args: Args.t)
      (stk: list Any)
      (oh: owned_heap3)
      (WTY: forall
          any
          (IN: In any stk)
        ,
          exists n ms st, (<<NTH: nth_error mss n = Some ms>>) /\
                          (<<CAST: @downcast (nat * ms.(ModSem.state)) any = Some (n, st)>>))
      (NNIL: stk <> nil)

  | State
      (stk: list Any)
      (oh: owned_heap3)
      (WTY: forall
          any
          (IN: In any stk)
        ,
          exists n ms st, (<<NTH: nth_error mss n = Some ms>>) /\
                          (<<CAST: @downcast (nat * ms.(ModSem.state)) any = Some (n, st)>>))
      (NNIL: stk <> nil)
  .
  Arguments Callstate _ stk: clear implicits.
  Arguments State stk: clear implicits.

  Definition get_stk (st: state): list Any :=
    match st with
    | Callstate _ stk _ _ _ => stk
    | State stk _ _ _ => stk
    end.

  Definition get_ohs (st: state): owned_heap3 :=
    match st with
    | Callstate _ _ ohs _ _ => ohs
    | State _ ohs _ _ => ohs
    end.

  (* Inductive step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop := *)
  (* | step_internal *)
  (*     n ms hd0 hd1 tl *)
  (*     (NTH: nth_error mss n = Some ms) *)
  (*     (HD0: st0.(stk) = (upcast (n, hd0)) :: tl) *)
  (*     (HD1: st1.(stk) = (upcast (n, hd1)) :: tl) *)
  (*     (STEP: Step ms hd0 tr hd1) *)
  (* | step_call *)
  (*     n0 n1 ms0 ms1 (hd0: ms0.(ModSem.state)) (hd1: ms1.(ModSem.state)) tl *)
  (*     (NTH0: nth_error mss n0 = Some ms0) *)
  (*     (NTH1: nth_error mss n1 = Some ms1) *)
  (*     (HD0: st0.(stk) = (upcast (n0, hd0)) :: tl) *)
  (*     (HD1: st1.(stk) = ((upcast (n1, hd1)) :: (upcast (n0, hd0)) :: tl)) *)
  (*     CALL: ... *)
  (* . *)

  Inductive find_fptr_owner (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms mss)
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Inductive step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  (* | step_call_inside *)
  (*     n ms ms_new (hd: ms.(ModSem.state)) tl tr ohs0 ohs1 args oh *)
  (*     (NTH: nth_error mss n = Some ms) *)

  (*     (AT: ms.(ModSem.at_external) hd oh args) *)
  (*     (MSFIND: find_fptr_owner (Args.get_fptr args) ms_new) *)
  (*     (* (OHS: ohs1 = Midx.update ohs0 ms.(ModSem.midx) (upcast oh)) *) *)
  (*     WTY0 NNIL0 WTY1 NNIL1 *)
  (*   : *)
  (*     step se ge (State (upcast (n, hd) :: tl) ohs0 WTY0 NNIL0) *)
  (*          tr (Callstate args (upcast (n, hd) :: tl) ohs1 WTY1 NNIL1) *)

  (* | step_call_inside *)
  (*     fr0 frs args oh ohs0 ohs1 ms *)
  (*     (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) oh args) *)
  (*     (MSFIND: find_fptr_owner (Args.get_fptr args) ms) *)
  (*     (OHS: ohs1 = Midx.update ohs0 fr0.(Frame.ms).(ModSem.midx) (upcast oh)): *)
  (*     step se ge (State (fr0 :: frs) ohs0) *)
  (*          E0 (Callstate args (fr0 :: frs) ohs1) *)

  (* | step_init_inside *)
  (*     args frs ms st_init oh ohs *)
  (*     (MSFIND: find_fptr_owner (Args.get_fptr args) ms) *)
  (*     (OH: Midx.get ohs ms.(ModSem.midx) = upcast oh) *)
  (*     (INIT: ms.(ModSem.initial_frame) oh args st_init): *)
  (*     step se ge (Callstate args frs ohs) *)
  (*          E0 (State ((Frame.mk ms st_init) :: frs) ohs) *)

  | step_internal
      n ms (hd0 hd1: ms.(ModSem.state)) tl tr ohs
      (NTH: nth_error mss n = Some ms)

      (STEP: Step ms hd0 tr hd1)
      WTY0 NNIL0 WTY1 NNIL1
    :
      step se ge (State (upcast (n, hd0) :: tl) ohs WTY0 NNIL0)
           tr (State (upcast (n, hd1) :: tl) ohs WTY1 NNIL1)
  .
  Reset step.

  Variable ms_bot: ModSem.t.

  Inductive step' (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop :=

  (* | step'_internal *)
  (*     n ms (hd0 hd1: ms.(ModSem.state)) tl *)
  (*     (NTH: nth_error mss n = Some ms) *)
  (*     (STK0: get_stk st0 = (upcast (n, hd0) :: tl)) *)
  (*     (STK1: get_stk st1 = (upcast (n, hd1) :: tl)) *)
  (*     (OH: get_ohs st0 = get_ohs st1) *)
  (*     (STEP: Step ms hd0 tr hd1) *)
  | step'_internal
      n
      (NTH: match (nth_error mss n) with
            | Some ms =>
              exists (hd0 hd1: ms.(ModSem.state)),
                <<STK0: hd_error (get_stk st0) = Some (upcast (n, hd0))>> /\
                <<STK1: hd_error (get_stk st1) = Some (upcast (n, hd1))>> /\
                <<OH: get_ohs st0 = get_ohs st1>> /\
                <<STEP: Step ms hd0 tr hd1>>
            | _ => False
            end
      )
  .
  (* Reset step'. *)

  Variable skenv_link: SkEnv.t.

  Variable link_skenv: SkEnv.t -> SkEnv.t -> SkEnv.t.

  Set Printing Universes.

  Record state2: Type := mkState {
    stk: list Any;
    ohs: owned_heap;
    is_call: bool;
    WTY: forall
        any
        (IN: In any stk)
      ,
        exists n ms st, (<<NTH: nth_error mss n = Some ms>>) /\
                        (<<CAST: @downcast (nat * ms.(ModSem.state)) any = Some (n, st)>>);
    NNIL: stk <> nil;
  }
  .
  Arguments mkState stk: clear implicits.

  Inductive step2 (se: Senv.t) (ge: genvtype): state2 -> trace -> state2 -> Prop :=
  | step2_call_inside
      n ms ms_new (hd: ms.(ModSem.state)) tl tr ohs0 ohs1 args oh
      (NTH: nth_error mss n = Some ms)

      (AT: ms.(ModSem.at_external) hd oh args)
      (MSFIND: find_fptr_owner (Args.get_fptr args) ms_new)
      (* (OHS: ohs1 = Midx.update ohs0 ms.(ModSem.midx) (upcast oh)) *)
      WTY0 NNIL0 WTY1 NNIL1
    :
      step2 se ge (mkState (upcast (n, hd) :: tl) ohs0 false WTY0 NNIL0)
           tr (mkState (upcast (n, hd) :: tl) ohs1 true WTY1 NNIL1)

  (* | step_call_inside *)
  (*     fr0 frs args oh ohs0 ohs1 ms *)
  (*     (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) oh args) *)
  (*     (MSFIND: find_fptr_owner (Args.get_fptr args) ms) *)
  (*     (OHS: ohs1 = Midx.update ohs0 fr0.(Frame.ms).(ModSem.midx) (upcast oh)): *)
  (*     step se ge (State (fr0 :: frs) ohs0) *)
  (*          E0 (Callstate args (fr0 :: frs) ohs1) *)

  (* | step_init_inside *)
  (*     args frs ms st_init oh ohs *)
  (*     (MSFIND: find_fptr_owner (Args.get_fptr args) ms) *)
  (*     (OH: Midx.get ohs ms.(ModSem.midx) = upcast oh) *)
  (*     (INIT: ms.(ModSem.initial_frame) oh args st_init): *)
  (*     step se ge (Callstate args frs ohs) *)
  (*          E0 (State ((Frame.mk ms st_init) :: frs) ohs) *)

  | step2_internal
      n ms (hd0 hd1: ms.(ModSem.state)) tl tr ohs
      (NTH: nth_error mss n = Some ms)

      (STEP: Step ms hd0 tr hd1)
      WTY0 NNIL0 WTY1 NNIL1
    :
      step2 se ge (mkState (upcast (n, hd0) :: tl) ohs false WTY0 NNIL0)
           tr (mkState (upcast (n, hd1) :: tl) ohs false WTY1 NNIL1)

  (* | step_return *)
  (*     fr0 fr1 frs retv st0 ohs0 ohs1 oh0 oh1 *)
  (*     (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) oh0 retv) *)
  (*     (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) oh1 retv st0) *)
  (*     (OHS: ohs1 = Midx.update ohs0 fr0.(Frame.ms).(ModSem.midx) (upcast oh0)) *)
  (*     (OH: Midx.get ohs1 fr1.(Frame.ms).(ModSem.midx) = upcast oh1): *)
  (*     step se ge (State (fr0 :: fr1 :: frs) ohs0) *)
  (*          E0 (State (((Frame.update_st fr1) st0) :: frs) ohs1) *)
  .

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
    
