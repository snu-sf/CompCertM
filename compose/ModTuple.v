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
Require Import Program.

Set Implicit Arguments.



Local Obligation Tactic := idtac.

Variable ms_bot: ModSem.t.

Section MODTUPLE.

  Variable skenv_link: SkEnv.t.

  Variable link_skenv: SkEnv.t -> SkEnv.t -> SkEnv.t.

  Variable msdl msdr: ModSem.t.

  Hypothesis MIDXL: msdl.(ModSem.midx) <> None.
  Hypothesis MIDXR: msdr.(ModSem.midx) <> None.

  Definition owned_heap: Type := (msdl.(ModSem.owned_heap) * msdr.(ModSem.owned_heap)).

  Definition initial_owned_heap: owned_heap :=
    (msdl.(ModSem.initial_owned_heap), msdr.(ModSem.initial_owned_heap)).

  Definition genvtype: Type := (msdl.(ModSem.genvtype) * msdr.(ModSem.genvtype)).

  Definition globalenv: genvtype := (msdl.(ModSem.globalenv), msdr.(ModSem.globalenv)).

  Variant dir: Type :=
  | dl
  | dr
  .

  Inductive stack: Type :=
  | StackNil
  | StackCons
      (d: dir)
      (st0: (if d then msdl else msdr).(ModSem.state))
      (* (st0: msdl.(ModSem.state) + msdr.(ModSem.state)) *)
      (tl: stack)
  .

  Lemma stack_inj
        b0 hd0 tl0 b1 hd1 tl1
        (EQ: (StackCons b0 hd0 tl0) = (StackCons b1 hd1 tl1))
    :
      b0 = b1 /\ hd0 ~= hd1 /\ tl0 = tl1
  .
  Proof.
    des_ifs; simpl_depind; clarify; esplits; eauto.
  Qed.

  Lemma state_inj
        b0 hd0 tl0 (ohs0: owned_heap) b1 hd1 tl1 ohs1
        (EQ: ((StackCons b0 hd0 tl0), ohs0) = ((StackCons b1 hd1 tl1), ohs1))
    :
      b0 = b1 /\ hd0 ~= hd1 /\ tl0 = tl1 /\ ohs0 = ohs1
  .
  Proof.
    des_ifs; simpl_depind; clarify; esplits; eauto.
  Qed.

  Definition state: Type := (stack * owned_heap).

  (***
Don't want to split call/init step, because we have to define Callstate separately.
To do this, I will require initial_state to be deterministic.
   ***)

  Variant find_fptr_owner (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms [msdl ; msdr])
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Variant step (se: Senv.t) (ge: genvtype): state -> trace -> state -> Prop :=
  | step_call_dl
      st0 st_new tl oh0 oh_new ohs0 ohs1 args
      (AT: msdl.(ModSem.at_external) st0 oh0 args)
      (OHS: ohs1 = (oh0, snd ohs0))

      (MSFIND: find_fptr_owner (Args.get_fptr args) msdr)
      (OH: snd ohs1 = oh_new)
      (INIT: msdr.(ModSem.initial_frame) oh_new args st_new)
    :
    step se ge ((StackCons dl st0 tl), ohs0)
         E0 ((StackCons dr st_new (StackCons dl st0 tl)), ohs1)

  | step_internal_dl
      st0 tr st1 tl ohs
      (STEP: Step msdl st0 tr st1)
    :
      step se ge ((StackCons dl st0 tl), ohs)
           tr ((StackCons dl st1 tl), ohs)

  | step_return_dl
      st_old st0 st1 tl oh0 oh_old ohs0 ohs1 retv
      (AT: msdl.(ModSem.final_frame) st0 oh0 retv)
      (OHS: ohs1 = (oh0, snd ohs0))

      (OH: snd ohs1 = oh_old)
      (INIT: msdr.(ModSem.after_external) st_old oh_old retv st1)
    :
    step se ge ((StackCons dl st0 (StackCons dr st_old tl)), ohs0)
         E0 ((StackCons dr st1 tl), ohs1)


  (* | step_internal *)
  (*     (b: bool) st0 tr st1 tl ohs *)
  (*     (STEP: ModSem.step (ms b) ((ms b).(ModSem.skenv_link)) ((ms b).(ModSem.globalenv)) st0 tr st1) *)
  (*   : *)
  (*     step se ge ((StackCons b st0 tl), ohs) *)
  (*          tr ((StackCons b st1 tl), ohs) *)

  | step_call_dr
      st0 st_new tl oh0 oh_new ohs0 ohs1 args
      (AT: msdr.(ModSem.at_external) st0 oh0 args)
      (OHS: ohs1 = (fst ohs0, oh0))

      (MSFIND: find_fptr_owner (Args.get_fptr args) msdr)
      (OH: fst ohs1 = oh_new)
      (INIT: msdl.(ModSem.initial_frame) oh_new args st_new)
    :
    step se ge ((StackCons dr st0 tl), ohs0)
         E0 ((StackCons dl st_new (StackCons dr st0 tl)), ohs1)

  | step_internal_dr
      st0 tr st1 tl ohs
      (STEP: Step msdr st0 tr st1)
    :
      step se ge ((StackCons dr st0 tl), ohs)
           tr ((StackCons dr st1 tl), ohs)

  | step_return_dr
      st_old st0 st1 tl oh0 oh_old ohs0 ohs1 retv
      (AT: msdr.(ModSem.final_frame) st0 oh0 retv)
      (OHS: ohs1 = (fst ohs0, oh0))

      (OH: fst ohs1 = oh_old)
      (INIT: msdl.(ModSem.after_external) st_old oh_old retv st1)
    :
    step se ge ((StackCons dr st0 (StackCons dl st_old tl)), ohs0)
         E0 ((StackCons dl st1 tl), ohs1)
  .

  Variant at_external: state -> owned_heap -> Args.t -> Prop :=
  | at_external_dl
      st0 tl oh0 ohs0 args
      (AT: msdl.(ModSem.at_external) st0 oh0 args)
      (MSFIND: forall msdr, ~find_fptr_owner (Args.get_fptr args) msdr)
    :
      at_external ((StackCons dl st0 tl), ohs0) (oh0, snd ohs0) args

  | at_external_dr
      st0 tl oh0 ohs0 args
      (AT: msdr.(ModSem.at_external) st0 oh0 args)
      (MSFIND: forall msdl, ~find_fptr_owner (Args.get_fptr args) msdl)
    :
      at_external ((StackCons dr st0 tl), ohs0) (fst ohs0, oh0) args
  .

  Variant initial_frame (ohs: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_dl
      st0
      (MSFIND: find_fptr_owner (Args.get_fptr args) msdl)
      (INIT: msdl.(ModSem.initial_frame) (fst ohs) args st0)
    :
      initial_frame ohs args (StackCons dl st0 StackNil, ohs)

  | initial_frame_dr
      st0
      (MSFIND: find_fptr_owner (Args.get_fptr args) msdr)
      (INIT: msdr.(ModSem.initial_frame) (snd ohs) args st0)
    :
      initial_frame ohs args (StackCons dr st0 StackNil, ohs)
  .

  Variant final_frame: state -> owned_heap -> Retv.t -> Prop :=
  | final_frame_dl
      st0 retv ohs0 oh0
      (FINAL: msdl.(ModSem.final_frame) st0 oh0 retv)
    :
      final_frame (StackCons dl st0 StackNil, ohs0) (oh0, snd ohs0) retv

  | final_frame_dr
      st0 retv ohs0 oh0
      (FINAL: msdr.(ModSem.final_frame) st0 oh0 retv)
    :
      final_frame (StackCons dr st0 StackNil, ohs0) (fst ohs0, oh0) retv
  .

  Variant after_external: state -> owned_heap -> Retv.t -> state -> Prop :=
  | after_external_dl
      tl st0 ohs0 ohs1 retv st1
      (AFTER: msdl.(ModSem.after_external) st0 (fst ohs1) retv st1)
    :
      after_external (StackCons dl st0 tl, ohs0) ohs1 retv (StackCons dl st1 tl, ohs1)

  | after_external_dr
      tl st0 ohs0 ohs1 retv st1
      (AFTER: msdr.(ModSem.after_external) st0 (snd ohs1) retv st1)
    :
      after_external (StackCons dr st0 tl, ohs0) ohs1 retv (StackCons dr st1 tl, ohs1)
  .

  Program Definition t: ModSem.t :=
    {|
      ModSem.state := state;
      ModSem.owned_heap := owned_heap;
      ModSem.genvtype := genvtype;
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.initial_owned_heap := initial_owned_heap;
      ModSem.globalenv := globalenv;
      ModSem.skenv := link_skenv msdl.(ModSem.skenv) msdr.(ModSem.skenv);
      ModSem.skenv_link := skenv_link;
      ModSem.midx := msdl.(ModSem.midx); (*** <-- TODO: prettify later ***)
    |}
  .
  Next Obligation.
    ii.
    inv AT0.
    - remember (StackCons dl st0 tl, ohs0) as Y.
      inv AT1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.at_external_dtm; esplits; et.
    - remember (StackCons dr st0 tl, ohs0) as Y.
      inv AT1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.at_external_dtm; esplits; et.
  Qed.
  Next Obligation.
    ii.
    inv FINAL0.
    - remember (StackCons dl st0 StackNil, ohs0) as Y.
      inv FINAL1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.final_frame_dtm; esplits; et.
    - remember (StackCons dr st0 StackNil, ohs0) as Y.
      inv FINAL1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.final_frame_dtm; esplits; et.
  Qed.
  Next Obligation.
    ii.
    inv AFTER0.
    - remember (StackCons dl st2 tl, ohs0) as Y.
      inv AFTER1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.after_external_dtm; esplits; et.
    - remember (StackCons dr st2 tl, ohs0) as Y.
      inv AFTER1; ss. eapply state_inj in H. des; clarify.
      determ_tac ModSem.after_external_dtm; esplits; et.
  Qed.
  Next Obligation.
    ii. rr. des.
    pose x0 as X.
    inv PR.
    - remember (StackCons dl st0 tl, ohs0) as Y.
      inv PR0; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
      determ_tac ModSem.at_external_dtm. eapply MSFIND; eauto.
    - remember (StackCons dr st0 tl, ohs0) as Y.
      inv PR0; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
      determ_tac ModSem.at_external_dtm. eapply MSFIND; eauto.
  Qed.
  Next Obligation.
    ii. rr. des.
    pose x0 as X.
    inv PR0.
    - remember (StackCons dl st0 StackNil, ohs0) as Y.
      inv PR; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
    - remember (StackCons dr st0 StackNil, ohs0) as Y.
      inv PR; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
  Qed.
  Next Obligation.
    ii. rr. des.
    pose x0 as X.
    inv PR.
    - remember (StackCons dl st0 tl, ohs0) as Y.
      inv PR0; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
    - remember (StackCons dr st0 tl, ohs0) as Y.
      inv PR0; ss; eapply state_inj in H; des; clarify; try (by ModSem.tac).
  Qed.
  Next Obligation.
    i. ss.
  Qed.

End MODTUPLE.


(*** if we put "MODTUPLE" section inside "ModTuple" module, "Print ModTuple" will be very messy ***)
Module ModTuple.
  Definition t := Eval red in t.
End ModTuple.
Print ModTuple.
Print ModTuple.t.

