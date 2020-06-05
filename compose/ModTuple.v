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
Require Import LinkingC LinkingProps SemProps ModSemProps.
Require Import BehaviorsC.

Require Import Simulation.
Require Import Mod Sem ModSem.
Require Import Any.
Require Import Program.

Set Implicit Arguments.












(*** TODO: move to Mod.v ***)
Lemma Mod_modsem_midx_spec
      (md: Mod.t) skenv_link
  :
    <<EQ: ModSem.midx (md skenv_link) = md.(Mod.midx)>>
.
Proof.
  u. rewrite Mod.get_modsem_midx_spec. ss.
Qed.

Lemma Mod_modsem_skenv_link_spec
      (md: Mod.t) skenv_link
  :
    <<EQ: ModSem.skenv_link (md skenv_link) = skenv_link>>
.
Proof.
  u. rewrite Mod.get_modsem_skenv_link_spec. ss.
Qed.

(*** TODO: move to ModSem.Midx ***)
Lemma NoDup_inj
      (prog: program)
      (NODUP: Midx.NoDup (map Mod.midx prog))
      md0 md1
      (NEQ: md0 <> md1)
      (SOME0: md0.(Mod.midx) <> None)
      (SOME1: md1.(Mod.midx) <> None)
      (IN0: In md0 prog)
      (IN1: In md1 prog)
  :
    md0.(Mod.midx) <> md1.(Mod.midx)
.
Proof.
  unfold Midx.NoDup, id in *.
  ginduction prog; i; ss.
  des_ifs.
  - inv NODUP. des; clarify; et.
    + intro T. rewrite <- T in *. eapply H1. eapply in_filter_map_iff. esplits; et. rewrite in_map_iff; et.
    + intro T. rewrite T in *. eapply H1. eapply in_filter_map_iff. esplits; et. rewrite in_map_iff; et.
  - des; clarify; et.
Qed.



(*** TODO: move to ModSem.Midx ***)
Lemma NoDup_app
      mis0 mis1
  :
    (<<NODUP: Midx.NoDup (mis0 ++ mis1)>>) <->
    ((<<NODUMIS0: Midx.NoDup mis0>>) /\ (<<NODUMIS1: Midx.NoDup mis1>>) /\
     (<<APP: forall mi0 mi1 (IN0: In mi0 mis0) (IN1: In mi1 mis1), (mi0 <> mi1 \/ mi0 = None \/ mi1 = None)>>))
.
Proof.
  split; i.
  - ginduction mis0; ii; ss.
    { esplits; et. econs; et. }
    eapply Midx.NoDup_cons_iff in H.
    des; clarify.
    + eapply IHmis0 in TL. des. esplits; et.
      ii. des; clarify.
      { destruct mi1 eqn:T; clarify; ss; et. }
      { exploit APP; et. }
    + dup TL. eapply IHmis0 in TL. des. esplits; et.
      { eapply Midx.NoDup_cons_iff. esplits; et. right. ii. eapply HD. rewrite in_app_iff. et. }
      { ii. des; clarify.
        - left. ii. clarify. eapply HD. rewrite in_app_iff. et.
        - exploit APP; et.
      }
  - ginduction mis0; ii; ss; des; ss.
    eapply Midx.NoDup_cons_iff in NODUMIS0.
    eapply Midx.NoDup_cons_iff.
    des; clarify.
    + esplits; et.
      eapply IHmis0; et. esplits; et.
    + exploit IHmis0; et.
      { esplits; et. }
      intro T; des.
      destruct a eqn:U; et.
      esplits; et.
      right. ii. rewrite in_app_iff in *. des; ss.
      exploit APP; et.
      i. des; ss.
Qed.

(*** TODO: move to ASTC ***)
Lemma internals_linkorder
      (sk0 sk1: Sk.t)
      (LO: linkorder sk0 sk1)
  :
    internals sk0 <1= internals sk1
.
Proof.
  Local Transparent Linker_prog.
  ss. des. ii.
  Local Opaque Linker_prog.
  unfold internals in *. des_ifs_safe.
  exploit LO1; et. i; des. des_ifs_safe. inv H0; ss. inv H; ss.
Qed.




Local Obligation Tactic := idtac.

Section MODSEMTUPLE.

  Variable msdl msdr: ModSem.t.
  Variable sk: Sk.t.
  Variable skenv_link: SkEnv.t.
  Let skenv := SkEnv.project skenv_link sk.
  Variable midx: string.

  Definition owned_heap: Type := (msdl.(ModSem.owned_heap) * msdr.(ModSem.owned_heap)).

  Definition initial_owned_heap: owned_heap :=
    (msdl.(ModSem.initial_owned_heap), msdr.(ModSem.initial_owned_heap)).

  (* Definition genvtype: Type := (msdl.(ModSem.genvtype) * msdr.(ModSem.genvtype)). *)

  (* Definition globalenv: genvtype := (msdl.(ModSem.globalenv), msdr.(ModSem.globalenv)). *)

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

  Variant step (se: Senv.t) (ge: unit): state -> trace -> state -> Prop :=
  | step_call_dl
      st0 st_new tl oh0 oh_new ohs0 ohs1 args
      (AT: msdl.(ModSem.at_external) st0 oh0 args)
      (OHS: ohs1 = (oh0, snd ohs0))

      (MSFIND: Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdr)
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
      (RET: msdl.(ModSem.final_frame) st0 oh0 retv)
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

      (MSFIND: Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdl)
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
      (RET: msdr.(ModSem.final_frame) st0 oh0 retv)
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
      (MSFIND: forall ms, ~Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) ms)
    :
      at_external ((StackCons dl st0 tl), ohs0) (oh0, snd ohs0) args

  | at_external_dr
      st0 tl oh0 ohs0 args
      (AT: msdr.(ModSem.at_external) st0 oh0 args)
      (MSFIND: forall ms, ~Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) ms)
    :
      at_external ((StackCons dr st0 tl), ohs0) (fst ohs0, oh0) args
  .

  Variant initial_frame (ohs: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_dl
      st0
      (MSFIND: Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdl)
      (INIT: msdl.(ModSem.initial_frame) (fst ohs) args st0)
    :
      initial_frame ohs args (StackCons dl st0 StackNil, ohs)

  | initial_frame_dr
      st0
      (MSFIND: Ge.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdr)
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
      ModSem.genvtype := unit;
      ModSem.step := step;
      ModSem.at_external := at_external;
      ModSem.initial_frame := initial_frame;
      ModSem.final_frame := final_frame;
      ModSem.after_external := after_external;
      ModSem.initial_owned_heap := initial_owned_heap;
      ModSem.globalenv := tt;
      (* ModSem.skenv := SkEnv.link msdl.(ModSem.skenv) msdr.(ModSem.skenv); *)
      ModSem.skenv := skenv;
      ModSem.skenv_link := skenv_link;
      (* ModSem.midx := msdl.(ModSem.midx); (*** <-- TODO: prettify later ***) *)
      ModSem.midx := Some midx; (*** <-- TODO: prettify later ***)
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

End MODSEMTUPLE.

Arguments StackNil {msdl} {msdr}.


(*** if we put "MODTUPLE" section inside "ModTuple" module, "Print ModTuple" will be very messy ***)
Module ModSemTuple.
  Definition t := Eval red in t.
End ModSemTuple.
Print ModSemTuple.
Print ModSemTuple.t.



Section MODTUPLE.

  Variable mdl mdr: Mod.t.
  Variable sk_link: Sk.t.
  Variable midx: string.
  (* Hypothesis SKLINK: link (Mod.sk mdl) (Mod.sk mdr) = Some sk_link. *)

  Program Definition t': Mod.t :=
    {|
      Mod.datatype := (mdl.(Mod.datatype) * mdr.(Mod.datatype))%type;
      Mod.get_sk := fun _ => sk_link;
      (* Mod.get_sk := fun '(l, r) => *)
      (*                 match link (Mod.get_sk mdl l) (Mod.get_sk mdr r) with *)
      (*                 | Some sk => sk *)
      (*                 | None => Sk.empty *)
      (*                 end; *)
      Mod.get_modsem := fun ske '(l, r) =>
                          ModSemTuple.t (Mod.get_modsem mdl ske l) (Mod.get_modsem mdr ske r) sk_link ske midx;
      Mod.data := (mdl.(Mod.data), mdr.(Mod.data));
      Mod.midx := Some midx;
    |}
  .
  Next Obligation.
    ii. ss.
    (* unfold Mod.sk in *. des_ifs. *)
  Qed.
  Next Obligation.
    ii. ss.
  Qed.
  Next Obligation.
    ii. ss. des_ifs.
  Qed.

End MODTUPLE.

Module ModTuple.
  Definition t := Eval red in t'.

  Section MERGE.
    Variable mdl mdr: Mod.t.
    Variable sk: Sk.t.
    Variable midx: string.
    Let md_link: Mod.t := t mdl mdr sk midx.
    Variable ctx1 ctx2: list Mod.t.
    Hypothesis (LINKSK: link (mdl: Sk.t) mdr = Some sk).
    Let mil: Midx.t := mdl.(Mod.midx).
    Let mir: Midx.t := mdr.(Mod.midx).
    Hypothesis MIDIFF: mil <> mir.
    Hypothesis (MIDXL: mil = Some midx).
    Hypothesis (MIDXR: mir <> None).
    Hypothesis (WFL: Sk.wf mdl).
    Hypothesis (WFR: Sk.wf mdr).
    Hypothesis DTML: forall
        skenv_link oh args st0 st1
        (INIT0: (Mod.modsem mdl skenv_link).(ModSem.initial_frame) oh args st0)
        (INIT1: (Mod.modsem mdl skenv_link).(ModSem.initial_frame) oh args st1)
      ,
        st0 = st1
    .
    Hypothesis DTMR: forall
        skenv_link oh args st0 st1
        (INIT0: (Mod.modsem mdr skenv_link).(ModSem.initial_frame) oh args st0)
        (INIT1: (Mod.modsem mdr skenv_link).(ModSem.initial_frame) oh args st1)
      ,
        st0 = st1
    .
    Hypothesis MICTX1: forall md (IN: In md ctx1), md.(Mod.midx) <> mir.
    Hypothesis MICTX2: forall md (IN: In md ctx2), md.(Mod.midx) <> mir.

    Let WFLINK: Sk.wf (t mdl mdr sk midx).
    Proof.
      eapply link_preserves_wf_sk in LINKSK; et.
    Qed.

    Let prog_src: program := (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2).
    Let prog_tgt: program := (ctx1 ++ [mdl] ++ [mdr] ++ ctx2).

    Let LINKSAME: forall
        (* (WFL: Sk.wf mdl) *)
        (* (WFR: Sk.wf mdr) *)
        (* (WF: Sk.wf sk) *)
        (* (WFCTX1: forall md (IN: In md ctx1), Sk.wf md) *)
        (* (WFCTX2: forall md (IN: In md ctx2), Sk.wf md) *)
        (WF: forall md (IN: In md (ctx1 ++ mdl :: mdr :: ctx2)), Sk.wf md)
      ,
        <<EQ: link_sk (ctx1 ++ [mdl] ++ [mdr] ++ ctx2) = link_sk (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2)>>.
    Proof.
      i. erewrite link_sk_prepend_eq; eauto.
      { ss. }
      unfold t. unfold link_sk. ss.
      replace (Mod.sk mdl :: Mod.sk mdr :: PList.map Mod.sk ctx2)
        with ([Mod.sk mdl ; Mod.sk mdr] ++ PList.map Mod.sk ctx2) by ss.
      erewrite link_list_assoc_one; ss; try eapply WF; ss; try rewrite in_app; ss; eauto.
      ii. rewrite PList.map_mono in *. rewrite in_map_iff in *. des; clarify; et.
      try eapply WF; ss; try rewrite in_app; ss; eauto.
    Qed.

    Section MATCH.
      Variable skenv_link: SkEnv.t.
      Let msdl: ModSem.t := (Mod.modsem mdl skenv_link).
      Let msdr: ModSem.t := (Mod.modsem mdr skenv_link).
      Let ms_link: ModSem.t := (ModSemTuple.t msdl msdr sk skenv_link midx).

      Inductive get_latest_focus: Frame.t -> ms_link.(ModSem.owned_heap) -> Prop :=
      | get_latest_stack_intro
          stk ohsl ohsr
        :
          get_latest_focus (Frame.mk ms_link (stk, (ohsl, ohsr))) (ohsl, ohsr)
      .

      Inductive get_latest: Smallstep.state (sem prog_src) -> Ohs -> Prop :=
      | get_latest_call
          args frs ohs
        :
          get_latest (Callstate args frs ohs) ohs
      | get_latest_normal_ctx
          hd frs ohs
          (NFOC: hd.(Frame.ms).(ModSem.midx) <> mil)
        :
          get_latest (State (hd :: frs) ohs) ohs
      | get_latest_normal_focus
          hd frs ohs oh_link
          (FOC: hd.(Frame.ms).(ModSem.midx) = mil)
          (GET: get_latest_focus hd oh_link)
        :
          get_latest (State (hd :: frs) ohs) (Midx.update ohs mil (upcast oh_link))
      .

      (*** TODO: move to CoqlibC ***)
      Lemma func_app_dep
            (X: Type) (Y: X -> Type)
            (f: forall (x: X), Y x)
            x0 x1
            (EQ: x0 = x1)
        :
          <<EQ: f x0 ~= f x1>>
      .
      Proof. clarify. Qed.
      Arguments func_app_dep [_] [_].

      Lemma get_latest_dtm
            st_src0 ohs0 ohs1
            (GET0: get_latest st_src0 ohs0)
            (GET1: get_latest st_src0 ohs1)
        :
          ohs0 = ohs1
      .
      Proof.
        inv GET0; inv GET1; ss.
        inv GET; inv GET0; ss. do 2 f_equal.
        apply func_app_dep with (f:= Frame.st) in H. ss. des. apply JMeq_eq in H. clarify.
      Qed.

      Inductive match_focus_stack: (stack msdl msdr) -> list Frame.t -> Prop :=
      | match_focus_stack_nil
        :
          match_focus_stack StackNil nil
      | match_focus_stack_cons_dl
          st_src st_tgt stk frs
          (TL: match_focus_stack stk frs)
          (STEQ: st_src = st_tgt)
        :
          match_focus_stack (StackCons dl st_src stk) ((Frame.mk msdl st_tgt) :: frs)
      | match_focus_stack_cons_dr
          st_src st_tgt stk frs
          (TL: match_focus_stack stk frs)
          (STEQ: st_src = st_tgt)
        :
          match_focus_stack (StackCons dr st_src stk) ((Frame.mk msdr st_tgt) :: frs)
      .

      (***
          Q: state maintains "owned_heap"... if it is outdated, what is the meaning of it?
          A(?): it is nothing special -- it is almost the same with "memory" (which is hidden inside state too)
          No(!): owned_heap is in (1) msl/msr.state (hidden), (2) ModSemTuple.state, and (3) Sem.state
       ***)

      (***
          Note: src synchronizes (update global Ohs) less than target.
          WTS: (at least) when synchronization happens, it should coincide
       ***)

      Inductive sim_ohs (ohs_src ohs_tgt: Ohs): Prop :=
      | sim_ohs_intro
          (OHS: forall mj (NL: mj <> mil) (NR: mj <> mir),
              ohs_src mj = ohs_tgt mj)
          ohl ohr
          (OHLR: @downcast ms_link.(ModSem.owned_heap) (ohs_src mil) = Some (ohl, ohr))
          (OHL: @downcast msdl.(ModSem.owned_heap) (ohs_tgt mil) = Some ohl)
          (OHR: @downcast msdr.(ModSem.owned_heap) (ohs_tgt mir) = Some ohr)
      .

      (*** ohs_tgt is the latest known global Ohs. src's internal Ohs should be consistent with it ***)
      Inductive match_stacks: list Frame.t -> list Frame.t -> Prop :=
      | match_stacks_nil
        :
          match_stacks [] []
      | match_stacks_cons_ctx
          tail_src tail_tgt
          (TAIL: match_stacks tail_src tail_tgt) hd
          (NL: hd.(Frame.ms).(ModSem.midx) <> mil)
          (NR: hd.(Frame.ms).(ModSem.midx) <> mir)
        :
          match_stacks (hd :: tail_src) (hd :: tail_tgt)
      | match_stacks_focus
          frs_src frs_tgt tail_src tail_tgt
          hd_src stk_src oh_src hd_tgt hds_tgt
          (FRSSRC: frs_src = (hd_src :: tail_src))
          (FRSTGT: frs_tgt = (hd_tgt :: hds_tgt ++ tail_tgt))
          (TAIL: match_stacks tail_src tail_tgt)
          (HD: match_focus_stack stk_src (hd_tgt :: hds_tgt))
          (STK: hd_src = Frame.mk ms_link (stk_src, oh_src))
        :
          match_stacks frs_src frs_tgt
      .

      Lemma match_stacks_right_nil
            frs
            (STK: match_stacks frs []) :
        <<NIL: frs = []>>.
      Proof.
        inv STK; ss.
      Qed.

      Inductive match_states : Sem.state -> Sem.state -> Prop :=
      | match_states_normal
          frs_src frs_tgt ohs_src ohs_latest_src ohs_tgt
          (STK: match_stacks frs_src frs_tgt)
          (* (OHS: forall mj (NL: mj <> msdl.(ModSem.midx)) (NR: mj <> msdr.(ModSem.midx)), *)
          (*     ohs_src mj = ohs_tgt mj) *)
          (LATEST: get_latest (State frs_src ohs_src) ohs_latest_src)
          (OHS: sim_ohs ohs_latest_src ohs_tgt)
        :
          match_states (State frs_src ohs_src) (State frs_tgt ohs_tgt)
      | match_states_call
          frs_src frs_tgt args ohs_src ohs_tgt
          (STK: match_stacks frs_src frs_tgt)
          (OHS: sim_ohs ohs_src ohs_tgt)
        :
          match_states (Callstate args frs_src ohs_src) (Callstate args frs_tgt ohs_tgt)
      .

    End MATCH.

    Section SIM.

      Variable sk_link: Sk.t.
      Hypothesis LINKSRC: link_sk prog_src = Some sk_link.
      Let skenv_link := Sk.load_skenv sk_link.
      Let msdl: ModSem.t := (Mod.modsem mdl skenv_link).
      Let msdr: ModSem.t := (Mod.modsem mdr skenv_link).
      Let ms_link: ModSem.t := (Mod.modsem md_link skenv_link).
      Hypothesis WFCTX1: forall md (IN: In md ctx1), <<WF: Sk.wf md>>.
      Hypothesis WFCTX2: forall md (IN: In md ctx2), <<WF: Sk.wf md>>.
      Let LINKTGT: link_sk prog_tgt = Some sk_link.
      Proof.
        unfold prog_src, prog_tgt in *. unfold link_sk in *.
        rewrite LINKSAME in *; ss.
        ii. rewrite in_app_iff in *. des; ss; des; clarify; eauto.
        - eapply WFCTX1; et.
        - eapply WFCTX2; et.
      Qed.
      Let INCLSRC: forall md (IN: In md prog_src), SkEnv.includes skenv_link (md: (Sk.t)).
      Proof. eapply link_includes; et. Qed.
      Let INCLTGT: forall md (IN: In md prog_tgt), SkEnv.includes skenv_link (md: (Sk.t)).
      Proof. eapply link_includes; et. Qed.
      Hypothesis NODUPSRC: Midx.NoDup (map Mod.midx prog_src).
      Hypothesis NODUPTGT: Midx.NoDup (map Mod.midx prog_tgt).
      (* Let NODUPTGT: Midx.NoDup (map Mod.midx prog_tgt). *)
      (* Proof. *)
      (*   clear - NODUPSRC MICTX1 MICTX2 MIDIFF MIDXL MIDXR. *)
      (*   unfold prog_src, prog_tgt in *. *)
      (*   rewrite ! map_app in *. *)
      (*   apply NoDup_app in NODUPSRC. destruct NODUPSRC as [A [B C]]. clear NODUPSRC. *)
      (*   apply NoDup_app in B. destruct B as [D [E F]]. *)
      (*   (* ss. rewrite cons_app with (xtl := map Mod.midx ctx2). *) *)
      (*   apply NoDup_app. *)
      (*   { esplits; et. *)
      (*     - rewrite app_assoc. *)
      (*       apply NoDup_app. *)
      (*       + esplits; et; ss. *)
      (*         * r. folder. rewrite MIDXL. ss. destruct mir eqn:T; ss. econs; ss; et. *)
      (*           { ii. des; clarify. } *)
      (*           { econs; et. econs; et. } *)
      (*         * ii. *)
      (*           exploit F; et. intro T. des_safe. des; ss; clarify; eauto. *)
      (*           rewrite in_map_iff in *. des; clarify. *)
      (*           hexploit MICTX2; et. *)
      (*     - ii. *)
      (*       destruct (classic (mi1 = mir)). *)
      (*       { clarify. *)
      (*         left. ii. clarify. rewrite in_map_iff in IN0. des; clarify. ss. exploit MICTX1; et. *)
      (*       } *)
      (*       exploit C; et. rewrite in_app_iff in *; ss. des; clarify; et. *)
      (*   } *)
      (* Qed. *)

      Ltac my_depdes H :=
        multimatch goal with
        | [ H': match_focus_stack _ ?a ?b |- _ ] =>
          check_equal H H';
          let X := fresh "X" in
          let HX := fresh "HX" in
          let Y := fresh "Y" in
          let HY := fresh "HY" in
          remember a as X eqn:HX; remember b as Y eqn:HY;
          depdes H; ss; try (apply stack_inj in HX; des); clarify
        | [ H': step _ _ ?a _ _ |- _ ] =>
          check_equal H H';
          let X := fresh "X" in
          let HX := fresh "HX" in
          remember a as X eqn:HX;
          depdes H; ss; try (apply state_inj in HX; des); clarify
        | [ H': get_latest_focus ?a ?b |- _ ] =>
          check_equal H H';
          let X := fresh "X" in
          let HX := fresh "HX" in
          let Y := fresh "Y" in
          let HY := fresh "HY" in
          remember a as X eqn:HX; remember b as Y eqn:HY;
          depdes H; ss; try (apply func_app_dep with (f:= Frame.st) in HX; des; ss; apply JMeq_eq in HX);
          clarify
        | [ H': final_frame ?a _ _ |- _ ] =>
          check_equal H H';
          let X := fresh "X" in
          let HX := fresh "HX" in
          remember a as X eqn:HX;
          depdes H; ss; try (apply state_inj in HX; des); clarify
        | [ H': after_external ?a _ _ ?b |- _ ] =>
          check_equal H H';
          let X := fresh "X" in
          let HX := fresh "HX" in
          let Y := fresh "Y" in
          let HY := fresh "HY" in
          remember a as X eqn:HX; remember b as Y eqn:HY;
          depdes H; ss; try (apply stack_inj in HX; des); try (apply stack_inj in HY; des); clarify
        end
      .

      Ltac simpl_md := try rewrite ! Mod_modsem_skenv_link_spec in *;
                       try rewrite ! Mod_modsem_midx_spec in *.

      Lemma final_bsim
            retv ohs_src frs_src ohs_tgt frs_tgt
            (MATCH: match_states skenv_link (State frs_src ohs_src) (State frs_tgt ohs_tgt))
            (FINAL: final_state (State frs_tgt ohs_tgt) retv)
            (SAFESRC: safe (sem prog_src) (State frs_src ohs_src)) :
        <<FINAL: final_state (State frs_src ohs_src) retv>>.
      Proof.
        ss. inv FINAL. inv MATCH; ss. inv STK; ss.
        - (* ctx *)
          exploit match_stacks_right_nil; eauto. i; des; clarify.
          econs; eauto.
        - (* focus *)
          clarify. destruct hds_tgt, tail_tgt; ss.
          exploit match_stacks_right_nil; et. i; des; clarify.
          my_depdes HD; ss.
          + my_depdes HD; ss. econs; ss; et. rp; econs; et.
          + my_depdes HD; ss. econs; ss; et. rp; econs; et.
      Qed.

      Lemma final_fsim
            retv frs_src frs_tgt ohs_src ohs_tgt
            (MATCH: match_states skenv_link (State frs_src ohs_src) (State frs_tgt ohs_tgt))
            (FINAL: final_state (State frs_src ohs_src) retv) :
        <<DFINAL: Dfinal_state (sem prog_tgt) (State frs_tgt ohs_tgt) retv>>.
      Proof.
        rr. econs; ss; et.
        { inv FINAL. inv MATCH; ss. inv STK; ss.
          (* ctx *)
          - inv TAIL; clarify. econs; et.
          (* focus *)
          - inv TAIL; clarify. rewrite app_nil_r in *. inv FINAL0; ss; clear_tac.
            + my_depdes HD. inv HD. econs; ss; et.
            + my_depdes HD. inv HD. econs; ss; et.
        }
        (*** TODO: put final_state_dtm in SemProps ***)
        { ii; ss. inv FINAL0; inv FINAL1; ss. determ_tac ModSem.final_frame_dtm. rewrite INT in *. clarify. }
        {
          i. inv FINAL0. ii. des_ifs. inv H; ModSem.tac.
        }
      Qed.

      Lemma src_no_mir
            ms
            (MODSEM: In ms (load_modsems prog_src skenv_link))
        :
          ModSem.midx ms <> mir
      .
      Proof.
        unfold load_modsems in *. rewrite in_map_iff in *. des; clarify.
        unfold prog_src in *. rewrite in_app_iff in *; ss. des; clarify.
        - unfold flip. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. et.
        - unfold flip. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. ss. congruence.
        - unfold flip. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. et.
      Qed.

      Let PROJL: SkEnv.project_spec skenv_link mdl (SkEnv.project skenv_link mdl).
      Proof.
        { eapply SkEnv.project_impl_spec. eapply INCLTGT. unfold prog_tgt. rewrite in_app_iff; ss. et. }
      Qed.
      Let PROJR: SkEnv.project_spec skenv_link mdr (SkEnv.project skenv_link mdr).
      Proof.
        { eapply SkEnv.project_impl_spec. eapply INCLTGT. unfold prog_tgt. rewrite in_app_iff; ss. et. }
      Qed.
      Let PROJLINK: SkEnv.project_spec skenv_link md_link (SkEnv.project skenv_link md_link).
      Proof.
        { eapply SkEnv.project_impl_spec. eapply INCLSRC. unfold prog_src. rewrite in_app_iff; ss. et. }
      Qed.

      Lemma msfind_fsim
            ms fptr
            (MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms)
        :
          exists ms_tgt,
            <<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms_tgt>> /\
                      ((<<CTX: ms_tgt = ms /\ ms.(ModSem.midx) <> mil /\ ms.(ModSem.midx) <> mir>>) \/
                       (<<FOCL: ms_tgt = Mod.modsem mdl skenv_link>> /\ <<FOC: ms = ms_link>>) \/
                       (<<FOCR: ms_tgt = Mod.modsem mdr skenv_link>> /\ <<FOC: ms = ms_link>>))
      .
      Proof.
        { clear - MSFIND ms_link msdl msdr LINKSK skenv_link INCLSRC INCLTGT MIDXL MIDXR NODUPSRC MIDIFF
                         MICTX1 MICTX2 PROJL PROJR PROJLINK.
          inv MSFIND. ss. des; clarify.
          { esplits; try left; et.
            - econs; et. ss. et.
            - ss. esplits; eauto with congruence.
          }
          destruct (classic (ms = ms_link)).
          - clarify. ss.
            assert(FIND: Genv.find_funct (SkEnv.project skenv_link mdl) fptr = Some (Internal if_sig)
                         \/ Genv.find_funct (SkEnv.project skenv_link mdr) fptr = Some (Internal if_sig)).
            { Local Transparent Linker_prog.
              dup LINKSK. apply link_linkorder in LINKSK0. des; ss; des.
              Local Opaque Linker_prog.
              ss.
              assert(DISJ: SkEnv.disj (SkEnv.project skenv_link mdl) (SkEnv.project skenv_link mdr)).
              { eapply SkEnv.project_respects_disj; et. eapply Sk.link_disj; et. }

              unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
              destruct (Genv.invert_symbol skenv_link b) eqn:INV.
              - inv PROJLINK. exploit DEFKEPT; et. i; des. ss. inv LO. inv H1.
                (*** TODO: make lemma ***)
                assert(<<LEFT: (prog_defmap (mdl: Sk.t)) ! i = (prog_defmap sk) ! i>> \/
                               <<RIGHT: (prog_defmap (mdr: Sk.t)) ! i = (prog_defmap sk) ! i>>).
                { clear - PROG LINKSK.
                  unfold link_prog in *. des_ifs. bsimpl; des; ss; des_sumbool.
                  unfold prog_defmap in *. ss. rewrite PTree_Properties.of_list_elements in *.
                  rewrite PTree.gcombine in *; ss. unfold link_prog_merge in PROG. des_ifs; ss; et.
                  Local Transparent Linker_def.
                  ss.
                  Local Opaque Linker_def.
                  unfold link_def in *. des_ifs. ss.
                  unfold link_skfundef in *. des_ifs; et.
                }
                des.
                + rewrite PROG in *. inv PROJL. exploit DEFKEEP0; et.
                  { unfold internals. des_ifs. }
                  i; des. clarify. left. des_ifs.
                + rewrite PROG in *. inv PROJR. exploit DEFKEEP0; et.
                  { unfold internals. des_ifs. }
                  i; des. clarify. right. des_ifs.
              - inv PROJLINK. exploit DEFORPHAN; et. i; des. ss. clarify.
            }
            des.
            + exists msdl. subst msdl. esplits; et. econs; ss; et.
              { right. unfold load_modsems, flip. rewrite in_map_iff. unfold prog_tgt.
                exists mdl. esplits; ss; et. rewrite in_app_iff; ss. et. }
              unfold Mod.modsem. rewrite <- Mod.get_modsem_skenv_spec. et.
            + exists msdr. subst msdr. esplits; et. econs; ss; et.
              { right. unfold load_modsems, flip. rewrite in_map_iff. unfold prog_tgt.
                exists mdr. esplits; ss; et. rewrite in_app_iff; ss. et. }
              unfold Mod.modsem. rewrite <- Mod.get_modsem_skenv_spec. et.
          - esplits; try left; et.
            + econs; et. ss. right.
              unfold load_modsems, flip in *. rewrite in_map_iff in *. unfold prog_src, prog_tgt in *.
              des. clarify.
              exists x. esplits; ss; et. rewrite in_app_iff in *; ss. des; clarify; et.
            + esplits; et.
              * unfold load_modsems in *. rewrite in_map_iff in *. des; clarify. unfold flip in *.
                unfold Mod.modsem, mil. rewrite Mod.get_modsem_midx_spec.
                replace (Mod.midx mdl) with (Mod.midx md_link) by ss.
                destruct (Mod.midx x) eqn:T; cycle 1.
                { ss. }
                rewrite <- T.
                eapply NoDup_inj with (md0 := x) (md1 := md_link); et; ss.
                { ii. clarify. }
                { congruence. }
                { unfold prog_src. rewrite in_app_iff; ss. et. }
              * eapply src_no_mir; et.
        }
      Qed.

      Lemma msfind_bsim
            ms fptr
            (MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms)
        :
          exists ms_src,
            <<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms_src>> /\
                      ((<<CTX: ms = ms_src /\ ms.(ModSem.midx) <> mil /\ ms.(ModSem.midx) <> mir>>) \/
                       (<<FOCL: ms = Mod.modsem mdl skenv_link>> /\ <<FOC: ms_src = ms_link>>) \/
                       (<<FOCR: ms = Mod.modsem mdr skenv_link>> /\ <<FOC: ms_src = ms_link>>))
      .
      Proof.
        {
          inv MSFIND. ss. des; clarify.
          { esplits; try left; et.
            - econs; et. ss. et.
            - ss. esplits; eauto with congruence.
          }
          destruct (classic (ms = msdl)).
          { clarify. exists ms_link. esplits; et.
            econs; et.
            { ss. right. unfold load_modsems, flip. rewrite in_map_iff. exists md_link. ss. esplits; et.
              unfold prog_src. rewrite in_app_iff. ss. et.
            }
            unfold msdl, Mod.modsem in INTERNAL. rewrite <- Mod.get_modsem_skenv_spec in *.
            unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
            destruct (Genv.invert_symbol skenv_link b) eqn:INV.
            - inv PROJL. exploit DEFKEPT; et. i; des.
              exploit internals_linkorder; eauto.
              { eapply link_linkorder in LINKSK. eapply LINKSK. }
              intro T.
              inv PROJLINK. exploit DEFKEEP0; et. i; des.
              unfold ms_link. ss. rewrite DEFSMALL.
              inv LO. inv H1. inv LO0; ss. inv H2; ss.
            - inv PROJL. exploit DEFORPHAN; et. unfold Mod.sk. intro T; des. rewrite T in *. ss.
          }
          destruct (classic (ms = msdr)).
          { clarify. exists ms_link. esplits; et.
            econs; et.
            { ss. right. unfold load_modsems, flip. rewrite in_map_iff. exists md_link. ss. esplits; et.
              unfold prog_src. rewrite in_app_iff. ss. et.
            }
            unfold msdr, Mod.modsem in INTERNAL. rewrite <- Mod.get_modsem_skenv_spec in *.
            unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs_safe.
            destruct (Genv.invert_symbol skenv_link b) eqn:INV.
            - inv PROJR. exploit DEFKEPT; et. i; des.
              exploit internals_linkorder; eauto.
              { eapply link_linkorder in LINKSK. eapply LINKSK. }
              intro T.
              inv PROJLINK. exploit DEFKEEP0; et. i; des.
              unfold ms_link. ss. rewrite DEFSMALL.
              inv LO. inv H2. inv LO0; ss. inv H3; ss.
            - inv PROJR. exploit DEFORPHAN; et. unfold Mod.sk. intro T; des. rewrite T in *. ss.
          }
          unfold load_modsems, flip in *. rewrite in_map_iff in *. des; clarify.
          exists (x skenv_link). esplits; et.
          - econs; et. ss. right. unfold load_modsems, flip in *. rewrite in_map_iff in *.
            esplits; et. unfold prog_src, prog_tgt in *. rewrite in_app_iff in *; ss. des; clarify; et.
          - left. esplits; et.
            + unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec; et.
              destruct (Mod.midx x) eqn:T; cycle 1.
              { congruence. }
              unfold mil. rewrite <- T.
              eapply NoDup_inj with (md0 := x) (md1 := mdl); et; ss.
              { ii. clarify. }
              { congruence. }
              { fold mil. congruence. }
              { unfold prog_tgt in *. unfold prog_src. rewrite in_app_iff in *; ss. des; clarify; et. }
            + unfold mir, Mod.modsem. rewrite Mod.get_modsem_midx_spec.
              destruct (Mod.midx x) eqn:T; cycle 1.
              { fold mir. congruence. }
              rewrite <- T.
              eapply NoDup_inj; et.
              { ii; clarify. }
              { congruence. }
              { unfold prog_tgt in *. unfold prog_src. rewrite in_app_iff in *; ss. des; clarify; et. }
        }
      Qed.

      Lemma match_states_xsim
            st_src0 st_tgt0
            (MATCH: match_states skenv_link st_src0 st_tgt0) :
        <<XSIM: xsim (sem (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2)) (sem (ctx1 ++ [mdl] ++ [mdr] ++ ctx2))
                     bot2 top1 top1 tt st_src0 st_tgt0>>
      .
      Proof.
        revert_until st_src0. revert st_src0.
        pcofix CIH. i. pfold.
        inv MATCH.
        - (* normal *)
          ss. destruct frs_src; ss.
          { inv STK; clarify. left. right.
            econs 1; eauto.
            econs 1; eauto.
            - econs 1; eauto. i. inv STEPSRC.
            - i. ss. inv FINALSRC; ss. }
          rename t0 into fr_src.
          destruct frs_tgt; ss.
          { exploit match_stacks_right_nil; et. i; des. clarify. }
          rename t0 into fr_tgt.
          ii. clear_tac.



          destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
          (* tgt call - fsim *)
          { left. right. econs; et. econs; et; cycle 1.
            { i. eapply final_fsim; et. econs; et. }
            destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
            * (* src call *)
              econs; ss; cycle 1.
              i. folder. rewrite LINKSRC in STEPSRC.
              assert(RCPT: receptive_at (sem prog_src) (State (fr_src :: frs_src) ohs_src)).
              { econs.
                - ii. inv H1; ModSem.tac.
                  inv H2. eexists. eapply step_call. instantiate (1:=args). eauto.
                  { eauto. }
                - ii. inv H1; ModSem.tac. ss. omega. }
              assert(DTM: determinate_at (sem prog_tgt) (State (fr_tgt :: frs_tgt) ohs_tgt)).
              { econs.
                - ii. ss. des_ifs.
                  clear H0.
                  inv H1; inv H2; ModSem.tac.
                  + split. econs. i. determ_tac ModSem.at_external_dtm.
                - i. ss. inv FINAL. inv STEP; ModSem.tac.
                - ii. inv H1; ss; try omega.
                  exfalso; eapply ModSem.call_step_disjoint. split. eapply H. eauto. }
              inv STEPSRC; ss; ModSem.tac.
              dup STK.
              inv STK; clarify; ss.
              { (* stk ctx *)
                set (upcast oh) as X.
                set (Midx.update ohs_tgt (ModSem.midx (Frame.ms fr_tgt)) X) as Y.
                esplits; eauto.
                - left. split; eauto.
                  eapply plus_one. econs; et. ss.
                  { des_ifs. econs; [et|].
                    (******************** TODO: Doing "refl" here breaks QED ***************************)
                    (* Is it a bug in Coq? or there is a resaon? *)
                    (* If there is a reason, it would be an interesting problem to prevent it... *)
                    (* refl. *)
                    instantiate (1:= Y).
                    subst X Y. refl.
                    (***********************************************************************************)
                  }
                - right. eapply CIH; et. subst X Y.
                  econs; ss; et.
                  { inv OHS. inv LATEST.
                    - econs; et; unfold Midx.update in *; ii; ss; des_ifs; et;
                        try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                    - econs; et; unfold Midx.update in *; ii; ss; des_ifs; et;
                        try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                  }
              }
              { (* stk focus *)
                inv AT; ss; clarify.
                - (* left *)
                  my_depdes HD.
                  esplits; eauto.
                  + left. split; eauto.
                    eapply plus_one. econs; et. ss.
                    { des_ifs. econs 1; ss; et. }
                  + right. eapply CIH; et. econs; et.
                    { inv OHS.
                      inv LATEST.
                      - econs; et; unfold Midx.update in *; ii; ss; des_ifs; et;
                          try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                      - eapply sim_ohs_intro with (ohl := oh0) (ohr := ohr);
                          et; unfold Midx.update in *; ii; ss; des_ifs; et;
                          try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                        + erewrite <- OHS0; et. des_ifs.
                        + do 2 f_equal.
                          * inv GET. apply func_app_dep with (f := Frame.st) in H1; ss. des.
                            apply JMeq_eq in H1. clarify.
                    }
                - (* right *)
                  my_depdes HD.
                  esplits; eauto.
                  + left. split; eauto.
                    eapply plus_one. econs; et. ss.
                    { des_ifs. econs 1; ss; et. }
                  + right. eapply CIH; et. econs; et.
                    { inv OHS.
                      inv LATEST.
                      - econs; et; unfold Midx.update in *; ii; ss; des_ifs; et;
                          try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                      - eapply sim_ohs_intro with (ohl := ohl) (ohr := oh0);
                          et; unfold Midx.update in *; ii; ss; des_ifs; et;
                          try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                        + erewrite <- OHS0; et. des_ifs.
                        + do 2 f_equal.
                          * inv GET. apply func_app_dep with (f := Frame.st) in H1; ss. des.
                            apply JMeq_eq in H1. clarify.
                        + unfold mil, mir in *. congruence.
                    }
              }
            * (* src step -- it "call"s inside focus *)
              rename H0 into NCALLSRC.
              i. ss. folder. rewrite LINKSRC in *.
              inv STEPSRC; ss; swap 2 3.
              { exfalso. contradict NCALLSRC. rr. eauto. }
              { exfalso. inv STK; ss. clarify; ss.
                inv FINAL; ss.
                - my_depdes HD. rr in H. des. ModSem.tac.
                - my_depdes HD. rr in H. des. ModSem.tac.
              }
              dup H. rename H0 into ISCALLTGT.
              rr in H. des.
              sguard in LINKSRC.
              inv STK; ss. clarify. ss.



              my_depdes HD.
              - (* left *)
                ss. pose st0 as TTT. my_depdes STEP; ss; revgoals.
                { ModSem.tac. }
                { ModSem.tac. }
                esplits; eauto.
                + left. esplits; eauto; cycle 1.
                  { (* receptive *)
                    eapply lift_receptive_at. ss.
                    { rewrite LINKSRC. simpl_md. folder. ss. }
                    econs; ii; ss.
                    - assert(t1 = E0).
                      { my_depdes H0; ss. ModSem.tac. }
                      clarify. inv H1. eauto.
                    - assert(t0 = E0).
                      { my_depdes H0; ss. ModSem.tac. }
                      clarify. ss. xomega. }

                  (*** TODO: make lemma ***)
                  assert(MSFIND1: Ge.find_fptr_owner (load_genv prog_tgt (Sk.load_skenv sk_link))
                                                     (Args.get_fptr args0) (mdr skenv_link)).
                  { clear - MSFIND.
                    inv MSFIND. econs; et. ss. right. unfold load_modsems.
                    rewrite in_map_iff. unfold flip. esplits; et. unfold prog_tgt.
                    rewrite in_app_iff. right; ss. et.
                  }

                  eapply plus_left with (t1 := E0) (t2 := E0); ss.
                  { econs; et.
                    { (* determinate *)
                      eapply lift_determinate_at; ss.
                      { rewrite LINKTGT. simpl_md. folder. ss. }
                      econs; ii; ss.
                      - ModSem.tac.
                      - ModSem.tac.
                    }
                    econs; eauto.
                  }
                  eapply star_left with (t1 := E0) (t2 := E0); ss.
                  { econs; et.
                    { (* determinate *)
                      (* NOTE: we exploit DTML/DTMR here *)
                      econs.
                      - ii. inv H0; inv H1.
                        determ_tac find_fptr_owner_determ. clear_tac. ss. rewrite LINKTGT in *.
                        esplits; et.
                        { econs. }
                        ii. f_equal.
                        (*** TODO: make lemma ***)
                        assert(ms0 = msdr).
                        { exploit (find_fptr_owner_determ prog_tgt).
                          { ss. rewrite LINKTGT. eapply MSFIND0. }
                          { ss. rewrite LINKTGT. eapply MSFIND1. }
                          i; clarify.
                        }
                        des.
                        { clarify. repeat f_equal. rewrite OH in *. clarify. eapply DTMR; et. }
                      - ii. ss. inv FINAL.
                      - ii. ss. inv H0. ss. xomega.
                    }
                    econs; et.
                    { ss. rewrite LINKTGT. ss. }
                    unfold Midx.update. des_ifs.
                    { folder. subst msdl msdr. simpl_md. ss. }
                    clear - MIDXL LATEST OHS.
                    inv LATEST; ss; clarify; try congruence.
                    inv OHS. simpl_md. folder. eapply upcast_downcast_iff; et. r. ss.
                    rewrite OHR. f_equal.
                    unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                    my_depdes GET.
                  }
                  apply star_refl.
                + right. eapply CIH.
                  econs; unfold Frame.update_st; ss; et.
                  { econs; et.
                    - f_equal. rewrite cons_app. rewrite app_assoc. f_equal.
                    - ss. econs; et. econs; et.
                  }
                  { econs 3; ss; et. }
                  { inv LATEST; ss; try congruence.
                    my_depdes GET. inv OHS.
                    determ_tac ModSem.at_external_dtm.
                    eapply sim_ohs_intro with (ohl := oh0) (ohr := ohr);
                      unfold Midx.update in *; ii; ss; des_ifs; et;
                        try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                    - rewrite <- OHS0; ss. des_ifs; ss.
                  }
              - (* right *)
                ss. pose st0 as TTT. my_depdes STEP; ss; revgoals.
                { ModSem.tac. }
                { ModSem.tac. }
                esplits; eauto.
                + left. esplits; eauto; cycle 1.
                  { (* receptive *)
                    eapply lift_receptive_at. ss.
                    { rewrite LINKSRC. simpl_md. folder. ss. }
                    econs; ii; ss.
                    - assert(t1 = E0).
                      { my_depdes H0; ss. ModSem.tac. }
                      clarify. inv H1. eauto.
                    - assert(t0 = E0).
                      { my_depdes H0; ss. ModSem.tac. }
                      clarify. ss. xomega. }

                  (*** TODO: make lemma ***)
                  assert(MSFIND1: Ge.find_fptr_owner (load_genv prog_tgt (Sk.load_skenv sk_link))
                                                     (Args.get_fptr args0) (mdl skenv_link)).
                  { clear - MSFIND.
                    inv MSFIND. econs; et. ss. right. unfold load_modsems.
                    rewrite in_map_iff. unfold flip. esplits; et. unfold prog_tgt.
                    rewrite in_app_iff. right; ss. et.
                  }

                  eapply plus_left with (t1 := E0) (t2 := E0); ss.
                  { econs; et.
                    { (* determinate *)
                      eapply lift_determinate_at; ss.
                      { rewrite LINKTGT. simpl_md. folder. ss. }
                      econs; ii; ss.
                      - ModSem.tac.
                      - ModSem.tac.
                    }
                    econs; eauto.
                  }
                  eapply star_left with (t1 := E0) (t2 := E0); ss.
                  { econs; et.
                    { (* determinate *)
                      (* NOTE: we exploit DTML/DTMR here *)
                      econs.
                      - ii. inv H0; inv H1.
                        determ_tac find_fptr_owner_determ. clear_tac. ss. rewrite LINKTGT in *.
                        esplits; et.
                        { econs. }
                        ii. f_equal.
                        (*** TODO: make lemma ***)
                        assert(ms0 = msdl).
                        { exploit (find_fptr_owner_determ prog_tgt).
                          { ss. rewrite LINKTGT. eapply MSFIND0. }
                          { ss. rewrite LINKTGT. eapply MSFIND1. }
                          i; clarify.
                        }
                        des.
                        { clarify. repeat f_equal. rewrite OH in *. clarify. eapply DTML; et. }
                      - ii. ss. inv FINAL.
                      - ii. ss. inv H0. ss. xomega.
                    }
                    econs; et.
                    { ss. rewrite LINKTGT. ss. }
                    unfold Midx.update. des_ifs.
                    { folder. subst msdl msdr. simpl_md. folder. congruence. }
                    clear - MIDXL LATEST OHS.
                    inv LATEST; ss; clarify; try congruence.
                    inv OHS. simpl_md. folder. eapply upcast_downcast_iff; et. r. ss.
                    rewrite OHL. f_equal.
                    unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                    my_depdes GET.
                  }
                  apply star_refl.
                + right. eapply CIH.
                  econs; unfold Frame.update_st; ss; et.
                  { econs; et.
                    - f_equal. rewrite cons_app. rewrite app_assoc. f_equal.
                    - ss. econs; et. econs; et.
                  }
                  { econs 3; ss; et. }
                  { inv LATEST; ss; try congruence.
                    my_depdes GET. inv OHS.
                    determ_tac ModSem.at_external_dtm.
                    eapply sim_ohs_intro with (ohl := ohl) (ohr := oh0);
                      unfold Midx.update in *; ii; ss; des_ifs; et;
                        try rewrite upcast_downcast in *; clarify;
                          try rewrite <- MIDXL in *; simpl_md; ss.
                    - rewrite <- OHS0; ss. des_ifs; ss.
                    - folder. congruence.
                  }
          }



          assert(CALLLE: forall (CALLSRC: ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src)),
                    <<CALLTGT: ModSem.is_call (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
          { i. inv STK.
            { eapply H in CALLSRC. clarify. }
            rr in CALLSRC. des.
            inv HD; clarify; ss; clarify; ss.
            - remember ((StackCons dl st_tgt stk), oh_src) as X.
              dependent destruction CALLSRC; ss. apply state_inj in HeqX. des; clarify.
              rr. esplits; eauto.
            - remember ((StackCons dr st_tgt stk), oh_src) as X.
              dependent destruction CALLSRC; ss. apply state_inj in HeqX. des; clarify.
              rr. esplits; eauto.
          }
          rename H into NCALLTGT.
          assert(NCALLSRC: ~ ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src)).
          { tauto. }



          destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_return) fr_tgt.(Frame.st))).
          { (* tgt return *)
            left. right. econs; et. econs; et; cycle 1.
            { i. eapply final_fsim; et. econs; et. }
            econs; et; cycle 1.
            i. ss. fold prog_src in STEPSRC. rewrite LINKSRC in *.

            assert(RECEP: receptive_at (sem prog_src) (State (fr_src :: frs_src) ohs_src)).
            { econs.
              - ii. inv H0.
                + exfalso. eapply NCALLSRC. eauto.
                + ss. rewrite LINKSRC in *.
                  rr in H. des. ss.
                  inv STK.
                  * exfalso; eapply ModSem.step_return_disjoint. split; eauto.
                  * clarify; ss. my_depdes HD; clarify; ss.
                    { my_depdes STEP; ss; ModSem.tac. inv H1.
                      eexists. econs 3; ss. rp; try eapply step_return_dl; eauto. }
                    { my_depdes STEP; ss; ModSem.tac. inv H1.
                      eexists. econs 3; ss. rp; try eapply step_return_dr; eauto. }
                + ss. des_ifs. inv H1. eexists. econs 4; eauto.
              - ii. ss. rewrite LINKSRC in *. inv H0; ss; try nia.
                rr in H. des. ss. inv STK.
                + exfalso; eapply ModSem.step_return_disjoint. split; eauto.
                + ss. my_depdes HD; clarify; ss.
                  { my_depdes STEP; ss; ModSem.tac. try xomega. }
                  { my_depdes STEP; ss; ModSem.tac. try xomega. }
            }

            inv STEPSRC; ss.
            { contradict NCALLSRC. rr. et. }
            - (* src step *)
              inv STK.
              { ModSem.tac. }
              my_depdes HD; ss.
              { my_depdes STEP; ss; ModSem.tac.
                my_depdes HD. esplits; eauto.
                + left. split ;ss. eapply plus_one with (t := E0); ss.
                  econs; et.
                  { (* determ *)
                    econs; ii; ss; folder; try rewrite LINKTGT in *.
                    - inv H0; ModSem.tac. ss. inv H1; ModSem.tac. ss.
                      esplits; et.
                      { econs; et. }
                      i.
                      determ_tac ModSem.final_frame_dtm. clear_tac.
                      determ_tac ModSem.final_frame_dtm. clear_tac.
                      unfold Midx.update in *.
                      destruct (Midx.eq_dec (ModSem.midx msdl) (ModSem.midx msdr)).
                      { (*** TODO: make lemma ***)
                        contradict MIDIFF. unfold mil, mir. unfold msdl, msdr, Mod.modsem in e.
                        rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                      rewrite OH in *. clarify.
                      repeat f_equal.
                      eapply ModSem.after_external_dtm; et.
                    - inv FINAL; ss.
                    - inv H0; ss; ModSem.tac. xomega.
                  }
                  ss. fold prog_tgt. rewrite LINKTGT.
                  econs 4; ss; et.
                  unfold Midx.update. des_ifs.
                  { contradict MIDIFF. unfold mil, mir. unfold msdl, msdr, Mod.modsem in e.
                    rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                  inv LATEST; ss.
                  { congruence. }
                  my_depdes GET. ss. inv OHS. replace (ModSem.midx (mdr skenv_link)) with mir; cycle 1.
                  { unfold mir, Mod.modsem. rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                  unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                  eapply upcast_downcast_iff; et.
                + right. eapply CIH. unfold Frame.update_st. ss. econs; ss; et.
                  { econs; et. econs; et. }
                  { econs 3; et. ss. }
                  { inv OHS. inv LATEST; ss; try congruence.
                    unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                    econs; ss; et.
                    - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs.
                      contradict NL. unfold mil. unfold msdl, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. ss.
                    - des_ifs; try rewrite upcast_downcast; et.
                    - des_ifs; try rewrite upcast_downcast; et.
                      contradict n. unfold mil. unfold msdl, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. ss.
                    - des_ifs; try rewrite upcast_downcast; et.
                      { contradict e0. unfold mir. unfold msdr, Mod.modsem.
                        rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                      rewrite OHR. my_depdes GET; ss.
                  }
              }
              { my_depdes STEP; ss; ModSem.tac.
                my_depdes HD. esplits; eauto.
                + left. split ;ss. eapply plus_one with (t := E0); ss.
                  econs; et.
                  { (* determ *)
                    econs; ii; ss; folder; try rewrite LINKTGT in *.
                    - inv H0; ModSem.tac. ss. inv H1; ModSem.tac. ss.
                      esplits; et.
                      { econs; et. }
                      i.
                      determ_tac ModSem.final_frame_dtm. clear_tac.
                      determ_tac ModSem.final_frame_dtm. clear_tac.
                      unfold Midx.update in *.
                      destruct (Midx.eq_dec (ModSem.midx msdl) (ModSem.midx msdr)).
                      { (*** TODO: make lemma ***)
                        contradict MIDIFF. unfold mil, mir. unfold msdl, msdr, Mod.modsem in e.
                        rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                      rewrite OH in *. clarify.
                      repeat f_equal.
                      eapply ModSem.after_external_dtm; et.
                    - inv FINAL; ss.
                    - inv H0; ss; ModSem.tac. xomega.
                  }
                  ss. fold prog_tgt. rewrite LINKTGT.
                  econs 4; ss; et.
                  unfold Midx.update. des_ifs.
                  { contradict MIDIFF. unfold mil, mir. unfold msdl, msdr, Mod.modsem in e.
                    rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                  inv LATEST; ss.
                  { congruence. }
                  my_depdes GET. ss. inv OHS. replace (ModSem.midx (mdl skenv_link)) with mil; cycle 1.
                  { unfold mil, Mod.modsem. rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                  unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                  eapply upcast_downcast_iff; et.
                + right. eapply CIH. unfold Frame.update_st. ss. econs; ss; et.
                  { econs; et. econs; et. }
                  { econs 3; et. ss. }
                  { inv OHS. inv LATEST; ss; try congruence.
                    unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                    econs; ss; et.
                    - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs.
                      contradict NR. unfold mir. unfold msdr, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. ss.
                    - des_ifs; try rewrite upcast_downcast; et.
                    - des_ifs; try rewrite upcast_downcast; et.
                      { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                        rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                      rewrite OHL. my_depdes GET; ss.
                    - des_ifs; try rewrite upcast_downcast; et.
                      contradict n. unfold mil. unfold msdl, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. ss.
                  }
              }
            - (* src return *)
              inv STK; ss; cycle 1.
              { (* top is focus *)
                clarify; ss.
                inv HD; ss; clarify; ss.
                { my_depdes FINAL. my_depdes TL.
                  inv TAIL; ss.
                  - (* snd is focus *)
                    esplits; et.
                    + left. esplits; et. eapply plus_one with (t := E0); ss.
                      econs; et.
                      { (* determ *)
                        econs; ii; ss; folder; try rewrite LINKTGT in *.
                        - inv H0; ModSem.tac. ss. inv H1; ModSem.tac. ss.
                          esplits; et.
                          { econs; et. }
                          i.
                          determ_tac ModSem.final_frame_dtm. clear_tac.
                          determ_tac ModSem.final_frame_dtm. clear_tac.
                          repeat f_equal.
                          assert(oh3 = oh5).
                          { rewrite OH0 in *. clarify. }
                          clarify.
                          eapply ModSem.after_external_dtm; et.
                        - inv FINAL0; ss.
                        - inv H0; ss; ModSem.tac. xomega.
                      }
                      { econs 4; ss; et. rewrite <- OH. unfold Midx.update. inv OHS. des_ifs; try congruence.
                        - contradict n. rewrite <- e. rewrite <- MIDXL. unfold mil, Mod.modsem.
                          rewrite ! Mod.get_modsem_midx_spec in *. ss.
                        - rewrite <- OHS0; ss. inv LATEST; ss.
                          unfold Midx.update in *. des_ifs; ss; eauto with congruence.
                      }
                    + right. eapply CIH. econs; et.
                      { econs; et. }
                      { econs; et. }
                      { inv OHS. unfold Midx.update in *. des_ifs; try congruence. econs; et.
                        - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                          { contradict n0. unfold mir. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                          { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                            unfold Midx.update in *. des_ifs. }
                        - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                        - des_ifs; try rewrite upcast_downcast; et.
                          { contradict n0. unfold mir. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                        - des_ifs; try rewrite upcast_downcast; et.
                          { contradict e. unfold mil. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                          rewrite OHR. inv LATEST; ss; try congruence.
                          my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                          rewrite upcast_downcast in *. clarify.
                      }
                  - (* snd is ctx *)
                    clarify. ss. my_depdes AFTER; ss.
                    + my_depdes HD; ss.
                      esplits; et.
                      * left. split; ss.
                        apply plus_one.
                        econs; et.
                        { eapply lift_determinate_at.
                          - ss. fold prog_tgt. rewrite LINKTGT. unfold Mod.modsem.
                            rewrite Mod.get_modsem_skenv_link_spec; et.
                          - econs; et.
                            + ii. ss. ModSem.tac.
                            + ii. ss. ModSem.tac. }
                        econs 4; ss; et. unfold Midx.update in *.
                        (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                        destruct (Midx.eq_dec (Some midx) (Some midx)); ss. clarify. des_ifs.
                      * right. eapply CIH; eauto. unfold Frame.update_st. destruct ohs1; ss.
                        econs; ss; et.
                        { econs; ss; et. econs; ss; et. }
                        { econs 3; ss; et. }
                        { inv OHS. unfold Midx.update in *. des_ifs; try congruence. clarify.
                          apply JMeq_eq in EQ0. clarify.
                          econs; et.
                          - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                            { contradict n0. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                            { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                              unfold Midx.update in *. des_ifs. }
                          - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict n. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                            rewrite OHR. inv LATEST; ss; try congruence.
                            my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                            rewrite upcast_downcast in *. clarify.
                        }
                    + my_depdes HD; ss.
                      esplits; et.
                      * left. split; ss.
                        apply plus_one.
                        econs; et.
                        { eapply lift_determinate_at.
                          - ss. fold prog_tgt. rewrite LINKTGT. unfold Mod.modsem.
                            rewrite Mod.get_modsem_skenv_link_spec; et.
                          - econs; et.
                            + ii. ss. ModSem.tac.
                            + ii. ss. ModSem.tac. }
                        econs 4; ss; et. unfold Midx.update in *.
                        (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                        destruct (Midx.eq_dec (Some midx) (Some midx)); ss. clarify. ss. des_ifs.
                        { contradict e0. unfold msdr, Mod.modsem.
                          rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                        inv OHS. inv LATEST; ss; try congruence. my_depdes GET; ss.
                        unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec; et. fold mir.
                        eapply upcast_downcast_iff; et.
                        unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify.
                      * right. eapply CIH; eauto. unfold Frame.update_st. destruct ohs1; ss.
                        econs; ss; et.
                        { econs; ss; et. econs; ss; et. }
                        { econs 3; ss; et. }
                        { inv OHS. unfold Midx.update in *. des_ifs; try congruence. clarify.
                          apply JMeq_eq in EQ0. clarify.
                          econs; et.
                          - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                            { contradict n0. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                            { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                              unfold Midx.update in *. des_ifs. }
                          - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict n. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                            rewrite OHR. inv LATEST; ss; try congruence.
                            my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                            rewrite upcast_downcast in *. clarify.
                        }
                }
                { my_depdes FINAL. my_depdes TL.
                  inv TAIL; ss.
                  - (* snd is focus *)
                    esplits; et.
                    + left. esplits; et. eapply plus_one with (t := E0); ss.
                      econs; et.
                      { (* determ *)
                        econs; ii; ss; folder; try rewrite LINKTGT in *.
                        - inv H0; ModSem.tac. ss. inv H1; ModSem.tac. ss.
                          esplits; et.
                          { econs; et. }
                          i.
                          determ_tac ModSem.final_frame_dtm. clear_tac.
                          determ_tac ModSem.final_frame_dtm. clear_tac.
                          repeat f_equal.
                          assert(oh3 = oh5).
                          { rewrite OH0 in *. clarify. }
                          clarify.
                          eapply ModSem.after_external_dtm; et.
                        - inv FINAL0; ss.
                        - inv H0; ss; ModSem.tac. xomega.
                      }
                      { econs 4; ss; et. rewrite <- OH. unfold Midx.update. inv OHS. des_ifs; try congruence.
                        - contradict NR. rewrite <- e. unfold mil, Mod.modsem.
                          rewrite ! Mod.get_modsem_midx_spec in *. ss.
                        - rewrite <- OHS0; ss. inv LATEST; ss.
                          unfold Midx.update in *. des_ifs; ss; eauto with congruence.
                      }
                    + right. eapply CIH. econs; et.
                      { econs; et. }
                      { econs; et. }
                      { inv OHS. unfold Midx.update in *. des_ifs; try congruence. econs; et.
                        - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                          { contradict NR0. unfold mir. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                          { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                            unfold Midx.update in *. des_ifs. }
                        - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                        - des_ifs; try rewrite upcast_downcast; et.
                          { contradict e. unfold mil. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                          rewrite OHL. inv LATEST; ss; try congruence.
                          my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                          rewrite upcast_downcast in *. clarify.
                        - des_ifs; try rewrite upcast_downcast; et.
                          { contradict n0. unfold mir. unfold msdr, Mod.modsem.
                            rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                      }
                  - (* snd is ctx *)
                    clarify. ss. my_depdes AFTER; ss.
                    + my_depdes HD; ss.
                      esplits; et.
                      * left. split; ss.
                        apply plus_one.
                        econs; et.
                        { eapply lift_determinate_at.
                          - ss. fold prog_tgt. rewrite LINKTGT. unfold Mod.modsem.
                            rewrite Mod.get_modsem_skenv_link_spec; et.
                          - econs; et.
                            + ii. ss. ModSem.tac.
                            + ii. ss. ModSem.tac. }
                        econs 4; ss; et. unfold Midx.update in *.
                        (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                        destruct (Midx.eq_dec (Some midx) (Some midx)); ss. clarify. ss.
                        inv LATEST; ss; try congruence. my_depdes GET. ss.
                        des_ifs.
                        { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                          rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                        { inv OHS. eapply upcast_downcast_iff; et. unfold msdr, Mod.modsem.
                          rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir.
                          unfold Midx.update in *. des_ifs. rewrite upcast_downcast in *. clarify. }
                      * right. eapply CIH; eauto. unfold Frame.update_st. destruct ohs1; ss.
                        econs; ss; et.
                        { econs; ss; et. econs; ss; et. }
                        { econs 3; ss; et. }
                        { inv OHS. unfold Midx.update in *. des_ifs; try congruence. clarify.
                          apply JMeq_eq in EQ0. clarify.
                          econs; et.
                          - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                            { contradict NR. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                            { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                              unfold Midx.update in *. des_ifs. }
                          - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                            rewrite OHL. inv LATEST; ss; try congruence.
                            my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                            rewrite upcast_downcast in *. clarify.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict n. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                        }
                    + my_depdes HD; ss.
                      esplits; et.
                      * left. split; ss.
                        apply plus_one.
                        econs; et.
                        { eapply lift_determinate_at.
                          - ss. fold prog_tgt. rewrite LINKTGT. unfold Mod.modsem.
                            rewrite Mod.get_modsem_skenv_link_spec; et.
                          - econs; et.
                            + ii. ss. ModSem.tac.
                            + ii. ss. ModSem.tac. }
                        econs 4; ss; et. unfold Midx.update in *.
                        (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                        destruct (Midx.eq_dec (Some midx) (Some midx)); ss. clarify. ss. des_ifs.
                      * right. eapply CIH; eauto. unfold Frame.update_st. destruct ohs1; ss.
                        econs; ss; et.
                        { econs; ss; et. econs; ss; et. }
                        { econs 3; ss; et. }
                        { inv OHS. unfold Midx.update in *. des_ifs; try congruence. clarify.
                          apply JMeq_eq in EQ0. clarify.
                          econs; et.
                          - ii. specialize (OHS0 mj). exploit OHS0; et. intro T. des_ifs; eauto with congruence.
                            { contradict NR. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                            { rewrite <- OHS0; et. inv LATEST; ss. my_depdes GET; ss.
                              unfold Midx.update in *. des_ifs. }
                          - ii. des_ifs; try congruence. rewrite upcast_downcast; et.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict e0. unfold mil. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                            rewrite OHL. inv LATEST; ss; try congruence.
                            my_depdes GET; ss. unfold Midx.update in *. des_ifs.
                            rewrite upcast_downcast in *. clarify.
                          - des_ifs; try rewrite upcast_downcast; et.
                            { contradict n. unfold mir. unfold msdr, Mod.modsem.
                              rewrite ! Mod.get_modsem_midx_spec in *. ss. }
                        }
                }
              }
              { (* top is ctx *)
                inv TAIL; ss; clarify; ss.
                - (* snd is ctx *)
                  inv LATEST; try congruence. destruct fr_tgt; ss.
                  esplits; et.
                  + left. split; ss.
                    apply plus_one.
                    econs; et.
                    { eapply lift_determinate_at.
                      - ss. fold prog_tgt. rewrite LINKTGT.
                        admit "ez - ms ModSem.skenv_link, maybe in SemTyping?".
                      - econs; et.
                        + ii. ss. ModSem.tac.
                        + ii. ss. ModSem.tac. }
                    econs 4; ss; et. unfold Midx.update in *.
                    (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                    des_ifs. inv OHS. rewrite <- OHS0; ss.
                  + right. eapply CIH. econs; et.
                    { econs; et. }
                    { econs; et. }
                    { inv OHS. unfold Midx.update in *.
                      econs; et.
                      - ii. specialize (OHS0 mj). exploit OHS0; et. intro T.
                        des_ifs; eauto with congruence.
                      - ii. destruct (Midx.eq_dec (ModSem.midx ms) mil); ss. et.
                      - des_ifs; try rewrite upcast_downcast; et.
                      - des_ifs; try rewrite upcast_downcast; et.
                    }
                - (* snd is focus *)
                  inv LATEST; try congruence. destruct fr_tgt; ss.
                  my_depdes AFTER; my_depdes HD; ss.
                  { esplits; et.
                    + left. split; ss.
                      apply plus_one.
                      econs; et.
                      { eapply lift_determinate_at.
                        - ss. fold prog_tgt. rewrite LINKTGT.
                          admit "ez - ms ModSem.skenv_link, maybe in SemTyping?".
                        - econs; et.
                          + ii. ss. ModSem.tac.
                          + ii. ss. ModSem.tac. }
                      econs 4; ss; et. unfold Midx.update in *.
                      (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                      destruct (Midx.eq_dec (ModSem.midx ms) (ModSem.midx (mdl skenv_link))); ss.
                      { contradict NL. rewrite e. unfold mil, Mod.modsem.
                        rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                      destruct (Midx.eq_dec (ModSem.midx ms) (Some midx)); ss.
                      { congruence. }
                      inv OHS. rewrite <- MIDXL in *. rewrite OH in *.
                      rewrite upcast_downcast in *. clarify. ss.
                      eapply upcast_downcast_iff; et. r. rewrite <- OHL.
                      repeat f_equal.
                      unfold mil, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence.
                    + right. eapply CIH. unfold Frame.update_st. destruct ohs1; ss. econs; et.
                      { ss. econs; et. econs; et. }
                      { econs 3; ss; et. }
                      { inv OHS. unfold Midx.update in *. rewrite <- MIDXL in *.
                        destruct (Midx.eq_dec (ModSem.midx ms) mil); ss.
                        rewrite OH in *. rewrite upcast_downcast in *; clarify.
                        econs; et.
                        - ii. specialize (OHS0 mj). exploit OHS0; et. intro T.
                          des_ifs; eauto with congruence.
                        - ii. destruct (Midx.eq_dec mil mil); ss. rewrite upcast_downcast; et.
                        - destruct (Midx.eq_dec (ModSem.midx ms) mil); ss.
                        - destruct (Midx.eq_dec (ModSem.midx ms) mir); ss.
                      }
                  }
                  { esplits; et.
                    + left. split; ss.
                      apply plus_one.
                      econs; et.
                      { eapply lift_determinate_at.
                        - ss. fold prog_tgt. rewrite LINKTGT.
                          admit "ez - ms ModSem.skenv_link, maybe in SemTyping?".
                        - econs; et.
                          + ii. ss. ModSem.tac.
                          + ii. ss. ModSem.tac. }
                      econs 4; ss; et. unfold Midx.update in *.
                      (*** TODO: Change Any; do not use existT. Using "des_ifs" here breaks things ***)
                      destruct (Midx.eq_dec (ModSem.midx ms) (ModSem.midx (mdl skenv_link))); ss.
                      { contradict NL. rewrite e. unfold mil, Mod.modsem.
                        rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. congruence. }
                      destruct (Midx.eq_dec (ModSem.midx ms) (Some midx)); ss.
                      { congruence. }
                      inv OHS. rewrite <- MIDXL in *. rewrite OH in *.
                      rewrite upcast_downcast in *. clarify. ss.
                      eapply upcast_downcast_iff; et. r. rewrite <- OHR.
                      repeat f_equal.
                      unfold mil, Mod.modsem.
                      rewrite ! Mod.get_modsem_midx_spec in *. fold mil mir. des_ifs.
                    + right. eapply CIH. unfold Frame.update_st. destruct ohs1; ss. econs; et.
                      { ss. econs; et. econs; et. }
                      { econs 3; ss; et. }
                      { inv OHS. unfold Midx.update in *. rewrite <- MIDXL in *.
                        destruct (Midx.eq_dec (ModSem.midx ms) mil); ss.
                        rewrite OH in *. rewrite upcast_downcast in *; clarify.
                        econs; et.
                        - ii. specialize (OHS0 mj). exploit OHS0; et. intro T.
                          des_ifs; eauto with congruence.
                        - ii. destruct (Midx.eq_dec mil mil); ss. rewrite upcast_downcast; et.
                        - destruct (Midx.eq_dec (ModSem.midx ms) mil); ss.
                        - destruct (Midx.eq_dec (ModSem.midx ms) mir); ss.
                      }
                  }
              }
          }



          assert(RETLE: forall (RETSRC: ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src)),
                    <<RETTGT: ModSem.is_return (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
          { i. inv STK; eauto.
            rr in RETSRC. des. clarify; ss.
            inv HD; ss; clarify; ss.
            - remember (StackCons dl st_tgt stk, oh_src) as X.
              dependent destruction RETSRC; ss. apply state_inj in HeqX. des; clarify.
              rr. esplits; eauto.
            - remember (StackCons dr st_tgt stk, oh_src) as X.
              dependent destruction RETSRC; ss. apply state_inj in HeqX. des; clarify.
              rr. esplits; eauto.
          }
          rename H into NRETTGT.
          assert(NRETSRC: ~ ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src)).
          { tauto. }



          (* src internal && tgt internal *)
          { right. econs. ii.
            inv STK.
            - (* ctx *)
              econs; ii; ss; fold_all prog_tgt; fold_all prog_src; try rewrite LINKSRC, LINKTGT in *; cycle 1.
              + (* progress *)
                right. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
                { inv SAFESRC. contradict NRETSRC. rr. et. }
                rewrite LINKSRC in *.
                inv SAFESRC; swap 2 3.
                { contradict NCALLSRC. rr. et. }
                { contradict NRETSRC. rr. et. }
                esplits; et. econs 3; et.
              + (* final *)
                exploit final_bsim; et.
                { econs; et. econs; et. }
                intro T; des. esplits; eauto. eapply star_refl.
              + (* bsim *)
                inv STEPTGT; swap 2 3.
                { contradict NCALLTGT. rr. et. }
                { contradict NRETTGT. rr. et. }
                esplits; eauto.
                * left. apply plus_one. econs; et.
                * right. eapply CIH. econs; et.
                  { econs; et. }
                  { clear - LATEST NL.
                    (*** TODO: make lemma? ***)
                    unfold Frame.update_st in *. ss.
                    inv LATEST; econs; et.
                    inv GET; ss.
                  }
            - (* focus *)
              clarify; ss. my_depdes HD; ss.
              { (* left *)
                econs; ii; ss; fold_all prog_tgt; fold_all prog_src; try rewrite LINKSRC, LINKTGT in *; cycle 1.
                + (* progress *)
                  right. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
                  { inv SAFESRC. contradict NRETSRC. rr. et. }
                  rewrite LINKSRC in *.
                  inv SAFESRC; swap 2 3.
                  { contradict NCALLSRC. rr. et. }
                  { contradict NRETSRC. rr. et. }
                  ss. my_depdes STEP; ss; swap 2 3.
                  { contradict NCALLTGT. rr. et. }
                  { contradict NRETTGT. rr. et. }
                  esplits; et. econs 3; ss; et.
                + (* final *)
                  exploit final_bsim; et.
                  { econs; et. econs; et. econs; et. }
                  intro T; des. esplits; eauto. eapply star_refl.
                + (* bsim *)
                  inv STEPTGT; swap 2 3.
                  { contradict NCALLTGT. rr. et. }
                  { contradict NRETTGT. rr. et. }
                  esplits; eauto.
                  * left. apply plus_one. ss. econs; ss; et. rp; try eapply step_internal_dl; eauto.
                  * right. eapply CIH. econs; et.
                    { econs; et. econs; et. ss. }
                    { ss. clear - LATEST.
                      (*** TODO: make lemma? ***)
                      unfold Frame.update_st in *. ss.
                      inv LATEST; econs; et. ss.
                      inv GET; ss.
                      (*** TODO: make frame_inj ***)
                      apply func_app_dep with (f:= Frame.st) in H; des; ss. apply JMeq_eq in H. clarify.
                    }
              }
              { (* right *)
                econs; ii; ss; fold_all prog_tgt; fold_all prog_src; try rewrite LINKSRC, LINKTGT in *; cycle 1.
                + (* progress *)
                  right. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
                  { inv SAFESRC. contradict NRETSRC. rr. et. }
                  rewrite LINKSRC in *.
                  inv SAFESRC; swap 2 3.
                  { contradict NCALLSRC. rr. et. }
                  { contradict NRETSRC. rr. et. }
                  ss. my_depdes STEP; ss; swap 2 3.
                  { contradict NCALLTGT. rr. et. }
                  { contradict NRETTGT. rr. et. }
                  esplits; et. econs 3; ss; et.
                + (* final *)
                  exploit final_bsim; et.
                  { econs; et. econs; et. econs; et. }
                  intro T; des. esplits; eauto. eapply star_refl.
                + (* bsim *)
                  inv STEPTGT; swap 2 3.
                  { contradict NCALLTGT. rr. et. }
                  { contradict NRETTGT. rr. et. }
                  esplits; eauto.
                  * left. apply plus_one. ss. econs; ss; et. rp; try eapply step_internal_dr; eauto.
                  * right. eapply CIH. econs; et.
                    { econs; et. econs; et. ss. }
                    { ss. clear - LATEST.
                      (*** TODO: make lemma? ***)
                      unfold Frame.update_st in *. ss.
                      inv LATEST; econs; et. ss.
                      inv GET; ss.
                      (*** TODO: make frame_inj ***)
                      apply func_app_dep with (f:= Frame.st) in H; des; ss. apply JMeq_eq in H. clarify.
                    }
              }
          }



        (* call state *)
        - right. clear SSSRC SSTGT. econs; ss; et.
          i.
          econs; cycle 1.
          { (* SAFE *)
            i. specialize (SAFESRC _ (star_refl _ _ _ _)). des; ss.
            { inv SAFESRC. }
            folder. rewrite LINKSRC in SAFESRC; ss.
            inv SAFESRC. right. rewrite LINKTGT. folder.
            set (Args.get_fptr args) as fptr in *.
            exploit msfind_fsim; et. i. des; clarify.
            - esplits; eauto. econs; eauto. inv OHS. exploit OHS0; et. i. congruence.
            - inv OHS. folder. unfold ms_link in OH. ss. rewrite <- MIDXL in *. rewrite OH in *.
              rewrite upcast_downcast in *. clarify.
              inv INIT.
              + esplits; eauto. econs; eauto.
                { eapply upcast_downcast_iff; et. r. unfold msdl, Mod.modsem.
                  rewrite Mod.get_modsem_midx_spec. eauto. }
              + folder.
                clear - MSFIND1 MSFIND0 msdl msdr MIDXL MIDXR MIDIFF LINKTGT.
                (*** TODO: make lemma ***)
                assert(Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr msdr).
                {
                  inv MSFIND1. econs; et. ss. unfold load_modsems. des; clarify.
                  - apply (func_app ModSem.midx) in MODSEM.
                    rewrite ! Mod.get_modsem_midx_spec in *. des. folder. congruence.
                  - clear_tac. right. rewrite in_map_iff. unfold flip. exists mdr. esplits; et.
                    unfold prog_tgt. rewrite in_app_iff; ss; et.
                }
                assert(CONTR: msdl = msdr).
                { eapply (find_fptr_owner_determ prog_tgt); ss; et; des_ifs; et. }
                apply (func_app ModSem.midx) in CONTR. subst msdl msdr. unfold Mod.modsem in *.
                rewrite ! Mod.get_modsem_midx_spec in *. des. folder. clarify.
            - inv OHS. folder. unfold ms_link in OH. ss. rewrite <- MIDXL in *. rewrite OH in *.
              rewrite upcast_downcast in *. clarify.
              inv INIT.
              + folder.
                clear - MSFIND1 MSFIND0 msdl msdr MIDXL MIDXR MIDIFF LINKTGT.
                (*** TODO: make lemma ***)
                assert(Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr msdl).
                {
                  inv MSFIND1. econs; et. ss. unfold load_modsems. des; clarify.
                  - clear_tac. right. rewrite in_map_iff. unfold flip. exists mdl. esplits; et.
                    unfold prog_tgt. rewrite in_app_iff; ss; et.
                  - apply (func_app ModSem.midx) in MODSEM.
                    rewrite ! Mod.get_modsem_midx_spec in *. des. folder. congruence.
                }
                assert(CONTR: msdl = msdr).
                { eapply (find_fptr_owner_determ prog_tgt); ss; et; des_ifs; et. }
                apply (func_app ModSem.midx) in CONTR. subst msdl msdr. unfold Mod.modsem in *.
                rewrite ! Mod.get_modsem_midx_spec in *. des. folder. clarify.
              + esplits; eauto. econs; eauto.
                { eapply upcast_downcast_iff; et. r. unfold msdr, Mod.modsem.
                  rewrite Mod.get_modsem_midx_spec. eauto. }
          }
          { (* FINAL *)
            i. inv FINALTGT.
          }
          { (* BSIM *)
            repeat fold prog_tgt. repeat fold prog_src.
            ss. rewrite LINKTGT in *. rewrite LINKSRC in *. fold skenv_link.
            i. inv STEPTGT.
            set (Args.get_fptr args) as fptr in *.
            inv OHS.
            exploit msfind_bsim; et. i; des; clarify.
            - esplits; et.
              + left. apply plus_one. econs; et. exploit OHS0; et. intro T. rewrite T in *. ss.
              + right. eapply CIH. econs; ss; et.
                * econs; ss; et.
                * econs; ss; et.
                * econs; ss; et.
            - esplits; et.
              + left. apply plus_one. econs; et.
                * eapply upcast_downcast_iff; et. ss. rewrite <- MIDXL. fold mil. et.
                * ss. rp; try eapply initial_frame_dl; et; ss.
                  { (*** TODO: make lemma ***)
                    inv MSFIND. econs; ss; et.
                  }
                  assert(ohl = oh).
                  { eapply upcast_downcast_iff in OHL.
                    replace (ModSem.midx (mdl skenv_link)) with mil in OH; cycle 1.
                    { unfold mil. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. ss. }
                    rewrite OHL in *. clarify. }
                  clarify. et.
              + right. eapply CIH. econs; ss; et.
                * econs 3; ss; et.
                  { instantiate (1:= nil). ss. }
                  econs; ss; et.
                  econs; ss; et.
                * econs 3; ss; et.
                * econs; ss; et.
                  { ii. unfold Midx.update. des_ifs. eapply OHS0; et. }
                  { unfold Midx.update. des_ifs. rewrite upcast_downcast. ss. }
            - esplits; et.
              + left. apply plus_one. econs; et.
                * eapply upcast_downcast_iff; et. ss. rewrite <- MIDXL. fold mil. et.
                * ss. rp; try eapply initial_frame_dr; et; ss.
                  { (*** TODO: make lemma ***)
                    inv MSFIND. econs; ss; et.
                  }
                  assert(ohr = oh).
                  { eapply upcast_downcast_iff in OHR.
                    replace (ModSem.midx (mdr skenv_link)) with mir in OH; cycle 1.
                    { unfold mir. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec. ss. }
                    rewrite OHR in *. clarify. }
                  clarify. et.
              + right. eapply CIH. econs; ss; et.
                * econs 3; ss; et.
                  { instantiate (1:= nil). ss. }
                  econs; ss; et.
                  econs; ss; et.
                * econs 3; ss; et.
                * econs; ss; et.
                  { ii. unfold Midx.update. des_ifs. eapply OHS0; et. }
                  { unfold Midx.update. des_ifs. rewrite upcast_downcast. ss. }
          }
      Unshelve.
        all: ss.
      Qed.

    End SIM.

    Theorem merge_correct:
      <<BEH: improves (sem prog_src) (sem prog_tgt)>>
    .
    Proof.
      eapply bsim_improves; eauto. ss.
      eapply Simulation.mixed_to_backward_simulation; et.
      econs. instantiate (1:= bot2). instantiate (1:= unit).
      econs; ss; try apply preservation_top; et; cycle 1.
      { ii. des. inv SAFESRC. folder. rewrite <- LINKSAME; et.
        { ii. unfold prog_tgt in *. rewrite in_app_iff in *. ss. des; clarify; et.
          - eapply WF. unfold prog_src. rewrite in_app_iff. ss. et.
          - eapply WF. unfold prog_src. rewrite in_app_iff. ss. et.
        }
      }
      econs 1; ss.
      ii. inv INITSRC; ss. des_ifs.
      assert(WFTGT: forall md, In md prog_tgt -> Sk.wf md).
      { ii. unfold prog_tgt in *. rewrite in_app_iff in *. ss. des; clarify; et.
        - eapply WF. unfold prog_src. rewrite in_app_iff. ss. et.
        - eapply WF. unfold prog_src. rewrite in_app_iff. ss. et.
      }
      assert(NODUPTGT: Midx.NoDup (None :: map ModSem.midx (load_modsems prog_tgt (Sk.load_skenv sk_link)))).
      {
        clear - OHSUNIQ MICTX1 MICTX2 MIDIFF MIDXL MIDXR.
        ss. unfold prog_src, prog_tgt, load_modsems in *.
        rewrite ! map_app in *.
        apply NoDup_app in OHSUNIQ. destruct OHSUNIQ as [A [B C]].
        rewrite cons_app in B. rewrite ! map_app in *.
        apply NoDup_app in B. destruct B as [D [E F]].
        rewrite ! map_map in *.
        (* ss. rewrite cons_app with (xtl := map Mod.midx ctx2). *)
        apply NoDup_app.
        { esplits; et.
          - replace (mdl :: mdr :: ctx2) with ([mdl ; mdr] ++ ctx2) by ss. rewrite map_app. unfold flip.
            apply NoDup_app.
            + esplits; et; ss.
              * r. folder. ss. unfold id. unfold Mod.modsem.
                rewrite ! Mod.get_modsem_midx_spec; et. des_ifs_safe. econs; et; ss.
                { ii; des; clarify. }
                econs; ss. econs; ss.
              * ii.
                exploit F; et. intro T. des_safe. unfold Mod.modsem in IN0.
                rewrite ! Mod.get_modsem_midx_spec in *. des; ss; clarify; eauto.
                rewrite in_map_iff in *. des; clarify. unfold Mod.modsem. rewrite Mod.get_modsem_midx_spec.
                hexploit MICTX2; et.
          - ii.
            destruct (classic (mi1 = mir)).
            { clarify.
              left. ii. clarify. rewrite in_map_iff in IN0. des; clarify. ss. exploit MICTX1; et.
              unfold flip, Mod.modsem in *. rewrite Mod.get_modsem_midx_spec in *. et.
            }
            exploit C; et. clear - MIDXL IN1 H. ss. rewrite in_map_iff in *.
            unfold flip, Mod.modsem in *. rewrite ! Mod.get_modsem_midx_spec in *. des; clarify; et.
        }
      }
      esplits; et.
      { econs; cycle 1.
        { eapply initial_state_determ; et. }
        ss. unfold prog_tgt. rewrite LINKSAME; et; cycle 1.
        econs; ss; et.
        - rewrite LINKSAME; et.
        - fold prog_src. des_ifs.
      }
      eapply match_states_xsim with (sk_link := sk_link); et.
      { ii. eapply WF. unfold prog_src. rewrite in_app_iff in *. ss. des; clarify; et. }
      { ii. eapply WF. unfold prog_src. rewrite in_app_iff in *. ss. des; clarify; et. }
      { clear - OHSUNIQ. ss. eapply Midx.NoDup_cons_iff in OHSUNIQ. des_safe; ss. clear HD.
        clearbody prog_src. clear_tac.
        erewrite f_equal with (f := Midx.NoDup); et. (*** TODO: make "rp" smarter? ***)
        clear TL.
        ginduction prog_src; ii; ss. unfold flip, Mod.modsem.
        rewrite Mod.get_modsem_midx_spec. f_equal. erewrite IHp; et.
      }
      { apply Midx.NoDup_cons_iff in NODUPTGT. des_safe.
        clear - TL. clearbody prog_tgt. clear_tac. 
        erewrite f_equal with (f := Midx.NoDup); et. (*** TODO: make "rp" smarter? ***)
        clear TL.
        ginduction prog_tgt; ii; ss. unfold flip, Mod.modsem.
        rewrite Mod.get_modsem_midx_spec. f_equal. erewrite IHp; et.
      }
      econs; et.
      { econs; et. }
      fold prog_src. rewrite Heq.
      econs; ss; et.
      - admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
    Unshelve.
      all: try eapply ModSem.initial_owned_heap.
    Qed.
  End MERGE.

End ModTuple.
Print ModTuple.t.



