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

      (MSFIND: DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdr)
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

      (MSFIND: DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdl)
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
      (MSFIND: forall ms, ~DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) ms)
    :
      at_external ((StackCons dl st0 tl), ohs0) (oh0, snd ohs0) args

  | at_external_dr
      st0 tl oh0 ohs0 args
      (AT: msdr.(ModSem.at_external) st0 oh0 args)
      (MSFIND: forall ms, ~DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) ms)
    :
      at_external ((StackCons dr st0 tl), ohs0) (fst ohs0, oh0) args
  .

  Variant initial_frame (ohs: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_dl
      st0
      (MSFIND: DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdl)
      (INIT: msdl.(ModSem.initial_frame) (fst ohs) args st0)
    :
      initial_frame ohs args (StackCons dl st0 StackNil, ohs)

  | initial_frame_dr
      st0
      (MSFIND: DtmAux.find_fptr_owner [msdl ; msdr] (Args.get_fptr args) msdr)
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
    Hypothesis (MIDXL: mdl.(Mod.midx) = Some midx).
    Hypothesis (MIDXR: mdr.(Mod.midx) <> None).
    Hypothesis (WFL: Sk.wf mdl).
    Hypothesis (WFR: Sk.wf mdr).

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
      replace (Mod.sk mdl :: Mod.sk mdr :: map Mod.sk ctx2)
        with ([Mod.sk mdl ; Mod.sk mdr] ++ map Mod.sk ctx2) by ss.
      erewrite link_list_assoc_one; ss; try eapply WF; ss; try rewrite in_app; ss; eauto.
      ii. rewrite in_map_iff in *. des; clarify; et.
      try eapply WF; ss; try rewrite in_app; ss; eauto.
    Qed.

    Let mil: Midx.t := mdl.(Mod.midx).
    Let mir: Midx.t := mdr.(Mod.midx).

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
      Hypothesis DTML: forall
          oh args st0 st1
          (INIT0: msdl.(ModSem.initial_frame) oh args st0)
          (INIT1: msdl.(ModSem.initial_frame) oh args st1)
        ,
          st0 = st1
      .
      Hypothesis DTMR: forall
          oh args st0 st1
          (INIT0: msdr.(ModSem.initial_frame) oh args st0)
          (INIT1: msdr.(ModSem.initial_frame) oh args st1)
        ,
          st0 = st1
      .
      Hypothesis WFCTX1: forall md (IN: In md ctx1), <<WF: Sk.wf md>>.
      Hypothesis WFCTX2: forall md (IN: In md ctx2), <<WF: Sk.wf md>>.
      Hypothesis MIDIFF: Mod.midx mdl <> Mod.midx mdr.
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

      Lemma match_states_xsim
            st_src0 st_tgt0
            (MATCH: match_states skenv_link st_src0 st_tgt0) :
        <<XSIM: xsim (sem (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2)) (sem (ctx1 ++ [mdl] ++ [mdr] ++ ctx2))
                     bot2 top1 top1 tt st_src0 st_tgt0>>
      .
      Proof.
        revert_until INCLTGT.
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
            admit "".
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
            assert(exists ms_tgt,
                      <<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms_tgt>> /\
                                ((<<CTX: ms_tgt = ms /\ ms.(ModSem.midx) <> mil /\ ms.(ModSem.midx) <> mir>>) \/
                                 (<<FOCL: ms_tgt = Mod.modsem mdl skenv_link>> /\ <<FOC: ms = ms_link>>) \/
                                 (<<FOCR: ms_tgt = Mod.modsem mdr skenv_link>> /\ <<FOC: ms = ms_link>>))).
            { clear - MSFIND ms_link msdl msdr LINKSK skenv_link INCLSRC INCLTGT MIDXL MIDXR.
              inv MSFIND. ss. des; clarify.
              { esplits; try left; et. - econs; et. ss. et. - ss. esplits; eauto with congruence. }
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

                  exploit (@SkEnv.project_impl_spec skenv_link mdl); et.
                  { eapply INCLTGT. unfold prog_tgt. rewrite in_app_iff; ss. et. }
                  intro PROJL.
                  exploit (@SkEnv.project_impl_spec skenv_link mdr); et.
                  { eapply INCLTGT. unfold prog_tgt. rewrite in_app_iff; ss. et. }
                  intro PROJR.
                  exploit (@SkEnv.project_impl_spec skenv_link md_link); et.
                  { eapply INCLSRC. unfold prog_src. rewrite in_app_iff; ss. et. }
                  intro PROJLINK.

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
                + admit "medium -- midx".
            }
            des; clarify.
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
            assert(exists ms_src,
                      <<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms_src>> /\
                                ((<<CTX: ms = ms_src /\ ms.(ModSem.midx) <> mil /\ ms.(ModSem.midx) <> mir>>) \/
                                 (<<FOCL: ms = Mod.modsem mdl skenv_link>> /\ <<FOC: ms_src = ms_link>>) \/
                                 (<<FOCR: ms = Mod.modsem mdr skenv_link>> /\ <<FOC: ms_src = ms_link>>))).
            { admit "medium -- bsim ". }
            inv OHS.
            des; clarify.
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

    Theorem merge:
      <<BEH: improves (sem prog_src) (sem prog_tgt)>>
    .
    Proof.
      eapply bsim_improves; eauto. ss.
      eapply Simulation.mixed_to_backward_simulation; et.
      econs. instantiate (1:= bot2). instantiate (1:= unit).
      econs; ss; try apply preservation_top; et; cycle 1.
      { ii. des. inv SAFESRC. rewrite <- LINKSAME; et. }
      econs 1; ss.
      ii. inv INITSRC; ss. des_ifs.
      esplits; et.
      { econs; cycle 1.
        { eapply initial_state_determ; et. }
        ss. rewrite <- LINKSAME; et.
        econs; ss; et.
        - rewrite <- LINKSAME; et.
        - i. rewrite in_app_iff in *. ss; des; clarify; try (by eapply WF; ss; try rewrite in_app; ss; et).
        - admit "ez - nodup".
      }
      eapply match_states_xsim with (skenv_link := Sk.load_skenv sk_link); et.
      econs 2; et.
      - econs; et.
      - ii. ss.
        admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
      - admit "ez - load_owned_heaps".
    Unshelve.
      all: try eapply ModSem.initial_owned_heap.
    Qed.
  End MERGE.

End ModTuple.
Print ModTuple.t.



