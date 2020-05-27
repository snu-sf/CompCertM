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

  Section PROPS.
    Variable mdl mdr: Mod.t.
    Variable sk: Sk.t.
    Variable midx: string.
    Variable ctx1 ctx2: list Mod.t.
    Hypothesis (LINKSK: link (mdl: Sk.t) mdr = Some sk).
    Hypothesis (MIDXL: mdl.(Mod.midx) = Some midx).
    Hypothesis (WFL: Sk.wf mdl).
    Hypothesis (WFR: Sk.wf mdr).

    Let WFLINK: Sk.wf (t mdl mdr sk midx).
    Proof.
      eapply link_preserves_wf_sk in LINKSK; et.
    Qed.

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

    Section MATCH.
      Variable skenv_link: SkEnv.t.
      Let msdl: ModSem.t := (Mod.get_modsem mdl skenv_link mdl.(Mod.data)).
      Let msdr: ModSem.t := (Mod.get_modsem mdr skenv_link mdr.(Mod.data)).
      Let ms_link: ModSem.t := (ModSemTuple.t (Mod.get_modsem mdl skenv_link mdl.(Mod.data))
                                              (Mod.get_modsem mdr skenv_link mdr.(Mod.data)) sk skenv_link midx).

      Inductive match_focus_stack: (stack msdl msdr) -> list Frame.t -> Prop :=
      | match_focus_stack_nil
        :
          match_focus_stack StackNil nil
      | match_focus_stack_cons_dl
          stl0 stk frs
          (TL: match_focus_stack stk frs)
        :
          match_focus_stack (StackCons dl stl0 stk) ((Frame.mk msdl stl0) :: frs)
      | match_focus_stack_cons_dr
          stl0 stk frs
          (TL: match_focus_stack stk frs)
        :
          match_focus_stack (StackCons dr stl0 stk) ((Frame.mk msdr stl0) :: frs)
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

      (*** ohs_tgt is the latest known global Ohs. src's internal Ohs should be consistent with it ***)
      Inductive match_stacks (ohs_tgt: Ohs): list Frame.t -> list Frame.t -> Prop :=
      | match_stacks_nil
        :
          match_stacks ohs_tgt [] []
      | match_stacks_cons_ctx
          tail_src tail_tgt
          (TAIL: match_stacks ohs_tgt tail_src tail_tgt) hd :
          match_stacks ohs_tgt (hd :: tail_src) (hd :: tail_tgt)
      | match_stacks_focus
          tail_src tail_tgt
          (TAIL: match_stacks ohs_tgt tail_src tail_tgt)
          hd_src stk_src oh_src hds_tgt
          (NNIL: stk_src <> StackNil)
          (HD: match_focus_stack stk_src hds_tgt)
          (STK: hd_src = Frame.mk ms_link (stk_src, oh_src))
          (OHL: ohs_tgt msdl.(ModSem.midx) = upcast (fst oh_src))
          (OHR: ohs_tgt msdr.(ModSem.midx) = upcast (snd oh_src))
        :
          match_stacks ohs_tgt (hd_src :: tail_src) (hds_tgt ++ tail_tgt)
      .

      Lemma match_stacks_right_nil
            ohs_tgt frs
            (STK: match_stacks ohs_tgt frs []) :
        <<NIL: frs = []>>.
      Proof.
        inv STK; ss. destruct hds_tgt, tail_tgt; ss.
        inv HD; ss.
      Qed.

      Inductive match_states : Sem.state -> Sem.state -> Prop :=
      | match_states_normal
          frs_src frs_tgt ohs_src ohs_tgt
          (STK: match_stacks ohs_tgt frs_src frs_tgt)
          (OHS: forall mj (NL: mj <> msdl.(ModSem.midx)) (NR: mj <> msdr.(ModSem.midx)),
              ohs_src mj = ohs_tgt mj)
        :
          match_states (State frs_src ohs_src) (State frs_tgt ohs_tgt)
      | match_states_call
          frs_src frs_tgt args ohs_src ohs_tgt
          (STK: match_stacks ohs_tgt frs_src frs_tgt)
          (OHS: forall mj (NL: mj <> msdl.(ModSem.midx)) (NR: mj <> msdr.(ModSem.midx)),
              ohs_src mj = ohs_tgt mj)
          ohl ohr
          (OHLR: @downcast ms_link.(ModSem.owned_heap) (ohs_src msdl.(ModSem.midx)) = Some (ohl, ohr))
          (OHL: @downcast msdl.(ModSem.owned_heap) (ohs_tgt msdl.(ModSem.midx)) = Some ohl)
          (OHR: @downcast msdr.(ModSem.owned_heap) (ohs_tgt msdr.(ModSem.midx)) = Some ohr)
        :
          match_states (Callstate args frs_src ohs_src) (Callstate args frs_tgt ohs_tgt)
      .

    End MATCH.

    Lemma match_states_xsim
          skenv_link st_src0 st_tgt0
          (MATCH: match_states skenv_link st_src0 st_tgt0) :
      <<XSIM: xsim (sem (ctx1 ++ [mdl] ++ [mdr] ++ ctx2)) (sem (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2))
                   bot2 top1 top1 tt st_src0 st_tgt0>>
    .
    Proof.
      revert_until LINKSAME.
      pcofix CIH. i. pfold.
      inv MATCH.
      - (* normal *)
        ss. destruct frs_src; ss.
        { inv STK. left. right.
          econs 1; eauto.
          econs 1; eauto.
          - econs 1; eauto. i. inv STEPSRC.
          - i. ss. inv FINALSRC; ss. }
        rename t into fr_src.
        destruct frs_tgt; ss.
        { exploit match_stacks_right_nil; et. i; des. clarify. }
        rename t into fr_tgt.
        ii. clear SSSRC. ss. rewrite LINKTGT in *.
        destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
        (* tgt call *)
        (* fsim *)
        { left. right. econs; et. econs; et; cycle 1.

        inv STK; ss.
        + destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
        
        ii.
        admit "".
      - (* call *)
        admit "".
    Qed.

    Theorem merge:
      <<BEH: improves (sem (ctx1 ++ [mdl] ++ [mdr] ++ ctx2)) (sem (ctx1 ++ [(t mdl mdr sk midx)] ++ ctx2))>>
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
  End PROPS.

End ModTuple.
Print ModTuple.t.



