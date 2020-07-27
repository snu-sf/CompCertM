From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require SimMemId SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon SIRStack CtypesC ClightC.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.



Definition Kbot := Kstop.

Inductive kle: cont -> cont -> Prop :=
(* | kle_refl *)
(*     k *)
(*   : *)
(*     kle k k *)
| kle_bot
    k
  :
    kle Kbot k
| Kseq_le
    st
    k0 k1
    (LE: kle k0 k1)
  :
    kle (Kseq st k0) (Kseq st k1)
| Kloop1_le
    cond body
    k0 k1
    (LE: kle k0 k1)
  :
    kle (Kloop1 cond body k0) (Kloop1 cond body k1)
| Kloop2_le
    cond body
    k0 k1
    (LE: kle k0 k1)
  :
    kle (Kloop2 cond body k0) (Kloop2 cond body k1)
| Kswitch_le
    k0 k1
    (LE: kle k0 k1)
  :
    kle (Kswitch k0) (Kswitch k1)
| Kcall_le
    oid fd e te
    k0 k1
    (LE: kle k0 k1)
  :
    kle (Kcall oid fd e te k0) (Kcall oid fd e te k1)
.

Program Instance kle_Reflexive: Reflexive kle.
Next Obligation.
  induction x; ii; ss; try (by econs; et).
Qed.

Lemma kle_refl k: kle k k. Proof. refl. Qed.
Hint Resolve kle_refl.

Inductive state_le: state -> state -> Prop :=
| State_le
    fd st e le m
    k0 k1
    (LE: kle k0 k1)
  :
    state_le (State fd st k0 e le m) (State fd st k1 e le m)
| Callstate_le
    fptr ty vs m
    k0 k1
    (LE: kle k0 k1)
  :
    state_le (Callstate fptr ty vs k0 m) (Callstate fptr ty vs k1 m)
| Returnstate_le
    v m k0 k1
    (LE: kle k0 k1)
  :
    state_le (Returnstate v k0 m) (Returnstate v k1 m)
.

Lemma kle_call_cont
      k0 k1
      (LE: kle k0 k1)
  :
    kle (call_cont k0) (call_cont k1)
.
Proof.
  ginduction k0; ii; ss; try inv LE; try econs; et; ss; et.
Qed.

(* Lemma kle_find_label: forall *)
(*       lbl body res *)
(*       k0 k1 *)
(*       (KLE: kle k0 k1) *)
(*       (LBL: find_label lbl body k0 = Some res) *)
(*   , *)
(*     <<LBL: find_label lbl body k1 = Some res>> *)
(* with *)
(* kle_find_label_ls: forall *)
(*     lbl body res *)
(*     k0 k1 *)
(*     (KLE: kle k0 k1) *)
(*     (LBL: find_label_ls lbl body k0 = Some res) *)
(*   , *)
(*     <<LBL: find_label_ls lbl body k1 = Some res>> *)
(* . *)
(* Proof. *)
(*   - ii. destruct body; ss. *)
(*     + des_ifs; et. *)
(*       * *)
(*   - ii. move body at top. revert_until kle_find_label_ls. induction body; ii; ss. *)
(*     + destruct body1; ss; et. *)
(*       * destruct body1; ss. eapply kle_find_label. *)
(* Qed. *)

Lemma step_step
      se ge st_bot0 tr st_bot1 st0
      (NOGOTO: True)
      (STEP: step2 se ge st_bot0 tr st_bot1)
      (LE: state_le st_bot0 st0)
  :
    exists st1, <<STEP: step2 se ge st0 tr st1>> /\ <<LE: state_le st_bot1 st1>>
.
Proof.
  inv STEP; inv LE; try inv LE0; ss; try (by esplits; repeat (econs; ss; eauto using kle_call_cont)).
  - esplits; et.
    + econs; ss; et. TTTTTTTTTTTTTTTTTTT <--------- this does not hold. Kbot is not really bot.
  - admit "goto".
  - admit "goto".
  - admit "goto".
  - admit "goto".
Qed.

Lemma plus_plus
      se ge st_bot0 tr st_bot1 st0
      (NOGOTO: True)
      (STEP: plus step2 se ge st_bot0 tr st_bot1)
      (LE: state_le st_bot0 st0)
  :
    exists st1, <<STEP: plus step2 se ge st0 tr st1>> /\ <<LE: state_le st_bot1 st1>>
.
Proof.
  admit "ez".
Admitted.



Section OWNEDHEAP.

Variable mi: string.
Variable md_src: SMod.t unit.
Variable p_tgt: program.
Let p_src := SMod.prog md_src.
Let md_tgt := module2_mi p_tgt (Some mi).
Hypothesis (MISRC: md_src.(SMod.midx) = mi).
Variable skenv_link: SkEnv.t.
Let ms_src := md_src skenv_link.
Let ms_tgt := md_tgt skenv_link.

Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function p_tgt).
Let ge: genv := Build_genv (SkEnv.revive (skenv) p_tgt) p_tgt.(prog_comp_env).

Notation ktr :=
  (ktree (eff1 unit) (unit * (mem * val)) (unit * (mem * val)))
.
Notation itr := (itree (eff1 unit) (unit * (mem * val))).



(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let fr_src := itree (E unit) (unit * (mem * val)).
Let fr_tgt := Clight.state.

Section FRAME.

Inductive _match_fr (match_fr: fr_src -> fr_tgt -> Prop): fr_src -> fr_tgt -> Prop :=
| match_fr_ret
    oh0 m0 v0
  :
    _match_fr match_fr (Ret (oh0, (m0, v0))) (Returnstate v0 Kbot m0)
| match_fr_tau
    st_src0 st_tgt0 st_tgt1
    (SIM: match_fr st_src0 st_tgt1)
    (TGT: Plus ms_tgt st_tgt0 E0 st_tgt1)
  :
    _match_fr match_fr (tau;; st_src0) (st_tgt0)
| match_fr_icall
    fname oh0 m0 vs0
    fblk ty fd
    (SYMB: Genv.find_symbol ge fname = Some fblk)
    (FINDF: Genv.find_funct ge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal fd))
    (TY: type_of_fundef (Ctypes.Internal fd) = ty)

    k_src
    (* (SIM: match_fr st_src0 st_tgt0) *)
    (* (TGT: Plus ms_tgt st_tgt0 E0 st_tgt1) *)
  :
    _match_fr match_fr
              (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_src)
              (Callstate (Vptr fblk Ptrofs.zero) ty vs0 Kbot m0)
| match_fr_ub
    kt st0
  :
    _match_fr match_fr
              (Vis (subevent _ (EUB)) kt)
              st0
| match_fr_ecall
    fptr oh0 m0 vs0 k_src
    sg targs tres cconv
    (EXTERNAL: Genv.find_funct ge fptr = None)
    (SG: (signature_of_type targs tres cconv) = sg)
    (SIG: exists skd, (Genv.find_funct skenv_link) fptr = Some skd
                      /\ Some (signature_of_type targs tres cconv) = Sk.get_csig skd)
  :
    _match_fr match_fr
              (Vis (subevent _ (ECall sg fptr oh0 m0 vs0)) k_src)
              (Callstate fptr (Tfunction targs tres cconv) vs0 Kbot m0)
.

Definition match_fr: _ -> _ -> Prop := paco2 _match_fr bot2.
Lemma match_fr_mon: monotone2 _match_fr.
Proof.
  ii. destruct IN; try (by econs; et; rr; et).
Qed.

End FRAME.
Hint Unfold match_fr.
Hint Resolve match_fr_mon: paco.






(*** I don't use record style in order not to contaminate namespace ***)
(* Inductive stack: Type := *)
(* | mk_stack *)
(*     (optid: option ident) *)
(*     (fd: Clight.function) *)
(*     (e: env) *)
(*     (le: temp_env) *)
(* . *)

(***
[ktr] [ktr] [tau ;; Ret 10]
let k0 := Kcall _ _ Kbot in
let k1 := Kcall _ _ k1 in
Callstate k1
***)

Inductive match_stack: list ktr -> cont -> Prop :=
| match_stack_nil
  :
    match_stack [] Kstop
| match_stack_cons
    hd tl
    oid fd e te ktl
    (TL: match_stack tl ktl)
    (HD: forall oh0 m0 r0,
        match_fr (hd (oh0, (m0, r0)))
                 (State fd Sskip ktl e (set_opttemp oid r0 te) m0))
  :
    match_stack (hd :: tl) (Kcall oid fd e te ktl)
.

Inductive match_states: SIRStack.state unit -> state -> Prop :=
| match_states_intro
    cur_src cont_src
    fptr ty vs ktl m0
    (CUR: match_fr cur_src (Callstate fptr ty vs Kbot m0))
    (CONT: match_stack cont_src ktl)
  :
    match_states (mk cur_src cont_src) (Callstate fptr ty vs ktl m0)
.

Inductive match_func: SIRCommon.function unit -> function -> Prop :=
| match_func_intro
    kt fd
    (SIM: forall
        oh0 m0 vs0
        e le m1
        (ENTRY: function_entry2 ge fd vs0 m0 e le m1)
      ,
        match_fr (kt oh0 m0 vs0) (State fd fd.(fn_body) Kbot e le m1))
  :
    match_func kt fd

.

Inductive match_prog: (SIRCommon.program unit) -> program -> Prop :=
| match_prog_intro
    p_src p_tgt
    (PROG: forall
        id
        (SRC: is_some (p_src id))
      ,
        <<TGT: is_some ((prog_defmap (program_of_program p_tgt)) ! id)>>)
    (SIM: forall
        id f_src f_tgt
        (SRC: p_src id = Some f_src)
        (TGT: ((prog_defmap (program_of_program p_tgt)) ! id) = Some (Gfun (Internal f_tgt)))
      ,
        <<SIM: match_func f_src f_tgt>>)
  :
    match_prog p_src p_tgt
.

(* Inductive match_states: SIRStack.state unit -> state -> Prop := *)
(* (* | match_states_nil *) *)
(* (*     oh0 m0 v0 *) *)
(* (*   : *) *)
(* (*     match_states (Ret (oh0, (m0, v0))) (Returnstate v0 Kbot m0) *) *)
(* | match_states_start *)
(*   : *)
(*     match_states (it0) (Callstate fptr ty vs0 k0 m0) *)
(* . *)

(* Inductive match_stack (stk_src: ktr) (stk_tgt: stack): Prop := *)
(* | match_stack_intro *)
(*     optid fd e le *)
(*     (TGT: stk_tgt = mk_stack optid fd e le) *)
(*     (SIM: forall oh0 m0 v0, *)
(*         match_states (stk_src (oh0, (m0, v0))) *)
(*                      (State fd Clight.Sskip Kunused e (set_opttemp optid v0 le) m0)) *)
(* . *)

End SYNTAX.
Hint Unfold match_fr.
Hint Constructors match_prog match_func match_states match_stack.
Hint Resolve match_fr_mon: paco.



Let SMO := SimMemOh_default_aux _ (Some mi).
Local Existing Instance SMO.

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

Ltac inv H := inversion H; clear H; substs.

Lemma match_states_lxsim
      st_src0 st_tgt0 smo0
      (MATCH: match_states st_src0 st_tgt0)
  :
    <<XSIM: lxsim ms_src ms_tgt 
                  (fun _ => () -> exists (_ : ()) (_ : mem), True)
                  (Ord.lift_idx unit_ord_wf tt) st_src0 st_tgt0 smo0>>
.
Proof.
  revert_until SMO.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.
  inv MATCH.
  punfold CUR. inv CUR.
  - pclearbot.
    + ss. econs 1. ii. econs 1; swap 2 3.
      { split; intro T; rr in T; des; ss; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. inv STEPSRC; ss. clarify. substs.
      exploit plus_plus; et.
      { instantiate (1:= Callstate fptr ty vs ktl m0). econs; et. econs; et.
      esplits; et.
      * left. eapply ModSemProps.spread_dplus.
        { eapply modsem2_mi_determinate; et. }
        ss; et.
      * right. eapply CIH. econs; ss; et.
Qed.








Section SIM.

  Hypothesis (SIMP: match_prog p_src p_tgt).

  Lemma match_prog_sim_st
        i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st bot2 tt (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    punfold SIM. inv SIM; cbn.
    - gstep. econs; et.
    - pclearbot. gstep. econs; et. gbase. et.
    - pclearbot. gstep. econs; et. gbase.
      eapply CIH. eapply match_itr_bind.
      { u. ii. repeat spc MATCH. pclearbot. eauto. }
      exploit (@SIMP fname); et. intro T. r in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      exploit T; et.
    - gstep. econs; et. u in *. gstep. econs; et. repeat spc MATCH. specialize (MATCH H0).
      des; ss. gbase. eapply CIH.
      eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - gstep. econs; et. ii. exploit SIM0; et. i; des_safe. pclearbot. esplits.
      gstep. econs; et. eauto with paco.
    - gstep. des. pclearbot. econs; et. esplits; et. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_tgt0)). cbn. econs; et. eauto with paco.
    - gstep. pclearbot. econs; et. ii. repeat spc SIM0. gstep.
      rewrite (unfold_interp_mrec _ (Tau i_src0)). cbn. econs; et. eauto with paco.
  Unshelve.
    all: ss.
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh_src oh_tgt
      (O: SO oh_src oh_tgt)
    ,
      (<<SIM: sim_st bot2 tt (interp_program p_src (ICall fname oh_src m vs))
                     (interp_program p_tgt (ICall fname oh_tgt m vs))
                     >>)
  .
  Proof.
    {
      ii.
      eapply match_prog_sim_st; ss.
      hexploit (@SIMP fname); et. intro T. r in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      repeat (spc T). des. ss.
    }
  Qed.

  Hypothesis (SIMMI: mi_src = mi_tgt).
  Hypothesis (SIMO: forall skenv, SO (md_src.(SMod.initial_owned_heap) skenv)
                                     (md_tgt.(SMod.initial_owned_heap) skenv)).
  Hypothesis (SIMSK: md_src.(SMod.sk) = md_tgt.(SMod.sk)).
  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    eapply SimSIR.sim_mod; eauto.
    econs; et.
    { eapply unit_ord_wf. }
    ii. clarify. esplits. eapply adequacy_local_local; et.
  Qed.

  Theorem correct: rusc defaultR [md_src: Mod.t] [md_tgt: Mod.t].
  Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

  Lemma match_itr_bind_assume
        P x y
        (MATCH: match_itr x y)
    :
      <<MATCH: match_itr (assume P ;; x) (assume P ;; y)>>
  .
  Proof.
    Fail eapply match_itr_bind.
    Fail progress f_equiv.
    (*** Like in SIRHoare, we need to parameterize "match_itr" in order to do this.
         However, we can't do that for arbitrary type S. (because it is not leibniz equality)
         TODO: current design is somewhat unsatisfactory. Probably what we want is following:
           - SIRLocalStrong: src/tgt can have different value/mem/owned_heap,
                             but weak match_itr_bind
           - SIRLocalWeak: src/tgt should have (leibniz) equal value/mem/owned_heap,
                           but strong match_itr_bind
     ***)
    unfold assume. des_ifs; irw; ss.
    unfold triggerUB. irw. pfold; econs; et.
  Qed.

  Lemma match_itr_bind_guarantee
        P x y
        (MATCH: match_itr x y)
    :
      <<MATCH: match_itr (guarantee P ;; x) (guarantee P ;; y)>>
  .
  Proof.
    unfold guarantee. des_ifs; irw; ss.
    unfold triggerNB. irw. pfold; econs; et.
  Qed.

End SIM.

End OWNEDHEAP.
Hint Unfold match_itr match_fn match_prog.
Hint Resolve match_itr_mon: paco.
Hint Constructors bindC: core.


Section REFL.
  Variable owned_heap: Type.
  Global Program Instance match_itr_Reflexive: Reflexive (match_itr (@eq owned_heap)).
  Next Obligation.
    rr. revert x.
    ginit.
    { intros. eapply cpn2_wcompat; eauto with paco. }
    gcofix CIH. ii. gstep.
    ides x.
    - destruct r0 as [oh [m vs]]. econs; et.
    - econs; et. eauto with paco.
    - destruct e.
      + destruct i. econs; et. ii. rr in H. des_ifs. des; clarify. eauto with paco.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify. eauto with paco.
        * destruct e; try econs; et. ii. esplits; et. eauto with paco.
  Qed.
  
  Global Program Instance match_fn_Reflexive: Reflexive (match_fn (@eq owned_heap)).
  Next Obligation.
    ii. clarify. r. refl.
  Qed.

  Global Program Instance match_prog_Reflexive: Reflexive (match_prog (@eq owned_heap)).
  Next Obligation.
    ii. clarify. r. des_ifs. r. refl.
  Qed.

End REFL.



(*** TODO: move to CoqlibC ***)
Ltac unfoldr term :=
  first[
      unfold term at 10|
      unfold term at 9|
      unfold term at 8|
      unfold term at 7|
      unfold term at 6|
      unfold term at 5|
      unfold term at 4|
      unfold term at 3|
      unfold term at 2|
      unfold term at 1|
      unfold term at 0
    ]
.

Ltac step :=
  match goal with
  | [ |- SIRLocal.match_itr eq (assume _ ;; _) (assume _ ;; _) ] =>
    eapply match_itr_bind_assume; irw
  | [ |- SIRLocal.match_itr eq (guarantee _ ;; _) (guarantee _ ;; _) ] =>
    eapply match_itr_bind_guarantee; irw
  | [ |- SIRLocal.match_itr eq (assume ?P ;; _) _ ] =>
    unfoldr assume;
    let name := fresh "_ASSUME" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      unfold triggerUB;
      rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
      pfold; by (econs; eauto)|irw]
  | [ |- SIRLocal.match_itr eq (guarantee ?P ;; _) _ ] =>
    unfoldr guarantee;
    let name := fresh "_GUARANTEE" in
    destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
      contradict name|irw]
  | [ |- SIRLocal.match_itr eq ((match ?x with _ => _ end) >>= guaranteeK _)
                            (match ?y with _ => _ end) ] =>
    tryif (check_equal x y)
    then let name := fresh "_DES" in
         destruct x eqn:name; clarify; irw
    else fail
  | [ |- SIRLocal.match_itr eq (triggerUB >>= _) _ ] =>
    unfold triggerUB; irw;
    pfold; by (econs; eauto)
  | [ |- SIRLocal.match_itr eq _ (triggerNB >>= _) ] =>
    unfold triggerNB; irw;
    pfold; by (econs; eauto)
  | [ |- SIRLocal.match_itr eq (guaranteeK ?P ?x) _ ] =>
    unfold guaranteeK;
    let name := fresh "_GUARANTEEK" in
    destruct (ClassicalDescription.excluded_middle_informative (P x)) as [name|name]; cycle 1; [
      contradict name|irw]
  | [ |- SIRLocal.match_itr eq (Ret _) (Ret _) ] =>
    pfold; try (by econs; eauto)
  | [ |- SIRLocal.match_itr eq (Vis (subevent _ (ICall _ _ _ _)) _)
                            (Vis (subevent _ (ICall _ _ _ _)) _) ] =>
    pfold; eapply match_icall; ss; et
  | [ |- HProper _ _ _ ] => ii
  | [ H: SALL _ _ _ |- _ ] => r in H; des_ifs_safe; des; clarify
  | [ |- upaco2 (_match_itr ?SO) bot2 _ _ ] =>
    left;
    replace (paco2 (_match_itr SO) bot2) with (SIRLocal.match_itr SO) by ss;
    irw
  end
.
