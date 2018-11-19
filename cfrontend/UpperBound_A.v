Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.
Require Import Equality.

Set Implicit Arguments.



(* TODO: move to CoqlibC *)
Ltac et:= eauto.

(* Goal (unit -> nat) = (unit -> Z). *)
(* Proof. *)
(* Abort. *)

(* Goal forall A B1 B2, (A -> B1) = (A -> B2) -> B1 = B2. *)

Lemma f_equal_h
      X1 X2 Y1 Y2 (f1: X1 -> Y1) (f2: X2 -> Y2) x1 x2
      (TYPX: X1 = X2)
      (FUNC: f1 ~= f2)
      (ARG: x1 ~= x2)
      (TYPY: Y1 = Y2) (* Do we need this? if above goal holds, we can remove this... *)
  :
    f1 x1 ~= f2 x2
.
Proof.
  subst.
  eapply JMeq_eq in ARG.
  subst.
  ss.
Qed.

Lemma f_equal_hr
      X1 X2 Y (f1: X1 -> Y) (f2: X2 -> Y) x1 x2
      (FUNC: f1 ~= f2)
      (TYP: X1 = X2)
      (ARG: x1 ~= x2)
  :
    f1 x1 = f2 x2
.
Proof.
  eapply JMeq_eq.
  eapply f_equal_h; eauto.
  (* exploit JMeq_func2; eauto. intro. subst. eapply JMeq_eq in FUNC. subst. ss. *)
  (* subst. *)
  (* eapply JMeq_eq in ARG. *)
  (* eapply JMeq_eq in FUNC. *)
  (* clarify. *)
Qed.

Lemma f_equal_rh
      X Y1 Y2 (f1: X -> Y1) (f2: X -> Y2) x
      (FUNC: f1 ~= f2)
      (TYP: Y1 = Y2)
  :
    f1 x ~= f2 x
.
Proof.
  eapply f_equal_h; eauto.
Qed.

(* TODO: move to LinkingC *)
Lemma link_list_aux_empty_inv
      X `{Linker X}
      xs
      (EMPTY: link_list_aux xs  = empty)
  :
    <<NIL: xs = []>>
.
Proof.
  ginduction xs; ii; ss. des_ifs.
Qed.

Lemma link_list_snoc_commut
      X `{Linker X}
      x0 x1 x_link xs
      (LINK: link x0 x1 = Some x_link)
  :
    <<CMT: link_list (xs ++ [x0 ; x1]) = link_list (xs ++ [x_link])>>
.
Proof.
  ginduction xs; ii; ss.
  { unfold link_list. ss. des_ifs. }
  exploit IHxs; eauto. intro IH; des.
  unfold link_list in IH.
  unfold link_list. ss.
  des_ifs; apply_all_once link_list_aux_empty_inv; clarify; ss.
  - destruct xs; ss.
  - destruct xs; ss.
Qed.

(* Lemma link_list_cons_commut *)
(*       X `{Linker X} *)
(*       x0 x1 x_link xs *)
(*       (LINK: link x0 x1 = Some x_link) *)
(*   : *)
(*     <<CMT: link_list (x0 :: x1 :: xs) = link_list (x_link :: xs)>> *)
(* . *)
(* Proof. *)
  
(*   { *)
(*     remember (rev xs) as rem. *)
(*     move rem at top. *)
(*     revert_until H. *)
(*     ginduction rem; ii; ss. *)
(*     { hexpl rev_nil. clarify. ss. unfold link_list; ss. des_ifs. } *)
    
(*   } *)
(*   ginduction xs; ii; ss. *)
(*   { unfold link_list. ss. des_ifs. } *)
(*   unfold link_list. ss. *)
(*   destruct  *)
(*   destruct (link_list_aux xs) eqn:T. *)
(*   { ss. *)
(*   ss. des_ifs. *)
(*   exploit IHxs; eauto. i; des. *)
  
(*   ss. *)
(* Qed. *)





(* put k1 inside k0 (k1 is executed later) *)
Fixpoint app_cont (k0 k1: cont) {struct k0}: cont :=
  match k0 with
  | Kstop => k1
  | Kdo k => Kdo (app_cont k k1)
  | Kseq s k => Kseq s (app_cont k k1)
  | Kifthenelse s1 s2 k => Kifthenelse s1 s2 (app_cont k k1)
  | Kwhile1 e s k => Kwhile1 e s (app_cont k k1)
  | Kwhile2 e s k => Kwhile2 e s (app_cont k k1)
  | Kdowhile1 e s k => Kdowhile1 e s (app_cont k k1)
  | Kdowhile2 e s k => Kdowhile2 e s (app_cont k k1)
  | Kfor2 e s1 s2 k => Kfor2 e s1 s2 (app_cont k k1)
  | Kfor3 e s1 s2 k => Kfor3 e s1 s2 (app_cont k k1)
  | Kfor4 e s1 s2 k => Kfor4 e s1 s2 (app_cont k k1)
  | Kswitch1 ls k =>  Kswitch1 ls (app_cont k k1)
  | Kswitch2 k =>  Kswitch2 (app_cont k k1)
  | Kreturn k => Kreturn (app_cont k k1)
  | Kcall f e em ty k => Kcall f e em ty (app_cont k k1)
  end
.

Definition get_cont (st0: Csem.state): option cont :=
  match st0 with
  | Csem.State _ _ k0 _ _ => Some k0
  | Csem.ExprState _ _ k0 _ _ => Some k0
  | Csem.Callstate _ _ _ k0 _ => Some k0
  | Csem.Returnstate _ k0 _ => Some k0
  | _ => None
  end
.

(* put k0 inside k1 *)
(* Fixpoint app_cont (k0 k1: cont) {struct k1}: cont := *)
(*   match k1 with *)
(*   | Kstop => k0 *)
(*   | Kdo k => Kdo (app_cont k0 k) *)
(*   | Kseq s k => Kseq s (app_cont k0 k) *)
(*   | Kifthenelse s1 s2 k => Kifthenelse s1 s2 (app_cont k0 k) *)
(*   | Kwhile1 e s k => Kwhile1 e s (app_cont k0 k) *)
(*   | Kwhile2 e s k => Kwhile2 e s (app_cont k0 k) *)
(*   | Kdowhile1 e s k => Kdowhile1 e s (app_cont k0 k) *)
(*   | Kdowhile2 e s k => Kdowhile2 e s (app_cont k0 k) *)
(*   | Kfor2 e s1 s2 k => Kfor2 e s1 s2 (app_cont k0 k) *)
(*   | Kfor3 e s1 s2 k => Kfor3 e s1 s2 (app_cont k0 k) *)
(*   | Kfor4 e s1 s2 k => Kfor4 e s1 s2 (app_cont k0 k) *)
(*   | Kswitch1 ls k =>  Kswitch1 ls (app_cont k0 k) *)
(*   | Kswitch2 k =>  Kswitch2 (app_cont k0 k) *)
(*   | Kreturn k => Kreturn (app_cont k0 k) *)
(*   | Kcall f e em ty k => Kcall f e em ty (app_cont k0 k) *)
(*   end *)
(* . *)

Lemma app_cont_stop_right
      k0
  :
    <<EQ: app_cont k0 Kstop = k0>>
.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_stop_left
      k0
  :
    <<EQ: app_cont Kstop k0 = k0>>
.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_kstop_inv
      k0 k1
      (APP: app_cont k0 k1 = Kstop)
  :
    k0 = Kstop /\ k1 = Kstop
.
Proof.
  destruct k0; ss.
Qed.



Section PRESERVATION.

  Variable cp_link cp0 cp1: Csyntax.program.
  Variable ctx: Syntax.program.
  Hypothesis FOCUS: link cp0 cp1 = Some cp_link.
  (* Let prog_src := cp_link.(CsemC.module) :: ctx. *)
  (* Let prog_tgt := cp1.(CsemC.module) :: cp2.(CsemC.module) :: ctx. *)
  Let prog_src := ctx ++ [cp_link.(CsemC.module)].
  Let prog_tgt := ctx ++ [cp0.(CsemC.module) ; cp1.(CsemC.module)].
  Variable sk_link: Sk.t.
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).
  Hypothesis (LINKSRC: link_sk prog_src = Some sk_link).
  Let ge_cp_link := (revive (SkEnv.project skenv_link (defs cp_link)) cp_link).
  Let ge_cp0 := (revive (SkEnv.project skenv_link (defs cp0)) cp0).
  Let ge_cp1 := (revive (SkEnv.project skenv_link (defs cp1)) cp1).

  Lemma link_sk_match
    :
      <<EQ: link_sk prog_src = link_sk prog_tgt>>
  .
  Proof.
    subst_locals.
    unfold link_sk.
    rewrite ! map_app. ss.
    symmetry.
    eapply link_list_snoc_commut; eauto.
    admit "this should hold - it should be proven somewhere else too. ask @minki".
  Qed.

  Let LINKTGT: link_sk prog_tgt = Some sk_link.
  Proof.
    rewrite link_sk_match in *. ss.
  Qed.




  Definition ms_is_c0 (ms: ModSem.t): Prop :=
    exists _skenv _cprog, CsemC.modsem _skenv _cprog = ms
  .

  (* Definition ms_is_c1 (ms: ModSem.t): Prop := *)
  (*   (<<ST: ms.(ModSem.state) = Csem.state>>) /\ *)
  (*   (<<AFTER: ms.(ModSem.after_external) ~= CsemC.after_external>>) /\ *)
  (*   (<<FINAL: ms.(ModSem.final_frame) ~= CsemC.final_frame>>) *)
  (* . *)


  Notation " 'ms_is_c1' ms" :=
    ((<<CST0: ms.(ModSem.state) = Csem.state>>) /\
     (<<CAT0: ms.(ModSem.at_external) ~= CsemC.at_external>>) /\
     (<<CAFT0: ms.(ModSem.after_external) ~= CsemC.after_external>>) /\
     (<<CFIN0: ms.(ModSem.final_frame) ~= CsemC.final_frame>>))
      (at level 50, no associativity, only parsing)
  .


  (* Inductive cont_frame_wf (conts: list Frame.t): Prop := *)
  (* | cont_wf_intro *)
  (*     (WF: forall *)
  (*         cont *)
  (*         (IN: In cont conts) *)
  (*       , *)
  (*         (<<ISC: ms_is_c cont.(Frame.ms)>>) *)
  (*         /\ *)
  (*         (<<CONT: exists _fptr _ty _vs _cont.(Frame.st) ~= Csem.Callstate >>) *)
  (*     ) *)
  (* . *)

  Definition is_focus (cp: Csyntax.program): Prop := cp = cp0 \/ cp = cp1.

  Inductive sum_cont: list Frame.t -> cont -> Prop :=
  | sum_cont_nil
    :
      sum_cont [] Kstop
  | sum_cont_cons
      _fptr _ty _vs k0 _m
      (CALL: is_call_cont_strong k0)
      tl k1
      (TL: sum_cont tl k1)
      k2
      (K: k2 = app_cont k0 k1)
      cp
      (FOCUS: is_focus cp)
    :
      sum_cont ((Frame.mk (CsemC.modsem skenv_link cp) (Csem.Callstate _fptr _ty _vs k0 _m)) :: tl) k2
  .

  Lemma sum_cont_kstop_inv
        frs
        (SUM: sum_cont frs Kstop)
    :
      frs = []
  .
  Proof.
    clear - SUM.
    inv SUM; ss.
    hexpl app_cont_kstop_inv. clarify.
  Qed.

  Inductive match_focus_state: Csem.state -> Csem.state -> cont -> Prop :=
  | reg_state_similar
      f s k k0 k1 e m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.State f s k e m) (Csem.State f s k1 e m) k0
  | expr_state_similar
      f ex k k0 k1 e m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.ExprState f ex k e m) (Csem.ExprState f ex k1 e m) k0
  | call_sate_similar
      fptr tyf vargs k k0 k1 m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.Callstate fptr tyf vargs k m) (Csem.Callstate fptr tyf vargs k1 m) k0
  | return_sate_similar
      vres k k0 k1 m
      (CONT: k = app_cont k1 k0)
    : match_focus_state (Csem.Returnstate vres k m) (Csem.Returnstate vres k1 m) k0
  (* | stuck_state_similar *)
  (*     k0 *)
  (*   : match_focus_state Csem.Stuckstate Csem.Stuckstate k0 *)
  .

  Section TEST.

    Class converter (X Y: Type) := { conv: X -> Y }.
    Notation "@" := conv (at level 50).
    Global Program Instance eq_converter X Y (EQ: X = Y): (converter X Y).

    Obligation Tactic := idtac.
    Program Definition match_focus' (fr_src: Frame.t) (frs_tgt: list Frame.t): Prop :=
      match fr_src, frs_tgt with
      | Frame.mk ms_src cst_src, (Frame.mk ms_tgt cst_tgt) :: tl_tgt =>
        exists ms_src ms_tgt cst_src cst_tgt tl_tgt k_tl_tgt,
        (<<MSSRC: ms_is_c1 ms_src>>) /\
        (<<MSTGT: ms_is_c1 ms_tgt>>) /\
        (<<SUM: sum_cont tl_tgt k_tl_tgt>>) /\
        (<<ST: match_focus_state cst_src cst_tgt k_tl_tgt>>)
      | _, _ => False
      end
    .
    Next Obligation.
      ii. des_ifs.
      admit "".
    Defined.
  End TEST.

  Inductive match_focus: Frame.t -> list Frame.t -> Prop :=
  | match_focus_cons_right
      cst_src cst_tgt
      (* `{ms_src.(ModSem.state) = Csem.state} *)
      (* `{ms_tgt.(ModSem.state) = Csem.state} *)
      (* (CSRC: ms_src.(ModSem.state) = Csem.state) *)
      (* (CTGT: ms_tgt.(ModSem.state) = Csem.state) *)
      (* fptr ty vs k_src k_tgt m *)
      (* (STSRC: cst_src ~= Csem.Callstate fptr ty vs k_src m) *)
      (* (STTGT: cst_tgt ~= Csem.Callstate fptr ty vs k_tgt m) *)
      tl_tgt k_tl_tgt
      (SUM: sum_cont tl_tgt k_tl_tgt)
      (* (CONT: k_src = app_cont k_tgt k_tl_tgt) *)
      (ST: match_focus_state cst_src cst_tgt k_tl_tgt)
      cp
      (FOCUS: is_focus cp)
    :
      match_focus (Frame.mk (CsemC.modsem skenv_link cp_link) cst_src)
                  ((Frame.mk (CsemC.modsem skenv_link cp) cst_tgt) :: tl_tgt)
  .

  Lemma match_focus_nonnil
        fr frs
        (FC: match_focus fr frs)
    :
      <<NONNIL: frs <> []>>
  .
  Proof.
    inv FC; ss.
  Qed.

  Inductive match_stacks: list Frame.t -> list Frame.t -> Prop :=
  | match_stacks_nil
    :
      match_stacks [] []
  | match_stacks_cons_ctx
      tail_src tail_tgt
      (TAIL: match_stacks tail_src tail_tgt)
      hd
    :
      match_stacks (hd :: tail_src) (hd :: tail_tgt)
  (* | match_stacks_cons_focus *)
  (*     tail_src tail_tgt *)
  (*     (TAIL: match_stacks tail_src tail_tgt) *)
  (*     hd_src hds_tgt *)
  (*     (HD: (admit "") hd_src hds_tgt) *)
  (*   : *)
  (*     match_stacks (hd_src :: tail_src) (hds_tgt ++ tail_tgt) *)
  | match_stacks_focus
      tail_src tail_tgt
      (TAIL: match_stacks tail_src tail_tgt)
      hd_src hds_tgt
      (HD: match_focus hd_src hds_tgt)
    :
      match_stacks (hd_src :: tail_src) (hds_tgt ++ tail_tgt)
  .

  Lemma match_stacks_right_nil
        frs
        (STK: match_stacks frs [])
    :
      <<NIL: frs = []>>
  .
  Proof.
    (* ginduction frs; ii; ss. *)
    inv STK; ss. destruct hds_tgt, tail_tgt; ss.
    exploit match_focus_nonnil; et. i; ss.
  Qed.

  Inductive match_states : Sem.state -> Sem.state -> Prop :=
  | match_states_normal
      frs_src frs_tgt
      (STK: match_stacks frs_src frs_tgt)
    :
      match_states (State frs_src) (State frs_tgt)
  | match_states_call
      frs_src frs_tgt
      args
      (STK: match_stacks frs_src frs_tgt)
    :
      match_states (Callstate args frs_src) (Callstate args frs_tgt)
  .

  Lemma init_fsim
        st_init_src
        (INIT: initial_state prog_src st_init_src)
    :
      exists (i0: unit) st_init_tgt,
        (<<INIT: Dinitial_state (sem prog_tgt) st_init_tgt>>) /\
        (<<MATCH: match_states st_init_src st_init_tgt>>)
  .
  Proof.
    exists tt, st_init_src.
    esplits; eauto.
    { inv INIT. econs; ss; eauto.
      - (* init *)
        econs; ss; eauto. rewrite <- link_sk_match; eauto.
      - (* dtm *)
        ii. inv INIT0; inv INIT1; ss. f_equal.
        generalize link_sk_match; i. des. rewrite H in *. clarify.
    }
    { inv INIT.
      econs; ss; eauto. econs; ss; eauto.
    }
  Qed.

  Lemma final_bsim
        retv
        frs_src frs_tgt
        (MATCH: match_states (State frs_src) (State frs_tgt))
        (FINAL: final_state (State frs_tgt) retv)
        (SAFESRC: safe (sem prog_src) (State frs_src))
    :
      <<FINAL: final_state (State frs_src) retv>>
  .
  Proof.
    ss.
    inv FINAL. inv MATCH; ss. inv STK; ss.
    - (* ctx *)
      exploit match_stacks_right_nil; eauto. i; des; clarify.
      econs; eauto.
    - (* focus *)
      exploit app_length; try rewrite H1; eauto. intro LEN; ss.
      hexploit match_focus_nonnil; et. i; des.
      destruct hds_tgt; ss. destruct tail_tgt; ss; try xomega. destruct hds_tgt; ss. clarify. clear_tac.
      exploit match_stacks_right_nil; et. i; des; clarify.
      econs; et.
      inv HD. ss. inv SUM.
      inv FINAL0; ss.
      inv ST; ss.
  Qed.

  Lemma final_fsim
        retv
        frs_src frs_tgt
        (MATCH: match_states (State frs_src) (State frs_tgt))
        (FINAL: final_state (State frs_src) retv)
    :
      <<DFINAL: Dfinal_state (sem prog_tgt) (State frs_tgt) retv>>
  .
  Proof.
    rr. econs; ss; et.
    {
      inv FINAL. inv MATCH; ss. inv STK; ss.
      - (* ctx *)
        inv TAIL. econs; et.
      - (* focus *)
        inv TAIL. rewrite app_nil_r in *. inv HD. ss. inv FINAL0; ss. inv ST; ss.
        hexpl app_cont_kstop_inv. clarify.
        hexpl sum_cont_kstop_inv. clarify.
        econs; ss; et.
    }
    { ii; ss. inv FINAL0; inv FINAL1; ss. determ_tac ModSem.final_frame_dtm. rewrite INT in *. clarify. }
    { ii. ss. des_ifs; ss.
      inv FINAL. inv MATCH; ss. inv STK; ss.
      - (* ctx *)
        inv TAIL. inv H; ModSem.tac.
      - (* focus *)
        inv TAIL. rewrite app_nil_r in *. inv FINAL0; ss. inv H; ss; ModSem.tac.
    }
      (* + rewrite CFIN1 in FINAL1. inv HD. *)
      (* exploit app_length; try rewrite H1; eauto. intro LEN; ss. *)
      (* hexploit match_focus_nonnil; et. i; des. *)
      (* destruct hds_tgt; ss. destruct tail_tgt; ss; try xomega. destruct hds_tgt; ss. clarify. clear_tac. *)
      (* exploit match_stacks_right_nil; et. i; des; clarify. *)
      (* econs; et. *)
      (* inv HD. ss. inv SUM. *)
      (* rewrite app_cont_stop_right in *. *)
      (* (* abstr (ModSem.state ms_tgt) st_tgt; abstr (ModSem.state ms_src) st_src. *) *)
      (* (* Fail abstr (ModSem.state ms_src) st_src; abstr (ModSem.state ms_tgt) st_tgt. *) *)
      (* erewrite JMeq_app_strong; try apply FINAL0; ss. *)
      (* des. subst. simpl_depind. *)
      (* eapply JMeq_app; eauto. *)
      (* { etrans; eauto. } *)
      (* { etrans; eauto. } *)
      (* { etrans; eauto. } *)
  Qed.

  Lemma msfind_fsim
        fptr ms
        (MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms)
    :
      (<<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms>>) \/
      (exists cp, (<<ISFOCSRC: ms = CsemC.modsem skenv_link cp_link>>)
                  /\ (<<ISFOCTGT: is_focus cp>>)
                  /\ (<<MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr (CsemC.modsem skenv_link cp)>>))
  .
  Proof.
    unfold load_genv in *. ss. inv MSFIND. ss. des.
    { clarify. left. econs; et. ss. left; ss. }
    unfold load_modsems in *.
    rewrite in_map_iff in *. des; ss. clarify. unfold prog_src in MODSEM0.
    rewrite in_app_iff in *. des; ss.
    { left. econs; et. ss. right. rewrite in_map_iff. esplits; et. unfold prog_tgt. rewrite in_app_iff. left; ss. }
    des; ss. clarify.
    right.
    unfold flip. ss.
    admit "this should hold".
  Qed.

  Lemma msfind_bsim
        fptr ms
        (MSFIND: Ge.find_fptr_owner (load_genv prog_tgt skenv_link) fptr ms)
    :
      (<<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr ms>>) \/
      ((<<MSFIND: Ge.find_fptr_owner (load_genv prog_src skenv_link) fptr (CsemC.modsem skenv_link cp_link)>>)
       /\ exists cp, (<<ISFOCSRC: ms = CsemC.modsem skenv_link cp>>)
                     /\ (<<ISFOCTGT: is_focus cp>>))
  .
  Proof.
    unfold load_genv in *. ss. inv MSFIND. ss. des.
    { clarify. left. econs; et. ss. left; ss. }
    unfold load_modsems in *.
    rewrite in_map_iff in *. des; ss. clarify. unfold prog_tgt in MODSEM0.
    rewrite in_app_iff in *. des; ss.
    { left. econs; et. ss. right. rewrite in_map_iff. esplits; et. unfold prog_src. rewrite in_app_iff. left; ss. }
    des; ss.
    - clarify.
      right.
      unfold flip. ss.
      esplits; et; rr; et.
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
      + instantiate (1:= if_sig). admit" this should hold".
    - clarify.
      right.
      unfold flip. ss.
      esplits; et; rr; et.
      econs; ss; et.
      + right. rewrite in_map_iff. exists (CsemC.module cp_link). ss. esplits; et.
        unfold prog_src. rewrite in_app_iff. right; ss. left; ss.
      + instantiate (1:= if_sig). admit" this should hold".
  Qed.

  Lemma cons_app
        X xhd (xtl: list X)
    :
      xhd :: xtl = [xhd] ++ xtl
  .
  Proof. ss. Qed.

  Lemma app_cont_call_cont_strong
        k0 k1
        (APP: is_call_cont_strong (app_cont k0 k1))
    :
      <<CONT: is_call_cont_strong k0>>
  .
  Proof.
    r in APP. rr. des_ifs. exploit app_cont_stop_left; et. i.
  Abort.

  Lemma match_xsim
        st_src0 st_tgt0
        (MATCH: match_states st_src0 st_tgt0)
    :
      <<XSIM: xsim (sem prog_src) (sem prog_tgt) bot2 tt st_src0 st_tgt0>>
  .
  Proof.
    revert_until LINKTGT.
    pcofix CIH. i. pfold.
    inv MATCH.
    - (* normal state *)
      ss.
      destruct frs_src; ss.
      { inv STK. admit "spurious case". }
      rename t into fr_src.
      destruct frs_tgt; ss.
      { exploit match_stacks_right_nil; et. i; des. clarify. }
      rename t into fr_tgt.
      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_call) fr_tgt.(Frame.st))).
      { (* tgt call *)

        (* fsim *)
        left. econs; et.
        { i. eapply final_fsim; et. econs; et. }

        destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
        - (* src call *)
          econs; ss; cycle 1.
          { admit "receptive - SemProps.v". }
          i; des_ifs.
          inv STEPSRC; ss; ModSem.tac.
          esplits; eauto.
          { left. eapply plus_one. econs; et.
            { admit "determinate - SemProps.v". }
            econs; eauto.
            instantiate (1:= args).
            inv STK; ss. inv HD; ss. des. clarify. ss.
            inv AT; ss.
            inv ST; ss.
            econs; ss; et.
            - admit "ez".
            - rr in H. des. inv H. ss.
          }
          {
            right. eapply CIH; et.
            econs; et.
          }
        - (* src step *)
          inv STK; ss.
          econs; ss; cycle 1.
          { admit "receptive - SemProps.v". }
          i; des_ifs.

          inv STEPSRC; ss; ModSem.tac; swap 2 3.
          { exfalso. contradict H0. rr. eauto. }
          { exfalso.
            inv HD; ss. clarify.
            clear - FINAL ST H.
            rr in H. des. ss. inv H; inv FINAL; inv ST.
          }

          rr in H. des.
          inv HD; ss. clarify. ss. inv H. ss. clarify.
          inv ST.
          rr in STEP. des; try (by inv STEP; ss).
          folder.
          (* set (LLL := (Csem.Callstate fptr_arg tyf vs_arg (app_cont k0 k_tl_tgt) m0)). *)
          (* set (RRR := st0). *)
          inv STEP; ss; cycle 1.
          { exfalso. admit "project only internals". }

          assert(TGTFIND: exists cp_top,
                    <<FINDMS: Ge.find_fptr_owner (load_genv prog_tgt skenv_link)
                                                 fptr_arg (CsemC.modsem skenv_link cp_top)>>
                              /\ <<FOUCS: is_focus cp_top>>).
          (* actually it is counterpart of current cp *)
          { admit "this should hold". }
          des.
          
          unfold Genv.find_funct, Genv.find_funct_ptr in SIG, FPTR. des_ifs. rename b into blk.
          assert(SYMB: exists id blk, Genv.find_symbol cp_top.(globalenv) id = Some blk).
          { admit "1) use SkEnv.wf or 2) change definition of wt_program". }
          des.

          esplits; eauto.
          { left.
            eapply plus_left with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { admit "determinate - SemProps.v". }
              econs 1; ss; et.
              econs; ss; et.
              esplits; eauto. unfold Genv.find_funct_ptr. des_ifs.
            }
            eapply star_two with (t1 := E0) (t2 := E0); ss.
            { econs; et.
              { admit "determinate - SemProps.v". }
              econs 2; ss; et.
              { des_ifs. folder. eauto. }
              ss. econs; ss; et.
              instantiate (1:= f).
              admit "this should hold".
            }
            { ss.
              (* assert(WTST: wt_state cp_top (Csem.Callstate (Vptr blk Ptrofs.zero true) (type_of_function f) vs_arg Kstop m0)). *)
              (* { admit "WT". } *)
              assert(WTPROG: wt_program cp_top).
              { admit "WT". }
              bar.
              (* inv WTST. ss. *)
              inv WTPROG. specialize (H id f). specialize (H (admit "this should hold")).
              inv H.
              econs; ss; et.
              { admit "determinate - SemProps.v". }
              des_ifs.
              econs 3; ss; et.
              rr. right.
              econs; ss; et.
              - inv FINDMS. ss. admit "ez".
              - admit "sizeof_stable".
              - admit "sizeof_stable".
            }
          }
          {
            right. eapply CIH; et.
            ss.
            econs; ss; et.
            unfold Frame.update_st. ss.
            rewrite ! app_comm_cons.
            econs 3; et.
            econs; et.
            { econs; et. }
            econs; et.
          }
      }


      assert(CALLLE: forall
                (CALLSRC: ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src))
              ,
                <<CALLTGT: ModSem.is_call (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
      { admit "this should hold". }
      rename H into NCALLTGT.
      assert(NCALLSRC: ~ ModSem.is_call (Frame.ms fr_src) (Frame.st fr_src)).
      { tauto. }


      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_return) fr_tgt.(Frame.st))).
      { (* tgt return *)
        left. econs; et.
        { i. eapply final_fsim; et. econs; et. }
        econs; et; cycle 1.
        { admit "receptive". }
        i. ss. des_ifs.


        (* inv STK; ss. *)
        (* { inv STEPSRC; ss; ModSem.tac. *)
        (*   assert(frs_tgt <> []). *)
        (*   { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". } *)
        (*   destruct frs_tgt as [|fr_snd frs_tgt]; ss. *)
        (*   esplits; et. *)
        (*   - left. apply plus_one. econs; ss; et. *)
        (*     { admit "determinate". } *)
        (*     des_ifs. *)
        (*     rpapply step_return; et. *)



        inv STEPSRC; ss.
        { contradict NCALLSRC. rr. et. }
        - (* src step *)
          inv STK; ss.
          { ModSem.tac. }
          inv HD; ss. clarify; ss.
          rr in H. des. ss. inv H.
          inv ST. ss.
          rr in STEP. des; inv STEP; ss.
          inv SUM; ss.
          rr in CALL. des_ifs. ss. clarify.
          esplits; eauto.
          + left. eapply plus_two with (t1 := E0) (t2 := E0); ss.
            * econs; et.
              { admit "determinate". }
              ss. des_ifs.
              econs 4; ss; et.
            * econs; et.
              { admit "determinate". }
              ss. des_ifs.
              unfold Frame.update_st. s.
              econs 3; ss; et.
              right.
              econs; ss; et.
          + right. ss. eapply CIH.
            econs; ss; et.
            unfold Frame.update_st. ss.
            rewrite app_comm_cons.
            econs 3; ss; et.
            econs; ss; et.
            econs; ss; et.
        - (* src return *)
          inv STK; ss; cycle 1.
          { (* top is focus *)
            inv HD; ss. clarify; ss.
            inv FINAL. inv ST. exploit app_cont_kstop_inv; et. i; des. clarify. ss. clear_tac.
            exploit sum_cont_kstop_inv; et. i; des. clarify. ss.
            inv SUM.
            assert(tail_tgt <> []).
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". }
            destruct tail_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                ss. des_ifs.
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et.
                rewrite app_comm_cons.
                econs 3; ss; et.
                econs; ss; et.
                econs; ss; et.
          }
          { (* top is ctx *)
            assert(frs_tgt <> []).
            { inv TAIL; ss. hexploit match_focus_nonnil; et. i; des. admit "ez". }
            destruct frs_tgt as [|fr_snd frs_tgt]; ss.
            inv TAIL.
            - (* snd is ctx *)
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et. econs; ss; et.
            - (* snd is focus *)
              hexploit match_focus_nonnil; et. i; des. destruct hds_tgt; ss. clarify.
              inv HD; ss.
              inv AFTER; ss. inv ST; ss.
              esplits; et.
              + left. apply plus_one.
                econs; et.
                { admit "determinate". }
                ss. des_ifs.
                econs 4; ss; et.
              + right. eapply CIH. unfold Frame.update_st. econs; ss; et.
                rewrite app_comm_cons.
                econs 3; ss; et.
                econs; ss; et.
                econs; ss; et.
          }
      }


      assert(RETLE: forall
                (RETSRC: ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src))
              ,
                <<RETTGT: ModSem.is_return (Frame.ms fr_tgt) (Frame.st fr_tgt)>>).
      { admit "this should hold". }
      rename H into NRETTGT.
      assert(NRETSRC: ~ ModSem.is_return (Frame.ms fr_src) (Frame.st fr_src)).
      { tauto. }




      (* src internal && tgt internal *)
      right. econs; et.
      { i. exploit final_bsim; et. { econs; et. } i; des. esplits; et. apply star_refl. }
      i.
      inv STK.
      {
        (* ctx *)
        clear_tac.
        econs; cycle 1.
        - (* progress *)
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
          { inv SAFESRC. contradict NRETTGT. rr. et. }
          des_ifs.
          inv SAFESRC; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          esplits; et.
          econs 3; et.
        - (* bsim *)
          i. ss. des_ifs. clear_tac.
          (* specialize (SAFESRC _ (star_refl _ _ _)). des; ss. *)
          (* { inv SAFESRC. contradict NRETTGT. rr. et. } *)
          (* des_ifs. *)
          inv STEPTGT; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          esplits; et.
          { left. apply plus_one. econs 3; et. }
          right. eapply CIH. econs; et. econs; et.
      }
      {
        (* focus *)
        inv HD; ss. clarify; ss.
        econs; cycle 1.
        - (* progress *)
          i. right. ss. des_ifs. clear_tac. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
          { inv SAFESRC. contradict NRETSRC. rr. et. }
          des_ifs.
          inv SAFESRC; swap 2 3.
          { contradict NCALLSRC. rr. et. }
          { contradict NRETSRC. rr. et. }
          ss.
          esplits; et.
          econs 3; et. ss.
          admit "match_focus_state - progress".
        - (* bsim *)
          i. ss. des_ifs. clear_tac.
          (* specialize (SAFESRC _ (star_refl _ _ _)). des; ss. *)
          (* { inv SAFESRC. contradict NRETTGT. rr. et. } *)
          (* des_ifs. *)
          inv STEPTGT; swap 2 3.
          { contradict NCALLTGT. rr. et. }
          { contradict NRETTGT. rr. et. }
          ss.
          esplits; et.
          { left. apply plus_one. econs 3; et. ss.
            admit "match_focus_state - bsim".
          }
          right. eapply CIH. econs; et. unfold Frame.update_st. ss. admit "match_focus_state - bsim".
      }
    - (* call state *)
      right.
      econs; ss; et.
      { i. inv FINALTGT. }
      econs; cycle 1.
      { i. specialize (SAFESRC _ (star_refl _ _ _)). des; ss.
        { inv SAFESRC. }
        des_ifs. inv SAFESRC.
        right. exploit msfind_fsim; eauto. i; des.
        - esplits; eauto. econs; eauto.
        - clarify. ss. inv INIT. ss. esplits; eauto. econs; eauto. ss. econs; et. ss. admit "ez".
      }
      i. inv STEPTGT. ss. des_ifs.
      exploit msfind_bsim; et. i; des.
      + esplits; eauto.
        { left. apply plus_one. econs; et. }
        right. eapply CIH. econs; et. econs; et.
      + clarify. ss. inv INIT.
        esplits; eauto.
        { left. apply plus_one. econs; et.
          ss. econs; et. ss. instantiate (1:= fd). admit "this should hold".
        }
        right. eapply CIH. econs; et.
        rewrite cons_app with (xtl := frs_tgt).
        econs 3; ss; et.
        econs; ss; et.
        { econs; ss; et. }
        econs; ss; et.
  Unshelve.
    all: ss.
  (*   - *)
  (*     left. *)
  (*     econs; ss; et. *)
  (*     { i. inv FINALSRC. } *)
  (*     econs; cycle 1. *)
  (*     { admit "receptive". } *)
  (*     i. inv STEPSRC. ss. des_ifs. *)
  (*     exploit msfind_fsim; et. i; des. *)
  (*     + esplits; eauto. *)
  (*       { left. apply plus_one. econs; et. *)
  (*         { admit "determinate". } *)
  (*         econs; et. *)
  (*         ss. des_ifs. *)
  (*       } *)
  (*       right. eapply CIH. econs; et. econs; et. *)
  (*     + clarify. ss. inv INIT. *)
  (*       esplits; eauto. *)
  (*       { left. apply plus_one. econs; et. *)
  (*         { admit "determinate". } *)
  (*         econs. *)
  (*         { ss. des_ifs. et. } *)
  (*         ss. econs; et. ss. *)
  (*         instantiate (1:= fd). *)
  (*         admit "this should hold". *)
  (*       } *)
  (*       right. eapply CIH. econs; et. *)
  (*       rewrite cons_app with (xtl := frs_tgt). *)
  (*       econs 3; ss; et. *)
  (*       econs; ss; et. *)
  (*       { econs; ss; et. } *)
  (*       econs; ss; et. *)
  (* Unshelve. *)
  (*   all: ss. *)
  Qed.

  Theorem upperbound_a_xsim
    :
      <<XSIM: mixed_simulation (Sem.sem prog_src) (Sem.sem prog_tgt)>>
  .
  Proof.
    econs; ss; eauto. econs; ss; eauto.
    { eapply unit_ord_wf. }
    econs 1.
    ii. exploit init_fsim; eauto. i; des. esplits; eauto.
    eapply match_xsim; et.
  Qed.

End PRESERVATION.

