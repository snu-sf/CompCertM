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

  Variable cp_link cp1 cp2: Csyntax.program.
  Variable ctx: Syntax.program.
  Hypothesis FOCUS: link cp1 cp2 = Some cp_link.
  (* Let prog_src := cp_link.(CsemC.module) :: ctx. *)
  (* Let prog_tgt := cp1.(CsemC.module) :: cp2.(CsemC.module) :: ctx. *)
  Let prog_src := ctx ++ [cp_link.(CsemC.module)].
  Let prog_tgt := ctx ++ [cp1.(CsemC.module) ; cp2.(CsemC.module)].
  Variable sk_link: Sk.t.
  Hypothesis (LINKSRC: link_sk prog_src = Some sk_link).
  Let skenv_link: SkEnv.t := (Sk.load_skenv sk_link).

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

  Definition is_call_cont_strong (k0: cont): Prop :=
    match k0 with
    | Kcall _ _ _ _ _ => True
    | _ => False
    end
  .

  Inductive sum_cont: list Frame.t -> cont -> Prop :=
  | sum_cont_nil
    :
      sum_cont [] Kstop
  | sum_cont_cons
      hd _fptr _ty _vs k0 _m
      (HD: ms_is_c1 hd.(Frame.ms) /\ hd.(Frame.st) ~= Csem.Callstate _fptr _ty _vs k0 _m)
      tl k1
      (TL: sum_cont tl k1)
      (CALL: is_call_cont_strong k0)
      k2
      (K: k2 = app_cont k0 k1)
    :
      (* sum_cont (hd :: tl) (app_cont k0 k1) *)
      sum_cont (hd :: tl) k2
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
      ms_src ms_tgt
      cst_src cst_tgt
      (* `{ms_src.(ModSem.state) = Csem.state} *)
      (* `{ms_tgt.(ModSem.state) = Csem.state} *)
      (* (CSRC: ms_src.(ModSem.state) = Csem.state) *)
      (* (CTGT: ms_tgt.(ModSem.state) = Csem.state) *)
      (MSSRC: ms_is_c1 ms_src)
      (MSTGT: ms_is_c1 ms_tgt)
      (* fptr ty vs k_src k_tgt m *)
      (* (STSRC: cst_src ~= Csem.Callstate fptr ty vs k_src m) *)
      (* (STTGT: cst_tgt ~= Csem.Callstate fptr ty vs k_tgt m) *)
      tl_tgt k_tl_tgt
      (SUM: sum_cont tl_tgt k_tl_tgt)
      (* (CONT: k_src = app_cont k_tgt k_tl_tgt) *)
      (ST: match_focus_state cst_src cst_tgt k_tl_tgt)
      st_src st_tgt
      (ABCSRC: st_src ~= cst_src)
      (ABCTGT: st_tgt ~= cst_tgt)
    :
      match_focus (Frame.mk ms_src st_src) ((Frame.mk ms_tgt st_tgt) :: tl_tgt)
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
      (* abstr (ModSem.state ms_tgt) st_tgt; abstr (ModSem.state ms_src) st_src. *)
      (* Fail abstr (ModSem.state ms_src) st_src; abstr (ModSem.state ms_tgt) st_tgt. *)
      erewrite f_equal_hr; try apply FINAL0; ss.
      des. subst. simpl_depind.
      eapply f_equal_h; eauto.
      { etrans; eauto. }
      { etrans; eauto. }
      { etrans; eauto.
        inv ST; try rewrite app_cont_stop_right in *; etrans; eauto.
      }
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
        inv TAIL. rewrite app_nil_r in *. inv HD. des. ss.
        assert(T: final_frame cst_src ~= ModSem.final_frame ms_src st_src).
        { eapply f_equal_h; eauto. }
        assert(N: final_frame cst_src retv0).
        { erewrite f_equal_hr; cycle 1.
          { apply T. }
          { refl. }
          { refl. }
          ss.
        }
        inv N.
        inv ST. ss. clarify.
        hexpl app_cont_kstop_inv. clarify.
        hexpl sum_cont_kstop_inv. clarify.
        ss. clear_tac.
        econs; ss; et.
        erewrite f_equal_hr; try apply FINAL0; try refl.
        { eapply f_equal_h; eauto; try (by etrans; eauto). }
        ss.
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

  Lemma match_xsim
        st_src0 st_tgt0
        (MATCH: match_states st_src0 st_tgt0)
    :
      <<XSIM: xsim (sem prog_src) (sem prog_tgt) bot2 tt st_src0 st_tgt0>>
  .
  Proof.
    revert_until prog_tgt.
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
        destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
        - (* src call *)
          left. econs; et.
          { i. eapply final_fsim; et. econs; et. }
          econs; cycle 1.
          { admit "receptive - SemProps.v". }
          i. inv STEPSRC; ss; ModSem.tac.
          esplits; eauto.
          { left. eapply plus_one. econs; et.
            { admit "determinate - SemProps.v". }
            econs; eauto.
            instantiate (1:= args).
            inv STK; ss. inv HD; ss. des. clarify. ss.
            assert(at_external cst_src args).
            
            simpl_depind.
          }
          admit "ez".
        - (* src focus *)
          admit "hard".
      }
      destruct (classic (fr_tgt.(Frame.ms).(ModSem.is_return) fr_tgt.(Frame.st))).
      { (* tgt return *)
        r in H0. des.
        right. econs; et.
        - admit "ez".
        - i. econs; ss; et. des_ifs.
        left. econs; et.
        - ii; ss. inv FINALSRC. inv STK; cycle 1.
          + inv TAIL. econs. ss. ss.
      }
      destruct (classic (fr_src.(Frame.ms).(ModSem.is_call) fr_src.(Frame.st))).
      { (* call *)
        r in H. des.
        left.
        econs; eauto.
        admit "TODO".
      }
      destruct (classic (fr_src.(Frame.ms).(ModSem.is_return) fr_src.(Frame.st))).
      { (* ret *)
        admit "TODO".
      }
      admit "step case".
    -
      assert((fr_src.(Frame.ms).(ModSem.is_step) fr_src.(Frame.st))).
      right. econs; eauto.
      { i. exploit final_bsim; eauto. i; des. esplits; eauto. eapply star_refl. }
      i.
      
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
  Qed.

  | match_regular_states
      frs_src frs_tgt
      (FMATCH: match_frames (frs_src) (frs_tgt))
    :
      match_states (State (frs_src)) (State (frs_tgt)) 0
  | match_call_states
      args_src frs_src args_tgt frs_tgt ms1 ms2
      (OWNER1: Ge.find_fptr_owner ge (Args.fptr args_src) ms1)
      (OWNER2: Ge.find_fptr_owner tge (Args.fptr args_tgt) ms2)
      (FMATCH: match_frames frs_src frs_tgt)
      (OWNER: match_owner ms1 ms2)
    :
      match_states (Callstate args_src frs_src) (Callstate args_tgt frs_tgt) 0
  | match_extcall_states
      fr_src fr_tgt frs_src frs_tgt prog_tgt
      fptr tyf args k m
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (FMATCH: match_frames (fr_src::frs_src) (fr_tgt::frs_tgt))
      (MSSRC: Frame.ms fr_src = CsemC.modsem skenv_link_src prog')
      (MSTGT: Frame.ms fr_tgt = CsemC.modsem skenv_link_src prog_tgt)
      (FRAMETGT: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) (Csem.Callstate fptr tyf args k m))
      (EXTCALL: external_state (Build_genv (local_genv prog_tgt) (prog_comp_env prog_tgt)) (Csem.Callstate fptr tyf args k m))
    :
      match_states (State (fr_src::frs_src)) (State (fr_tgt::frs_tgt)) 1
  | match_ret_states
      fr_src fr_tgt frs_src frs_tgt prog_tgt
      m r
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (FMATCH: match_frames (fr_src::frs_src) (fr_tgt::frs_tgt))
      (MSSRC: Frame.ms fr_src = CsemC.modsem skenv_link_src prog')
      (MSTGT: Frame.ms fr_tgt = CsemC.modsem skenv_link_src prog_tgt)
      (FRAMETGT: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) (Csem.Returnstate r Kstop m))
    :
      match_states (State (fr_src::frs_src)) (State (fr_tgt::frs_tgt)) 1
  .



  Lemma transf_program_correct:
    mixed_simulation (Sem.sem prog_src) (Sem.sem prog_tgt).
  Proof.
    eapply Mixed_simulation. eapply transf_xsim_properties.
  Qed.

  (** ********************* linking *********************************)    
  Variable prog1 : Csyntax.program.
  Variable prog2 : Csyntax.program.
  Variable prog' : Csyntax.program.
  Hypothesis LINK : link prog1 prog2 = Some prog'.
  Let tprog' : Syntax.program := List.map CsemC.module [prog2; prog1].
  Variable ctx : Syntax.program.
  Let prog : Syntax.program := CsemC.module prog' :: ctx.
  Let tprog : Syntax.program := tprog' ++ ctx.
  (** ********************* linking *********************************)
  Variable sk_src: Sk.t.
  Hypothesis LINK_SK_SRC: link_sk prog = Some sk_src.
  (* TODO: consider linking fail case *)
  Let skenv_link_src := Sk.load_skenv sk_src.
  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link_tgt := Sk.load_skenv sk_tgt.
  
  Let ge := load_genv prog skenv_link_src.
  (* Let ge_ce : composite_env := prog_comp_env prog. *)
  (* Let tge_ce : composite_env := prog_comp_env prog. *)
  Let tge := load_genv tprog skenv_link_tgt.
  (* Inductive match_states_aux : Csem.State -> Sem.state -> nat -> Prop := *)
  Definition local_genv (p : Csyntax.program) :=
    (skenv_link_src.(SkEnv.project) p.(defs)).(revive) p.
  Lemma skenv_link_same:
    skenv_link_src = skenv_link_tgt.
  Proof.
  Admitted.
  
End PRESERVATION.



Local Opaque Z.mul.
Section PRESERVATION.
  Existing Instance Val.mi_final.
(** UpperBound A *)
(*
A
* : Physical
+ : Logical 
(c0 * c1) + ctx
>=
(c0 + c1) + ctx
*)
  
(*
B
* : Physical
+ : Logical 
c0 * empty
>=
c0 + empty
*)
  
  Section PLANB1.
(** ********************* linking *********************************)    
  Variable prog1 : Csyntax.program.
  Variable prog2 : Csyntax.program.
  Variable prog' : Csyntax.program.
  Hypothesis LINK : link prog1 prog2 = Some prog'.
  Let tprog' : Syntax.program := List.map CsemC.module [prog2; prog1].
  Variable ctx : Syntax.program.
  Let prog : Syntax.program := CsemC.module prog' :: ctx.
  Let tprog : Syntax.program := tprog' ++ ctx.
(** ********************* linking *********************************)
  Variable sk_src: Sk.t.
  Hypothesis LINK_SK_SRC: link_sk prog = Some sk_src.
  (* TODO: consider linking fail case *)
  Let skenv_link_src := Sk.load_skenv sk_src.
  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link_tgt := Sk.load_skenv sk_tgt.
  
  Let ge := load_genv prog skenv_link_src.
  (* Let ge_ce : composite_env := prog_comp_env prog. *)
  (* Let tge_ce : composite_env := prog_comp_env prog. *)
  Let tge := load_genv tprog skenv_link_tgt.
(* Inductive match_states_aux : Csem.State -> Sem.state -> nat -> Prop := *)
  Definition local_genv (p : Csyntax.program) :=
    (skenv_link_src.(SkEnv.project) p.(defs)).(revive) p.
  Lemma skenv_link_same:
    skenv_link_src = skenv_link_tgt.
  Proof.
  Admitted.
  
  (*
  (c0 * c1) + ctx
  >=
  (c0 + c1) + ctx
  src : physical
  tgt : logical
  src has 3 Modules (C0*C1), ctx, Sys
  tgt has 4 Modules C0, C1, ctx, Sys
  there are "5" kinds of match states needed(maybe)
  1. reg - reg 
  2. call - call
  3. reg - call ----> only btw c maybe
  (* 4. ret - ret *)
  (* 5. reg - ret *)
  what is reg state? 1. internal 
   *)
  Fixpoint app_cont (c1 c2: cont) : cont :=
    match c1 with
    | Kstop => c2
    | Kdo c => Kdo (app_cont c c2)
    | Kseq s c => Kseq s (app_cont c c2)
    | Kifthenelse s1 s2 c => Kifthenelse s1 s2 (app_cont c c2)
    | Kwhile1 e s c => Kwhile1 e s (app_cont c c2)
    | Kwhile2 e s c => Kwhile2 e s (app_cont c c2)
    | Kdowhile1 e s c => Kdowhile1 e s (app_cont c c2)
    | Kdowhile2 e s c => Kdowhile2 e s (app_cont c c2)
    | Kfor2 e s1 s2 c => Kfor2 e s1 s2 (app_cont c c2)
    | Kfor3 e s1 s2 c => Kfor3 e s1 s2 (app_cont c c2)
    | Kfor4 e s1 s2 c => Kfor4 e s1 s2 (app_cont c c2)
    | Kswitch1 ls c =>  Kswitch1 ls (app_cont c c2)
    | Kswitch2 c =>  Kswitch2 (app_cont c c2)
    | Kreturn c => Kreturn (app_cont c c2)
    | Kcall f e em ty c => Kcall f e em ty (app_cont c c2)
    end.
  Inductive similar_state : Csem.state -> Csem.state -> cont -> Prop :=
  | reg_state_similar
      f s c c0 c1 e m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.State f s c e m) (Csem.State f s c1 e m) c0
  | expr_state_similar
      f ex c c0 c1 e m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.ExprState f ex c e m) (Csem.ExprState f ex c1 e m) c0
  | call_sate_similar
      fptr tyf vargs c c0 c1 m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.Callstate fptr tyf vargs c m) (Csem.Callstate fptr tyf vargs c1 m) c0
  | return_sate_similar
      vres c c0 c1 m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.Returnstate vres c m) (Csem.Returnstate vres c1 m) c0
  | stuck_state_similar
      c0
    : similar_state Csem.Stuckstate Csem.Stuckstate c0.
  Inductive match_frames : list Frame.t -> list Frame.t -> Prop :=
  | match_frames_nil
    :
      match_frames nil nil
  | match_frames_cons_sys
      fr_src frs_src fr_tgt frs_tgt st
      (MATCH: match_frames frs_src frs_tgt)
      (SYS1: fr_src = Frame.mk (System.modsem skenv_link_src) st)
      (SYS1: fr_tgt = Frame.mk (System.modsem skenv_link_tgt) st)
    :
      match_frames (fr_src::frs_src) (fr_src::frs_tgt)
  | match_frames_cons_ctx
      fr_src frs_src fr_tgt frs_tgt
      m st1 st2 (* state must be same?? i dont think so *)
      (MATCH: match_frames frs_src frs_tgt)
      (MOD: In m ctx)
      (CTX1: fr_src = Frame.mk (Mod.get_modsem m skenv_link_src (Mod.data m)) st1)
      (CTX2: fr_tgt = Frame.mk (Mod.get_modsem m skenv_link_src (Mod.data m)) st2)
      (SAME: st1 = st2)
    :
      match_frames (fr_src::frs_src) (fr_src::frs_tgt)
  | match_frames_cons_c_one
      fr_src frs_src fr_tgt frs_tgt prog_tgt st_src st_tgt
      (MATCH: match_frames frs_src frs_tgt)
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (CSTATE1: fr_src = Frame.mk (CsemC.modsem skenv_link_src prog') st_src)
      (CSTATE2: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) st_tgt)
      (SAME: st_src = st_tgt) (* everything is the same, including cont *)
    :
      match_frames (fr_src::frs_src) (fr_tgt::frs_tgt) (* this case needed? *)
  | match_frames_cons_c_two
      fr_src frs_src fr_tgt0 fr_tgt1 frs_tgt
      st_src st_tgt0 st_tgt1 fptr tyf vs_arg c0 m0 prog_tgt
      (MATCH: match_frames frs_src frs_tgt)
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (C0STATE: st_tgt0 = Csem.Callstate fptr tyf vs_arg c0 m0)      
      (C0EXT: at_external skenv_link_tgt prog_tgt st_tgt0 (Args.mk fptr vs_arg m0))
      (SIMILAR: similar_state st_src st_tgt1 c0)
    :
      match_frames (fr_src::frs_src) (fr_tgt1::fr_tgt0::frs_tgt).
  Inductive match_owner : ModSem.t -> ModSem.t -> Prop :=
  | match_sys
      ms1 ms2
      (SYS1: ms1 = System.modsem skenv_link_src)
      (SYS2: ms2 = System.modsem skenv_link_tgt)
    :
      match_owner ms1 ms2
  | match_ctx
      m ms1 ms2
      (MOD: In m ctx)
      (CTX1: ms1 = Mod.get_modsem m skenv_link_src (Mod.data m))
      (CTX2: ms2 = Mod.get_modsem m skenv_link_tgt (Mod.data m))
    :
      match_owner ms1 ms2
  | match_cmod
      prog_tgt ms1 ms2
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (CMOD1: ms1 = CsemC.modsem skenv_link_src prog')
      (CMOD2: ms2 = CsemC.modsem skenv_link_tgt prog_tgt)
    :
      match_owner ms1 ms2.
  (*  there are "5" kinds of match states needed(maybe)
  1. reg - reg 
  2. call - call
  3. reg - call ----> only btw c maybe
  (* 4. ret - ret *)
  (* 5. reg - ret *)
   *)
  
  Inductive match_states : Sem.state -> Sem.state -> nat -> Prop :=
  | match_regular_states
      frs_src frs_tgt
      (FMATCH: match_frames (frs_src) (frs_tgt))
    :
      match_states (State (frs_src)) (State (frs_tgt)) 0
  | match_call_states
      args_src frs_src args_tgt frs_tgt ms1 ms2
      (OWNER1: Ge.find_fptr_owner ge (Args.fptr args_src) ms1)
      (OWNER2: Ge.find_fptr_owner tge (Args.fptr args_tgt) ms2)
      (FMATCH: match_frames frs_src frs_tgt)
      (OWNER: match_owner ms1 ms2)
    :
      match_states (Callstate args_src frs_src) (Callstate args_tgt frs_tgt) 0
  | match_extcall_states
      fr_src fr_tgt frs_src frs_tgt prog_tgt
      fptr tyf args k m
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (FMATCH: match_frames (fr_src::frs_src) (fr_tgt::frs_tgt))
      (MSSRC: Frame.ms fr_src = CsemC.modsem skenv_link_src prog')
      (MSTGT: Frame.ms fr_tgt = CsemC.modsem skenv_link_src prog_tgt)
      (FRAMETGT: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) (Csem.Callstate fptr tyf args k m))
      (EXTCALL: external_state (Build_genv (local_genv prog_tgt) (prog_comp_env prog_tgt)) (Csem.Callstate fptr tyf args k m))
    :
      match_states (State (fr_src::frs_src)) (State (fr_tgt::frs_tgt)) 1
  | match_ret_states
      fr_src fr_tgt frs_src frs_tgt prog_tgt
      m r
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (FMATCH: match_frames (fr_src::frs_src) (fr_tgt::frs_tgt))
      (MSSRC: Frame.ms fr_src = CsemC.modsem skenv_link_src prog')
      (MSTGT: Frame.ms fr_tgt = CsemC.modsem skenv_link_src prog_tgt)
      (FRAMETGT: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) (Csem.Returnstate r Kstop m))
    :
      match_states (State (fr_src::frs_src)) (State (fr_tgt::frs_tgt)) 1
  .
  (* | match_reg_call *) (* this match case isn't necessary *)
  (*     prog_tgt fr_tgt fr_src *)
  (*     frs_src frs_tgt args_tgt *)
  (*     (PROG: prog_tgt = prog1 \/ prog_tgt = prog2) *)
  (*     (MSSRC: Frame.ms fr_src = CsemC.modsem skenv_link_src prog') *)
  (*     (MSTGT: Frame.ms fr_tgt = CsemC.modsem skenv_link_tgt prog_tgt) *)
  (*     (FMATCH: match_frames (fr_src::frs_src) (fr_tgt::frs_tgt)) *)
  (*     (ATEXT: ModSem.at_external (Frame.ms fr_tgt) (Frame.st fr_tgt) args_tgt) *)
  (*   : *)
  (*     match_states (State (fr_src::frs_src)) (Callstate args_tgt (fr_tgt::frs_tgt))       *)
  End PLANB1.
End PRESERVATION.
  (* 
  Inlining
  src - not inlined 
  tgt - inlined 
  so....
  src has more "function call"
  1. reg - reg 
  2. call - call
  3. call - reg
  4. ret - ret
  5. ret - reg
  *)
(*   Inductive match_states: RTL.state -> RTL.state -> Prop := *)
(*   | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' F fenv ctx *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs') *)
(*         (COMPAT: fenv_compat prog fenv) *)
(*         (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code)) *)
(*         (AG: agree_regs F ctx rs rs') *)
(*         (SP: F sp = Some(sp', ctx.(dstk))) *)
(*         (MINJ: Mem.inject F m m') *)
(*         (VB: Mem.valid_block m' sp') *)
(*         (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize)) *)
(*         (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned) *)
(*         (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)), *)
(*       match_states (State stk f (Vptr sp Ptrofs.zero true) pc rs m) *)
(*                    (State stk' f' (Vptr sp' Ptrofs.zero true) (spc ctx pc) rs' m') *)
(*   | match_call_states: forall stk fptr sg tfptr args m stk' args' m' F *)
(*         (MS: match_stacks F m m' stk stk' (Mem.nextblock m')) *)
(*         (FPTR: Val.inject F fptr tfptr) *)
(*         (VINJ: Val.inject_list F args args') *)
(*         (MINJ: Mem.inject F m m'), *)
(*       match_states (Callstate stk fptr sg args m) *)
(*                    (Callstate stk' tfptr sg args' m') *)
(*   | match_call_regular_states: forall stk fptr sg f vargs m stk' f' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs') *)
(*         (FPTR: Genv.find_funct ge fptr = Some (Internal f)) *)
(*         (COMPAT: fenv_compat prog fenv) *)
(*         (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code)) *)
(*         (BELOW: context_below ctx' ctx) *)
(*         (NOP: f'.(fn_code)!pc' = Some(Inop pc1')) *)
(*         (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint))) *)
(*         (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs) *)
(*         (MINJ: Mem.inject F m m') *)
(*         (VB: Mem.valid_block m' sp') *)
(*         (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize)) *)
(*         (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned) *)
(*         (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)), *)
(*       match_states (Callstate stk fptr sg vargs m) *)
(*                    (State stk' f' (Vptr sp' Ptrofs.zero true) pc' rs' m') *)
(*   | match_return_states: forall stk v m stk' v' m' F *)
(*         (MS: match_stacks F m m' stk stk' (Mem.nextblock m')) *)
(*         (VINJ: Val.inject F v v') *)
(*         (MINJ: Mem.inject F m m'), *)
(*       match_states (Returnstate stk v m) *)
(*                    (Returnstate stk' v' m') *)
(*   | match_return_regular_states: forall stk v m stk' f' sp' rs' m' F ctx pc' or rinfo *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs') *)
(*         (RET: ctx.(retinfo) = Some rinfo) *)
(*         (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo)) *)
(*         (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end) *)
(*         (MINJ: Mem.inject F m m') *)
(*         (VB: Mem.valid_block m' sp') *)
(*         (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize)) *)
(*         (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned) *)
(*         (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)), *)
(*       match_states (Returnstate stk v m) *)
(*                    (State stk' f' (Vptr sp' Ptrofs.zero true) pc' rs' m'). *)
(*   Inductive match_stacks (F: meminj) (m m': mem): *)
(*              list stackframe -> list stackframe -> block -> Prop := *)
(*   | match_stacks_nil: forall bound1 bound *)
(*         (MG: match_globalenvs F bound1) *)
(*         (BELOW: Ple bound1 bound), *)
(*       match_stacks F m m' nil nil bound *)
(*   | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound fenv ctx *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs') *)
(*         (COMPAT: fenv_compat prog fenv) *)
(*         (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code)) *)
(*         (AG: agree_regs F ctx rs rs') *)
(*         (SP: F sp = Some(sp', ctx.(dstk))) *)
(*         (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize)) *)
(*         (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned) *)
(*         (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)) *)
(*         (RES: Ple res ctx.(mreg)) *)
(*         (BELOW: Plt sp' bound), *)
(*       match_stacks F m m' *)
(*                    (Stackframe res f (Vptr sp Ptrofs.zero true) pc rs :: stk) *)
(*                    (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero true) (spc ctx pc) rs' :: stk') *)
(*                    bound *)
(*   | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs') *)
(*         (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize)) *)
(*         (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned) *)
(*         (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)) *)
(*         (RET: ctx.(retinfo) = Some (rpc, res)) *)
(*         (BELOW: Plt sp' bound), *)
(*       match_stacks F m m' *)
(*                    stk *)
(*                    (Stackframe res f' (Vptr sp' Ptrofs.zero true) rpc rs' :: stk') *)
(*                    bound *)
(* with match_stacks_inside (F: meminj) (m m': mem): *)
(*         list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop := *)
(*   | match_stacks_inside_base: forall stk stk' f' ctx sp' rs' *)
(*         (MS: match_stacks F m m' stk stk' sp') *)
(*         (RET: ctx.(retinfo) = None) *)
(*         (DSTK: ctx.(dstk) = 0), *)
(*       match_stacks_inside F m m' stk stk' f' ctx sp' rs' *)
(*   | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' *)
(*         (MS: match_stacks_inside F m m' stk stk' f' ctx' sp' rs') *)
(*         (COMPAT: fenv_compat prog fenv) *)
(*         (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code)) *)
(*         (AG: agree_regs F ctx' rs rs') *)
(*         (SP: F sp = Some(sp', ctx'.(dstk))) *)
(*         (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk)) *)
(*         (RES: Ple res ctx'.(mreg)) *)
(*         (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res)) *)
(*         (BELOW: context_below ctx' ctx) *)
(*         (SBELOW: context_stack_call ctx' ctx), *)
(*       match_stacks_inside F m m' (Stackframe res f (Vptr sp Ptrofs.zero true) pc rs :: stk) *)
