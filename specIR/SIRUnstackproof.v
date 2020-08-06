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

Definition get_cont (st: state): cont :=
  match st with
  | State _ _ k _ _ _ => k
  | Callstate _ _ _ k _ => k
  | Returnstate _ k _ => k
  end
.

Definition set_cont (st: state) (k1: cont): state :=
  match st with
  | State fd s k0 e te m0 => State fd s k1 e te m0
  | Callstate fptr ty args k0 m0 => Callstate fptr ty args k1 m0
  | Returnstate res k0 m0 => Returnstate res k1 m0
  end
.

(*** copy-pasted from UBD_Aextra and modified ***)
Fixpoint app_cont (k0 k1: cont) {struct k0}: cont :=
  match k0 with
  | Kstop => k1
  | Kseq s k => Kseq s (app_cont k k1)
  | Kloop1 e s k => Kloop1 e s (app_cont k k1)
  | Kloop2 e s k => Kloop2 e s (app_cont k k1)
  | Kswitch k =>  Kswitch (app_cont k k1)
  | Kcall f e em ty k => Kcall f e em ty (app_cont k k1)
  end.

Lemma app_cont_stop_right
      k0:
    <<EQ: app_cont k0 Kstop = k0>>.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_stop_left
      k0:
    <<EQ: app_cont Kstop k0 = k0>>.
Proof.
  ginduction k0; ii; ss; des; clarify; ss; r; f_equal; ss.
Qed.

Lemma app_cont_kstop_inv
      k0 k1
      (APP: app_cont k0 k1 = Kstop):
    k0 = Kstop /\ k1 = Kstop.
Proof. destruct k0; ss. Qed.

Definition is_call_cont_strong (k0: cont): Prop :=
  match k0 with
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

Lemma call_cont_app_cont
      k k0
      (* tl_tgt *)
      (* (SUM: sum_cont tl_tgt k0) *)
      (CALL: is_call_cont k0)
  :
  (app_cont (call_cont k) k0) = call_cont (app_cont k k0).
Proof.
  assert(CASE: k0 = Kstop \/ is_call_cont_strong k0).
  { destruct k0; ss; et. }
  des.
  { clarify. repeat rewrite app_cont_stop_right. ss. }
  { rr in CASE. des_ifs. clear_tac. clear - c.
    ginduction k; ii; ss; des; repeat rewrite app_cont_stop_right; ss; clarify. }
Qed.

Lemma app_cont_is_call_cont
      k k0
      (CALL0: is_call_cont k)
      (CALL1: is_call_cont k0)
  :
    is_call_cont (app_cont k k0)
.
Proof. destruct k; ss. Qed.

Definition app_cont_state (st0: state) (k0: cont): state :=
  set_cont st0 (app_cont (get_cont st0) k0)
.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

Lemma find_label_none:
  (forall body,
      (forall lbl
              k0 k1
              (LBL: find_label lbl body k0 = None)
        ,
          <<LBL: find_label lbl body k1 = None>>))
  /\ (forall body,
         (forall lbl
                 k0 k1
                 (LBL: find_label_ls lbl body k0 = None)
           ,
             <<LBL: find_label_ls lbl body k1 = None>>))
.
Proof.
  eapply statement_labeled_statements_ind; i; ss.
  - des_ifs_safe. exploit H0; et. intro U. rewrite U in *. des_ifs.
    exploit H; et. intro T. rewrite T in *. ss.
  - des_ifs_safe. exploit H0; et. intro U. rewrite U in *. des_ifs.
    exploit H; et. intro T. rewrite T in *. ss.
  - des_ifs_safe. exploit H0; et. intro U. rewrite U in *. des_ifs.
    exploit H; et. intro T. rewrite T in *. ss.
  - exploit H; et.
  - des_ifs. exploit H; et.
  - des_ifs_safe. exploit H0; et. intro U. rewrite U in *. des_ifs.
    exploit H; et. intro T. rewrite T in *. ss.
Qed.

Lemma find_label_app_cont:
  (forall body,
      (forall lbl
              k0 k1 s kres
              (LBL: find_label lbl body k0 = Some (s, kres))
        ,
          <<LBL: find_label lbl body (app_cont k0 k1) = Some (s, app_cont kres k1)>>))
  /\ (forall body,
         (forall lbl
                 k0 k1 s kres
                 (LBL: find_label_ls lbl body k0 = Some (s, kres))
           ,
             <<LBL: find_label_ls lbl body (app_cont k0 k1) = Some (s, app_cont kres k1)>>))
.
Proof.
  generalize find_label_none. intros [A B].
  eapply statement_labeled_statements_ind; i; ss.
  - destruct (find_label lbl s (Kseq s0 k0)) eqn:T; clarify.
    + exploit H; et. intro U. ss. rewrite U in *. ss.
    + exploit H0; et. intro U. ss. rewrite U in *. des_ifs.
      exfalso. exploit A; et. intro V. rewrite V in *. ss.
  - destruct (find_label lbl s k0) eqn:T; clarify.
    + exploit H; et. intro U. ss. rewrite U in *. ss.
    + exploit H0; et. intro U. ss. rewrite U in *. des_ifs.
      exfalso. exploit A; et. intro V. rewrite V in *. ss.
  - destruct (find_label lbl s (Kloop1 s s0 k0)) eqn:T; clarify.
    + exploit H; et. intro U. ss. rewrite U in *. ss.
    + exploit H0; et. intro U. ss. rewrite U in *. des_ifs.
      exfalso. exploit A; et. intro V. rewrite V in *. ss.
  - exploit H; et.
  - des_ifs. exploit H; et.
  - destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k0)) eqn:T; clarify.
    + exploit H; et. intro U. ss. rewrite U in *. ss.
    + exploit H0; et. intro U. ss. rewrite U in *. des_ifs.
      exfalso. exploit A; et. intro V. rewrite V in *. ss.
Qed.

Lemma step_step
      se ge st0 tr st1
      (STEP: step2 se ge st0 tr st1)
  :
    <<STEP: forall k0 (CALL: is_call_cont k0),
      step2 se ge (app_cont_state st0 k0) tr (app_cont_state st1 k0)>>
.
Proof.
  (* unfold set_cont in STEP. *)
  ii.
  inv STEP; ss; clarify; try (by econs; ss; et).
  - erewrite f_equal2; try econs; ss; et.
    f_equal. eapply call_cont_app_cont; et.
  - erewrite f_equal2; try econs; ss; et.
    f_equal. eapply call_cont_app_cont; et.
  - erewrite f_equal2; try econs; ss; et.
    eapply app_cont_is_call_cont; et.
  - erewrite f_equal2; try econs; ss; et.
    clear_tac.
    rewrite <- call_cont_app_cont; et. eapply find_label_app_cont; et.
Qed.

Lemma star_star
      se ge st0 tr st1
      (STEP: star step2 se ge st0 tr st1)
  :
    <<STEP: forall k0 (CALL: is_call_cont k0),
      star step2 se ge (app_cont_state st0 k0) tr (app_cont_state st1 k0)>>
.
Proof.
  ginduction STEP; ii; ss.
  { apply star_refl. }
  clarify.
  econs; et.
  { eapply step_step; et. }
Qed.

Lemma plus_plus
      se ge st0 tr st1
      (STEP: plus step2 se ge st0 tr st1)
  :
    <<STEP: forall k0 (CALL: is_call_cont k0),
      plus step2 se ge (app_cont_state st0 k0) tr (app_cont_state st1 k0)>>
.
Proof.
  destruct STEP; ii; ss.
  clarify. econs; ss; et.
  { eapply step_step; ss; et. }
  { eapply star_star; ss; et. }
Qed.





(*** MOVE TO PROPER PLACE ***)
Section CTYPESC.
  Context {F: Type}.
  Variable p: Ctypes.program F.
  Definition internal_funs: ident -> bool :=
    fun id => match (prog_defmap p)!id with
              | Some (Gfun (Ctypes.Internal fd)) => true
              | _ => false
              end.
End CTYPESC.




Notation ktr := (ktree (eff1 unit) (unit * (mem * val)) (unit * (mem * val))).
Notation itr := (itree (eff1 unit) (unit * (mem * val))).

Section OWNEDHEAP.

(* Variable md_src: SMod.t unit. *)
(* Variable p_tgt: program. *)
(* Let p_src := SMod.prog md_src. *)
(* Let md_tgt := module2_mi p_tgt (Some mi). *)
(* Hypothesis (MISRC: md_src.(SMod.midx) = mi). *)
(* Variable skenv_link: SkEnv.t. *)
(* Hypothesis (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function p_tgt)). *)
(* Let ms_src := md_src skenv_link. *)
(* Let ms_tgt := md_tgt skenv_link. *)

(* Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function p_tgt). *)
(* Let ge: genv := Build_genv (SkEnv.revive (skenv) p_tgt) p_tgt.(prog_comp_env). *)
(* Hypothesis SK: (SMod.sk) md_src = (Mod.sk) md_tgt. *)





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Let fr_src := itree (E unit) (unit * (mem * val)).
Let fr_tgt := Clight.state.

Section MATCH.

Variable skenv_link: SkEnv.t.
Variable ge: genv.

Section FRAME.

(*** guaranteed to return this type ***)
Variable rty: type.

Inductive _match_fr (match_fr: fr_src -> fr_tgt -> Prop): fr_src -> fr_tgt -> Prop :=
| match_fr_ret
    oh0 m0 v0
    (TYP: Cop.val_casted v0 rty)
  :
    _match_fr match_fr (Ret (oh0, (m0, v0))) (Returnstate v0 Kbot m0)
| match_fr_tau
    st_src0 st_tgt0 st_tgt1
    (SIM: match_fr st_src0 st_tgt1)
    (TGT: plus step2 skenv_link ge st_tgt0 E0 st_tgt1)
  :
    _match_fr match_fr (tau;; st_src0) (st_tgt0)
| match_fr_icall
    fname oh0 m0 vs0
    fblk ty fd
    (SYMB: Genv.find_symbol ge fname = Some fblk)
    (FINDF: Genv.find_funct ge (Vptr fblk Ptrofs.zero) = Some (Ctypes.Internal fd))
    (TY: type_of_fundef (Ctypes.Internal fd) = ty)
    (TYP: typecheck vs0 (signature_of_function fd) vs0)
    (DEF: Forall (fun v => v <> Vundef) vs0)
    (* (CANSTEP: exists e le m1, function_entry2 ge fd vs0 m0 e le m1) *)
    k_src
    oid e le k
    (AFTER: forall
        oh1 m1 v1
        (TYP: Cop.val_casted v1 (fn_return fd))
      ,
        match_fr (k_src (oh1, (m1, v1)))
                 (State fd Sskip k e (set_opttemp oid v1 le) m1))
  :
    _match_fr match_fr
              (Vis (subevent _ (ICall fname oh0 m0 vs0)) k_src)
              (Callstate (Vptr fblk Ptrofs.zero) ty vs0 (Kcall oid fd e le k) m0)
  (* | step_call : forall (f : function) (optid : option ident) (a : expr) (al : list expr)  *)
  (*                 (k : cont) (e : env) (le : temp_env) (m : mem) (tyargs : typelist)  *)
  (*                 (tyres : type) (cconv : calling_convention) (vf : val) (vargs : list val), *)
  (*               Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cconv -> *)
  (*               eval_expr ge e le m a vf -> *)
  (*               eval_exprlist ge e le m al tyargs vargs -> *)
  (*               Coqlib.DUMMY_PROP -> *)
  (*               Coqlib.DUMMY_PROP -> *)
  (*               step se ge function_entry (State f (Scall optid a al) k e le m) E0 *)
  (*                 (Callstate vf (Tfunction tyargs tyres cconv) vargs (Kcall optid f e le k) m) *)
  (*               step se ge function_entry (Returnstate v (Kcall optid f e le k) m) E0 *)
  (*                 (State f Sskip k e (set_opttemp optid v le) m) *)
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
                      /\ Some sg = Sk.get_csig skd)
    oid f e le k
    (AFTER: forall oh1 m1 v1,
        match_fr (k_src (oh1, (m1, v1)))
                 (State f Sskip k e (set_opttemp oid v1 le) m1))
  :
    _match_fr match_fr
              (Vis (subevent _ (ECall sg fptr oh0 m0 vs0)) k_src)
              (Callstate fptr (Tfunction targs tres cconv) vs0 (Kcall oid f e le k) m0)
.

Definition match_fr: _ -> _ -> Prop := paco2 _match_fr bot2.
Lemma match_fr_mon: monotone2 _match_fr.
Proof.
  ii. destruct IN; try (by econs; et; rr; et).
Qed.

End FRAME.

(* Definition get_call_cont_ty (ktl: cont): type := *)
(*   match ktl with *)
(*   | Kcall _ fd _ _ _ => (fn_return fd) *)
(*   | _ => Tvoid *)
(*   end *)
(* . *)

(*** assuming this type ***)
Inductive match_stack (ety: type): list ktr -> cont -> Prop :=
| match_stack_nil
  :
    match_stack ety [] Kstop
| match_stack_cons
    hd tl
    oid fd e te khd ktl rty
    (TL: match_stack rty tl ktl)
    (HD: forall
        oh0 m0 r0
        (TYP: Cop.val_casted r0 ety)
      ,
        match_fr rty (hd (oh0, (m0, r0)))
                 (State fd Sskip khd e (set_opttemp oid r0 te) m0))
  :
    match_stack ety (hd :: tl) (Kcall oid fd e te (app_cont khd ktl))
.

Lemma match_stack_is_call_cont
      ety stk_src k_tgt
      (MATCH: match_stack ety stk_src k_tgt)
  :
    <<CALL: is_call_cont k_tgt>>
.
Proof.
  induction MATCH; ii; ss.
Qed.

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

Inductive match_states: SIRStack.state unit -> state -> Prop :=
| match_states_intro
    cur_src cont_src
    st0
    khd ktl rty
    (CUR: match_fr rty cur_src (set_cont st0 khd))
    (CONT: match_stack rty cont_src ktl)
    (STCONT: get_cont st0 = app_cont khd ktl)
  :
    match_states (mk cur_src cont_src) st0
.

Inductive match_func: SIRCommon.function unit -> function -> Prop :=
| match_func_intro
    kt fd
    (SIM: forall
        oh0 m0 vs0
        (TYP: typecheck vs0 (signature_of_function fd) vs0)
        (DEF: Forall (fun v => v <> Vundef) vs0)
      ,
        exists e le m1, (<<ENTRY: function_entry2 ge fd vs0 m0 e le m1>>) /\
                        (<<SIM: match_fr fd.(fn_return) (kt oh0 m0 vs0)
                                                        (State fd fd.(fn_body) Kbot e le m1)>>))
  :
    match_func kt fd
.

End MATCH.
Hint Unfold match_fr.
Hint Resolve match_fr_mon: paco.





Notation "'geof'" :=
  (fun skenv_link p_tgt =>
     Build_genv (SkEnv.revive ((SkEnv.project skenv_link)
                                 (CSk.of_program signature_of_function p_tgt)) p_tgt)
                (p_tgt.(prog_comp_env))) (at level 50).

Inductive match_prog: (SIRCommon.program unit) -> program -> Prop :=
| match_prog_intro
    (p_src: (SIRCommon.program unit)) (p_tgt: program)
    (PROG: forall
        (id: ident)
      ,
        (<<SAME: is_some (p_src id) = (internal_funs p_tgt id)>>))
    (SIM: forall
        (id: ident)
        skenv_link
        (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function p_tgt))
        f_src f_tgt
        (SRC: p_src id = Some f_src)
        (TGT: ((prog_defmap (program_of_program p_tgt)) ! id) = Some (Gfun (Internal f_tgt)))
      ,
        <<SIM: match_func skenv_link (geof skenv_link p_tgt) f_src f_tgt>>)
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











Section SIMMODSEM.

Variable md_src: SMod.t unit.
Let mi := md_src.(SMod.midx).
Variable p_tgt: program.
Let p_src := SMod.prog md_src.
Let md_tgt := module2_mi p_tgt (Some mi).
Variable skenv_link: SkEnv.t.
Hypothesis (INCL: SkEnv.includes skenv_link (CSk.of_program signature_of_function p_tgt)).
Let ms_src := md_src skenv_link.
Let ms_tgt := md_tgt skenv_link.

Let skenv: SkEnv.t := (SkEnv.project skenv_link) (CSk.of_program signature_of_function p_tgt).
Let ge: genv := Build_genv (SkEnv.revive (skenv) p_tgt) p_tgt.(prog_comp_env).
Hypothesis SK: (SMod.sk) md_src = (Mod.sk) md_tgt.

Let match_states := match_states skenv_link ge.

Lemma find_defmap
      fid fblk fd
      (SYMB: Genv.find_symbol (SkEnv.revive skenv p_tgt) fid = Some fblk)
      (FINDF: Genv.find_funct_ptr (SkEnv.revive skenv p_tgt) fblk = Some (Internal fd))
  :
    <<DEFMAP: (prog_defmap p_tgt) ! fid = Some (Gfun (Internal fd))>>
.
Proof.
  exploit (SkEnv.project_impl_spec); try apply INCL. intro SPEC.
  exploit CSkEnv.project_revive_precise; et. intro T. inv T.
  exploit SYMB2P; et. intro U. dup U. unfold NW, defs in U0. des_sumbool.
  exploit prog_defmap_dom; et. intro V; des.
  exploit P2GE; et. intro W; des.
  folder.
  assert(fblk = b).
  { clear - SPEC SYMB SYMB0 U. (*** TODO: this is too extensional ***) uge. ss. clarify. }
  clarify.
  unfold Genv.find_funct_ptr in *. unfold Clight.fundef in *. rewrite DEF in *. des_ifs.
Qed.

Lemma external_bsim
      fptr
      (EXTERNAL: Genv.find_funct (SkEnv.revive skenv p_tgt) fptr = None)
      skd
      (SIG: Genv.find_funct skenv_link fptr = Some skd)
  :
    <<EXTERNAL: Genv.find_funct (SkEnv.project skenv_link (SMod.sk md_src)) fptr = None>>
.
Proof.
  rewrite SK in *. folder.
  unfold SkEnv.revive in *. uge. ss. des_ifs_safe.
  rewrite PTree_filter_map_spec in *. des_ifs.
  + uo. des_ifs_safe.
    rewrite PTree_filter_map_spec in *. uo. des_ifs. clear_tac.
    generalize (CSk.of_program_prog_defmap p_tgt signature_of_function i); intro T.
    assert(i0 = i).
    { clear - Heq3 Heq5. subst_locals. apply_all_once Genv.invert_find_symbol. uge. ss.
      rewrite PTree_filter_key_spec in *. des_ifs.
      eapply Genv.genv_vars_inj; et. } subst.
    rewrite Heq6 in *. rewrite Heq2 in *. inv T. inv H1.
  + uo. des_ifs_safe.
    rewrite PTree_filter_map_spec in *. uo. des_ifs_safe. clear_tac.
    assert(Genv.invert_symbol skenv b = Some i).
    { clear - Heq2 Heq Heq0. subst_locals. apply_all_once Genv.invert_find_symbol.
      apply Genv.find_invert_symbol. uge. ss.
      rewrite PTree_filter_key_spec in *. des_ifs.
      unfold defs in *. des_sumbool. contradict Heq1. eapply prog_defmap_image; et.
    }
    des_ifs. clear_tac.
    generalize (CSk.of_program_prog_defmap p_tgt signature_of_function i); intro T.
    rewrite Heq5 in *. rewrite Heq2 in *. inv T.
Qed.



Let SMO := SimMemOh_default_aux _ (Some mi).
Local Existing Instance SMO.

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

Ltac inv H := inversion H; clear H; substs.

Hypothesis (SIMP: match_prog p_src p_tgt).

Lemma match_states_lxsim
      st_src0 st_tgt0 smo0
      (WF: SimMem.wf smo0)
      (MATCH: match_states st_src0 st_tgt0)
  :
    <<XSIM: lxsim ms_src ms_tgt 
                  (fun _ => () -> exists (_ : ()) (_ : mem), True)
                  (Ord.lift_idx lt_wf 42%nat) st_src0 st_tgt0 smo0>>
.
Proof.
  revert_until SIMP.
  pcofix CIH. i. pfold.
  ii. clear SUSTAR.
  inv MATCH.
  punfold CUR. inv CUR.
  - (* return *)
    ss. destruct st_tgt0; ss. clarify. substs.
    inv CONT.
    + econs 4; ss; cycle 1.
      { instantiate (1:= SimMemId.mk _ _); ss. }
      * rr. esplits; ss; et. econs; ss.
      * et.
    + econs 1. ii. econs 1; swap 2 3.
      { split; intro T; rr in T; des; ss; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. inv STEPSRC; ss; csc.
      esplits; et.
      * left. eapply ModSemProps.spread_dplus.
        { eapply modsem2_mi_determinate; et. }
        eapply plus_one. econs; ss; et.
      * right. eapply CIH.
        { instantiate (1:= SimMemId.mk _ _); ss. }
        econs; ss; et.
  - (* tau/plus *)
    pclearbot.
    + ss. econs 1. ii. econs 1; swap 2 3.
      { split; intro T; rr in T; des; ss; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. inv STEPSRC; ss. clarify. substs.
      esplits; et.
      * left. eapply ModSemProps.spread_dplus.
        { eapply modsem2_mi_determinate; et. }
        ss; et.
        replace st_tgt0 with (app_cont_state (set_cont st_tgt0 khd) ktl); cycle 1.
        { (*** TODO: make lemma ***) clear - STCONT. destruct st_tgt0; ss; clarify. }
        eapply plus_plus; et.
        eapply match_stack_is_call_cont; et.
      * right. eapply CIH.
        { instantiate (1:= SimMemId.mk _ _); ss. }
        econs; ss; et.
        { rr. instantiate (1:= get_cont st_tgt2).
          replace (set_cont (app_cont_state st_tgt2 ktl) (get_cont st_tgt2)) with st_tgt2; cycle 1.
          { (*** TODO: make lemma ***) clear - st_tgt2. destruct st_tgt2; ss. }
          ss.
        }
        { (*** TODO: make lemma ***) clear - st_tgt2. destruct st_tgt2; ss. }
  - (* icall *)
    pclearbot.
    destruct st_tgt0; ss. csc. des_ifs. des. clear_tac.
    + ss. econs 1. ii. econs 1; swap 2 3.
      { split; intro T; rr in T; des; ss; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. inv STEPSRC; ss. clarify. simpl_depind. substs. clear_tac.

      fold p_src. 
      assert(T: (prog_defmap p_tgt) ! fid = Some (Gfun (Internal fd))).
      { eapply find_defmap; et. }
      des_ifs; cycle 1.
      { (*** TODO: make lemma ***)
        exfalso. clear - T SYMB SIMP Heq.
        inv SIMP. spc PROG. rewrite Heq in *. ss. unfold internal_funs in *. rewrite T in *. ss.
      }
      inv SIMP.
      exploit (SIM fid skenv_link); et. intro U. folder. inv U.
      hexploit (SIM0 tt m0 vs0); et. i; des.
      esplits; et.
      * left. eapply ModSemProps.spread_dplus.
        { eapply modsem2_mi_determinate; et. }
        ss; et.
        apply plus_one.
        econs; ss; et.
      * right. eapply CIH.
        { instantiate (1:= SimMemId.mk _ _); ss. }
        econs; ss; et; ss.
        econs; ss; et. 
        { ii. exploit AFTER; et. intro U. pclearbot. et. }
  - (* ub *)
    + ss. econs 1. ii. econs 1; swap 2 3.
      { split; intro T; rr in T; des; ss; inv T; ss. }
      { eapply modsem_receptive; et. }
      ii. inv STEPSRC; ss.
  - (* ecall *)
    pclearbot.
    des. ss. destruct st_tgt0; ss. clarify. csc.
    econs 3; ss.
    { rr. esplits; ss. econs; ss; et.
      - eapply external_bsim; et.
      - esplits; et. (*** TODO: make lemma ***) unfold Sk.get_csig in *. des_ifs.
    }
    ii. des_u. inv ATSRC; ss. csc. clear_tac. substs.
    eexists _, _, (SimMemId.mk m0 m0). esplits; ss; et.
    + rr. esplits; ss; et. econs; ss; et.
    + econs; ss; et.
    + ii. inv AFTERSRC. ss. clarify. rr in SIMRETV. des. ss. clear_tac.
      inv SIMRETV0; ss. clarify. substs. destruct smo_ret; ss. substs.
      inv GETK. ss. csc. substs.
      eexists _, _, (Ord.lift_idx lt_wf 43%nat).
      esplits; et.
      * econs; ss; et.
      * left. pfold.
        ss. econs 1. ii. econs 2; ss; et.
        { split.
          { eapply ModSemProps.spread_dplus.
            { eapply modsem2_mi_determinate; et. }
            apply plus_one. econs; ss; et.
          }
          eapply Ord.lift_idx_spec. instantiate (1:= 42%nat). xomega.
        }
        right. eapply CIH.
        { instantiate (1:= SimMemId.mk _ _); ss. }
        econs; ss; et.
        assert(U: (proj_sig_res (signature_of_type targs tres cconv)) = (typ_of_type tres)).
        { (*** TODO: make lemma ***)
          clear - tres. destruct tres; ss.
        }
        rewrite U. ss.
Unshelve.
  all: ss.
  all: try (by apply Mem.empty).
Qed.

Variable sm_link: SimMem.t.
Definition msp: ModSemPair.t := ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link)
                                              (SimSymbId.mk md_src md_tgt) sm_link _.
Theorem sim_modsem: ModSemPair.sim msp.
Proof.
  econstructor 1 with (sidx := unit) (sound_states := top4); eauto;
    try apply SoundTop.sound_state_local_preservation; et; try (by ii; ss).
  { ii. eapply Preservation.local_preservation_noguarantee_weak.
    apply SoundTop.sound_state_local_preservation; et.
  }
  { ii. ss. destruct sm; ss. substs. eexists (SimMemId.mk _ _); ss. esplits; eauto.
    destruct (SMod.initial_owned_heap md_src skenv_link) eqn:T. ss. }
  ii. ss. esplits; eauto.
  - ii. des. inv INITTGT. inv SAFESRC. ss. des_ifs_safe.
    rr in SIMARGS. des. inv SIMARGS0; ss. substs. clarify. clear_tac. inv MWF. ss. destruct sm_arg; ss.
    substs. des_ifs. clear_tac. substs.
    rename tgt into m0. rename vs_tgt into vs0.
    folder. rewrite SK in *. folder.
    dup SIMP. inv SIMP0.
    spc PROG. des.
    assert(T: internal_funs p_tgt fid).
    { unfold Genv.find_funct_ptr, Genv.find_funct in *. des_ifs. substs.
      clear - Heq Heq0 SYMB INCL.
      exploit SkEnv.project_impl_spec; et. intro SPEC. folder.
      exploit CSkEnv.project_revive_precise; et. intro T.
      inv T.
      exploit GE2P; et. i; des. ss.
      assert(id = fid).
      { (*** TODO: strengthen revive spec ***)
        clear - SYMB SYMB0. unfold SkEnv.revive in *. uge. ss.
        rewrite PTree_filter_key_spec in *. des_ifs.
        eapply Genv.genv_vars_inj; et. }
      clarify.
      unfold internal_funs. des_ifs. }
    rewrite T in *. unfold is_some in PROG. des_ifs. substs. unfold internal_funs in *. des_ifs. substs.
    assert(f1 = fd).
    { exploit find_defmap; et. intro U. rewrite U in *. clarify. }
    substs. clear_tac.
    assert(sg_init_tgt = (signature_of_function fd)).
    {
      (*** TODO: make lemma ***)
      clear - FINDF FINDF0.
      unfold SkEnv.revive in *. uge. ss. des_ifs_safe.
      rewrite ! PTree_filter_map_spec in *. uo. des_ifs.
      assert(i = i0).
      { apply_all_once Genv.invert_find_symbol. subst skenv.
        uge. ss. rewrite PTree_filter_key_spec in *. des_ifs.
        eapply Genv.genv_vars_inj; et.
      } subst.
      exploit CSk.of_program_prog_defmap; et. intro T. rewrite Heq4 in *.
      inv T; ss. inv H1. r in H4. des_ifs. rewrite <- H in *. clarify.
    }
    substs.
    assert(tvs = vs0).
    { clear - TYP TYP0.
      (*** TODO: make determ lemma ***)
      inv TYP. inv TYP0. ss.
    }
    exploit (SIM fid skenv_link); et. intro SIMF. inv SIMF. folder.
    hexploit (SIM0 tt m0 vs0); et. intro T. des.

    eexists _, _, (Ord.lift_idx lt_wf 43%nat).
    esplits; et.
    + econs; ss; et.
    + des_ifs.
      pfold. econs 1. econs 2; ss; et.
      { esplits; et.
        - eapply ModSemProps.spread_dplus.
          { eapply modsem2_mi_determinate; et. }
          eapply plus_one. econs; ss; et.
        - eapply Ord.lift_idx_spec; et. }
      left.
      eapply match_states_lxsim; et.
      { instantiate (1:=SimMemId.mk m0 m0). ss. }
      econs; ss; et; cycle 1.
  - i; des. inv SAFESRC. ss. des_ifs.
    rr in SIMARGS. des. ss. clarify. clear_tac. inv SIMARGS0; ss. substs.
    assert(fd = sg_init_tgt).
    { (*** TODO: make lemma ***)
      clear - SK FINDFTGT FINDF. uge. des_ifs. ss. rewrite PTree_filter_map_spec in *. uo. des_ifs.
      rewrite SK in *. clarify. }
    substs. ss. des_ifs. substs.
    assert(CFINDF: exists fd_tgt,
             Genv.find_funct_ptr
               (SkEnv.revive
                  (SkEnv.project skenv_link (CSk.of_program signature_of_function p_tgt)) p_tgt) blk =
             Some (Internal fd_tgt) /\ (signature_of_function fd_tgt) = sg_init_src).
    { (*** TODO: make lemma ***)
      clear - FINDF FINDFTGT SYMB SK.
      rewrite SK in *. ss. des_ifs.
      unfold Genv.find_funct_ptr in *. des_ifs_safe. clear_tac.
      uge. ss. rewrite ! PTree_filter_map_spec in *. rewrite ! PTree_filter_key_spec in *.
      uo. des_ifs_safe.
      assert(DEFS: defs (CSk.of_program signature_of_function p_tgt) i).
      { unfold defs. des_sumbool. eapply prog_defmap_image; et. }
      assert(Genv.invert_symbol
               (SkEnv.project skenv_link (CSk.of_program signature_of_function p_tgt)) blk = Some i).
      { apply Genv.find_invert_symbol. apply_all_once Genv.invert_find_symbol.
        uge. ss. rewrite ! PTree_filter_key_spec in *. des_ifs. }
      des_ifs_safe.
      exploit CSk.of_program_prog_defmap; et. intro T. rewrite Heq3 in *.
      inv T; ss. inv H1. r in H4. des_ifs. et. }
    des. substs.
    esplits; et. econs; ss; et.
Unshelve.
  all: ss.
Qed.

End SIMMODSEM.

End OWNEDHEAP.







Section SIMMOD.

Variable md_src: SMod.t unit.
Let mi := md_src.(SMod.midx).
Variable p_tgt: program.
Let p_src := SMod.prog md_src.
Let md_tgt := module2_mi p_tgt (Some mi).
Hypothesis SK: (SMod.sk) md_src = (Mod.sk) md_tgt.

Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

Hypothesis (SIMP: match_prog p_src p_tgt).

Theorem sim_mod: ModPair.sim mp.
Proof.
  econs; ss.
  - ii. inv SIMSKENVLINK. eexists. eapply sim_modsem; eauto.
Qed.

Theorem correct: rusc defaultR [md_src: Mod.t] [md_tgt: Mod.t].
Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

End SIMMOD.
