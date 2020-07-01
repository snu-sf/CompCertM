Require Import CoqlibC.
Require Import Memory.
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

Require Import Sem ModSem Any.

Set Implicit Arguments.




(* ownership *)
Inductive ownership: Type :=
| privmod (mi: string)
| etc
.

Definition is_privmod (ons: ownership) (mi: Midx.t): bool :=
  match mi with
  | Some mi =>
    match ons with
    | privmod mj => string_dec mi mj
    | _ => false
    end
  | _ => false
  end
.

Notation partition := (block -> Z -> ownership).

Definition privmods (mi: Midx.t) (ptt: partition): block -> Z -> bool :=
  fun b ofs =>
    match mi with
    | Some mi =>
      match (ptt b ofs) with
      | privmod mj => (string_dec mi mj)
      | _ => false
      end
    | _ => false
    end
.

Definition privmod_others (mi: Midx.t) (ptt: partition): block -> Z -> bool :=
  fun b ofs =>
    match (ptt b ofs) with
    | privmod mj =>
      match mi with
      | Some mi => negb (string_dec mi mj)
      | _ => true
      end
    | _ => false
    end
.

Definition ons_mem (ptt: partition) (ons: ownership): block -> Z -> Prop :=
  fun b ofs => (ptt b ofs) = ons
.

Hint Unfold ons_mem privmods privmod_others.

Lemma ons_mem_privmods
      ptt mi
  :
    ons_mem ptt (privmod mi) = privmods (Some mi) ptt
.
Proof.
  u. apply func_ext2. ii. apply AxiomsC.prop_ext. split; i; des_ifs; des_sumbool; clarify; ss.
Qed.

Module SimMem.

  Class class :=
  { t: Type;
    src: t -> mem;
    ptt_src: t -> partition;
    tgt: t -> mem;
    ptt_tgt: t -> partition;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;

    le_PreOrder :> PreOrder le;
    lepriv_PreOrder :> PreOrder lepriv;

    pub_priv: forall sm0 sm1, le sm0 sm1 -> lepriv sm0 sm1;

    sim_val: t -> val -> val -> Prop;
    sim_val_list: t -> list val -> list val -> Prop;
    le_sim_val: forall mrel0 mrel1 (MLE: le mrel0 mrel1), sim_val mrel0 <2= sim_val mrel1;
    sim_val_list_spec: forall sm0, (List.Forall2 sm0.(sim_val) = sm0.(sim_val_list));
    sim_val_int: forall sm0 v_src v_tgt, sim_val sm0 v_src v_tgt -> forall i, v_src = Vint i -> v_tgt = Vint i;

    (* Note: SimMemId/Ext does not satisfiy Mem.unchanged_on, because of NB (nextblock) *)
    (* Ideally, I would like to obligate NB thing in SimMemId/SimMemExt proof too,
       but Xavier might not accept it*)
    unchanged_on (P: block -> Z -> Prop) (m0 m1: mem): Prop;
    unchanged_on_PreOrder P:> PreOrder (unchanged_on P);
    unchanged_on_monotone: forall
        P0 P1
        (INCL: P1 <2= P0)
      ,
        <<INCL: unchanged_on P0 <2= unchanged_on P1>>;
  }.

  Inductive unch `{SM: class} (mi: Midx.t) (sm0 sm1: t): Prop :=
  | unch_intro
      (UNCHSRC: unchanged_on (privmod_others mi sm0.(ptt_src)) sm0.(src) sm1.(src))
      (UNCHTGT: unchanged_on (privmod_others mi sm0.(ptt_tgt)) sm0.(tgt) sm1.(tgt))
      (LESRC: forall mj (NEQ: mi <> mj),
          (privmods mj sm0.(ptt_src)) <2= (privmods mj sm1.(ptt_src)))
      (LETGT: forall mj (NEQ: mi <> mj),
          (privmods mj sm0.(ptt_tgt)) <2= (privmods mj sm1.(ptt_tgt)))
  .

  Global Program Instance unch_PreOrder `{SM: class} (mi: Midx.t): PreOrder (unch mi).
  Next Obligation.
    ii. econs; eauto; try refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; eauto; try etrans; et.
    - eapply unchanged_on_monotone; et. intros b ofs ?.
      unfold privmod_others in PR. des_ifs; ss; cycle 1.
      + hexploit (LESRC (Some mi0)); et. { congruence. } intro U. specialize (U b ofs); ss.
        unfold privmod_others.
        des_ifs. eapply U. des_sumbool. ss.
      + des_sumbool. (**** TODO: fix tactic ****)
        unfold is_true in PR. simpl_bool. des_sumbool.
        hexploit (LESRC (Some mi0)); et. { congruence. } intro U. specialize (U b ofs); ss.
        hexploit (LESRC0 (Some mi0)); et. { congruence. } intro V. specialize (V b ofs); ss.
        clear - PR U V Heq.
        unfold privmods, privmod_others in *. des_ifs_safe.
        exploit U; et. { des_sumbool; ss. } intro W; des_ifs_safe. des_sumbool. clarify.
        simpl_bool. des_sumbool. ii. clarify.
    - eapply unchanged_on_monotone; et. intros b ofs ?.
      unfold privmod_others in PR. des_ifs; ss; cycle 1.
      + hexploit (LETGT (Some mi0)); et. { congruence. } intro U. specialize (U b ofs); ss.
        unfold privmod_others.
        des_ifs. eapply U. des_sumbool. ss.
      + des_sumbool. (**** TODO: fix tactic ****)
        unfold is_true in PR. simpl_bool. des_sumbool.
        hexploit (LETGT (Some mi0)); et. { congruence. } intro U. specialize (U b ofs); ss.
        hexploit (LETGT0 (Some mi0)); et. { congruence. } intro V. specialize (V b ofs); ss.
        clear - PR U V Heq.
        unfold privmods, privmod_others in *. des_ifs_safe.
        exploit U; et. { des_sumbool; ss. } intro W; des_ifs_safe. des_sumbool. clarify.
        simpl_bool. des_sumbool. ii. clarify.
  Qed.

  Lemma sim_val_list_length
        `{SM: class} (sm0: t)
        vs_src vs_tgt
        (SIMVS: sm0.(sim_val_list) vs_src vs_tgt):
      length vs_src = length vs_tgt.
  Proof. rewrite <- sim_val_list_spec in SIMVS. ginduction SIMVS; ii; ss. congruence. Qed.

  Definition sim_block `{SM: class} (sm0: t) (blk_src blk_tgt: block): Prop :=
    sm0.(sim_val) (Vptr blk_src Ptrofs.zero) (Vptr blk_tgt Ptrofs.zero).

  Definition future `{SM: class}: t -> t -> Prop := rtc (lepriv \2/ le).


  Definition sim_regset `{SM: class} (sm0: SimMem.t) (rs_src rs_tgt: Asm.regset): Prop := forall pr, sm0.(sim_val) (rs_src pr) (rs_tgt pr).

  Inductive sim_args `{SM: class} (args_src args_tgt: Args.t) (sm0: SimMem.t): Prop :=
  | sim_args_Cstyle
      fptr_src vs_src m_src fptr_tgt vs_tgt m_tgt
      (CSRC: args_src = Args.Cstyle fptr_src vs_src m_src)
      (CTGT: args_tgt = Args.Cstyle fptr_tgt vs_tgt m_tgt)
      (FPTR: sm0.(SimMem.sim_val) fptr_src fptr_tgt)
      (VALS: sm0.(SimMem.sim_val_list) vs_src vs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt))
  | sim_args_Asmstyle
      rs_src m_src rs_tgt m_tgt
      (ASMSRC: args_src = Args.Asmstyle rs_src m_src)
      (ASMTGT: args_tgt = Args.Asmstyle rs_tgt m_tgt)
      (RS: (sim_regset sm0) rs_src rs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt)).

  Inductive sim_retv `{SM: class} (retv_src retv_tgt: Retv.t) (sm0: SimMem.t): Prop :=
  | sim_retv_Cstyle
      v_src m_src v_tgt m_tgt
      (CSRC: retv_src = Retv.Cstyle v_src m_src)
      (CTGT: retv_tgt = Retv.Cstyle v_tgt m_tgt)
      (RETV: sm0.(SimMem.sim_val) v_src v_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt))
  | sim_retv_Asmstyle
      rs_src m_src rs_tgt m_tgt
      (ASMSRC: retv_src = Retv.Asmstyle rs_src m_src)
      (ASMTGT: retv_tgt = Retv.Asmstyle rs_tgt m_tgt)
      (RS: (sim_regset sm0) rs_src rs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt)).

  Lemma sim_args_sim_fptr `{SM: class}: forall sm0 args_src args_tgt (ARGS: sim_args args_src args_tgt sm0),
      sm0.(sim_val) (Args.get_fptr args_src) (Args.get_fptr args_tgt).
  Proof. i. inv ARGS; ss. Qed.

  Lemma sim_val_list_le
        `{SM: class}
        sm0 sm1 vs_src vs_tgt
        (LEPRIV: SimMem.le sm0 sm1)
        (SIMVS: SimMem.sim_val_list sm0 vs_src vs_tgt):
      <<SIMVS: SimMem.sim_val_list sm1 vs_src vs_tgt>>.
  Proof.
    rewrite <- sim_val_list_spec in *. induction SIMVS; ii; ss.
    econs; eauto. eapply le_sim_val; et.
  Qed.

  Lemma unch_implies
        `{SimMem.class}
        mi
    :
      <<IMPL: SimMem.unch None <2= SimMem.unch mi>>
  .
  Proof.
    ii. inv PR. econs; et.
    { eapply unchanged_on_monotone; et. u. ii. des_ifs. }
    { eapply unchanged_on_monotone; et. u. ii. des_ifs. }
    { ii. destruct mj; try (by ss). exploit LESRC; et. ss. }
    { ii. destruct mj; try (by ss). exploit LETGT; et. ss. }
  Qed.

End SimMem.

Hint Unfold SimMem.future.
Hint Resolve SimMem.pub_priv.


Module SimMemOh.
Section SimMemOh.

  (* Context {SM: SimMem.class}. *)
  (* Variable owned_heap_src owned_heap_tgt: Type. *)

  Local Open Scope signature_scope.
  Class class {SM: SimMem.class} :=
  {
    t: Type;
    sm:> t -> SimMem.t;
    oh_src: t -> Any;
    oh_tgt: t -> Any;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;
    midx: Midx.t;

    le_PreOrder :> PreOrder le;
    lepriv_PreOrder :> PreOrder lepriv;

    pub_priv: forall smo0 smo1, le smo0 smo1 -> lepriv smo0 smo1;

    wf_proj: wf <1= SimMem.wf <*> sm;
    le_proj: (le ==> SimMem.le) sm sm; (* TODO: better style? *)
    lepriv_proj: (lepriv ==> SimMem.lepriv) sm sm; (* TODO: better style? *)
    (* set_sm_spec: forall smo0, sm <*> (set_sm smo0) = id; *)

    set_sm: t -> SimMem.t -> t;
    (* set_sm_le: forall smo0 sm1, SimMem.le smo0.(sm) sm1 -> *)
    (*                             le smo0 (set_sm smo0 sm1); *)
    (* set_sm_lepriv: forall smo0 sm1, SimMem.lepriv smo0.(sm) sm1 -> *)
    (*                                 lepriv smo0 (set_sm smo0 sm1); *)
    (* can we state it nicely? adjoint? *)

    set_sm_le: forall
      sm0 sm1 smo0 smo1
      (MLE: SimMem.le sm0 sm1)
      (MLE: le smo0 smo1)
    ,
      <<MLE: le (set_sm smo0 sm0) (set_sm smo1 sm1)>>;
    set_sm_lepriv: forall
      sm0 sm1 smo0 smo1
      (MLE: SimMem.lepriv sm0 sm1)
      (MLE: lepriv smo0 smo1)
    ,
      <<MLE: lepriv (set_sm smo0 sm0) (set_sm smo1 sm1)>>;
    set_sm_wf: forall
        smo0 sm1
        (WF: wf smo0)
        (WF: SimMem.wf sm1)
        (MLEPRIV: SimMem.lepriv smo0.(sm) sm1)
        (UNCHSRC: SimMem.unchanged_on (privmods midx smo0.(sm).(SimMem.ptt_src))
                                      smo0.(sm).(SimMem.src) sm1.(SimMem.src))
        (UNCHTGT: SimMem.unchanged_on (privmods midx smo0.(sm).(SimMem.ptt_tgt))
                                      smo0.(sm).(SimMem.tgt) sm1.(SimMem.tgt))
        (PMSRC: (privmods midx smo0.(sm).(SimMem.ptt_src)) <2= (privmods midx sm1.(SimMem.ptt_src)))
        (PMTGT: (privmods midx smo0.(sm).(SimMem.ptt_tgt)) <2= (privmods midx sm1.(SimMem.ptt_tgt)))
      ,
        <<WF: wf (set_sm smo0 sm1)>>;

    getset_sm: forall smo0 sm1, (set_sm smo0 sm1).(sm) = sm1;
    setget_sm: forall smo0, (set_sm smo0 smo0.(sm)) = smo0;
    setset_sm: forall smo0 sm0 sm1, (set_sm (set_sm smo0 sm0) sm1) = (set_sm smo0 sm1);
    set_sm_oh_src: forall smo0 sm0, oh_src (set_sm smo0 sm0) = oh_src smo0;
    set_sm_oh_tgt: forall smo0 sm0, oh_tgt (set_sm smo0 sm0) = oh_tgt smo0;

    midx_none: midx = None -> t = SimMem.t /\ JMeq.JMeq sm (@id SimMem.t);
  }.

  Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t.

  Definition sim_args `{SMO: class} (oh_src: Any) (oh_tgt: Any)
             (args_src args_tgt: Args.t) (smo0: SimMemOh.t): Prop :=
    (<<SIMARGS: SimMem.sim_args args_src args_tgt smo0>>) /\
    (<<OHSRC: oh_src = smo0.(SimMemOh.oh_src)>>) /\ (<<OHTGT: oh_tgt = smo0.(SimMemOh.oh_tgt)>>)
  .

  Definition sim_retv `{SMO: class} (oh_src: Any) (oh_tgt: Any)
             (retv_src retv_tgt: Retv.t) (smo0: SimMemOh.t): Prop :=
    (<<SIMRETV: SimMem.sim_retv retv_src retv_tgt smo0>>) /\
    (<<OHSRC: oh_src = smo0.(SimMemOh.oh_src)>>) /\ (<<OHTGT: oh_tgt = smo0.(SimMemOh.oh_tgt)>>)
  .

End SimMemOh.
End SimMemOh.
Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t.

(* Create HintDb SimMem. *)
Hint Resolve SimMemOh.pub_priv SimMemOh.wf_proj SimMemOh.le_proj SimMemOh.lepriv_proj
     SimMemOh.set_sm_le SimMemOh.set_sm_wf.


Local Obligation Tactic := try (by econs); try (by ii; ss).

(* Global Program Instance SimMemOh_default (SM: SimMem.class): (SimMemOh.class) | 100 := *)
(*   { *)
(*     sm := fun x => x; *)
(*     oh_src := fun _ => upcast tt; *)
(*     oh_tgt := fun _ => upcast tt; *)
(*     wf := SimMem.wf; *)
(*     le := SimMem.le; *)
(*     lepriv := SimMem.lepriv; *)
(*   } *)
(* . *)
Program Definition SimMemOh_default_aux (SM: SimMem.class) (mi: Midx.t): (SimMemOh.class) :=
  {|
    SimMemOh.sm := fun x => x;
    SimMemOh.oh_src := fun _ => upcast tt;
    SimMemOh.oh_tgt := fun _ => upcast tt;
    SimMemOh.wf := SimMem.wf;
    SimMemOh.le := SimMem.le;
    SimMemOh.lepriv := SimMem.lepriv;
    SimMemOh.midx := mi;
  |}
.
Next Obligation. i. eapply SimMem.pub_priv; eauto. Qed.

Program Definition SimMemOh_default (SM: SimMem.class): (SimMemOh.class) := SimMemOh_default_aux _ None.




Module Simple.
Section SIMPLE.

  Context `{SM: SimMem.class}.
  Variable owned_heap_src owned_heap_tgt: Type.
  Variable sim_oh: owned_heap_src -> owned_heap_tgt -> Prop.
  Variable mi: string.

  Record t: Type :=
    mk {
        sm :> SimMem.t;
        oh_src: owned_heap_src;
        oh_tgt: owned_heap_tgt;
      }
  .

  Inductive wf (smo: t): Prop :=
  | wf_intro
      (MWF: SimMem.wf smo)
      (O: sim_oh smo.(oh_src) smo.(oh_tgt))
  .

  Local Obligation Tactic := try (by ii; des; ss).

  Program Instance class: (SimMemOh.class) :=
    {|
    SimMemOh.t := t;
    SimMemOh.sm := sm;
    (* SimMemOh.oh_src := upcast <*> oh_src; *)
    (* SimMemOh.oh_tgt := upcast <*> oh_tgt; *)
    SimMemOh.oh_src := fun smo => upcast smo.(oh_src);
    SimMemOh.oh_tgt := fun smo => upcast smo.(oh_tgt);
    SimMemOh.wf := wf;
    SimMemOh.le := SimMem.le;
    SimMemOh.lepriv := SimMem.lepriv;
    SimMemOh.midx := Some mi;
    SimMemOh.set_sm := fun smo sm => mk sm smo.(oh_src) smo.(oh_tgt);
    |}
  .
  Next Obligation.
    econs.
    - ii. refl.
    - ii. etrans; et.
  Qed.
  Next Obligation.
    econs.
    - ii. refl.
    - ii. etrans; et.
  Qed.
  Next Obligation.
    ss. ii. eauto.
  Qed.
  Next Obligation.
    ii. inv PR. ss.
  Qed.
  Next Obligation.
    ss. ii. econs; ss. inv WF; ss.
  Qed.
  Next Obligation.
    ss. ii. destruct smo0; ss.
  Qed.

End SIMPLE.
End Simple.

(* Section TEST. *)

(*   Variable A B: Type. *)
(*   Context {SM: SimMem.class}. *)
(*   Context {SMO: SimMemOh.class A B}. *)

(*   Check SimMem.t. *)
(*   Check (SimMemOh.t). *)
(*   Set Printing All. *)
(*   Variable ab: (@SimMemOh.t SM A B SMO). *)
(*   Variable abc: (SimMemOh.t (SM := SM) (owned_heap_src := A) (owned_heap_tgt := B)). *)
(*   Variable abcd: SimMemOh.t. *)
(*   Fail Check abcd: SimMem.t. *)
(*   Check abcd.(SimMemOh.sm): SimMem.t. *)
(*   Print Coercions. *)
(*   Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t. *)
(*   Check abcd: SimMem.t. *)

(* End TEST. *)

Module SimMemOhs.
Section SimMemOhs.

  (* Context {SM: SimMem.class}. *)
  (* Variable owned_heap_src owned_heap_tgt: Type. *)

  Local Open Scope signature_scope.
  Class class {SM: SimMem.class} :=
  {
    t: Type;
    sm:> t -> SimMem.t;
    ohs_src: t -> Ohs;
    ohs_tgt: t -> Ohs;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;

    le_PreOrder :> PreOrder le;
    lepriv_PreOrder :> PreOrder lepriv;

    pub_priv: forall smo0 smo1, le smo0 smo1 -> lepriv smo0 smo1;

    wf_proj: wf <1= SimMem.wf <*> sm;
    le_proj: (le ==> SimMem.le) sm sm; (* TODO: better style? *)
    lepriv_proj: (lepriv ==> SimMem.lepriv) sm sm; (* TODO: better style? *)
  }.

  Coercion SimMemOhs.sm: SimMemOhs.t >-> SimMem.t.

  Require Import Program.

  Definition sim_args `{SMOS: class} (ohs_src: Ohs) (ohs_tgt: Ohs)
             (args_src args_tgt: Args.t) (smo0: SimMemOhs.t): Prop :=
    (<<SIMARGS: SimMem.sim_args args_src args_tgt smo0>>) /\
    (* (<<OHSRC: ohs_src midx ~= projT2 (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx ~= projT2 (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (* (<<OHSRC: nth_error ohs_src midx = (nth_error smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: nth_error ohs_tgt midx = (nth_error smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (* (<<OHSRC: ohs_src midx = (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx = (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (<<OHSRC: ohs_src = (smo0.(SimMemOhs.ohs_src))>>) /\
    (<<OHTGT: ohs_tgt = (smo0.(SimMemOhs.ohs_tgt))>>)
  .

  Definition sim_retv `{SMOS: class} (ohs_src: Ohs) (ohs_tgt: Ohs)
             (retv_src retv_tgt: Retv.t) (smo0: SimMemOhs.t): Prop :=
    (<<SIMRETV: SimMem.sim_retv retv_src retv_tgt smo0>>) /\
    (* (<<OHSRC: ohs_src midx ~= projT2 (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx ~= projT2 (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (* (<<OHSRC: nth_error ohs_src midx = (nth_error smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: nth_error ohs_tgt midx = (nth_error smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (* (<<OHSRC: ohs_src midx = (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx = (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (<<OHSRC: ohs_src = (smo0.(SimMemOhs.ohs_src))>>) /\
    (<<OHTGT: ohs_tgt = (smo0.(SimMemOhs.ohs_tgt))>>)
  .

  Definition unch `{SMOS: class} (mi: Midx.t) (smos0 smos1: t): Prop :=
    forall mj (NEQ: mi <> mj),
      (<<UNCHSRC: SimMemOhs.ohs_src smos0 mj = SimMemOhs.ohs_src smos1 mj>>) /\
      (<<UNCHTGT: SimMemOhs.ohs_tgt smos0 mj = SimMemOhs.ohs_tgt smos1 mj>>)
  .

End SimMemOhs.
End SimMemOhs.

Coercion SimMemOhs.sm: SimMemOhs.t >-> SimMem.t.
Hint Resolve SimMemOhs.pub_priv SimMemOhs.wf_proj SimMemOhs.le_proj SimMemOhs.lepriv_proj.
Hint Unfold SimMemOhs.unch.

