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
Require Import Asmregs.
Require Import Integers.

Require Import Skeleton.
Require Import ModSem.
Require Import Mod.

Set Implicit Arguments.



Module SimMem.

  Class class :=
  {
    t: Type;
    src_mem: t -> mem;
    tgt_mem: t -> mem;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lift: t -> t;
    (* Time order: unlift second arg into first arg. *)
    (* TODO: reorder arg? from->to? *)
    unlift: t -> t -> t;

    le_PreOrder :> PreOrder le;

    (* lift_le: forall mrel, le mrel (lift mrel); *)
    lift_wf: forall mrel, wf mrel -> wf (lift mrel);
    lift_src: forall mrel, (lift mrel).(src_mem) = mrel.(src_mem);
    lift_tgt: forall mrel, (lift mrel).(tgt_mem) = mrel.(tgt_mem);
    unlift_src: forall mrel0 mrel1, (unlift mrel0 mrel1).(src_mem) = mrel1.(src_mem);
    unlift_tgt: forall mrel0 mrel1, (unlift mrel0 mrel1).(tgt_mem) = mrel1.(tgt_mem);
    unlift_spec: forall mrel0 mrel1, le (lift mrel0) mrel1 -> wf mrel0 -> le mrel0 (unlift mrel0 mrel1);
    unlift_wf: forall mrel0 mrel1,
        wf mrel0 -> wf mrel1 -> le (lift mrel0) mrel1 -> wf (unlift mrel0 mrel1);

    sim_val: t -> val -> val -> Prop;
    le_sim_val: forall mrel0 mrel1 (MLE: le mrel0 mrel1), sim_val mrel0 <2= sim_val mrel1;
    lift_sim_val: forall mrel, sim_val mrel <2= sim_val (lift mrel);

  (* val_rel_list: t -> list val -> list val -> Prop; *)
  (* val_rel_list_spec: forall mrel vs0 vs1, val_rel_list mrel vs0 vs1 <-> List.Forall2 (val_rel mrel) vs0 vs1; *)

  (* lift_val_rel_list: forall mrel vs0 vs1, val_rel_list mrel vs0 vs1 -> val_rel_list (lift mrel) vs0 vs1; *)
  (* val_rel_int: forall mrel i v, val_rel mrel (Vint i) v -> v = Vint i; *)




    (* load_respects_ss: forall *)
    (*     ss sk_src sk_tgt *)
    (*     (* (SS: mp.(ModPair.SS) = SS) *) *)
    (*     (CLOSED: SimSymb.closed ss sk_src sk_tgt) *)
    (*     skenv_src skenv_tgt m_src m_tgt *)
    (*     (LOADSRC: sk_src.(Sk.load_skenv) = skenv_src /\ sk_src.(Sk.load_mem) = Some m_src) *)
    (*     (LOADTGT: sk_tgt.(Sk.load_skenv) = skenv_tgt /\ sk_tgt.(Sk.load_mem) = Some m_tgt) *)
    (*   , *)
    (*     exists sm, *)
    (*        (<<SRCM: sm.(src_mem) = m_src>>) /\ *)
    (*        (<<TGTM: sm.(tgt_mem) = m_tgt>>) /\ *)
    (*        (<<SIM: SimSymb.sim_skenv ss skenv_src skenv_tgt>>) *)
    (* ; *)





    (* load_exact_preserved: forall *)
    (*     ss sk_src sk_tgt *)
    (*     (WF: SimSymb.wf ss) *)
    (*     skenv_src skenv_tgt m_src m_tgt *)
    (*     (LOADSRC: skenv_src = sk_src.(Sk.load_skenv) /\ sk_src.(Sk.load_mem) = Some m_src) *)
    (*     (LOADTGT: skenv_tgt = sk_tgt.(Sk.load_skenv) /\ sk_tgt.(Sk.load_mem) = Some m_tgt) *)
    (*   , *)
    (*     exists sm, *)
    (*       (<<SRCM: sm.(src_mem) = m_src>>) /\ *)
    (*       (<<TGTM: sm.(tgt_mem) = m_tgt>>) /\ *)
    (*       (<<SIM: ss.(SimSymb.sim_skenv) skenv_src skenv_tgt>>) *)
    (*       (* (<<EXACT: forall *) *)
    (*       (*     id_src id_tgt b_src b_tgt *) *)
    (*       (*     (SRCFIND: skenv_src.(Genv.find_symbol) id_src = Some b_src) *) *)
    (*       (*     (TGTFIND: skenv_tgt.(Genv.find_symbol) id_tgt = Some b_tgt) *) *)
    (*       (*   , *) *)
    (*       (*     sm.(sim_val) (Vptr b_src Ptrofs.zero true) (Vptr b_tgt Ptrofs.zero true) <-> *) *)
    (*       (*     ss id_src id_tgt>>) *) *)
    (* ; *)
  }
  .

  Definition sim_val_list `{SM: class} (sm0: t) (vs_src vs_tgt: list val): Prop :=
    List.Forall2 sm0.(sim_val) vs_src vs_tgt
  .

  Definition sim_block `{SM: class} (sm0: t) (blk_src blk_tgt: block): Prop :=
    sm0.(sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)
  .

  Definition sim_regset `{SM: class} (sm0: t) (rs_src rs_tgt: regset): Prop :=
    forall pr, sm0.(sim_val) (rs_src pr) (rs_tgt pr)
  .

End SimMem.


(* Program Instance sm_ident: SimMem.class ss_ident := *)
(* { *)
(* } *)


(* Inductive senv_incl (se0 se1: Senv.t): Prop := *)
(* | senv_incl_intro *)
(*     (INCL: forall *)
(*         id b *)
(*         (FIND: se0.(Senv.find_symbol) id = Some b) *)
(*       , *)
(*         <<FIND: se1.(Senv.find_symbol) id = Some b>>) *)
(* . *)

(* Module PLAYGROUND. *)

(*   Definition blockinj := block -> option block. *)

(*   Inductive compat `{SM: SimMem} (sm0: t) (bi0: blockinj) (ms_src: ModSem.t) (ms_tgt: ModSem.t): Prop := *)
(*   | compat_intro *)
(*       (COMPAT: forall *)
(*           b_src b_tgt *)
(*           (INSRC: List.In b_tgt ms_src.(ModSem.internals)) *)
(*           (INTGT: List.In b_src ms_tgt.(ModSem.internals)) *)
(*         , *)
(*           sm0.(sim_val) (Vptr b_src Ptrofs.zero true) (Vptr b_tgt Ptrofs.zero true) <-> *)
(*           bi0 b_src = Some b_tgt) *)
(*   . *)

(*   (* Lemma compat_le *) *)
(*   (*       `{SM: SimMem} *) *)
(*   (*       sm *) *)
(*   (*       bi bi_linked *) *)
(*   (*       (SYMB: True (* BI_INCL *)) *) *)
(*   (*       (******* ############################# SkEnv? GenvLinked? unity with symbinj_linked *) *) *)
(*   (*       se_src skenv_src *) *)
(*   (*       (SENVSRC: senv_incl se_src skenv_src) *) *)
(*   (*       se_tgt skenv_tgt *) *)
(*   (*       (SENVTGT: senv_incl se_tgt skenv_tgt) *) *)
(*   (*       (COMPAT: compat sm bi_linked skenv_src skenv_tgt) *) *)
(*   (*   : *) *)
(*   (*     <<COMPAT: compat sm bi se_src se_tgt>> *) *)
(*   (* . *) *)
(*   (* Proof. *) *)
(*   (*   inv COMPAT. *) *)
(*   (*   econs; eauto. *) *)
(*   (*   i. exploit COMPAT0; eauto. *) *)
(*   (*   { eapply SENVSRC; eauto. } *) *)
(*   (*   { eapply SENVTGT; eauto. } *) *)
(*   (*   i. erewrite H. *) *)
(*   (*   split; i. *) *)
(*   (*   - (* linked$ id is some *) *) *)
(*   (*     rewrite <- H0. *) *)
(*   (*     (* 1) Senv.find_symbol id is Some -> I linked it. should be same. *) *) *)
(*   (*     (* 2) Senv.find_symbol id is None -> I didn't link it. *) *) *)
(*   (*     admit "". *) *)
(*   (*   - eapply SYMB; eauto. *) *)
(*   (* Abort. *) *)


(* End PLAYGROUND. *)



(* (* Fix: My si. My se_src/se_tgt. *) *)
(* Inductive compat `{SM: SimMem} (sm0: t) (si0: symbinj) (se_src: Senv.t) (se_tgt: Senv.t): Prop := *)
(* | compat_intro *)
(*     (COMPAT: forall *)
(*         id_src id_tgt b_src b_tgt *)
(*         (SRCB: se_src.(Senv.find_symbol) id_src = Some b_src) *)
(*         (TGTB: se_tgt.(Senv.find_symbol) id_tgt = Some b_tgt) *)
(*       , *)
(*         sm0.(sim_val) (Vptr b_src Ptrofs.zero true) (Vptr b_tgt Ptrofs.zero true) <-> *)
(*         si0$ id_src = Some id_tgt) *)
(* . *)

(* Lemma compat_le *)
(*       `{SM: SimMem} *)
(*       sm *)
(*       si si_linked *)
(*       (SYMB: symbinj_incl si si_linked) *)
(*       (******* ############################# SkEnv? GenvLinked? unity with symbinj_linked *) *)
(*       se_src skenv_src *)
(*       (SENVSRC: senv_incl se_src skenv_src) *)
(*       se_tgt skenv_tgt *)
(*       (SENVTGT: senv_incl se_tgt skenv_tgt) *)
(*       (COMPAT: compat sm si_linked skenv_src skenv_tgt) *)
(*   : *)
(*     <<COMPAT: compat sm si se_src se_tgt>> *)
(* . *)
(* Proof. *)
(*   inv COMPAT. *)
(*   econs; eauto. *)
(*   i. exploit COMPAT0; eauto. *)
(*   { eapply SENVSRC; eauto. } *)
(*   { eapply SENVTGT; eauto. } *)
(*   i. erewrite H. *)
(*   split; i. *)
(*   - (* linked$ id is some *) *)
(*     rewrite <- H0. *)
(*     (* 1) Senv.find_symbol id is Some -> I linked it. should be same. *) *)
(*     (* 2) Senv.find_symbol id is None -> I didn't link it. *) *)
(*     admit "". *)
(*   - eapply SYMB; eauto. *)
(* Abort. *)

(* Proper migration of below? *)
(* Hint Rewrite lift_src lift_tgt init_src init_tgt : MR. *)
(* Hint Resolve lift_val_rel lift_val_rel_list lift_le lift_valid. *)

(* IDK why but "*" does not work here *)
(* Ltac MR_rewrite0 := *)
(*   repeat multimatch goal with *)
(*   | [H: _ |- _] => try erewrite lift_src in H; *)
(*                    try erewrite lift_tgt in H; *)
(*                    try erewrite init_src in H; *)
(*                    try erewrite init_tgt in H; *)
(*                    try erewrite unlift_src in H; *)
(*                    try erewrite unlift_tgt in H *)
(*          end; *)
(*   try erewrite lift_src; *)
(*   try erewrite lift_tgt; *)
(*   try erewrite unlift_src; *)
(*   try erewrite unlift_tgt; *)
(*   try erewrite init_src; *)
(*   try erewrite init_tgt *)
(* . *)

(* Ltac MR_rewrite := repeat MR_rewrite0. *)

(* Ltac MR_eauto := repeat (try (first [eapply lift_fptr_rel *)
(*                                     |eapply lift_val_rel *)
(*                                     |eapply lift_val_rel_list *)
(*                                     (* |eapply lift_le *) *)
(*                                     |eapply lift_valid *)
(*                                     |eapply unlift_spec]); eauto) *)
(* . *)
