Require Import Events.
Require Import Values.
Require Import AST.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import IntegersC.
Require Import ASTC.
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimSymb.
Require Import SimMem.
Require Import SimMemInjC.
Require Import ModSem.


(* Copied from Unusedglob.v *)
Definition ref_init (il : list init_data) (id : ident): Prop :=
  exists ofs, In (Init_addrof id ofs) il.

Section MEMINJ.

(* Definition t': Type := ident -> bool. *)
Definition t': Type := ident -> Prop.

Inductive sim_sk (ss: t') (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (KEPT: forall id
        (KEPT: ~ ss id),
       sk_tgt.(prog_defmap) ! id = sk_src.(prog_defmap) ! id)
    (DROP: forall id
        (DROP: ss id),
        sk_tgt.(prog_defmap) ! id = None)
    (* (SIMSK: forall *)
    (*     id *)
    (*   , *)
    (*    sk_tgt.(prog_defmap) ! id = if ss id then None else sk_src.(prog_defmap) ! id) *)
    (CLOSED: ss <1= sk_src.(privs))
    (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
    (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
    (NOREF: forall id gv
        (PROG: sk_tgt.(prog_defmap) ! id  = Some (Gvar gv)),
        <<NOREF: forall id_drop (DROP: ss id_drop), ~ ref_init gv.(gvar_init) id_drop>>)
    (NODUP: NoDup (prog_defs_names sk_tgt))
    (NOMAIN: ~ ss sk_src.(prog_main)).

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (SIMSYMB1: forall id blk_src blk_tgt delta
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src),
        (<<DELTA: delta = 0>>) /\
        (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
        (<<KEPT: ~ ss id>>))
    (SIMSYMB2: forall id blk_src
        (KEPT: ~ ss id)
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src),
        exists blk_tgt,
          (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>))
    (SIMSYMB3: forall id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt),
        exists blk_src,
          (<<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>))
    (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    (SIMDEF: forall blk_src blk_tgt delta def_src
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src),
        exists def_tgt, (<<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>))
    (DISJ: forall id blk_src0 blk_src1 blk_tgt
        (SYMBSRC: Genv.find_symbol skenv_src id = Some blk_src0)
        (SIMVAL0: sm0.(SimMemInj.inj) blk_src0 = Some (blk_tgt, 0))
        (SIMVAL1: sm0.(SimMemInj.inj) blk_src1 = Some (blk_tgt, 0)),
        blk_src0 = blk_src1)
    (SIMDEFINV: forall blk_src blk_tgt delta def_tgt
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt),
        exists def_src, (<<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>))
    (PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
    (PUB: skenv_src.(Genv.genv_public) = skenv_tgt.(Genv.genv_public))
    (* NOW BELOW IS DERIVABLE FROM WF *)
    (* (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm0.(src_parent_nb)) *)
    (* (BOUNDTGT: Ple skenv_tgt.(Genv.genv_next) sm0.(tgt_parent_nb)) *)
    (NBSRC: skenv_src.(Genv.genv_next) = sm0.(src_ge_nb))
    (NBTGT: skenv_tgt.(Genv.genv_next) = sm0.(tgt_ge_nb)).

Theorem sim_skenv_symbols_inject
        sm0 ss0 skenv_src skenv_tgt
        (SIMSKENV: sim_skenv sm0 ss0 skenv_src skenv_tgt):
    <<SINJ: symbols_inject sm0.(SimMemInj.inj) skenv_src skenv_tgt>>.
Proof.
  { clear - SIMSKENV. inv SIMSKENV; ss. rr. esplits; ii; ss.
    - unfold Genv.public_symbol. rewrite <- PUB.
      destruct (Genv.find_symbol skenv_tgt id) eqn:T.
      + exploit SIMSYMB3; et. i; des. rewrite BLKSRC. ss.
      + des_ifs. des_sumbool. ii. exploit PUBKEPT; et.
        apply NNPP. ii. exploit SIMSYMB2; et. i; des. clarify.
    - exploit SIMSYMB1; eauto. i; des. esplits; et.
    - exploit SIMSYMB2; eauto.
      { ii. eapply PUBKEPT; eauto. unfold Genv.public_symbol in H. des_ifs. des_sumbool. ss. }
      i; des. esplits; eauto.
    - unfold Genv.block_is_volatile, Genv.find_var_info.
      destruct (Genv.find_def skenv_src b1) eqn:T0.
      { exploit SIMDEF; try eassumption. i; des. des_ifs. }
      destruct (Genv.find_def skenv_tgt b2) eqn:T1.
      { exploit SIMDEFINV; try eassumption. i; des. des_ifs. }
      ss.
  }
Qed.

Definition sim_skenv_splittable (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
    (<<SIMSYMB1: forall id blk_src blk_tgt delta
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src),
        (<<DELTA: delta = 0>>) /\
        (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
        (<<KEPT: ~ ss id>>)>>) /\
    (<<SIMSYMB2: forall id blk_src
        (KEPT: ~ ss id)
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src),
        exists blk_tgt,
          (<<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>)>>) /\
    (<<SIMSYMB3: forall id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt),
        exists blk_src,
          (<<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>) /\
          (<<SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, 0)>>)>>) /\
    (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    (<<SIMDEF: forall blk_src blk_tgt delta def_src
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src),
        exists def_tgt, (<<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>)>>) /\
    (<<DISJ: forall id blk_src0 blk_src1 blk_tgt
        (SYMBSRC: Genv.find_symbol skenv_src id = Some blk_src0)
        (SIMVAL0: sm0.(SimMemInj.inj) blk_src0 = Some (blk_tgt, 0))
        (SIMVAL1: sm0.(SimMemInj.inj) blk_src1 = Some (blk_tgt, 0)),
        blk_src0 = blk_src1>>) /\
    (<<SIMDEFINV: forall blk_src blk_tgt delta def_tgt
        (SIMVAL: sm0.(SimMemInj.inj) blk_src = Some (blk_tgt, delta))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt),
        exists def_src, (<<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>>) /\
                        (<<DELTA: delta = 0>>) /\
                        (<<SIM: def_src = def_tgt>>)>>) /\
    (<<PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss>>) /\
    (<<PUB: skenv_src.(Genv.genv_public) = skenv_tgt.(Genv.genv_public)>>) /\
    (* /\ (<<BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm0.(src_parent_nb)>>) *)
    (* /\ (<<BOUNDTGT: Ple skenv_tgt.(Genv.genv_next) sm0.(tgt_parent_nb)>>) *)
    (<<NBSRC: skenv_src.(Genv.genv_next) = sm0.(src_ge_nb)>>) /\
    (<<NBTGT: skenv_tgt.(Genv.genv_next) = sm0.(tgt_ge_nb)>>).

Theorem sim_skenv_splittable_spec:
    (sim_skenv_splittable <4= sim_skenv) /\ (sim_skenv <4= sim_skenv_splittable).
Proof.
  split; ii; inv PR; ss; des; econs; eauto. splits; ss.
Qed.

Inductive le (ss0: t') (sk_src sk_tgt: Sk.t) (ss1: t'): Prop :=
| le_intro
    (LE: ss0 <1= ss1)
    (OUTSIDE: forall id
        (IN: (ss1 -1 ss0) id),
        <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>).

Global Program Definition link_ss (ss0 ss1: t'): option t' :=
  (* Some (fun id => orb (ss0 id) (ss1 id)) *)
  Some (ss0 \1/ ss1).

Global Program Instance Linker_t: Linker t' := {|
  link := link_ss;
  linkorder (ss0 ss1: t') := ss0 <1= ss1;
|}.


Lemma linkorder_defs
      F V
      `{Linker F} `{Linker V}
      (p0 p1: AST.program F V)
      (LINKORD: linkorder p0 p1):
    <<DEFS: p0.(defs) <1= p1.(defs)>>.
Proof.
  inv LINKORD. ii. u in *. des.
  simpl_bool. des_sumbool. apply prog_defmap_spec in PR. des.
  exploit H3; try eassumption. i; des.
  apply prog_defmap_spec. esplits; eauto.
Qed.

Lemma Genv_invert_symbol_none_spec
      F V b
      (ge: Genv.t F V):
    <<INV: Genv.invert_symbol ge b = None>> <-> <<FIND: forall id, Genv.find_symbol ge id <> Some b>>.
Proof.
  unfold Genv.find_symbol, Genv.invert_symbol in *.
  abstr (Genv.genv_symb ge) tree.
  split; i; des; red.
  - generalize dependent H.
    eapply PTree_Properties.fold_rec; ii; ss; clarify.
    + eapply H0; eauto. erewrite H; eauto.
    + erewrite PTree.gempty in H0. ss.
    + des_ifs. rewrite PTree.gsspec in *. des_ifs. eapply H1; eauto.
  - eapply PTree_Properties.fold_rec; ii; ss; clarify. des_ifs.
    contradict H. ii. eapply H; eauto.
Qed.


Lemma or_des A B (OR: A \/ B):
  (A /\ B) \/ (A /\ ~ B) \/ (~ A /\ B).
Proof. tauto. Qed.

Let init_meminj (sk_src sk_tgt:Sk.t) : meminj :=
  fun b =>
    match Genv.invert_symbol (Sk.load_skenv sk_src) b with
    | Some id =>
      match Genv.find_symbol (Sk.load_skenv sk_tgt) id with
      | Some b' => Some (b', 0)
      | None => None
      end
    | None => None
    end.

Remark init_meminj_invert
       sk_src sk_tgt ss b b' delta
       (INJ: (init_meminj sk_src sk_tgt) b = Some(b', delta))
       (SIMSK : sim_sk ss sk_src sk_tgt):
  delta = 0 /\ exists id, Genv.find_symbol (Sk.load_skenv sk_src) id = Some b /\ Genv.find_symbol (Sk.load_skenv sk_tgt) id = Some b' /\ ~ ss id.
Proof.
  unfold init_meminj in *; intros.
  destruct (Genv.invert_symbol (Sk.load_skenv sk_src) b) as [id|] eqn:S; try discriminate.
  destruct (Genv.find_symbol (Sk.load_skenv sk_tgt) id) as [b''|] eqn:F; inv INJ.
  split. auto. exists id. split. apply Genv.invert_find_symbol; auto. split. auto.
  ii. unfold Sk.load_skenv in *. apply Genv.find_symbol_inversion in F. apply prog_defmap_dom in F. des.
  inv SIMSK. apply DROP in H. congruence.
Qed.

Remark init_meminj_eq
       sk_src sk_tgt ss id b b'
       (SYMBOL: Genv.find_symbol (Sk.load_skenv sk_src) id = Some b)
       (SYMBOL2: Genv.find_symbol (Sk.load_skenv sk_tgt) id = Some b')
       (SIMSK: sim_sk ss sk_src sk_tgt):
  (init_meminj sk_src sk_tgt) b = Some(b', 0).
Proof.
  intros. unfold init_meminj. erewrite Genv.find_invert_symbol by eauto. rewrite SYMBOL2. auto.
Qed.

Lemma init_mem_exists
      sk_src sk_tgt ss m_src
      (SIMSK: sim_sk ss sk_src sk_tgt)
      (LOADMEMSRC: Sk.load_mem sk_src = Some m_src):
    exists m_tgt, Sk.load_mem sk_tgt = Some m_tgt.
Proof.
  inv SIMSK. unfold Sk.load_mem in *. apply Genv.init_mem_exists. i.
  assert (P: (prog_defmap sk_tgt)!id = Some (Gvar v)).
  { eapply prog_defmap_norepet; eauto. apply NoDup_norepet. ss. }
  assert (Q: (prog_defmap sk_src) ! id = Some (Gvar v)).
  { rewrite <- KEPT; ss. ii. rewrite DROP in P; ss. }
  exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
  split; auto. intros. exploit FV; eauto. intros (b & FS).
  eapply Genv.find_symbol_inversion in FS. apply prog_defmap_dom in FS. destruct FS as (g & R).
  apply Genv.find_symbol_exists with g. apply in_prog_defmap. rewrite KEPT; ss.
  ii. eapply NOREF; et. r. exists o; et.
Qed.

Lemma init_meminj_simskenv
      sk_src sk_tgt ss m_src m_tgt
      (LOADMEMSRC: Sk.load_mem sk_src = Some m_src)
      (LOADMEMTGT: Sk.load_mem sk_tgt = Some m_tgt)
      (SIMSK: sim_sk ss sk_src sk_tgt)
  : sim_skenv (mk m_src m_tgt (init_meminj sk_src sk_tgt) bot2 bot2 (Mem.nextblock m_src) (Mem.nextblock m_tgt)
                  (Mem.nextblock m_src) (Mem.nextblock m_tgt))
              ss (Sk.load_skenv sk_src) (Sk.load_skenv sk_tgt).
Proof.
  econs; ss; i; try (by inv SIMSK; erewrite Genv.init_mem_genv_next; eauto).
  - exploit init_meminj_invert; eauto. intros (A & id1 & B & C & D).
    assert (id1 = id) by (eapply (Genv.genv_vars_inj (Sk.load_skenv sk_src)); eauto). subst id1. esplits; auto.
  - assert(exists blk_tgt : block, Genv.find_symbol (Sk.load_skenv sk_tgt) id = Some blk_tgt).
    { apply Genv.find_symbol_inversion in BLKSRC. apply prog_defmap_dom in BLKSRC. destruct BLKSRC as (g & P).
      apply Genv.find_symbol_exists with g. apply in_prog_defmap. inv SIMSK. rewrite KEPT0; ss.
    }
    des. exists blk_tgt; split; auto. eapply init_meminj_eq; eauto.
  - assert(exists blk_src : block, Genv.find_symbol (Sk.load_skenv sk_src) id = Some blk_src).
    { apply Genv.find_symbol_inversion in BLKTGT. apply prog_defmap_dom in BLKTGT. destruct BLKTGT as (g & P).
      apply Genv.find_symbol_exists with g. apply in_prog_defmap. inv SIMSK. rewrite <- KEPT; ss.
      ii. rewrite DROP in P; ss.
    }
    des. exists blk_src; split; auto. eapply init_meminj_eq; eauto.
  - exploit init_meminj_invert; eauto. intros (A & id & B & C & D).
    assert ((prog_defmap sk_src)!id = Some def_src).
    { rewrite Genv.find_def_symbol. exists blk_src; auto. }
    assert ((prog_defmap sk_tgt)!id = Some def_src).
    { inv SIMSK. rewrite KEPT; ss. }
    rewrite Genv.find_def_symbol in H0. destruct H0 as (b & P & Q).
    unfold Sk.load_skenv in *. replace b with blk_tgt in * by congruence. exists def_src. split; auto.
  - unfold init_meminj in *. des_ifs. apply_all_once Genv.find_invert_symbol. rewrite Heq2 in Heq0. inv Heq0.
    apply_all_once Genv.invert_find_symbol. congruence.
  - exploit init_meminj_invert; eauto. intros (A & id & B & C & D).
    assert ((prog_defmap sk_tgt)!id = Some def_tgt).
    { rewrite Genv.find_def_symbol. exists blk_tgt; auto. }
    inv SIMSK. rewrite KEPT in H; ss. rewrite Genv.find_def_symbol in H. destruct H as (b & P & Q).
    unfold Sk.load_skenv in *. replace b with blk_src in * by congruence. exists def_tgt. split; auto.
  - ii. inv SIMSK. apply CLOSED in H. unfold privs in *. apply andb_true_iff in H. des.
    apply negb_true_iff in H0. unfold Sk.load_skenv in *. rewrite Genv.globalenv_public in PR. des_sumbool. ss.
  - inv SIMSK. unfold Sk.load_skenv. do 2 rewrite Genv.globalenv_public. ss.
  (* - inv SIMSK. erewrite Genv.init_mem_genv_next; et. xomega. *)
  (* - inv SIMSK. erewrite Genv.init_mem_genv_next; et. xomega. *)
Qed.

Lemma init_meminj_invert_strong
      sk_src sk_tgt ss b b' delta
      (INJ: (init_meminj sk_src sk_tgt) b = Some(b', delta))
      (SIMSK : sim_sk ss sk_src sk_tgt):
    delta = 0 /\
    exists id gd,
      Genv.find_symbol (Sk.load_skenv sk_src) id = Some b
      /\ Genv.find_symbol (Sk.load_skenv sk_tgt) id = Some b'
      /\ Genv.find_def (Sk.load_skenv sk_src) b = Some gd
      /\ Genv.find_def (Sk.load_skenv sk_tgt) b' = Some gd.
Proof.
  intros. exploit init_meminj_invert; eauto. intros (A & id & B & C & D). unfold Sk.load_skenv in *.
  assert (exists gd, (prog_defmap sk_src)!id = Some gd).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct H as [gd DM].
  assert ((prog_defmap sk_tgt)!id = Some gd).
  { inv SIMSK. rewrite KEPT; ss. }
  rewrite Genv.find_def_symbol in DM. destruct DM as (b'' & P & Q). rewrite P in B; inv B.
  rewrite Genv.find_def_symbol in H. destruct H as (b'' & R & S). rewrite R in C; inv C. esplits; et.
Qed.

Lemma bytes_of_init_inject
      sk_src sk_tgt ss m_src il
      (SIMSK: sim_sk ss sk_src sk_tgt)
      (LOADMEMSRC: Sk.load_mem sk_src = Some m_src)
      (REF: forall id, ref_init il id -> ~ ss id):
    list_forall2 (memval_inject (init_meminj sk_src sk_tgt)) (Genv.bytes_of_init_data_list (Sk.load_skenv sk_src) il) (Genv.bytes_of_init_data_list (Sk.load_skenv sk_tgt) il).
Proof.
  exploit init_mem_exists; et. intros LOADMEMTGT; des.
  induction il as [ | i1 il]; simpl; intros; try constructor.
  - apply list_forall2_app.
    + exploit init_meminj_simskenv; try eapply SIMSK; et. i. inv H; ss.
      destruct i1; simpl; try (apply inj_bytes_inject).
      { induction (Z.to_nat z); simpl; constructor. constructor. auto. }
      destruct (Genv.find_symbol (Sk.load_skenv sk_src) i) as [b|] eqn:FS.
      * assert (~ ss i). { apply REF. red. exists i0; auto with coqlib. }
        exploit SIMSYMB2; et. intros (b' & A & B). rewrite A. apply inj_value_inject.
        econstructor; eauto. symmetry; apply Ptrofs.add_zero.
      * destruct (Genv.find_symbol (Sk.load_skenv sk_tgt) i) as [b'|] eqn:FS'.
        exploit SIMSYMB3; et. intros (b & A & B). congruence. apply repeat_Undef_inject_self.
    + apply IHil. intros id [ofs IN]. apply REF. exists ofs; auto with coqlib.
Qed.

Lemma Mem_getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 i n p,
  list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
  p <= i -> i < p + Z.of_nat n ->
  P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
- simpl in H1. omegaContradiction.
- inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p); try congruence.
+ apply IHn with (p + 1); auto. omega. omega.
Qed.

Global Program Instance SimSymbDrop: SimSymb.class SimMemInj := {
  t := t';
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}.
(* Next Obligation. *)
(*   inv SIMSK. *)
(*   econs; eauto. *)
(*   ii. *)
(*   destruct (classic (ss id)). *)
(*   - erewrite DROP in *; eauto. ss. *)
(*   - erewrite <- KEPT; ss. *)
(*     esplits; eauto. *)
(*     reflexivity. *)
(* Qed. *)
Next Obligation. econs; eauto. ii. des; ss. Qed.
Next Obligation.
  inv LE0. inv LE1. econs; eauto. ii; des.
  specialize (OUTSIDE id). specialize (OUTSIDE0 id). destruct (classic (ss1 id)).
  - exploit OUTSIDE; eauto.
  - exploit OUTSIDE0; eauto. i; des.
    hexploit (linkorder_defs LINKORD0); eauto. i; des.
    hexploit (linkorder_defs LINKORD1); eauto. i; des. esplits; eauto.
Qed.
Next Obligation.
  inv SIMSK. inv WFSRC. econs; et. i. apply prog_defmap_norepet in IN; cycle 1.
  { apply NoDup_norepet; ss. }
  destruct (classic (ss0 id_to)).
  - exploit NOREF; et; ss. rr. esplits; et.
  - assert(KEPT0: ~ ss0 id_fr).
    { ii. exploit DROP; et. i; clarify. }
    dup IN. rewrite KEPT in IN; ss. exploit WFPTR; et.
    { eapply in_prog_defmap; et. }
    i; des. eapply prog_defmap_spec in H0. des. eapply prog_defmap_image; et. erewrite KEPT; et.
  - rewrite <- PUB. ii. exploit prog_defmap_dom; eauto. i; des.
    destruct (classic (ss0 a)).
    + exploit CLOSED; et. intro T. unfold privs in T. bsimpl. des. unfold NW in *. bsimpl. des_sumbool. ss.
    + exploit KEPT; eauto. intro T. rewrite H0 in *. exploit prog_defmap_image; eauto.
  - ss. i. eapply WFPARAM. instantiate (1:=id). destruct (classic (ss0 id)).
    + exploit DROP; eauto. i. exploit prog_defmap_norepet; eauto.
      rewrite <- NoDup_norepet. eauto. i. rewrite H1 in H0. clarify.
    + exploit KEPT; eauto. i. eapply prog_defmap_norepet in IN; cycle 1.
      rewrite <- NoDup_norepet. eauto. eapply in_prog_defmap. rewrite <- H0. eauto.
Qed.
Next Obligation.
  inv SIMSK. inv SIMSK0.
  exploit (link_prog_inv sk_src0 sk_src1); eauto. i; des.
  assert(AUX1: forall id, ss1 id -> ~ ss0 id -> (prog_defmap sk_src0) ! id = None).
  { i. destruct ((prog_defmap sk_src0) ! id) eqn:T; ss.
    apply CLOSED0 in H2. unfold privs, defs, NW in *. bsimpl. des. des_sumbool.
    exploit prog_defmap_dom; eauto. i; des. exploit H0; eauto. i; des. clarify.
  }
  assert(AUX2: forall id, ss0 id -> ~ ss1 id -> (prog_defmap sk_src1) ! id = None).
  { i. destruct ((prog_defmap sk_src1) ! id) eqn:T; ss.
    apply CLOSED in H2. unfold privs, defs, NW in *. bsimpl. des. des_sumbool.
    exploit prog_defmap_dom; eauto. i; des. exploit H0; eauto. i; des. clarify.
  }
  i. exists (ss0 \1/ ss1). eexists. esplits; eauto.
  - eapply (link_prog_succeeds sk_tgt0 sk_tgt1); eauto; try congruence. i. exploit H0.
    { erewrite <- KEPT; et. ii. eapply DROP in H4. congruence. }
    { erewrite <- KEPT0; et. ii. eapply DROP0 in H4. congruence. }
    i; des. esplits; congruence.
  - econs; ii; et. des; des_ifs.
    esplits; et; ii; eapply defs_prog_defmap in H1; des; exploit AUX1; eauto; try congruence; exploit KEPT; eauto; congruence.
  - econs; ii; et. des; des_ifs.
    esplits; et; ii; eapply defs_prog_defmap in H1; des; exploit AUX2; eauto; try congruence; exploit KEPT0; eauto; congruence.
  - subst. econs; ss; ii; try congruence.
    + eapply not_or_and in KEPT1. des. rewrite ! prog_defmap_elements, !PTree.gcombine by auto.
      rewrite KEPT; ss. rewrite KEPT0; ss.
    + rewrite prog_defmap_elements. rewrite PTree.gcombine; ss. apply or_des in DROP1. des.
      * rewrite DROP; ss. rewrite DROP0; ss.
      * rewrite DROP; ss. rewrite KEPT0; ss. apply AUX2; ss.
      * rewrite DROP0; ss. rewrite KEPT; ss. rewrite AUX1; ss.
    + rr. unfold privs. ss. bsimpl. split.
      { assert(T: exists x1, link_prog_merge (prog_defmap sk_src0) ! x0 (prog_defmap sk_src1) ! x0 = Some x1).
        { des.
          - exploit CLOSED; et. intro T. unfold privs in T. unfold NW in *. bsimpl. des_safe. des_sumbool.
            apply defs_prog_defmap in T. des. rewrite T. destruct ((prog_defmap sk_src1) ! x0) eqn:EQN.
            + exploit H0; et. i; des. ss.
            + eexists. ss.
          - exploit CLOSED0; et. intro T. unfold privs in T. unfold NW in *. bsimpl. des_safe. des_sumbool.
            apply defs_prog_defmap in T. des. rewrite T. destruct ((prog_defmap sk_src0) ! x0) eqn:EQN.
            + exploit H0; et. i; des. ss.
            + eexists. ss.
        }
        clear PR. des_safe. rr. unfold defs. unfold NW. des_sumbool. unfold prog_defs_names. ss.
        rewrite in_map_iff. eexists (_, _). s. esplits; eauto.
        eapply PTree.elements_correct; eauto. rewrite PTree.gcombine; ss. eauto.
      }
      unfold NW. bsimpl. des_sumbool. intro T. rewrite in_app_iff in T. destruct PR.
      * exploit CLOSED; eauto. intro TT. unfold privs, NW in TT. bsimpl. des_safe. des_sumbool.
        des; ss. apply defs_prog_defmap in TT. inv WFSRC1. apply PUBINCL in T. apply prog_defmap_dom in T. des.
        exploit H0; et. i; des. ss.
      * exploit CLOSED0; eauto. intro TT. unfold privs, NW in TT. bsimpl. des_safe. des_sumbool.
        des; ss. apply defs_prog_defmap in TT. inv WFSRC0. apply PUBINCL in T. apply prog_defmap_dom in T. des.
        exploit H0; et. i; des. ss.
    + assert(T: (In (id, Gvar gv) (prog_defs sk_tgt0)) \/ (In (id, Gvar gv) (prog_defs sk_tgt1))).
      { unfold prog_defmap in PROG. ss. rewrite PTree_Properties.of_list_elements in *.
        rewrite PTree.gcombine in *; ss. unfold link_prog_merge in PROG. clear - PROG. des_ifs.
        - apply PTree_Properties.in_of_list in Heq. apply PTree_Properties.in_of_list in Heq0.
          exploit (link_unit_same g g0); et. i; des; clarify; et.
        - apply PTree_Properties.in_of_list in Heq. eauto.
        - apply PTree_Properties.in_of_list in PROG. eauto.
      }
      assert(U: ~ In id_drop (prog_defs_names sk_tgt0) /\ ~ In id_drop (prog_defs_names sk_tgt1)).
      { split.
        - destruct (classic (ss0 id_drop)).
          + exploit DROP; eauto. intro V. intro W. exploit prog_defmap_dom; et. i; des; clarify.
          + desH DROP1; et. exploit KEPT; et. intro V.
            exploit AUX1; eauto. i. ii. exploit prog_defmap_dom; et. i; des_safe; clarify. congruence.
        - destruct (classic (ss1 id_drop)).
          + exploit DROP0; eauto. intro V. intro W. exploit prog_defmap_dom; et. i; des; clarify.
          + desH DROP1; et. exploit KEPT0; et. intro V.
            exploit AUX2; eauto. i. ii. exploit prog_defmap_dom; et. i; des_safe; clarify. congruence.
      }
      desH T.
      * inv WFTGT0. rr in H1. des_safe. exploit WFPTR; eauto.
      * inv WFTGT1. rr in H1. des_safe. exploit WFPTR; eauto.
    + apply NoDup_norepet. apply PTree.elements_keys_norepet.
    + des; congruence.
Qed.
Next Obligation.
  inv SIMSKE. unfold Genv.public_symbol. apply func_ext1. intro i0.
  destruct (Genv.find_symbol skenv_tgt i0) eqn:T.
  - exploit SIMSYMB3; et. i; des. des_ifs. rewrite PUB. ss.
  - des_ifs. des_sumbool. ii. eapply PUBKEPT in H. exploit SIMSYMB2; et. i; des. clarify.
Qed.
Next Obligation.
  exploit init_mem_exists; et. intros LOADMEMTGT; des.
  exploit init_meminj_simskenv; try eapply SIMSK; et. intros SIMSKENV.
  eexists m_tgt. exists (mk m_src m_tgt (init_meminj sk_src sk_tgt) bot2 bot2 (Mem.nextblock m_src) (Mem.nextblock m_tgt) (Mem.nextblock m_src) (Mem.nextblock m_tgt)).
  esplits; et.
  { econs; ss; try xomega. constructor; intros.
    { intros; constructor; intros.
      - exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E).
        exploit (Genv.init_mem_characterization_gen sk_src); eauto.
        exploit (Genv.init_mem_characterization_gen sk_tgt); eauto.
        destruct gd as [f|v].
        + intros (P2 & Q2) (P1 & Q1). apply Q1 in H0. destruct H0. subst. apply Mem.perm_cur. auto.
        + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1). apply Q1 in H0. destruct H0. subst.
          apply Mem.perm_cur. eapply Mem.perm_implies; eauto. apply P2. omega.
      - exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta. apply Z.divide_0_r.
      - exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E).
        exploit (Genv.init_mem_characterization_gen sk_src); eauto.
        exploit (Genv.init_mem_characterization_gen sk_tgt); eauto.
        destruct gd as [f|v].
        + intros (P2 & Q2) (P1 & Q1). apply Q1 in H0. destruct H0; discriminate.
        + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1). apply Q1 in H0. destruct H0.
          assert (NO: gvar_volatile v = false).
          { unfold Genv.perm_globvar in H1. destruct (gvar_volatile v); auto. inv H1. }
          Local Transparent Mem.loadbytes.
          generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
          generalize (S2 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E2; inv E2.
          rewrite Z.add_0_r. apply Mem_getN_forall2 with (p := 0) (n := nat_of_Z (init_data_list_size (gvar_init v))); try omega.
          rewrite H3, H4. eapply bytes_of_init_inject; et.
          { ii. inv SIMSK. eapply NOREF; et. eapply Genv.find_def_symbol. eexists. split; et. }
          rewrite nat_of_Z_eq by (apply init_data_list_size_pos). omega.
    }
    - destruct ((init_meminj sk_src sk_tgt) b) as [[b' delta]|] eqn:INJ; auto.
      elim H. exploit init_meminj_invert; eauto. intros (A & id & B & C & D).
      unfold Sk.load_skenv, Sk.load_mem in *. eapply Genv.find_symbol_not_fresh; eauto.
    - exploit init_meminj_invert; eauto. intros (A & id & B & C & D).
      unfold Sk.load_skenv, Sk.load_mem in *. eapply Genv.find_symbol_not_fresh; eauto.
    - red; intros.
      exploit init_meminj_invert; try eapply H0; et. intros (A1 & id1 & B1 & C1 & D1).
      exploit init_meminj_invert; try eapply H1; et. intros (A2 & id2 & B2 & C2 & D2).
      destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
    - exploit init_meminj_invert; eauto. intros (A & id & B & C & D). subst delta.
      split. omega. generalize (Ptrofs.unsigned_range_2 ofs). omega.
    - exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E).
      exploit (Genv.init_mem_characterization_gen sk_src); eauto.
      exploit (Genv.init_mem_characterization_gen sk_tgt); eauto.
      destruct gd as [f|v].
      + intros (P2 & Q2) (P1 & Q1). apply Q2 in H0. destruct H0. subst. replace ofs with 0 by omega.
        left; apply Mem.perm_cur; auto.
      + intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1). apply Q2 in H0. destruct H0. subst.
        left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto. apply P1. omega.
  }
  { ss. inv SIMSK. rewrite <- MAIN. unfold init_meminj.
    inv SIMSKENV. ss. unfold Genv.symbol_address. des_ifs; cycle 1.
    { exploit SIMSYMB2; et. i; des. clarify. }
    apply Genv.find_invert_symbol in Heq. econs; eauto; cycle 1.
    { psimpl. ss. }
    rewrite Heq. rewrite Heq0. eauto.
  }
Qed.
Next Obligation.
  inv MLE. inv SIMSKENV.
  assert (SAME: forall b b' delta, Plt b (Genv.genv_next skenv_src) ->
                                   inj sm1 b = Some(b', delta) -> inj sm0 b = Some(b', delta)).
  { i. erewrite frozen_preserves_src; eauto. congruence. }
  apply sim_skenv_splittable_spec. rr. dsplits; eauto; try congruence; ii.
  - i. eapply SIMSYMB1; eauto. eapply SAME; try eapply Genv.genv_symb_range; eauto.
  - i. exploit SIMSYMB2; eauto. i; des. eexists. splits; eauto.
  - i. exploit SIMSYMB3; eauto. i; des. eexists. splits; eauto.
  - i. exploit SIMDEF; eauto. eapply SAME; try eapply Genv.genv_defs_range; eauto.
  - i. eapply DISJ; eauto. eapply SAME; try eapply Genv.genv_symb_range; eauto.
    destruct (inj sm0 blk_src1) eqn:T; ss.
    { destruct p; ss. exploit INCR; et. i; clarify. }
    exfalso. inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des.
    exploit SPLITHINT; try apply SYMBSRC; eauto. i; des. clear_tac.
    exploit Genv.genv_symb_range; eauto. i. clear - H OUTSIDE_TGT NBTGT. rewrite NBTGT in *. xomega.
  - i. eapply SIMDEFINV; eauto.
    destruct (inj sm0 blk_src) as [[b1 delta1] | ] eqn: J.
    + exploit INCR; eauto. congruence.
    + inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des.
      exploit Genv.genv_defs_range; eauto. i. rewrite NBTGT in *. xomega.
Qed.
Next Obligation.
  set (SkEnv.project skenv_link_src sk_src) as skenv_src.
  generalize (SkEnv.project_impl_spec INCLSRC); intro LESRC.
  set (SkEnv.project skenv_link_tgt sk_tgt) as skenv_tgt.
  generalize (SkEnv.project_impl_spec INCLTGT); intro LETGT.
  exploit SkEnv.project_spec_preserves_wf; try apply LESRC; eauto. intro WFSMALLSRC.
  exploit SkEnv.project_spec_preserves_wf; try apply LETGT; eauto. intro WFSMALLTGT.
(* THIS IS TOP *)
  inv SIMSKENV. ss. apply sim_skenv_splittable_spec. folder.
  dsplits; eauto; ii; ss.
  - (* SIMSYMB1 *)
    inv LESRC. destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    exploit SIMSYMB1; eauto. { rewrite <- KEEP. ss. } i; des.

    inv LETGT. destruct (classic (defs sk_tgt id)); cycle 1.
    { erewrite SYMBDROP0; ss. exfalso. clear - LE KEPT H H0 SIMSK.
      apply H0. clear H0. inv SIMSK. u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss. esplits; eauto.
      - exfalso. apply KEPT. inv LE. eauto.
    }
    erewrite SYMBKEEP0; ss. esplits; eauto.
    { clear - LE H0 KEPT. inv LE. ii. apply KEPT.
      apply NNPP. ii. exploit OUTSIDE; eauto. { split; eauto. }
    }


  - (* SIMSYMB2 *)
    inv LESRC. destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    rewrite KEEP in *.
    exploit (SIMSYMB2 id); eauto.
    { inv LE. ii. eapply KEPT. specialize (OUTSIDE id).
      exploit OUTSIDE; eauto. i; des. ss.
    }
    i; des. esplits; eauto. inv LETGT. erewrite SYMBKEEP0; ss.
    destruct (classic (defs sk_tgt id)); ss.
    { exfalso. clear - LE KEPT H H0 SIMSK. apply H0. clear H0.
      inv SIMSK. u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss.
      - exfalso. apply KEPT. ss.
    }

  - (* SIMSYMB3 *)
    inv LETGT. destruct (classic (defs sk_tgt id)); cycle 1.
    { exploit SYMBDROP; eauto. i; des. clarify. }

    erewrite SYMBKEEP in *; ss. exploit SIMSYMB3; eauto. i; des. esplits; eauto.

    inv LESRC. erewrite SYMBKEEP0; ss.

    { clear - H SIMSK. inv SIMSK.
      u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); ss.
      { erewrite DROP in *; ss. }
      exploit KEPT; eauto. i; des. rewrite <- H1. esplits; eauto.
    }

  - (* SIMDEF *)

    inv LESRC. inv WFSMALLSRC. exploit DEFSYMB; eauto. intro SYMBSMALL; des. rename SYMB into SYMBSMALL.
    destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des. rewrite SYMBSMALL in *. symmetry in SYMBBIG. inv WFSRC.
    exploit SYMBDEF; eauto. i; des.
    exploit SIMDEF; eauto. i; des. clarify.

    exploit SPLITHINT; eauto. i; des. move DEFSRC at bottom. move H0 at bottom.

    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des. rename H1 into KEEP. clarify.

    (* assert(def_src = def_tgt). *)
    (* { exploit DEFKEEP; eauto. eapply Genv.find_invert_symbol; eauto. i. *)
    (*   rewrite DEFSRC in *. rewrite H0 in *. des. clarify. } clarify. *)
    esplits; eauto. inv LETGT. exploit SIMSYMB1; eauto. i; des.


    destruct (Genv.find_def skenv_tgt blk_tgt) eqn:T.
    { exploit DEFKEPT0; eauto.
      { eapply Genv.find_invert_symbol; eauto. }
      i; des. clarify. inv SIMSK. specialize (KEPT1 id).
      destruct (classic (ss id)).
      { exploit DROP; et. i; clarify. }
      exploit KEPT1; et. i; clarify. congruence.
    }
    exploit DEFKEEP0; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    { inv SIMSK. exploit (KEPT1 id); eauto. i.
      unfold internals in *. des_ifs.
    }
    i; des. clarify.

  - inv LESRC. destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; et. i; des. clarify. }
    eapply DISJ; et. erewrite <- SYMBKEEP; et.

  - (* SIMDEFINV *)

    assert(exists gd_big, <<DEFBIG: Genv.find_def skenv_link_tgt blk_tgt = Some gd_big>>
                                    /\ <<LO: linkorder def_tgt gd_big>>).
    {
      inv LETGT. destruct (Genv.invert_symbol skenv_link_tgt blk_tgt) eqn:T.
      - exploit DEFKEPT; eauto. i; des. ss. esplits; et.
      - exploit DEFORPHAN; eauto. i; des. clarify.
    }
    des. exploit SIMDEFINV; eauto. i; des. clarify. esplits; eauto.

    inv WFSMALLTGT. exploit DEFSYMB; eauto. intro SYMBSMALLTGT; des. rename SYMB into SYMBSMALLTGT.
    exploit SPLITHINT1; eauto. i; des.
    Fail clears blk_src. assert(blk_src = blk_src0).
    { symmetry. eapply SPLITHINT3; et. }
    clarify. inv LESRC. inv WFSRC. exploit DEFSYMB; eauto. i; des.
    assert(id = id0). { eapply Genv.genv_vars_inj. apply SYMBSMALLTGT. eauto. } clarify.
    assert(DSRC: defs sk_src id0).
    { apply NNPP. ii. erewrite SYMBDROP in *; eauto. ss. }
    exploit SYMBKEEP; eauto. i; des. rewrite BLKSRC in *. symmetry in H.
    assert(DTGT: defs sk_tgt id0).
    { apply NNPP. ii. inv LETGT. erewrite SYMBDROP0 in *; eauto. ss. }
    assert(ITGT: internals sk_tgt id0).
    { dup DTGT. unfold defs in DTGT. des_sumbool. apply prog_defmap_spec in DTGT. des.

      inv INCLTGT. exploit DEFS; et. i; des.
      assert(blk = blk_tgt).
      { inv LETGT. exploit SYMBKEEP0; et. i; des. congruence. }
      clarify. inv LETGT. exploit DEFKEPT0; et.
      { apply Genv.find_invert_symbol; eauto. }
      i; des. ss.
    }
    assert(ISRC: internals sk_src id0).
    { inv SIMSK. unfold internals in *. des_ifs_safe.
      exploit SPLITHINT; et. i; des. clear_tac.
      hexploit (KEPT id0); et. intro T. rewrite Heq in *. des_ifs.
    }
    exploit DEFKEEP; et.
    { apply Genv.find_invert_symbol; eauto. }
    i; des. rewrite DEFSMALL.
    { inv LETGT. exploit DEFKEPT0; eauto.
      { eapply Genv.find_invert_symbol; eauto. rewrite <- SYMBKEEP0; et. }
      i; des. clarify. inv SIMSK.
      specialize (KEPT id0).
      destruct (classic (ss id0)).
      { exploit DROP; et. i; clarify. }
      exploit KEPT; et. i; clarify. congruence.
    }

  - (* PUBS *)
    exploit PUBKEPT; eauto.
    { eapply INCLSRC; et. }
    inv LE. eauto.
  - inv SIMSK. ss.
Qed.
Next Obligation.
  inv SIMSKENV. econs; eauto; ii; ss.
  - inv SIMFPTR; ss.
    des_ifs_safe; ss. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEF; eauto. i; des.
    inv SIM. rewrite DEFTGT. esplits; eauto. des_ifs.
  - inv SIMFPTR; ss; cycle 1.
    des_ifs_safe. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEFINV; eauto. i; des. clarify. psimpl. clarify.
    rewrite DEFSRC. esplits; eauto. des_ifs.
Qed.
Next Obligation.
  inv SIMSKENV. unfold System.skenv in *. esplits; eauto.
  econs; ii; ss; eauto; try rewrite Genv_map_defs_symb in *; apply_all_once Genv_map_defs_def; eauto.
  - des. exploit SIMDEF; eauto. i; des. clarify.
    esplits; eauto. eapply Genv_map_defs_def_inv in DEFTGT. rewrite DEFTGT. ss.
  - des. exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto. eapply Genv_map_defs_def_inv in DEFSRC. rewrite DEFSRC. ss.
  - eapply PUBKEPT; eauto.
Qed.
Next Obligation.
  inv ARGS; ss. destruct sm0; ss. inv MWF; ss. clarify.
  inv SIMSKENV; ss.
  exploit external_call_mem_inject_gen; eauto.
  { instantiate (1:= skenv_sys_tgt).
    rr. esplits; ii; ss.
    - unfold Genv.public_symbol. rewrite <- PUB.
      destruct (Genv.find_symbol skenv_sys_tgt id) eqn:T.
      + exploit SIMSYMB3; et. i; des. rewrite BLKSRC. ss.
      + des_ifs. des_sumbool. ii. exploit PUBKEPT; et. apply NNPP. ii. exploit SIMSYMB2; et. i; des. clarify.
    - exploit SIMSYMB1; eauto. i; des. esplits; et.
    - exploit SIMSYMB2; eauto.
      { ii. eapply PUBKEPT; eauto. unfold Genv.public_symbol in H. des_ifs. des_sumbool. ss. }
      i; des. esplits; eauto.
    - unfold Genv.block_is_volatile, Genv.find_var_info.
      destruct (Genv.find_def skenv_sys_src b1) eqn:T0.
      { exploit SIMDEF; try eassumption. i; des. des_ifs.
      }
      destruct (Genv.find_def skenv_sys_tgt b2) eqn:T1.
      { exploit SIMDEFINV; try eassumption. i; des. des_ifs. }
      ss.
  }
  i; des.




  (* TODO: almost exactly copied from SimMemInj. we may remove duplicate code some way *)
  do 2 eexists. dsplits; eauto.
  - instantiate (1:= Retv.mk _ _); ss. eauto.
  - destruct retv_src; ss. instantiate (1:= mk _ _ _ _ _ _ _ _ _). econs 1; ss; eauto.
    instantiate (1:= retv_src.(Retv.m)). ss.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
      eapply SRCEXT in H6. unfold src_private in *. ss. des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
      eapply TGTEXT in H6. unfold tgt_private in *. ss. des; ss.
    + eapply inject_separated_frozen in H5. inv H5. econs; eauto. i. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. esplits; xomega.
    + eapply inject_separated_frozen in H5. inv H5. econs; eauto. i. exploit NEW_IMPLIES_OUTSIDE; eauto. i; des. esplits; xomega.
    + ii. eapply external_call_max_perm; eauto.
    + ii. eapply external_call_max_perm; eauto.
  - apply inject_separated_frozen in H5. econs; ss.
    + etrans; eauto. unfold src_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. destruct (f' x0) eqn:T; ss. destruct p; ss.
        inv H5. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *.
        unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + etrans; eauto. unfold tgt_private. ss. ii. des. esplits; eauto.
      * rr. rr in PR. ii. destruct (inj b0) eqn:T; ss.
        -- destruct p; ss. exploit H4; eauto. i; clarify.
           eapply PR; et. eapply external_call_max_perm; et.
           eapply Mem.valid_block_inject_1; try apply T; et.
        -- inv H5. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des. unfold valid_blocks in *.
           unfold Mem.valid_block in *. xomega.
      * r. eapply Mem.valid_block_unchanged_on; et.
    + inv H2. xomega.
    + inv H3. xomega.
Qed.

End MEMINJ.
