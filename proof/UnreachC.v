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

(* Require Import IntegersC LinkingC. *)
(* Require Import SimSymb Skeleton Mod ModSem. *)
Require Import ModSem Skeleton.
(* Require SimSymbId. *)
(* Require Import SimMem. *)

Require Import Sound.
Require Unreach.
Include Unreach.
Require Import SemiLattice.
Require Import FinFun.

Set Implicit Arguments.


Local Open Scope nat.











(* Remark: if econs/econsr gives different goal, at least 2 econs is possible *)
Ltac econsr :=
  first
    [
    econstructor 16
    |econstructor 15
    |econstructor 14
    |econstructor 13
    |econstructor 12
    |econstructor 11
    |econstructor 10
    |econstructor  9
    |econstructor  8
    |econstructor  7
    |econstructor  6
    |econstructor  5
    |econstructor  4
    |econstructor  3
    |econstructor  2
    |econstructor  1
    ]
.

(* Let cons_sig *)
(*     X (P: X -> Prop) (Q: X -> Prop) (R: X -> Prop) *)
(*     (PR: P <1= R) *)
(*     (QR: Q <1= R) *)
(*     (x: { x: X | P x }) *)
(*     (xs: list { x: X | Q x}) *)
(*   : *)
(*     exists (xxs: list { x: X | R x}), *)
(*       exists hd tl, xxs = hd :: tl /\ <<HD: hd$ = x$>> /\ <<TL: List.map (@proj1_sig _ _) tl = List.map (@proj1_sig _ _) xs>> *)
(* . *)
(* Proof. *)
(*   admit "". *)
(*   (* ginduction xs; ii; ss. *) *)
(* Qed. *)

(* Lemma Finite_sig *)
(*       X (P: X -> Prop) *)
(*       (FIN: exists l, forall x (PROP: P x), In x l) *)
(*   : *)
(*     <<FIN: FinFun.Finite { x: X | P x }>> *)
(* . *)
(* Proof. *)
(*   des. rr. ginduction l; ii; ss. *)
(*   - exists []. rr. i. destruct a. eauto. *)
(*   - destruct (classic (P a)); cycle 1. *)
(*     { exploit IHl; eauto. i. exploit FIN; eauto. i; des; clarify; eauto. } *)
(*     specialize (IHl (fun x => P x /\ a <> x)). *)
(*     exploit IHl; eauto. *)
(*     { ii. des. exploit FIN; eauto. i; des; clarify. } *)
(*     i; des. *)
(*     unfold FinFun.Full. *)
(*     assert(exists (hd: {x: X | , hd $ = a). *)
(*     exploit (cons_sig _ _ a l0); eauto. *)
(*     exists (a :: l0). *)
(*               exploit IHl; eauto. i. *)
(*   exists l. *)
(*   econs; eauto. *)
(* Qed. *)

Definition val' (su: Unreach.t) (nb: block) (v: val): Prop :=
  forall blk ofs (PTR: v = Vptr blk ofs true), ~su blk /\ (blk < nb)%positive
.

Definition memval' (su: Unreach.t) (nb: block) (mv: memval): Prop :=
  forall v q n (PTR: mv = Fragment v q n), su.(val') nb v
.

Inductive mem': Unreach.t -> Memory.mem -> Prop :=
| mem'_intro
    (su: Unreach.t) m0
    (SOUND: forall
        blk ofs
        (PUB: ~ su blk)
        (PERM: Mem.perm m0 blk ofs Cur Readable) (* <------------ Cur? *)
      ,
        su.(memval') m0.(Mem.nextblock) (ZMap.get ofs (Mem.mem_contents m0) !! blk))
    (BOUND: su.(unreach) <1= m0.(Mem.valid_block))
    (* (BOUND: Ple su.(Unreach.nb) m0.(Mem.nextblock)) *)
    (GENB: Ple su.(Unreach.ge_nb) m0.(Mem.nextblock))
    (NB: su.(Unreach.nb) = m0.(Mem.nextblock))
  :
    mem' su m0
.

Lemma mle_mem
      su0 m0 m1
      (MEM: mem' su0 m0)
      (MLE: mle su0 m0 m1)
      (NB: Ple m0.(Mem.nextblock) m1.(Mem.nextblock))
  :
    <<MEM: mem' su0 m1>>
.
Proof.
  inv MEM.
  inv MLE.
  econs; eauto; cycle 1.
  { ii. unfold Mem.valid_block in *. exploit BOUND; eauto. i. xomega. }
  { xomega. }
  ii. clarify.
  (* MLE: private is not changed *)
  (* we need to show: public may changed, but still not pointing private *)
Abort.

Hint Unfold val' memval'.

Definition le' (x y: Unreach.t): Prop :=
  (<<PRIV: x.(unreach) <1= y.(unreach)>>)
  /\
  (<<PUB: x.(ge_nb) = y.(ge_nb)>>)
  (* /\ *)
  (* (<<NB: x.(nb) = y.(nb)>>) *)
.

Global Program Instance le'_PreOrder: PreOrder le'.
Next Obligation.
  ii; r; esplits; ss; eauto.
Qed.
Next Obligation.
  ii. r in H. r in H0. des.
  r; esplits; ss; eauto; etrans; eauto.
Qed.

(* TODO: I really don't want to define this. It is redundant with `Sound.args`, but it seems there is no other way *)
Definition args' (su: Unreach.t) (args0: Args.t) :=
  (<<VAL: val' su args0.(Args.m).(Mem.nextblock) (Args.fptr args0)>>)
  /\ (<<VALS: List.Forall (su.(val') args0.(Args.m).(Mem.nextblock)) (Args.vs args0)>>)
  /\ (<<MEM: mem' su (Args.m args0)>>)
  /\ (<<WF: forall blk (PRIV: su blk) (PUB: Plt blk su.(ge_nb)), False>>)
  /\ (<<WF: forall blk (PRIV: su blk) (PUB: Ple su.(nb) blk), False>>)
.

Definition retv' (su: Unreach.t) (retv0: Retv.t) :=
  (<<VAL: val' su retv0.(Retv.m).(Mem.nextblock) (Retv.v retv0)>>)
  /\ (<<MEM: mem' su (Retv.m retv0)>>)
  /\ (<<WF: forall blk (PRIV: su blk) (PUB: Ple su.(nb) blk), False>>)
.

(* Inductive flatten_list: block -> list t -> Prop := *)
(* | flatten_list_nil *)
(*   : *)
(*     flatten_list 1%positive [] *)
(* | flatten_list_cons *)
(*     nb xs *)
(*     (LIST: flatten_list nb xs) *)
(*   : *)
(*     flatten_list (nb + 1)%positive (xs ++ xs) *)
(* . *)
Lemma not_ex_all_not
      U (P: U -> Prop)
      (NEX: ~ (exists n : U, P n))
  :
    <<NALL: forall n : U, ~ P n>>
.
Proof. eauto. Qed.

Lemma finite_map
      X (P: X -> Prop) Y
      (j: X -> Y)
      (INJ: Injective j)
      (FIN: exists ly, forall x, P x -> In (j x) ly)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  rr in FIN. des.
  ginduction ly; ii; ss.
  { exists []. ii. exploit FIN; eauto. }
  rename a into y0.
  specialize (IHly X (fun x => P x /\ j x <> y0) j INJ).
  exploit IHly; eauto.
  { ii. des. exploit FIN; eauto. i; des; ss; clarify. }
  i; des.
  destruct (classic (exists x0, j x0 = y0)); cycle 1.
  { eapply not_ex_all_not in H0. exists lx. i. eapply H. esplits; eauto. }
  des.
  exists (x0 :: lx).
  i. ss.
  destruct (classic (x0 = x)); eauto.
  right. eapply H; eauto. esplits; eauto. ii.
  assert(x0 = x).
  { eapply INJ. congruence. }
  clarify.
Qed.

Lemma finite_map_prop
      X (P: X -> Prop) Y
      (j: X -> Y -> Prop)
      (INJ: forall x0 x1 y, P x0 -> P x1 -> j x0 y -> j x1 y -> x0 = x1)
      (FUNC: forall x, P x -> exists y, j x y)
      (* (FUNC: forall x, exists ! y, j x y) *)
      (FIN: exists ly, forall x y, P x -> j x y -> In y ly)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  rr in FIN. des.
  ginduction ly; ii; ss.
  { exists []. ii. exploit FUNC; eauto. i; des. (* destruct H0. destruct H0. *) exploit FIN; eauto. }
  rename a into y0.
  specialize (IHly X (fun x => P x /\ ~(j x y0)) j).
  exploit IHly; eauto.
  { ii. des. eauto. }
  { ii. des. eauto. }
  { ii. des. exploit FIN; eauto. i; des; ss; clarify. }
  i; des.
  destruct (classic (exists x0, j x0 y0 /\ P x0)); cycle 1.
  { eapply not_ex_all_not in H0. exists lx. i. eapply H. esplits; eauto. ii. eapply H0; eauto. }
  des.
  exists (x0 :: lx).
  i. ss.
  destruct (classic (x0 = x)); eauto.
  right. eapply H; eauto.
Qed.

Fixpoint range (n: nat): list nat :=
  match n with
  | 0%nat => [0]
  | S n => (S n) :: range n
  end
.

Lemma range_0
      bound
  :
    In 0 (range bound)
.
Proof.
  ginduction bound; ii; ss; try tauto.
Qed.

Lemma range_spec
      x bound
      (BDD: (x <= bound))
  :
    In x (range bound)
.
Proof.
  admit "ez".
Qed.

Lemma finite_nat
      X (P: X -> Prop)
      (j: positive -> X -> option nat)
      (fuel: positive)
      (INJ: Injective (j fuel))
      (FIN: exists bound, forall x, P x -> exists n, j fuel x = Some n /\ (n <= bound))
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  eapply finite_map with (j := j fuel); eauto. des.
  exists (map Some (range bound)). ii. exploit FIN; eauto. i.
  des; ss. rewrite H0.
  rewrite in_map_iff. esplits; eauto. eapply range_spec; eauto.
Qed.

Lemma finite_nat_prop
      X (P: X -> Prop)
      (j: positive -> X -> nat -> Prop)
      (fuel: positive)
      (INJ: forall x0 x1 n, P x0 -> P x1 -> j fuel x0 n -> j fuel x1 n -> x0 = x1)
      (FUNC: forall x, P x -> exists y, j fuel x y)
      (* (FIN: exists bound, forall x, P x -> exists n, j fuel x n /\ (n <= bound)) *)
      (FIN: exists bound, forall x n, P x -> j fuel x n -> (n <= bound))
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  eapply finite_map_prop with (j := j fuel); eauto.
  des.
  exists (range bound). ii. exploit FIN; eauto. i.
  eapply range_spec; eauto.
Qed.

Lemma finite_pos_prop
      X (P: X -> Prop)
      (j: positive -> X -> positive -> Prop)
      (fuel: positive)
      (INJ: forall x0 x1 n, P x0 -> P x1 -> j fuel x0 n -> j fuel x1 n -> x0 = x1)
      (FUNC: forall x, P x -> exists y, j fuel x y)
      (* (FIN: exists bound, forall x, P x -> exists n, j fuel x n /\ (n <= bound)) *)
      (FIN: exists bound, forall x n, P x -> j fuel x n -> (n <= bound)%positive)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
Admitted.
(* Function J (fuel: positive) (su: t): option nat := *)
(*   match fuel with *)
(*   | 0%positive => None *)
(*   | Pos.succ n *)
(*   end *)
(* . *)
(*   match fuel.(Pos.to_nat) with *)
(*   | 0 => None *)
(*   | S n => J n su *)
(*   end *)
(* . *)
(*   match fuel with *)
(*   | *)

Inductive J: positive -> Unreach.t -> nat -> Prop :=
| J_runout
    su 
  :
    J (1%positive) su 0
| J_true
    fuel su n
    (PRED: J fuel su n)
    (TRUE: su fuel = true)
  :
    J fuel.(Pos.succ) su (2 * n + 1)
| J_false
    fuel su n
    (PRED: J fuel su n)
    (FALSE: su fuel = false)
  :
    J fuel.(Pos.succ) su (2 * n)
.

Compute (Pos.to_nat ((1%positive) ~ 0 ~ 0 ~ 1)).
Inductive Jpos: positive -> Unreach.t -> positive -> Prop :=
| Jpos_runout
    su 
  :
    Jpos (1%positive) su (1%positive)
| Jpos_true
    fuel su n
    (PRED: Jpos fuel su n)
    (TRUE: su fuel = true)
  :
    Jpos fuel.(Pos.succ) su (n ~ 1)
| Jpos_false
    fuel su n
    (PRED: Jpos fuel su n)
    (FALSE: su fuel = false)
  :
    Jpos fuel.(Pos.succ) su (n ~ 0) 
.

(* Let Jpos_injective: forall *)
(*     fuel x0 x1 n *)
(*     (J0: Jpos fuel x0 n) *)
(*     (J1: Jpos fuel x1 n) *)
(*     (BDD0: forall blk, x0 blk = true -> Plt blk fuel) *)
(*     (BDD1: forall blk, x1 blk = true -> Plt blk fuel) *)
(*   , *)
(*     x0 = x1 *)
(* . *)
(* Proof. *)
(*   i. *)
(*   apply func_ext1. *)
(*   revert_until fuel. *)
(*   pattern fuel. *)
(*   eapply Pos.peano_ind; clear fuel; i. *)
(*   - destruct (x0 x2) eqn:T0; ss. *)
(*     { exfalso. exploit BDD0; eauto. i. xomega. } *)
(*     destruct (x1 x2) eqn:T1; ss. *)
(*     { exfalso. exploit BDD1; eauto. i. xomega. } *)
(*   - inv J0; inv J1; ss. *)
(*     { xomega. } *)
(*     + assert(p = fuel) by (eapply Pos.succ_inj; eauto). *)
(*       assert(p = fuel0) by (eapply Pos.succ_inj; eauto). *)
(*       clarify. clear_tac. *)
(*       exploit H; [exact PRED|exact PRED0|..]; eauto. *)
(*       { i. exploit BDD0; eauto. i. xomega. *)
(* Qed. *)

Lemma pos_elim_succ
      p
  :
    <<ONE: p = 1%positive>> \/
    <<SUCC: exists q, q.(Pos.succ) = p>>
.
Proof.
  hexploit (Pos.succ_pred_or p); eauto. i; des; ss; eauto.
Qed.

Ltac it TERM := instantiate (1:=TERM).
Ltac itl TERM :=
  first[
      instantiate (10:=TERM)|
      instantiate (9:=TERM)|
      instantiate (8:=TERM)|
      instantiate (7:=TERM)|
      instantiate (6:=TERM)|
      instantiate (5:=TERM)|
      instantiate (4:=TERM)|
      instantiate (3:=TERM)|
      instantiate (2:=TERM)|
      instantiate (1:=TERM)|
      fail
    ]
.

Lemma ple_elim_succ
      p q
      (PLE: Ple p q)
  :
    <<EQ: p = q>> \/
    <<SUCC: Ple p.(Pos.succ) q>>
.
Proof.
  revert_until p.
  pattern p. apply Pos.peano_ind; clear p; i.
  { hexploit (pos_elim_succ q); eauto. i. des; clarify; eauto.
    right. r. xomega. }
  hexploit (pos_elim_succ q); eauto. i.
  des; clarify.
  { left. xomega. }
  exploit H; eauto.
  { it q0. xomega. }
  i; des; clarify.
  - left. r. xomega.
  - right. r. xomega.
Qed.

Let eta
      x0 x1
      (FIELD0: x0.(unreach) = x1.(unreach))
      (FIELD1: x0.(ge_nb) = x1.(ge_nb))
      (FIELD2: x0.(nb) = x1.(nb))
  :
    <<EQ: x0 = x1>>
.
Proof. destruct x0, x1; ss. clarify. Qed.

Let Jpos_injective: forall
    fuel x0 x1 n
    (J0: Jpos fuel x0 n)
    (J1: Jpos fuel x1 n)
    (BDD: forall blk, Ple fuel blk -> x0 blk = x1 blk)
    (GENB: x0.(ge_nb) = x1.(ge_nb))
    (NB: x0.(nb) = x1.(nb))
  ,
    x0 = x1
.
Proof.
  i.
  eapply eta; ss.
  apply func_ext1.
  revert_until fuel.
  pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  - eapply BDD; eauto. xomega.
  - inv J0; inv J1; ss.
    { xomega. }
    + assert(p = fuel) by (eapply Pos.succ_inj; eauto).
      assert(p = fuel0) by (eapply Pos.succ_inj; eauto).
      clarify. clear_tac.
      exploit H; [exact PRED|exact PRED0|..]; eauto.
      { i. eapply ple_elim_succ in H0. des; clarify.
        eapply BDD; eauto.
      }
    + assert(p = fuel) by (eapply Pos.succ_inj; eauto).
      assert(p = fuel0) by (eapply Pos.succ_inj; eauto).
      clarify. clear_tac.
      exploit H; [exact PRED|exact PRED0|..]; eauto.
      { i. eapply ple_elim_succ in H0. des; clarify.
        eapply BDD; eauto.
      }
Qed.

Let Jpos_func: forall
    fuel x
  ,
    exists n, Jpos fuel x n
.
Proof.
  intro fuel. pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  - esplits; eauto. econs; eauto.
  - specialize (H x). des.
    destruct (x p) eqn:T.
    + esplits; eauto.
      econs; eauto.
    + esplits; eauto.
      econsr; eauto.
Qed.

Let Jpos_bound: forall
    fuel x n
    (J: Jpos fuel x n)
  ,
    (n <= 3 ^ fuel)%positive
.
Proof.
  intro fuel. pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  { inv J0; try xomega. }
  inv J0; exploit Pos.succ_inj; eauto; i; clarify; clear_tac; hexploit H; eauto; i.
  - ss. rewrite Pos.pow_succ_r. xomega.
  - ss. rewrite Pos.pow_succ_r. xomega.
Unshelve.
  all: ss.
Qed.

Let to_inj (su: t) (bound: positive): meminj :=
  fun blk =>
    if (su blk)
    then None
    else
      (if plt blk bound
       then Some (blk, 0%Z)
       else None)
.

(* Let to_su (j: meminj) (bound: positive): t := *)
(*   fun blk => *)
(*     if plt blk bound *)
(*     then *)
(*       match j blk with *)
(*       | Some _ => false *)
(*       | None => true *)
(*       end *)
(*     else *)
(*       false *)
(* . *)
Let to_su (j: meminj) (ge_nb: block) (bound: positive): t :=
  mk
    (fun blk =>
       if plt blk bound
       then
         match j blk with
         | Some _ => false
         | None => true
         end
       else
         false)
    ge_nb
    bound
.

Let to_inj_mem: forall
    su m
    (SUM: mem' su m)
  ,
    @Mem.inject Val.mi_normal (to_inj su m.(Mem.nextblock)) m m
.
Proof.
  i. unfold to_inj. inv SUM. u in BOUND.
  econs; eauto; ii; ss; des_ifs; zsimpl; ss; try tauto.
  - econs; ii; ss; des_ifs; zsimpl; eauto.
    + apply Z.divide_0_r.
    + spc SOUND. spc SOUND.
      hexploit SOUND; eauto.
      { ii. bsimpl. clarify. }
      intro MV; des.
      r in MV.
      abstr (ZMap.get ofs (Mem.mem_contents m) !! b2) mv.
      destruct mv; ss; try (by econs; eauto).
      destruct v; ss; try (by econs; eauto).
      destruct b0; ss; try (by econs; eauto).
      destruct (su b) eqn:T.
      { exploit MV; ss; eauto. i; des. ss. }
      econs; eauto. econs; eauto.
      { des_ifs. exploit MV; eauto. i; des. ss. }
      rewrite Ptrofs.add_zero. ss.
  - split.
    + eauto with xomega.
    + eapply Ptrofs.unsigned_range_2; eauto.
Qed.

Definition lub (x y: t): option t :=
  if eq_block x.(ge_nb) y.(ge_nb) then
    if eq_block x.(nb) y.(nb)
    then Some (mk (fun blk => orb (x blk) (y blk)) x.(ge_nb) x.(nb))
    else None
  else None
.
Hint Unfold lub.

Lemma lubsucc: forall
    su0 x y args
    (PX: le' su0 x /\ args' x args)
    (PY: le' su0 y /\ args' y args)
  ,
    exists z, <<LUB: lub x y = Some z>>
.
Proof.
  ii. des. unfold le', args' in *. des.
  u. des_ifs; try congruence.
  - econs; ii; eauto.
  - inv MEM. inv MEM0. congruence.
Qed.

Lemma lubspec: forall
    x y z
    (LUB: lub x y = Some z)
  ,
    (<<LE: le' x z>>) /\ (<<LE: le' y z>>)
.
Proof.
  ii. unfold lub in *. des_ifs. unfold le'.
  esplits; ii; ss; bsimpl; ss; eauto.
Qed.

Lemma lubclosed: forall
    su0 args x y
    (PX: <<LE: le' su0 x>> /\ args' x args)
    (PY: <<LE: le' su0 y>> /\ args' y args)
    z
    (LUB: lub x y = Some z)
  ,
    <<PXY: le' su0 z /\ args' z args>>
.
Proof.
  ii. des. unfold lub in *. des_ifs. inv PX0. inv PY0. des. u in *.
  rewrite Forall_forall in *.
  esplits; eauto.
  { clear - LE LE0. r in LE. r in LE0. u in *. r. ii; ss. bsimpl. des. esplits; ii; ss.
    repeat spc LE. repeat spc LE0. bsimpl. eauto. }
  r; esplits; u; ii; bsimpl; ss; des; eauto.
  { repeat (spc H). repeat (spc H1). des. esplits; eauto. ii; des; eauto. }
  { rewrite Forall_forall in *. i. repeat (spc VALS0). repeat (spc VALS). des. esplits; eauto. ii; bsimpl; ss; des; eauto. }
  { inv MEM0. inv MEM.
    econs; ss.
    + ii; clarify. bsimpl. Nsimpl. des_safe; eauto.
      unfold memval', val' in *.
      hexpl SOUND; hexpl SOUND0; eauto.
      esplits; eauto. ii. ss. bsimpl. des; eauto.
    + ii. bsimpl. des; eauto.
  }
  { eapply WF; eauto with congruence. }
  { eapply WF0; eauto with congruence. }
Qed.

(* copied from Globalenvs.v - store_init_data *)
Definition loadable_init_data (m: mem) (ske: SkEnv.t) (b: block) (p: Z) (id: init_data): Prop :=
  match id with
  | Init_int8 n => Mem.load Mint8unsigned m b p = Some (Vint n)
  | Init_int16 n => Mem.load Mint16unsigned m b p = Some (Vint n)
  | Init_int32 n => Mem.load Mint32 m b p = Some (Vint n)
  | Init_int64 n => Mem.load Mint64 m b p = Some (Vlong n)
  | Init_float32 n => Mem.load Mfloat32 m b p = Some (Vsingle n)
  | Init_float64 n => Mem.load Mfloat64 m b p = Some (Vfloat n)
  | Init_addrof symb ofs =>
      match ske.(Genv.find_symbol) symb with
      | None => False
      | Some b' => Mem.load Mptr m b p = Some (Vptr b' ofs true)
      end
  | Init_space n => True
  end
.

Fixpoint loadable_init_data_list (m: mem) (ske: SkEnv.t) (b: block) (p: Z) (idl: list init_data): Prop :=
  match idl with
  | nil => True
  | id :: idl' => <<HD: loadable_init_data m ske b p id>> /\ <<TL: loadable_init_data_list m ske b (p + init_data_size id) idl'>>
  end.

(* TODO: Move to CoqlibC.v *)
Lemma app_eq_inv
      A
      (x0 x1 y0 y1: list A)
      (EQ: x0 ++ x1 = y0 ++ y1)
      (LEN: x0.(length) = y0.(length))
  :
    x0 = y0 /\ x1 = y1
.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify.
  exploit IHx0; eauto. i; des. clarify.
Qed.

(* copied from ValueAnalysis.v *)
Definition definitive_initializer (init: list init_data) : bool :=
  match init with
  | nil => false
  | Init_space _ :: nil => false
  | _ => true
  end.

Inductive skenv (su: Unreach.t) (m0: mem) (ske: SkEnv.t): Prop :=
| skenv_intro
    (PUB: su.(ge_nb) = ske.(Genv.genv_next))
    (RO: forall
        blk gv
        (GVAR: ske.(Genv.find_var_info) blk = Some gv)
        (* copied from ValueAnalysis - alloc_global *)
        (GRO: gv.(gvar_readonly))
        (GVOL: ~ gv.(gvar_volatile))
        (GDEF: definitive_initializer gv.(gvar_init))
      ,
        (* <<LABLE: loadable_init_data_list m0 ske blk 0 gv.(gvar_init)>> *)
        (<<PERM: forall
            ofs p
            (PERM: Mem.perm m0 blk ofs Max p)
          ,
            <<OFS: (0 <= ofs < init_data_list_size gv.(gvar_init))%Z>> /\ <<ORD: perm_order Readable p>>>>) /\
        (<<LABLE: Genv.load_store_init_data ske m0 blk 0 gv.(gvar_init)>>))
    (NB: Ple ske.(Genv.genv_next) m0.(Mem.nextblock))
.

(* Lemma loadbytes_loadable *)
(*       sk_link m0 blk ids lo *)
(*       (LO: (0 <= lo)%Z) *)
(*       (GDEF: definitive_initializer ids) *)
(*       (LOAD: Mem.loadbytes m0 blk lo (init_data_list_size ids) = *)
(*              Some (Genv.bytes_of_init_data_list (Genv.globalenv sk_link) ids)) *)
(*   : *)
(*     <<LOADABLE: loadable_init_data_list m0 (Genv.globalenv sk_link) blk lo ids>> *)
(* . *)
(* Proof. *)
(*   ginduction ids; ii; ss. *)
(*   eapply Mem.loadbytes_split in LOAD; cycle 1. *)
(*   { eapply init_data_size_pos. } *)
(*   { eapply init_data_list_size_pos. } *)
(*   des. ss. *)
(*   eapply app_eq_inv in LOAD1; cycle 1. *)
(*   { set (X := a). *)
(*     destruct a; ss; *)
(*       repeat (rewrite length_inj_bytes; ss; check_safe); *)
(*       repeat (rewrite encode_int_length; ss; check_safe); *)
(*       repeat (rewrite length_list_repeat; ss; check_safe); *)
(*       repeat (erewrite Mem.loadbytes_length; eauto; ss; check_safe). *)
(*     - des_ifs. *)
(*     { instantiate (1:= (init_data_size a)). *)
(*       ss. } *)
(*   exploit IHids; eauto. *)
(* Qed. *)

Notation "'prange' '#' hi" := (fun blk => Plt blk hi) (at level 50, no associativity (* , only parsing *)).
Notation "'prange' lo '#'" := (fun blk => Ple blk lo) (at level 50, no associativity (* , only parsing *)).
Notation "'prange' lo hi" := (fun blk => Ple lo blk /\ Plt blk hi) (at level 50, no associativity (* , only parsing *)).
(* Definition prange (hi: block): block -> Prop := *)
(*   fun blk => Plt blk hi *)
(* . *)

Definition hle' (x y: Unreach.t): Prop :=
  (<<PRIV: x.(unreach) <1= y.(unreach)>>)
  /\
  (<<OLD: y.(unreach) /1\ (prange # x.(nb)) <1= x.(unreach)>>)
  /\
  (<<NB: Ple x.(nb) y.(nb)>>)
  /\
  (<<GENB: x.(ge_nb) = y.(ge_nb)>>)
.

Global Program Instance hle_PreOrder: PreOrder hle'.
Next Obligation.
  rr. ii; des. esplits; eauto.
  - ii. des; ss.
  - xomega.
Qed.
Next Obligation.
  ii; des.
  unfold hle' in *. des.
  esplits; eauto.
  - ii. des; ss. eapply OLD0; eauto. esplits; eauto. eapply OLD; eauto. esplits; eauto. xomega.
  - xomega.
  - congruence.
Qed.

Lemma hle_le
      su0 su1
      (HLE: hle' su0 su1)
  :
    <<LE: le' su0 su1>>
.
Proof.
  rr. rr in HLE. des. esplits; eauto.
Qed.

Global Program Instance Unreach: Sound.class := {
  t := Unreach.t;
  le := le';
  hle := hle';
  get_greatest (su0: t) (args: Args.t) := greatest le' (fun su => <<LE: le' su0 su>> /\ su.(args') args);
  args := args';
  retv := retv';
  (* mle := Unreach.mle; *) (* TODO: How did `Program` guess the implementation of `mle` ???? *)
  skenv := skenv;
}
.
Next Obligation.
  eapply hle_le; et.
Qed.
Next Obligation.
  eapply mle_monotone; try apply MLE; eauto.
  r in LE. des; ss.
Qed.
Next Obligation.
  rr in GR0. rr in GR1. des.
  assert(le' su_gr0 su_gr1).
  { eauto. }
  assert(le' su_gr1 su_gr0).
  { eauto. }
  rr in H. rr in H0. des.
  eapply eta; ss.
  apply func_ext1; i.
  destruct (su_gr0 x0) eqn:T0, (su_gr1 x0) eqn:T1; ss.
  { rewrite PRIV0 in *; eauto. }
  { rewrite PRIV in *; eauto. }
  { inv PROP0. inv PROP1. des. inv MEM0. inv MEM. congruence. }
Qed.
(* Next Obligation. *)
(*   rr in GR. des. eapply MAX; eauto. (* econs; eauto. *) *)
(* Qed. *)
Next Obligation.
  rename INHAB into inhab. rename H into INHAB. rename H0 into INHAB0.
  eapply find_greatest with (lub:= lub); eauto.
  - typeclasses eauto.
  - ii. eapply lubsucc; eauto.
  - ii. eapply lubspec; eauto.
  - rr. destruct args0.
    eapply finite_pos_prop with (j:= Jpos) (fuel := m.(Mem.nextblock)); eauto.
    + ii. des. inv H0. inv H3. des; ss.
      inv MEM0. inv MEM.
      eapply Jpos_injective; eauto; cycle 1.
      { unfold le' in *. des. congruence. }
      { congruence. }
      ii. u in BOUND. u in BOUND0. destruct (x0 blk) eqn:T0, (x1 blk) eqn:T1; ss.
      { hexploit BOUND; eauto. i. r in H4. xomega. }
      { hexploit BOUND0; eauto. i. r in H4. xomega. }
    + ii. eapply Jpos_func.
    + i. exists (3 ^ (m.(Mem.nextblock)))%positive. i.
      eapply Jpos_bound; eauto.
  - ii. eapply lubclosed; try apply LUB; eauto.
Qed.
Next Obligation.
  rr in GR. des. eauto.
Qed.
Next Obligation.
  hexploit (@greatest_le_irr _ le' lub (fun su => args' su args0)); eauto.
  { typeclasses eauto. }
  { i. eapply lubsucc; eauto. }
  { i. eapply lubspec; eauto. }
  { i. eapply lubclosed; revgoals; eauto. }
  { eapply hle_le; et. }
Qed.
Next Obligation.
  set (Sk.load_skenv sk_link) as skenv.
  exists (mk (fun _ => false) skenv.(Genv.genv_next) m_init.(Mem.nextblock)).
  esplits; eauto.
  - rr; ss. esplits; eauto.
    + ii. esplits; eauto. unfold Genv.symbol_address in *. des_ifs. u in MEM. erewrite <- Genv.init_mem_genv_next; eauto.
      eapply Genv.genv_symb_range; eauto.
    + econs; eauto.
      * ii; ss. clarify. esplits; eauto.
        admit "this should hold. see Genv.initmem_inject".
      * ii; ss.
      * ss. u in *. erewrite <- Genv.init_mem_genv_next; eauto. folder. refl.
  - econs; eauto; cycle 1.
    { subst skenv. u in *. erewrite Genv.init_mem_genv_next; eauto. refl. }
    ii. u in *. subst skenv.
    hexploit Genv.init_mem_characterization; eauto. intro CHAR. des.
    hexploit Genv.init_mem_characterization_gen; eauto. intro X. r in X.
    unfold Genv.find_var_info in *. des_ifs.
    exploit (X blk (Gvar gv)); eauto. intro GEN; des.
    unfold Genv.perm_globvar in *. des_ifs.
    esplits; eauto.
Qed.
Next Obligation.
  inv LE.
  inv SKE. econs; eauto.
  congruence.
Qed.
Next Obligation.
  inv MLE.
  inv SKE. econs; eauto; cycle 1.
  { etrans; eauto. eauto with mem. }
  ii. exploit RO0; eauto. i; des.
  esplits; eauto.
  - ii. eapply PERM0; eauto. eapply PERM; eauto.
    { r. eapply Plt_Ple_trans; eauto.
      admit "ez".
    }
  - eapply Genv.load_store_init_data_invariant; try apply LABLE; eauto.
    unfold Genv.find_var_info in *. des_ifs.
    i. eapply Mem.load_unchanged_on_1; try apply RO; eauto.
    { admit "ez". }
    ii. exploit PERM0; eauto. i; des. inv ORD.
Qed.
Next Obligation.
  exploit SkEnv.project_spec_preserves_wf; eauto. intro WFSMALL.
  inv SKE. inv LE. inv WFSMALL.
  econs; eauto; swap 2 3.
  { congruence. }
  { etrans; eauto. rewrite NEXT. refl. }
  ii.
  unfold Genv.find_var_info in *. des_ifs.
  exploit DEFSYMB; eauto. i; des.
  destruct (classic (defs0 id)); cycle 1.
  { exploit SYMBDROP; eauto. i; des. clarify. }
  exploit SYMBKEEP; eauto. i; des. rewrite H in *. symmetry in H1.
  inv WF.
  exploit SYMBDEF0; eauto. intro DEF; des.
  exploit DEFKEEP; eauto.
  { eapply Genv.find_invert_symbol; eauto. }
  intro DEF2; des. rewrite DEF in *. clarify.
  exploit RO; eauto.
  { rewrite DEF. ss. }
  i; des.
  admit "raw admit: we need good_prog".
Qed.
Next Obligation.
  split; i; inv H; ss.
  - econs; eauto.
    i. eapply RO; eauto.
    unfold Genv.find_var_info in *. des_ifs_safe.
    unfold System.skenv in *.
    apply_all_once Genv_map_defs_def. des. des_ifs.
  - econs; eauto.
    i. eapply RO; eauto.
    unfold Genv.find_var_info in *. des_ifs_safe.
    unfold System.skenv.
    eapply_all_once Genv_map_defs_def_inv. rewrite Heq. ss.
Qed.
Next Obligation.
  set (CTX := Val.mi_normal).
  r in ARGS. des.
  exploit (@external_call_mem_inject_gen CTX ef skenv0 skenv0 (Args.vs args0) (Args.m args0) tr v_ret m_ret
                                         (to_inj su0 (Args.m args0).(Mem.nextblock)) (Args.m args0) (Args.vs args0)); eauto.
  { unfold to_inj. r. esplits; ii; ss; des_ifs; eauto.
    - exfalso. eapply WF; eauto. inv SKE. rewrite PUB. admit "ez".
    - exfalso. apply n; clear n. admit "ez".
  }
  { eapply to_inj_mem; eauto. }
  { clear - VALS. abstr (Args.vs args0) vs_arg.
    ginduction vs_arg; ii; ss. inv VALS. econs; eauto. destruct a; ss.
    unfold to_inj. r in H1. destruct b0; ss; cycle 1.
    { econs; eauto. }
    hexploit H1; ss; eauto.  i.
    econs; eauto.
    - des. des_ifs.
    - rewrite Ptrofs.add_zero. ss.
  }
  intro AX; des.
  exists (to_su f' su0.(ge_nb) m_ret.(Mem.nextblock)). unfold to_su.
  esplits; eauto.
  - r. s.
    unfold to_inj in AX4, AX5. r in AX4. r in AX5.
    esplits; eauto.
    + ii.
      inv MEM. exploit BOUND; eauto. i. des_ifs; cycle 1.
      { unfold Mem.valid_block in *. inv AX2. xomega. }
      destruct p0; ss.
      exploit AX5; eauto.
      { des_ifs. }
      i; des.
      ss.
    + ii. des. des_ifs.
      rename x0 into bb.
      apply NNPP. ii.
      exploit (AX4 bb bb); eauto; i; clarify.
      des_ifs. exfalso.
      eapply n. eapply Plt_Ple_trans; et. inv MEM. rewrite NB. xomega.
    + inv MEM. rewrite NB. inv AX2; ss.
  - r. s. esplits; eauto.
    + s. r. ii; ss. clarify. inv AX0. des_ifs.
      esplits; eauto.
      inv AX1. apply NNPP. ii. exploit mi_freeblocks; eauto. i; clarify.
    + s. econs; cycle 1; ss; eauto.
      { ii. des_ifs. }
      { inv MEM. etrans; eauto. inv AX2; ss. }
      { ii. clarify. exploit Mem.perm_valid_block; eauto. i. unfold Mem.valid_block in H. des_ifs_safe.
        inv AX1. inv mi_inj. destruct p0; ss. exploit mi_memval; eauto. intro MV.
        rewrite PTR in *. inv MV. inv H1. des_ifs_safe.
        exploit mi_freeblocks; eauto. i; clarify.
      }
    + ii. des_ifs. xomega.
  - econs; eauto.
    + ii; ss. eapply external_call_max_perm; try apply EXT; eauto.
    + ii; ss. eapply external_call_readonly; try apply EXT; eauto.
    + eapply Mem.unchanged_on_implies; eauto.
      unfold flip in *. ii; ss.
      rr. unfold to_inj. des_ifs.
Qed.


Local Opaque Z.mul Z.add Z.sub Z.div.
Local Transparent Mem.load.
Lemma mem'_load_val'
      su m0
      (MEM: mem' su m0)
      chunk blk ofs v
      (PUB: ~ su blk)
      (LOAD: Mem.load chunk m0 blk ofs = Some v)
  :
    <<VAL: val' su m0.(Mem.nextblock) v>>
.
Proof.
  inv MEM.
  unfold Mem.load in *. des_ifs. ii.
  hexploit SOUND; eauto.
  { admit "ez". }
  intro MV; des.
  unfold decode_val in *.
  Local Opaque Mem.getN.
  des_ifs; cbn in *; unfold Pos.to_nat in *; ss.
  -
    (* Local Opaque ZMap.get. *)
    ss. des_ifs.
    unfold proj_value in *. des_ifs.
    ss.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    clear_tac.
    Local Transparent Mem.getN. ss. clarify.
    specialize (SOUND blk ofs PUB).
    exploit MV; eauto.
  - ss. des_ifs.
  - Local Opaque Mem.getN.
    unfold proj_value in *. des_ifs.
    ss.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    clear_tac.
    Local Transparent Mem.getN. ss. clarify.
    specialize (SOUND blk ofs PUB).
    exploit MV; eauto.
Qed.
