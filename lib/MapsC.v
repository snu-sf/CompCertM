Require Import LinkingC.
Require Import CoqlibC Maps Errors ASTC.
Require Import sflib.
Require Import RelationClasses.

Require Export Maps.

Set Implicit Arguments.

Local Open Scope o_monad_scope.



(* partial mapping *)
Definition PTree_filter_map A B (f: positive -> A -> option B) (m: PTree.t A): PTree.t B.
  admit "".
Qed.

About PTree.gmap.

Lemma PTree_filter_map_spec
      A B (f: positive -> A -> option B) i m
  :
      (PTree_filter_map f m) ! i = o_bind (m ! i) (f i)
.
Proof.
  admit "".
Qed.

About PTree.filter1.
Definition PTree_filter_key A (f: positive -> bool) (m: PTree.t A): PTree.t A.
  admit "".
Qed.

Lemma PTree_filter_key_spec
      A (f: positive -> bool) i (m: PTree.t A)
  :
      (PTree_filter_key f m) ! i = assertion (f i); m ! i
.
Proof.
  admit "".
Qed.


Lemma PTree_elements_map
      X Y (f: X -> Y) xm
  :
    map (update_snd f) (PTree.elements xm) = PTree.elements (PTree.map (fun _ => f) xm)
.
Proof.
  unfold PTree.elements.
  unfold PTree.map.
  generalize 1%positive.
  assert(LIST: [] = map (update_snd f) ([]: list (prod positive X))).
  { ss. }
  revert LIST.
  generalize ([]: list (prod positive X)) as lx.
  generalize ([]: list (prod positive Y)) as ly.
  induction xm; ii; ss.
  cbn in *.
  destruct o; ss; cycle 1.
  - erewrite IHxm1; ss. erewrite IHxm2; ss.
  - erewrite IHxm1; ss. erewrite IHxm2; ss.
Qed.

Lemma PTree_combine_map
      X Y
      (combx: option X -> option X -> option X)
      (comby: option Y -> option Y -> option Y)
      (f: X -> Y)
      (COMMUTE: True)
      xs0 xs1
  :
    PTree.map (fun _ => f) (PTree.combine combx xs0 xs1) =
    PTree.combine comby (PTree.map (fun _ => f) xs0) (PTree.map (fun _ => f) xs1)
.
Proof.
  unfold PTree.map.
  unfold PTree.combine.
Abort.

