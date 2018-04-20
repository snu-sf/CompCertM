Require Import LinkingC.
Require Import CoqlibC Maps Errors ASTC.
Require Import sflib.
Require Import RelationClasses.

Set Implicit Arguments.

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

