Require Import LinkingC.
Require Import CoqlibC Maps Errors ASTC.
Require Import sflib.
Require Import RelationClasses.

Require Export Maps.

Set Implicit Arguments.

Local Open Scope o_monad_scope.

Fixpoint xfilter_map (A B : Type) (f : positive -> A -> option B) (m : PTree.t A) (i : positive)
         {struct m} : PTree.t B :=
  match m with
  | PTree.Leaf => PTree.Leaf
  | PTree.Node l o r => PTree.Node (xfilter_map f l (xO i))
                                  (match o with None => None | Some x => (f (PTree.prev i) x) end)
                                  (xfilter_map f r (xI i))
  end.

Lemma xfilter_map_get:
  forall (A B: Type) (f: positive -> A -> option B) (i j : positive) (m: PTree.t A),
    PTree.get i (xfilter_map f m j) = o_bind (PTree.get i m) (f (PTree.prev (PTree.prev_append i j))).
Proof. induction i; intros; destruct m; simpl; auto. des_ifs. Qed.

(* partial mapping *)
Definition PTree_filter_map A B (f: positive -> A -> option B) (m: PTree.t A): PTree.t B := xfilter_map f m 1.

About PTree.gmap.

Lemma PTree_filter_map_spec
      A B (f: positive -> A -> option B) i m:
      (PTree_filter_map f m) ! i = o_bind (m ! i) (f i).
Proof.
  unfold PTree_filter_map. rewrite xfilter_map_get. f_equal. rewrite PTree.prev_append_prev. ss.
Qed.

About PTree.filter1.
Definition PTree_filter_key A (f: positive -> bool) (m: PTree.t A): PTree.t A :=
  PTree_filter_map (fun k v => if f k then Some v else None) m.

Lemma PTree_filter_key_spec
      A (f: positive -> bool) i (m: PTree.t A):
      (PTree_filter_key f m) ! i = assertion (f i); m ! i.
Proof.
  unfold PTree_filter_key. rewrite PTree_filter_map_spec. uo. des_ifs.
Qed.

Lemma PTree_elements_map
      X Y (f: X -> Y) xm:
    map (update_snd f) (PTree.elements xm) = PTree.elements (PTree.map (fun _ => f) xm).
Proof.
  unfold PTree.elements. unfold PTree.map. generalize 1%positive.
  assert(LIST: [] = map (update_snd f) ([]: list (prod positive X))) by ss.
  revert LIST. generalize ([]: list (prod positive X)) as lx. generalize ([]: list (prod positive Y)) as ly.
  induction xm; ii; ss. cbn in *. destruct o; ss; erewrite IHxm1; ss; erewrite IHxm2; ss.
Qed.
