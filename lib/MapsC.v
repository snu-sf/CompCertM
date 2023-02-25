Require Import LinkingC.
Require Import CoqlibC ASTC.
From compcertr Require Import Maps Errors.
From compcertr Require Import sflib.
Require Import RelationClasses.

From compcertr Require Export Maps.

Set Implicit Arguments.

Local Open Scope o_monad_scope.

Definition compose_ptree' (A: Type) (l: option (PTree.tree' A)) (o: option A) (r: option (PTree.tree' A)) : option (PTree.tree' A) :=
  match l, o, r with
  | None, None, None => None
  | None, None, Some r' => Some (PTree.Node001 r')
  | None, Some o', None => Some (PTree.Node010 o')
  | None, Some o', Some r' => Some (PTree.Node011 o' r')
  | Some l', None, None => Some (PTree.Node100 l')
  | Some l', None, Some r' => Some (PTree.Node101 l' r')
  | Some l', Some o', None => Some (PTree.Node110 l' o')
  | Some l', Some o', Some r' => Some (PTree.Node111 l' o' r')
  end.

Fixpoint xfilter_map' (A B : Type) (f : positive -> A -> option B) (m : PTree.tree' A) (i : positive)
         {struct m} : option (PTree.tree' B) :=
  match m with
  | PTree.Node001 r => compose_ptree' None None (xfilter_map' f r (xI i))
  | PTree.Node010 o => compose_ptree' None (f (PTree.prev i) o) None
  | PTree.Node011 o r => compose_ptree' None (f (PTree.prev i) o) (xfilter_map' f r (xI i))
  | PTree.Node100 l => compose_ptree' (xfilter_map' f l (xO i)) None None
  | PTree.Node101 l r => compose_ptree' (xfilter_map' f l (xO i)) None (xfilter_map' f r (xI i))
  | PTree.Node110 l o => compose_ptree' (xfilter_map' f l (xO i)) (f (PTree.prev i) o) None
  | PTree.Node111 l o r => compose_ptree' (xfilter_map' f l (xO i)) (f (PTree.prev i) o) (xfilter_map' f r (xI i))
  end.

Definition xfilter_map (A B : Type) (f : positive -> A -> option B) (m : PTree.tree A) (i : positive) : PTree.tree B :=
  match m with
  | PTree.Empty => PTree.Empty
  | PTree.Nodes t =>
      match xfilter_map' f t i with
      | Some t' => PTree.Nodes t'
      | None => PTree.Empty
      end
  end.

Lemma xfilter_map_get:
  forall (A B: Type) (f: positive -> A -> option B) (i j : positive) (m: PTree.t A),
    PTree.get i (xfilter_map f m j) = o_bind (PTree.get i m) (f (PTree.prev (PTree.prev_append i j))).
Proof.
  intros. destruct m as [| m]; auto. cbn. revert m j.
  induction i; intros.
  - simpl.
    destruct m; simpl.
    + specialize (IHi m (xI j)). desf.
    + desf.
    + specialize (IHi m (xI j)). desf.
    + specialize (IHi m (xO j)). desf. simpl in Heq. inv Heq. auto.
    + generalize (IHi m1 (xO j)). generalize (IHi m2 (xI j)). desf.
    + specialize (IHi m (xO j)). desf; simpl in Heq; desf.
    + generalize (IHi m1 (xO j)). generalize (IHi m2 (xI j)).
      desf; simpl in *; desf.
  - simpl.
    destruct m; simpl.
    + specialize (IHi m (xI j)). desf.
    + desf.
    + specialize (IHi m (xI j)). desf.
    + specialize (IHi m (xO j)). desf. simpl in Heq. inv Heq. auto.
    + generalize (IHi m1 (xO j)). generalize (IHi m2 (xI j)). desf.
    + specialize (IHi m (xO j)). desf; simpl in Heq; desf.
    + generalize (IHi m1 (xO j)). generalize (IHi m2 (xI j)).
      desf; simpl in *; desf.
  - simpl. destruct m; simpl; try (desf; fail).
    + destruct (xfilter_map' f m (xO j)); auto.
    + destruct (xfilter_map' f m1 (xO j)); destruct (xfilter_map' f m2 (xI j)); auto.
    + destruct (f (PTree.prev j) a) eqn: O; destruct (xfilter_map' f m (xO j)); auto.
    + destruct (f (PTree.prev j) a) eqn: O;
        destruct (xfilter_map' f m1 (xO j)); destruct (xfilter_map' f m2 (xI j)); auto.
Qed.

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
  destruct xm; ii; ss. revert ly lx LIST p.
  induction t;
    ii; simpl; try rewrite LIST; try erewrite IHt; eauto.
  - erewrite IHt1; eauto. erewrite IHt2; eauto.
  - erewrite IHt1; eauto. cbn. erewrite IHt2; eauto.
Qed.
