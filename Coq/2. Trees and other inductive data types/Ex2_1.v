Require Import List.
Import ListNotations.


Inductive tree (X : Type) :=
| Leaf : X -> tree X
| Node : tree X -> X -> tree X -> tree X.


Arguments Leaf {X} _.
Arguments Node {X} _ _ _.

Fixpoint preOrder {X : Type} (t : tree X): list X := 
match t with 
| Leaf val => [val]
| Node l val r => val :: preOrder l ++ preOrder r
end.

Fixpoint postOrder {X  : Type} (t : tree X) : list X :=
match t with 
| Leaf val => [val]
| Node l val r => postOrder l ++ postOrder r ++ [val]
end.

Fixpoint inOrder {X : Type}(t : tree X) : list X :=
match t with 
| Leaf val => [val]
| Node l val r => inOrder l ++ val :: inOrder r 
end.

Fixpoint mirror {X : Type} (t : tree X) : tree X :=
match t with 
| Node l val r => Node (mirror r) val (mirror l)
| tr => tr
end.

Lemma pre_pre_counterExample : 
  let t := Node (Leaf 2) 1 (Leaf 3) in preOrder (mirror t) <> rev (preOrder t).
Proof.
  intro.
  intro.
  unfold t in H. discriminate.
Qed.

Lemma pre_post {X : Type} (t : tree X): preOrder (mirror t) = rev (postOrder t).
Proof.
  induction t.
  + reflexivity.
  + simpl. rewrite rev_app_distr. rewrite rev_app_distr.
    rewrite IHt1. simpl. rewrite IHt2. reflexivity.
Qed.

Lemma post_pre {X : Type} (t : tree X): postOrder (mirror t) = rev (preOrder t).
Proof.
  induction t.
  + reflexivity.
  + simpl. rewrite rev_app_distr. rewrite IHt1. rewrite IHt2. intuition.
Qed.


Lemma pre_in_counterExample: 
  let t := Node (Leaf 2) 1 (Leaf 3) in preOrder (mirror t) <> rev (inOrder t).
Proof.
  intro.
  intro.
  unfold t in H.
  discriminate.
Qed.

Lemma in_pre_counterexample : 
  let t := Node (Leaf 2) 1 (Leaf 3) in inOrder (mirror t) <> rev (preOrder t).
Proof.
  intro.
  intro. 
  unfold t in H.
  discriminate.
Qed.

Lemma post_post_counterexample :
  let t := Node (Leaf 2) 1 (Leaf 3) in postOrder (mirror t) <> rev (postOrder t).
Proof.
  intro.
  intro.
  unfold t in H.
  discriminate.
Qed.

Lemma post_in_counterexample :
  let t := Node (Leaf 2) 1 (Leaf 3) in postOrder (mirror t) <> rev (inOrder t).
Proof.
  intro.
  intro.
  discriminate.
Qed.

Lemma in_post_counterexample : 
  let  t := Node (Leaf 2) 1 (Leaf 3) in inOrder (mirror t) <> rev (postOrder t).
Proof.
  intro.
  intro.
  discriminate.
Qed.

Lemma in_in {X : Type} (t : tree X):
  inOrder (mirror t) = rev (inOrder t).
Proof.
  induction t.
  + reflexivity.
  + simpl. rewrite rev_app_distr. simpl. rewrite <- IHt1. rewrite <- IHt2. 
    rewrite <- app_assoc. reflexivity.
Qed.




