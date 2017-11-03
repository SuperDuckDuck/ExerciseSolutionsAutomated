Require Import List.
Import ListNotations.


Fixpoint sum (ls : list nat): nat := 
match ls with 
| [] => 0 
| x::xs => x + sum xs
end.

Fixpoint flatten {A : Type}(ls : list (list A)): list A :=
match ls with 
| [] => []
| x::xs => x ++ flatten xs 
end.

Example sum1: sum [2;4;8] = 14.
Proof. reflexivity. Qed.

Example flatten1: flatten [[2;3];[4;5];[7;9]] = [2;3;4;5;7;9].
Proof. reflexivity. Qed.



Lemma sumflat1 {X : Type}(xs : list (list X)): length (flatten xs) = sum (map (@length X) xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite <- IHxs. rewrite app_length. reflexivity.
Qed.


Lemma sum_append (xs ys : list nat): sum (xs ++ ys) = sum xs + sum ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. intuition.
Qed.


