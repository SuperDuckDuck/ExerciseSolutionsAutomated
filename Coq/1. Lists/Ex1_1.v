Require Import List.
Import ListNotations.
Open Scope list_scope.


Fixpoint snoc {A : Type} (ls: list A) (val : A) : list A := 
match ls with 
  | [] => [val]
  | x :: xs => x :: snoc xs val
end.

Theorem helper {A : Type} (xs ys : list A)(val : A) : snoc (xs ++ ys) val = xs ++ snoc ys val.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed. 


Theorem rev_cons {A : Type} (xs : list A) (x : A) : rev (x :: xs) = snoc (rev xs) x.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite helper.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.