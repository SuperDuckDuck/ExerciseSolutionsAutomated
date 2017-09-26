Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.
Variable A : Type.
Compute  (eqb 3 4).




Fixpoint alls (P : A -> bool)(ls : list A): bool := 
match ls with 
  | [] => true
  | x::xs => P x && alls P xs
end.

Fixpoint exs (P : A -> bool)(ls : list A): bool := 
match ls with 
  | [] => false
  | x::xs => P x || exs P xs
end.

Lemma quantifying_1 (P Q : A -> bool)(xs : list A) : 
  alls (fun x => (andb (P x)  (Q x))) xs  =  (andb (alls P xs) (alls Q xs)).
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (P a); destruct (Q a).
    - simpl. apply IHxs.
    - simpl. rewrite andb_comm. reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Lemma helper1 (P : A -> bool)(xs ys : list A): 
  alls P (xs ++ ys) = alls P xs  && alls P ys .
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (P a).
    - simpl. apply IHxs.
    - reflexivity.
Qed.


Theorem quantifying_2 (P : A -> bool)(xs : list A):
  alls P (rev xs) = alls P xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite helper1. simpl. rewrite andb_comm. 
    rewrite (andb_comm (P a)  true). rewrite IHxs. reflexivity.
Qed.

Theorem quantifying_3: @exs nat (fun x => @eq nat x  3::nat) [1;2] = false. 
 
    
    
    
    