Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.
Require Import EquivDec.


Compute  (eqb 3 4).




Fixpoint alls {A : Type} (P : A -> bool)(ls : list A): bool := 
match ls with 
  | [] => true
  | x::xs => P x && alls P xs
end.

Fixpoint exs {A : Type}(P : A -> bool)(ls : list A): bool := 
match ls with 
  | [] => false
  | x::xs => P x || exs P xs
end.

Lemma quantifying_1 {A : Type}(P Q : A -> bool)(xs : list A) : 
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

Lemma helper1  {A : Type}(P : A -> bool)(xs ys : list A): 
  alls P (xs ++ ys) = alls P xs  && alls P ys .
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (P a).
    - simpl. apply IHxs.
    - reflexivity.
Qed.


Theorem quantifying_2 {A :Type}(P : A -> bool)(xs : list A):
  alls P (rev xs) = alls P xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite helper1. simpl. rewrite andb_comm. 
    rewrite (andb_comm (P a)  true). rewrite IHxs. reflexivity.
Qed.


Theorem quantifying_3: exs (fun x =>  equiv_decb x  3) [1;2] = false.
Proof.
  reflexivity.
Qed.

Theorem quantifying_4 {A B: Type} (P : B -> bool)(f : A -> B)(xs : list A): 
  exs P (map f xs) = exs (fun x => P (f x)) xs. 
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. reflexivity.
Qed.


 
 
    
    
    
    