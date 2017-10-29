Require Import List.
Import ListNotations.
Require Import EqNat.
Require Import Nat.
Require Import Bool.



Fixpoint first_pos {X : Type} (P : X -> bool) (l : list X) : nat := 
match l with 
| [] => 0
| x::xs => if P x then 0 else 1 + first_pos P xs
end.


Lemma test1  : first_pos (fun x =>  beq_nat x  3) [1;3;5;3;1] = 1.
Proof. reflexivity. Qed.

Lemma test2 : first_pos (fun x =>   4 <=? x) [1;3;5;7] = 2.
Proof. reflexivity. Qed.

Lemma test3 : first_pos (fun x => 2 <=? length x ) [[] ; [1;2] ; [3]] = 1.
Proof. reflexivity. Qed.



Theorem first_pos1 {X : Type} (P : X -> bool) (l : list X): 
  (forall (x:X), In x l ->  (P x)  = false) -> first_pos P l = length l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl. destruct (P a) eqn:?. 
    - pose proof (H a). rewrite Heqb in H0. exfalso.
      apply diff_true_false. apply H0. left. reflexivity. 
    - apply eq_S. apply IHl. intros. apply H. simpl. right. exact H0.
Qed.

Theorem first_pos2 {X : Type} (P : X -> bool) (l : list X): 
  forallb (fun x =>  negb (P x)) (firstn (first_pos P l) l) = true.
Proof.
  induction l.
  + reflexivity.
  + simpl. destruct (P a) eqn:?. 
    - simpl. reflexivity.
    - simpl. rewrite Heqb. simpl. exact IHl.
Qed.

Theorem first_pos3 {X : Type}(P Q : X -> bool)(l : list X): 
  first_pos (fun x => P x || Q x) l = min (first_pos P l) (first_pos Q l).
Proof.
  induction l.
  + reflexivity.
  + simpl. destruct (P a) eqn:? ; destruct (Q a) eqn:?.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl. apply eq_S. exact IHl.
Qed.
(*
Theorem first_pos4 {X : Type} : 
  ~(exists (F : nat -> nat -> nat),forall (X : Type), forall (P Q : X -> bool), forall (l : list X), 
    first_pos (fun x => P x && Q x) l = F (first_pos P l) (first_pos Q l)).
Proof.
  intro. 
  *)
  
  
Theorem first_pos5 {X : Type}(l : list X) (P Q : X -> bool): 
  (forall x ,( negb (P x) || Q x = true)) -> first_pos P l >= first_pos Q l.
Proof.
  intros.
  induction l.
  + simpl. apply le_n.
  + simpl. destruct (P a) eqn:?.
    - destruct (Q a) eqn:?. 
      * apply le_n.
      * pose proof (H a). rewrite Heqb in H0. rewrite Heqb0 in H0. simpl in H0.
        discriminate.
    - destruct (Q a) eqn:?. 
      * unfold ">=". apply PeanoNat.Nat.le_0_l. 
      * unfold ">=". apply le_n_S. unfold ">=" in IHl. exact IHl.
Qed.


Fixpoint count {X : Type} (P : X -> bool) (l : list X): nat :=
match l with 
| [] => 0
| x::xs => (if P x then 1 else 0) + count P xs
end.

Lemma helper {X : Type}(P : X -> bool) (xs ys : list X): count P (xs ++ ys) = 
  count P xs + count P ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. intuition.
Qed. 

Theorem count1 {X : Type} (P : X -> bool) (l : list X) : count P l = count P (rev l).
Proof.
  induction l.
  + reflexivity.
  + simpl. rewrite helper. simpl. destruct (P a).
    - rewrite IHl. intuition.
    - rewrite IHl. intuition.
Qed.
(*
Fixpoint fold {X Y: Type}(f : X -> Y -> Y)(ls : list X)(startVal : Y): Y :=
match ls with 
| [] => startVal 
| x::xs => fold f xs (f x startVal)
end.

Example foldTest1:  fold (fun x y => x + y) [1;1;1;1;1;5] 0 = 10. Proof. reflexivity. Qed.
Example foldTest2: fold (fun curr res => curr :: res) [1;2;3;4] [] = [4;3;2;1].
Proof. reflexivity. Qed.
*)




Theorem countFilterConnection {X : Type}(P : X -> bool)(l : list X):
  count P l = length (filter P l).
Proof.
  induction l.
  + reflexivity.
  + simpl. destruct (P a).
    - simpl. rewrite IHl. reflexivity.
    - auto.
Qed.


