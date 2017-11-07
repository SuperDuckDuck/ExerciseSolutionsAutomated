Require Import List.
Import ListNotations.
Require Import Nat.
Require Import PeanoNat.



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


Lemma flatten_append {X : Type}(xs ys : list (list X)): 
  flatten (xs ++ ys) = flatten xs ++ flatten ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs.
    intuition.
Qed.

Lemma flatten2 {A : Type} (xs : list (list A)): 
  flatten (map (@rev A)  (rev xs)) = rev (flatten xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl.  rewrite (rev_app_distr a (flatten xs)) . rewrite <- IHxs.
    rewrite map_app. simpl. rewrite flatten_append. simpl. rewrite app_nil_r.
    reflexivity.
Qed.

Lemma flatten3 {X : Type} (xs : list (list X)): flatten (rev (map (@rev X) xs)) = rev (flatten xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite rev_app_distr. rewrite <- IHxs. rewrite flatten_append. simpl.
    rewrite app_nil_r. reflexivity.
Qed.

Lemma flatten4 {X : Type} (xs : list (list X)) (P : X -> bool) : 
  forallb (forallb P) xs = forallb P (flatten xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite forallb_app. rewrite IHxs. reflexivity.
Qed.

Lemma flatten5_disproof : let ls := [[1;2];[3;4]] in flatten (rev ls) <> flatten ls.
Proof.
  intro. unfold ls. intro. simpl in H. discriminate.
Qed.

Lemma sum2 (xs : list nat) : sum (rev xs) = sum xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite sum_append. rewrite IHxs. simpl. rewrite <- plus_n_O. intuition.
Qed.

Lemma helper1 {X : Type} (val : X)(ls : list X): val :: ls = [val] ++ ls.
Proof.
  induction ls.
  + reflexivity.
  + simpl. reflexivity.
Qed.
(*
Lemma helper2 (n m : nat): leb (S n) (S m) = leb n m.
Proof.  reflexivity. Qed.

Lemma helper3 (n m p : nat): leb n m = true -> leb n (p + m) = true.
Proof.
  intro. 
  induction p.
  + intuition.
  + rewrite plus_Sn_m.
  Require Import PeanoNat. 
*)
Lemma list_all (xs : list nat) : forallb (fun x => leb 1 x) xs = true ->  leb (length xs) (sum xs) = true.
Proof.
  intro. 
  induction xs.
  + reflexivity.
  + rewrite Nat.leb_le. simpl length. simpl sum. rewrite helper1 in H. rewrite forallb_app in H.
    rewrite Bool.andb_true_iff in H .
    destruct H. apply IHxs in H0. 
    destruct a.
    - discriminate.
    - rewrite plus_Sn_m. apply le_n_S. rewrite Nat.leb_le in H0. rewrite H0. intuition.
Qed.



    
Fixpoint list_exists {X : Type} (P : X -> bool)(ls : list X): bool :=
match ls with 
| [] => false
| x::xs => P x || list_exists P xs
end.

Example list_exists_1 : list_exists (fun x => x <? 3) [4;3;7] = false.
Proof. reflexivity. Qed.


Example list_exists_2 : list_exists (fun x => x <? 4) [4;3;7] = true.
Proof. reflexivity. Qed.

Lemma list_exists_append {X : Type} (P : X -> bool) (xs ys : list X): 
  list_exists P (xs++ys) = ( (list_exists P xs) || (list_exists P ys))%bool .
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. rewrite <- Bool.orb_assoc. reflexivity.
Qed.
  
Lemma list_exists_3 {X :Type} (P : X -> bool) (xs : list (list X)): 
  list_exists (list_exists P) xs = list_exists P (flatten xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite list_exists_append. rewrite IHxs. reflexivity.
Qed.

Definition list_exists2 {X : Type} (P : X -> bool) (xs : list X): bool :=
negb (forallb  (fun x => negb (P x)) xs) .



Theorem list_exists_eq_list_exists2 {X : Type} (P : X -> bool) (xs : list X):
  list_exists P xs = list_exists2 P xs.
Proof.
  induction xs.
  + reflexivity.
  + unfold list_exists2. simpl. rewrite IHxs. rewrite Bool.negb_andb. rewrite Bool.negb_involutive.
    reflexivity.
Qed.
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  