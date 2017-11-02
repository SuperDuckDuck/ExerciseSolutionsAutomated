Require Import List.
Import ListNotations.
Require Import EquivDec.
Require Import Bool.
Require Import Nat.


Fixpoint occurs {X : Type} `{EqDec X} (a : X)(ls : list X): nat := 
match ls with 
| [] => 0
| x::xs => (if equiv_dec x a then 1 else 0 ) + occurs a xs
end.


Lemma helper {X : Type} `{EqDec X} (a : X)(xs ys : list X): occurs a (xs ++ ys) = occurs a xs + occurs a ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. intuition.
Qed.


Lemma occurs_1 {X : Type} `{EqDec X} (a : X)(ls : list X): 
  occurs a ls = occurs a (rev ls).
Proof.
  induction ls.
  + reflexivity.
  + simpl. rewrite helper. rewrite <- IHls. simpl. rewrite <- plus_n_O. 
    intuition.
Qed.

Lemma occurs_2 {X : Type} `{EqDec X} (a : X)(ls : list X): 
  occurs a ls <= length ls.
Proof.
  induction ls.
  + reflexivity.
  + simpl. destruct (equiv_dec a0 a); intuition.
Qed.

Lemma occurs_3_disproof : 
  let func := (fun x => x + 1) in occurs 1 (map func [1;2]) <> occurs (func 1) [1;2].
Proof.
  intros. intro.  simpl in H. discriminate.
Qed.

Lemma occurs_4 {X : Type} `{EqDec X} (a : X)(P : X -> bool)(xs : list X): occurs a (filter P xs) =  occurs true (map (fun x => P x && equiv_decb a x) xs).
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (P a0).
    - unfold "==b". simpl. destruct ( a == a0). 
      * simpl. destruct (equiv_dec a0 a).
        ++ rewrite IHxs. reflexivity.
        ++ rewrite e in c. destruct c. reflexivity.
      * simpl. destruct (equiv_dec a0 a). 
        ++ rewrite e in c. destruct c. reflexivity.
        ++ rewrite IHxs. reflexivity.
    - unfold "==b". simpl. rewrite IHxs. reflexivity.
Qed.

Fixpoint remDups {X : Type} `{EqDec X} (ls : list X) : list X :=
match ls with 
| [] => []
| x::xs => let tmp := remDups xs in if eqb (occurs x tmp) 0  then  x :: tmp else tmp
end.

Lemma helper2 {X : Type} `{EqDec X} (a x : X) (xs : list X): 
  x === a  -> eqb (occurs x xs) 0 = eqb (occurs a xs) 0.
Proof.
  intro.
  induction xs. reflexivity.
  simpl. destruct (equiv_dec a0 x) eqn:?.
  + simpl. rewrite <- e in H0.
    destruct (occurs x xs =? 0).
    - destruct (occurs a xs =? 0). 
      * destruct (equiv_dec a0 a). simpl. reflexivity.
        ++ destruct c. exact H0. 
      * destruct (equiv_dec a0 a).
        ++ simpl. reflexivity. 
        ++ simpl. destruct c. exact H0.
    - destruct (equiv_dec a0 a).
      * simpl. reflexivity.
      * simpl. destruct c. intuition.
  + simpl. destruct (equiv_dec a0 a).
    - simpl. rewrite <- e in H0 . destruct c. rewrite H0. reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed.

Lemma helper3 {X : Type} `{EqDec X} (xs : list X): 
  forall (x:X), eqb (occurs x (remDups xs)) 0 = eqb (occurs x xs) 0.
Proof.
  induction xs.
  + reflexivity.
  + intro. simpl. destruct (occurs a (remDups xs) =? 0) eqn:?.
    - simpl. destruct (equiv_dec a x) eqn:?.
      * simpl. reflexivity.
      * simpl. rewrite IHxs. reflexivity.
    - destruct (equiv_dec a x) eqn:?. 
      * simpl. rewrite IHxs. rewrite IHxs in Heqb. rewrite <- (helper2 a x) in Heqb.
        ++ rewrite Heqb. reflexivity.
        ++ rewrite e. reflexivity.
      * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma occurs_5 {X : Type} `{EqDec X} (x : X)(xs : list X): occurs x (remDups xs) = 
if eqb (occurs x xs) 0 then 0 else 1.
Proof. 
  induction xs.
  + reflexivity.
  + simpl. rewrite helper3. destruct (equiv_dec a x) eqn:?.
    - simpl. destruct (occurs a  xs =? 0) eqn:?. 
      * simpl. rewrite Heqs. rewrite  IHxs. rewrite (helper2 a x). 
        ++ rewrite Heqb. reflexivity.
        ++ rewrite e. reflexivity.
      * rewrite IHxs. rewrite (helper2 a x xs). 
        ++ rewrite Heqb. reflexivity.
        ++ rewrite e. reflexivity.
    - simpl. destruct (occurs a xs) eqn:?.
      * simpl. destruct (equiv_dec a x).
        ++ discriminate. 
        ++ simpl. rewrite IHxs. reflexivity. 
      * simpl. rewrite IHxs. reflexivity.
Qed.