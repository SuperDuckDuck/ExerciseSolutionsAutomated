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


Lemma helper2{A : Type} (P : A -> bool) (xs ys: list A): 
  exs P (xs ++ ys) = exs P xs || exs P ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. rewrite orb_assoc. reflexivity.
Qed.

Theorem quantifying_5 {A : Type}(P : A -> bool)(xs : list A) : 
  exs P (rev xs) = exs P xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite helper2. rewrite IHxs. rewrite orb_comm. 
    simpl exs. rewrite <- orb_assoc. rewrite orb_false_l. reflexivity.
Qed.


Theorem quantifying_6 {A : Type}(P Q : A -> bool) (xs : list A): 
  exs (fun x => P x || Q x) xs = exs P xs || exs Q xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite -> IHxs. repeat rewrite orb_assoc. 
    rewrite <- (orb_assoc (P a) (exs P xs) (Q a)). 
    rewrite (orb_comm (exs P xs) (Q a)). rewrite orb_assoc. reflexivity.
Qed.

Require Import Coq.Program.Basics.


Lemma negb_alls {A : Type}(P : A -> bool)(xs : list A): 
  negb (alls P xs)  = exs (compose negb P) xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite negb_andb. rewrite IHxs. reflexivity.
Qed.

Theorem quantifying_7 {A : Type}(P : A -> bool)(xs : list A):
  exs P xs  = negb ((alls (compose negb P )) xs ) .
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite  (negb_andb (compose negb P a) (alls (compose negb P) xs)).
    rewrite <- IHxs. unfold compose. rewrite negb_involutive. reflexivity.
Qed.


Fixpoint is_in {X : Type} `{EqDec X} (x : X)(ls : list X) : bool := 
match ls with 
| [] => false
| h::xs => if equiv_decb h x then true else is_in x xs
end.

Lemma quantifying_8 {X : Type} `{EqDec X} (a : X)(xs : list X): 
  is_in a xs = exs (fun (y:X) => equiv_decb y a) xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (a0 ==b a) eqn:?. 
    - reflexivity. 
    - simpl. rewrite IHxs. reflexivity.
Qed.

Fixpoint nodups {X : Type} `{EqDec X} (l : list X) : bool :=
match l with 
| [] => true
| x::xs =>  negb (is_in x xs) && nodups xs
end.

Fixpoint deldups {X : Type} `{EqDec X} (l : list X) : list X :=
match l with
| [] => []
| x::xs => let tmp := deldups xs in if is_in x tmp then tmp else x::tmp
end.

Lemma dups_1 {X : Type} `{EqDec X} (xs : list X): length (deldups xs) <= length xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (is_in a (deldups xs)).
    - auto.
    - simpl. apply le_n_S. exact IHxs.
Qed.

Lemma dups_2 {X : Type} `{EqDec X} (xs : list X): nodups (deldups xs) = true.
Proof.
  induction xs.
  + reflexivity.
  + simpl. destruct (is_in a (deldups xs))  eqn:?.
    - exact IHxs.
    - simpl. rewrite Heqb. simpl. exact IHxs.
Qed.

Lemma dups_3 : deldups (rev [1;2;3;2]) <> rev (deldups [1;2;3;2]).
Proof. 
  intro. simpl in H. discriminate.
Qed.
