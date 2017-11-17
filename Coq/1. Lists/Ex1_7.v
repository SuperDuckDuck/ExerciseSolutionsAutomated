Require Import List.
Import ListNotations.
Require Import EquivDec.
Require Export ListSet.
Require Import Bool.


Lemma natdec : forall x y : nat, {x = y}+{x <> y}.
Proof.
  decide equality.
Defined.

Fixpoint list_to_set {A : Type}(Aeq_dec : forall x y : A, {x = y}+{x <> y} )(ls : list A) : 
  set A := 
match ls with 
| [] => @empty_set A
|z::zs => set_add Aeq_dec z (list_to_set Aeq_dec zs)
end.

Eval compute in list_to_set natdec [1;2;1;4;5;2;1;3;3].

Lemma bla : @list_to_set nat natdec [2;2] =  set_add natdec 2 (empty_set nat).
Proof.
  reflexivity.
Qed.


Theorem allInSet {A : Type} (Aeq_dec : forall x y : A, {x = y}+{x <> y}) 
  (x : A) (ls : list A) : 
  In x ls -> @set_In A x (list_to_set Aeq_dec ls).
Proof.
  intros.
  induction ls.
  + inversion H.
  + simpl in *. destruct H. 
    - apply set_add_intro2. auto.
    - apply set_add_intro1. apply IHls. exact H. 
Qed.


Definition setEq {A : Type} (stA stB : set A)  := forall (val : A), set_In val stA <-> set_In val stB.

Notation "stA s= stB" := (setEq stA stB) (at level 11). 

Fixpoint list_union {X : Type} `{EqDec X}(ls ys : list X): list X := 
match ls with 
| [] => ys 
| x::xs => let tmp := list_union xs ys in 
  if (existsb (fun y => equiv_decb x y) tmp) then tmp else x :: tmp
end.

(*
Lemma existsb {A : Type} `{EqDec A}(a : A)(P : A -> bool)(ls : list A) : 
  existsb (fun y => a ==b y) ls = true -> P a = true -> existsb P ls = true.
Proof.
  intros.
  induction ls.
  + auto.
  + simpl. simpl in H0. rewrite orb_true_iff in H0. destruct H0.
    - destruct (a == a0) eqn:?. rewrite 
   destruct (P a0).
      * simpl. reflexivity.
      * simpl. apply IHls.  
      
*)
(*
Lemma existb_In_true {A : Type} (ls : list A)
*)
(*
Lemma existsb_list_union_distrib {A : Type}`{EqDec A}  (xs ys : list A) :
  forall (P : A -> bool), existsb P (list_union xs ys) = existsb P xs || existsb P ys.
Proof.
  induction xs.
  + reflexivity.
  + intro. simpl list_union. rewrite -> IHxs. 
    destruct (existsb (fun y : A => a ==b y) xs) eqn:?.
    - simpl. rewrite <- orb_assoc. rewrite IHxs.
  *)  

Lemma list_union_correct {A : Type} `{EqDec A} (Aeq_dec : forall x y : A, {x = y}+{x <> y})
  (xs ys : list A): 
  list_to_set Aeq_dec (list_union xs ys) s= set_union Aeq_dec (list_to_set Aeq_dec xs) (list_to_set Aeq_dec ys).
Proof.
  induction xs.
  + simpl. unfold "s=". intro. split.
    - intro. rewrite set_union_iff. right. exact H0.
    - intro. rewrite set_union_iff in H0. destruct H0. 
      * contradiction.
      * exact H0.
  + unfold "s=". intro. split.
    - intro. rewrite set_union_iff. simpl. simpl in H0. 
      destruct (existsb (fun y : A => a ==b y) (list_union xs ys)) eqn:?.
      * 






