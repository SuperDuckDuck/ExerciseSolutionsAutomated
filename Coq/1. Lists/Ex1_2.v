Require Import EquivDec.
Require Import List.
Import ListNotations.

Open Scope list_scope.


Fixpoint replace {A : Type} `{EqDec A} (old new : A)(ls : list A) : list A := 
match ls with 
  | [] => []
  | x::xs => (if equiv_dec x old then new else x) :: replace old new xs
end.



Lemma helper1 {A : Type}`{EqDec A}(xs ys : list A)(old new :A): 
  replace old new (xs ++ ys) = replace old new xs ++ replace old new ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs.
    reflexivity.
Qed.
  

Theorem replace_1 {A : Type} `{EqDec A}(x y : A)(zs : list A) : 
  rev (replace x y zs) = replace x y (rev zs).
Proof.
  induction zs.
  - reflexivity.
  - simpl. 
    rewrite IHzs. rewrite helper1.
    reflexivity.
Qed.


Theorem replace_2 : 
  replace 2 1 (replace 1 2 [1;2;2;1]) = replace 1 2 (replace 2 1 [1;2;2;1]) 
  -> False. 
  Proof. 
  intro.
  simpl in H.
  discriminate.
Qed.

Theorem replace_3  : 
  replace 2 3 (replace 1 2 [2] ) = replace 1 3 [2] -> False.
Proof.
  intro.
  discriminate.
Qed.
  
Fixpoint del1 {A : Type} `{EqDec A} (val : A) (ls : list A) : list A := 
match ls with 
  | [] => []
  | x::xs => if equiv_dec x val then xs else x :: del1 val xs
end.

Fixpoint delall {A : Type} `{EqDec A} (val : A) (ls : list A) : list A :=
match ls with 
  | [] => []
  | x::xs => if equiv_decb x val then delall val xs else x :: delall val xs
end.

Theorem del_1 {A : Type} `{EqDec A} (val : A)(ls : list A): 
  del1 val (delall val ls) = delall val ls.
Proof.
  induction ls.
  + reflexivity.
  + simpl. 
    destruct (a ==b val) eqn:?.
    - apply IHls.
    - simpl del1.
      unfold equiv_decb in Heqb.
      destruct (a == val).
      * discriminate.
      * rewrite IHls.
        reflexivity.
Qed.

Theorem del_2 {A : Type} `{EqDec A} (val : A) (ls : list A): 
  delall val (delall val ls) = delall val ls.
Proof.
  induction ls.
  + reflexivity.
  + destruct (a ==b val) eqn:?.
    - simpl delall at 2.
      simpl delall at 4.
      rewrite Heqb.
      apply IHls.
    - simpl. rewrite Heqb.
      simpl. rewrite Heqb.
      rewrite IHls.
      reflexivity.
Qed.


Theorem del_3 {A : Type} `{EqDec A} (val : A) (ls : list A):
  delall val (del1 val ls) = delall val ls.
Proof.
  induction ls.
  + reflexivity.
  + destruct (a ==b val) eqn:?.
    - simpl. rewrite Heqb.
      unfold equiv_decb in Heqb.
      destruct (a == val).
      * reflexivity.
      * discriminate.
    - simpl. assert (H2 := Heqb). unfold equiv_decb in Heqb. 
      destruct (a == val). 
      * discriminate.
      * simpl. rewrite H2. rewrite IHls. 
        reflexivity.
Qed.

Theorem del_4 {A : Type} `{EqDec A} (x y : A) (ls : list A) :
  del1 x (del1 y ls) = del1 y (del1 x ls).
Proof.
  induction ls.
  + reflexivity.
  + simpl. 
    - destruct (equiv_dec a y).
      * destruct (equiv_dec a x).
        rewrite e0 in e.
        clear IHls. 
        induction ls.
        ++ reflexivity.
        ++ simpl del1.
           destruct (equiv_dec a0 x).
           -- destruct (equiv_dec a0 y).
              ** reflexivity.
              ** rewrite <- e in c.
                 contradiction.
           -- destruct (equiv_dec a0 y).
              +++ rewrite <- e in e1.
                  contradiction.
              +++ rewrite IHls.
                  reflexivity.
        ++ simpl. destruct (equiv_dec a y).
           -- reflexivity.
           -- contradiction.
      * destruct (equiv_dec a x).
        simpl. destruct (equiv_dec a x).
        ++ reflexivity.
        ++ contradiction.
        ++ simpl. destruct (equiv_dec a x).
           -- contradiction.
           -- destruct (equiv_dec a y).
              ** contradiction.
              ** rewrite IHls.
                 reflexivity.
Qed.
(*
Lemma helper2 {A : Type} `{EqDec A} (x : A) (ls : list A):
  delall x ls = del1 x (delall x ls).
Proof.
  induction ls.
  + reflexivity.
  + simpl. destruct (equiv_decb a x) eqn:?.
    apply IHls. simpl. unfold "==b" in Heqb. destruct (equiv_dec a x).
    - discriminate.
    - rewrite IHls at 1. reflexivity.
Qed.
*)
Theorem del_5 {A : Type} `{EqDec A}(x y : A)(ls : list A) : 
  delall x (del1 y ls) = del1 y (delall x ls).
Proof.
  induction ls.
  + reflexivity.
  + simpl. unfold "==b". destruct (equiv_dec a x) eqn:?.
    - destruct (equiv_dec a y).
      * assert (e1 := e0). rewrite e in e0.
        clear IHls. induction ls. 
        ++ reflexivity.
        ++ simpl. unfold "==b". destruct (equiv_dec a0 x).
              -- apply IHls.
              -- simpl. destruct (equiv_dec a0 y).
                 ** rewrite <- e0 in e2. contradiction.
                 ** rewrite IHls at 1. reflexivity.
      * simpl. unfold "==b". rewrite Heqs. apply IHls.
    - simpl. destruct (equiv_dec a y).  
      * reflexivity.
      * simpl. unfold "==b". rewrite Heqs. rewrite IHls. reflexivity.
Qed.

Theorem del_6 {A : Type} `{EqDec A} (x y : A)(zs : list A): 
  delall x (delall y zs) = delall y (delall x zs).
Proof.
  induction zs.
  + reflexivity.
  + simpl. destruct (equiv_decb a y) eqn:? ; destruct (equiv_decb a x) eqn:?.
    - apply IHzs.
    - simpl. rewrite Heqb. apply IHzs.
    - simpl. rewrite Heqb0. apply IHzs.
    - simpl. rewrite Heqb. rewrite Heqb0.
      rewrite IHzs. reflexivity.
Qed.

