Require Import List.
Import ListNotations.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.


Fixpoint snoc {X : Type}(ls : list X)(val : X) : list X :=
if ls is cons x xs then x :: snoc xs  val else [val].


Lemma snoc_app {X : Type}(val : X)(xs ys : list X): snoc (xs ++ ys) val = xs ++ snoc ys val.
Proof.
  elim : xs => [| x xs IH].
  + by [].
  + simpl. rewrite {} IH. by [].
Qed.

Theorem rev_cons {X : Type}(x : X)(xs : list X): rev (x :: xs) = snoc (rev xs) x.
Proof.
  elim : xs => [| val xs IH].
  + by []. 
  + simpl. rewrite snoc_app. simpl. rewrite <- app_assoc. by [].
Qed.
