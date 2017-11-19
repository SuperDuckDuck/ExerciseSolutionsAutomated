Require Import List.
Import ListNotations.
Require Import EquivDec.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.


Fixpoint replace {A : Type} `{EqDec A} (old new : A) (ls : list A) : list A :=
match ls with 
| [] => []
| x::xs => (if equiv_dec old x then new else x) :: replace old new xs
end.


Lemma replace_app {A : Type} `{EqDec A} (old new : A)(xs ys : list A):
  replace old new (xs ++ ys) =  replace old new xs ++ replace old new ys.
Proof.
  elim : xs.
  + by [].
  + move => a l Hyp.
    simpl. rewrite {} Hyp. by [].
Qed.

Theorem rev_replace {A : Type} `{EqDec A} (old new : A)(ls:list A):
  rev (replace old new ls) = replace old new (rev ls).
Proof.
  elim : ls.
  + by [].
  + move => a l Hyp.
    simpl. rewrite replace_app . by[rewrite Hyp].
Qed.
