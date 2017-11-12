Require Import List.
Import ListNotations.
Require Import EquivDec.
Require Import Coq.MSets.MSetWeakList.

Fixpoint list_union {X : Type} `{EqDec X}(ls ys : list X): list X := 
match ls with 
| [] => ys 
| x::xs => let tmp := list_union xs ys in 
  if (existsb (fun y => equiv_decb x y) tmp) then tmp else x :: tmp
end.

