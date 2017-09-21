open list 
open eq


def replace {a : Type}[decidable_eq a]:  a → a → list a → list a 
  | _ _ [] := []
  | old new (x::xs) := (if old = x then new else x) :: replace old new xs


theorem rep1 {A : Type} [decidable_eq A] (old new : A) (ls : list A): reverse (replace old new ls) = replace old new (reverse ls) :=
list.rec_on ls
  (show reverse (replace old new []) = replace old new (reverse []), from rfl)
  (
   take aa : A,
   take ls : list A,
   assume hyp1:reverse (replace old new ls) = replace old new (reverse ls)
   show reverse (replace old new (aa::ls)) = replace old new (reverse (aa::ls)), from  eq.cases_on aa old
     (
      assume hyp2:aa = old,
      
