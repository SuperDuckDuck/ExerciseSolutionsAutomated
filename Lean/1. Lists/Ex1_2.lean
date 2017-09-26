open decidable


def replace {a : Type}[decidable_eq a]:  a → a → list a → list a 
  | _ _ [] := []
  | old new (x::xs) := (if eq old x then new else x) :: replace old new xs

 
lemma helper1 {A : Type}[c: decidable_eq A] (old new : A) (xs ys : list A): replace old new (xs ++ ys) = replace old new xs ++ replace old new ys := 
list.rec_on xs
  (
   show replace old new ([] ++ ys) = replace old new [] ++ replace old new ys, from calc
     replace old new ([] ++ ys) = replace old new ys : by simp
     ... =  [] ++ replace old new ys : by simp
     ... = replace old new [] ++ replace old new ys : by simp[replace]
  )
  (
    take aa: A,
    take xs: list A,
    assume hyp:replace old new (xs ++ ys) = replace old new xs ++ replace old new ys,
    show  replace old new ((aa :: xs) ++ ys) = replace old new (aa::xs) ++ replace old new ys, from by_cases 
    (
      assume ct : old = aa,
      show replace old new ((aa :: xs) ++ ys) = replace old new (aa::xs) ++ replace old new ys , from calc
        replace old new ((aa :: xs) ++ ys) = replace old new (aa :: (xs ++ ys)) : by simp
        ... = new :: replace old new (xs ++ ys) :  by simp[ct,replace]
        ... = new :: (replace old new xs ++  replace old new ys) :  by simp[hyp]
        ... = replace old new (aa ::xs) ++  replace old new ys :  by simp[ct,replace]
    )
    (
      assume cf : ¬(old = aa),
      show replace old new ((aa :: xs) ++ ys) = replace old new (aa::xs) ++ replace old new ys, from calc
        replace old new ((aa :: xs) ++ ys) = aa :: replace old new (xs ++ ys) : by simp[cf,replace]
        ... =  aa :: replace old new xs ++ replace old new ys : by simp[hyp]
        ... = replace old new (aa :: xs) ++ replace old new ys : by simp[cf,replace]
    )
  )  

