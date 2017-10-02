open decidable
open list

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
    assume aa: A,
    assume xs: list A,
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

lemma helper2 {A : Type} (xs ys : list A): reverse (xs ++ ys) = reverse ys ++ reverse xs := 
list.rec_on xs 
  ( 
    show (reverse ([] ++ ys)) = (reverse ys ++ reverse []) , from calc
      reverse ([] ++ ys) = reverse ys : by simp
      ... = reverse ys ++ reverse [] : by simp
  )
  (
    take aa:A,
    take xs: list A,
    assume hyp: reverse (xs ++ ys) = reverse ys ++ reverse xs, 
    show reverse ((aa :: xs) ++ ys) = reverse ys ++ reverse (aa :: xs) , from calc
      reverse ((aa :: xs) ++ ys) = reverse (aa :: xs ++ ys) : by simp
      ... = reverse (xs ++ ys) ++ [aa] : by simp
      ... = reverse ys ++ reverse xs  ++ [aa] : by simp[hyp]
      ... = reverse ys ++ reverse (aa :: xs) : by simp
  )



lemma rev_1  {a : Type}[decidable_eq a] (x y : a)(ls : list a): reverse (replace x y ls) = replace x y(reverse ls) :=
list.rec_on ls
  (
    show reverse (replace x y []) = replace x y (reverse []), from rfl
  )
  (
   
    assume aa : a,
    assume ls : list a,
    let tmp := (if eq x aa then y else x) in
    assume hyp:reverse (replace x y ls) = replace x y(reverse ls),
    show reverse (replace x y (aa :: ls)) = replace x y(reverse (aa :: ls)), from calc
      reverse (replace x y (aa :: ls)) = reverse ( (if eq x aa then y else x) :: replace x y ls) : by simp[replace]
      ... = reverse (replace x y ls) ++ [(if eq x aa then y else x)] : by simp[reverse]
      ... = 
    
      
  )
