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



lemma helper2{A:Type}  : ∀ (xs ys : list A), reverse_core xs ys  = reverse_core xs [] ++ ys
| [] ys := rfl
| (a::xs) ys := 
  show reverse_core (a::xs) ys = reverse_core (a::xs) [] ++ ys , from calc 
    reverse_core (a::xs) ys = reverse_core xs [] ++ (a::ys) : by simp[ reverse_core , helper2 xs (a::ys)]
    ... = reverse_core xs [] ++ [a] ++ ys : by simp
    ... = reverse_core xs [a] ++ ys : by simp[helper2 xs ([a])]
    ... = reverse_core (a::xs) [] ++ ys : by simp[reverse_core]

  

lemma helper3 {A : Type} (xs ys : list A): reverse (xs ++ ys) =  reverse ys ++ reverse xs := 
list.rec_on xs 
  ( 
    show (reverse ([] ++ ys)) = (reverse ys ++ reverse []) , from calc
      reverse ([] ++ ys) = reverse ys : by simp
      ... = reverse ys ++ reverse [] : by simp[reverse, reverse_core]
  )
  (
   assume aa: A,
   assume xs : list A ,
   assume hyp: reverse (xs ++ ys) =  reverse ys ++ reverse xs ,
   show reverse ((aa :: xs ) ++ ys) = reverse ys ++ reverse (aa:: xs) , from calc
     reverse ((aa:: xs) ++ys) = reverse_core (xs ++ ys) [] ++ [aa] : by simp[reverse, reverse_core , helper2 (xs ++ ys) ([aa])]
     ... = reverse (xs ++ ys) ++ [aa] : by simp[reverse]
     ... = reverse ys ++ reverse xs ++ [aa] : by simp[hyp]
     ... = reverse ys ++ reverse (aa::xs) : by simp[reverse, reverse_core , helper2 xs ([aa])]
  )



lemma rev_1  {a : Type}[decidable_eq a] (x y : a)(ls : list a): reverse (replace x y ls) = replace x y(reverse ls) :=
list.rec_on ls
  (
    show reverse (replace x y []) = replace x y (reverse []), from rfl
  )
  (
    assume aa : a,
    assume ls : list a,
    let tmp := (if eq x aa then y else aa) in
    assume hyp:reverse (replace x y ls) = replace x y(reverse ls),
    show reverse (replace x y (aa :: ls)) = replace x y(reverse (aa :: ls)), from calc
      reverse (replace x y (aa :: ls)) = reverse (tmp :: replace x y ls) : by simp[replace]
      ... = reverse (replace x y ls) ++ [tmp] : by simp[reverse, reverse_core , helper2 (replace x y ls) ([tmp])]
      ... = replace x y (reverse ls) ++ [tmp] :by simp[hyp]
      ... = replace x y (reverse ls) ++ replace x y [aa] : by simp[replace]
      ... = replace x y (reverse  ls ++ [aa]) :by simp[helper1 x y (reverse ls) ([aa])]
      ... = replace x y (reverse (aa::ls)) : by simp[reverse, reverse_core , helper2 ls ([aa])]
  )

