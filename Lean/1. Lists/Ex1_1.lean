open list 



def snoc {a : Type}: list a → a → list a 
  | [] val := [val]
  | (x::xs) val := x :: snoc xs val

@[simp]
lemma helper {A : Type} (xs ys : list A)(val : A): snoc (xs ++ ys) val = xs ++ snoc ys val := 
list.rec_on xs
  (show snoc ([] ++ ys) val = [] ++ snoc ys val, by simp)
  (
   take aa: A,
   take xs: list A,
   assume hyp: snoc (xs ++ ys) val = xs ++ snoc ys val,
   show  snoc ((aa :: xs) ++ ys) val =  (aa :: xs)  ++ snoc ys val , from calc
     snoc ((aa :: xs) ++ ys) val = snoc (aa :: (xs ++ ys)) val : by simp
     ... = aa :: snoc (xs ++ ys) val : by simp[snoc]
     ... = aa :: (xs ++ snoc ys val) : by simp[hyp]
     ... = aa :: xs ++ snoc ys val : by simp
  )
    

lemma rev_cons {A : Type}(ls : list A)(val : A) : reverse (val :: ls) = snoc (reverse ls) val :=
list.rec_on ls
 (show reverse (val :: []) = snoc (reverse []) val, by simp[snoc])
 (
  take aa : A,
  take ls : list A,
  assume hyp: reverse (val :: ls) = snoc (reverse ls) val,
  show reverse (val :: aa :: ls) = snoc (reverse (aa :: ls)) val, from calc
    reverse (val :: aa :: ls) = reverse ls ++ [aa , val] : by simp
    ... =  reverse ls ++ snoc [aa] val : by simp[snoc]
    ... =  snoc (reverse ls ++ [aa]) val : by simp[hyp]
    ... =  snoc (reverse (aa :: ls)) val : by simp
 )
