open list 

def snoc {a : Type}: list a → a → list a 
  | [] val := [val]
  | (x::xs) val := x :: snoc xs val


lemma helper1 {A : Type} (xs ys : list A)(val : A): snoc (xs ++ ys) val = xs ++ snoc ys val := 
list.rec_on  xs
  (show snoc ([] ++ ys) val = [] ++ snoc ys val, by simp)
  (
   assume aa: A,
   assume xs: list A,
   assume hyp: snoc (xs ++ ys) val = xs ++ snoc ys val,
   show  snoc ((aa :: xs) ++ ys) val =  (aa :: xs)  ++ snoc ys val , from calc
     snoc ((aa :: xs) ++ ys) val = snoc (aa :: (xs ++ ys)) val : by simp
     ... = aa :: snoc (xs ++ ys) val : by simp[snoc]
     ... = aa :: (xs ++ snoc ys val) : by simp[hyp]
     ... = aa :: xs ++ snoc ys val : by simp
  )

lemma helper1_2 {A:Type}:∀(xs ys:list A), ∀  (val: A) ,  snoc (xs ++ ys) val = xs ++ snoc ys val 
  |[] ys val := rfl
  | (a::xs) ys val := 
  show snoc ((a::xs) ++ ys) val = (a :: xs) ++ snoc ys val ,from calc
    snoc ((a::xs) ++ ys) val  = snoc (a :: (xs ++ ys)) val : by simp
    ... = a :: snoc (xs ++ ys) val : by simp[snoc]
    ... = a :: (xs ++ snoc ys val) : by simp[helper1_2]
    ... = (a :: xs) ++ snoc ys val : by simp
    

lemma helper2 {A : Type}(ls : list A) : ∀ (xs : list A) ,  reverse_core ls xs = reverse_core ls [] ++ xs :=
list.rec_on ls
  ( assume xs : list A,
    show ( reverse_core [] xs = reverse_core [] [] ++ xs), from rfl
  )
  (
   assume aa:A,
   assume ls:list A,
   assume hyp: ∀(xs : list A), reverse_core ls xs = reverse_core ls [] ++ xs,
   assume xs : list A,
   show reverse_core (aa::ls) xs = reverse_core (aa::ls) [] ++ xs, from calc 
     reverse_core (aa::ls) xs =  reverse_core ls (aa :: xs) : by simp[reverse_core]
     ... = reverse_core ls [] ++ (aa :: xs) : by simp[hyp (aa :: xs)]
     ... = reverse_core ls [] ++ ([aa] ++ xs) : by simp
     ... = reverse_core ls [] ++ [aa] ++ xs : by simp
     ... = reverse_core ls [aa] ++ xs : by simp[hyp ([aa])]
     ... = reverse_core (aa::ls) [] ++ xs :by simp[reverse_core]
  )
  
lemma helper2_2 {A : Type} : ∀ (ls xs : list A) ,  reverse_core ls xs = reverse_core ls [] ++ xs 
| [] xs := rfl
| (a::ls) xs := 
  show reverse_core (a::ls) xs = reverse_core (a::ls) [] ++ xs , from calc
    reverse_core (a::ls) xs = reverse_core ls (a::xs) : by simp[reverse_core]
    ... = reverse_core ls [] ++ (a::xs) : by simp[helper2_2 ls (a::xs)]
    ... = reverse_core ls [] ++ ([a] ++ xs) : by simp
    ... = reverse_core ls [] ++ [a] ++ xs :by simp
    ... = reverse_core ls [a] ++ xs : by simp[helper2_2 ls ([a])]
    ... = reverse_core (a::ls) [] ++xs : by simp[reverse_core] 

theorem rev_cons {A : Type}(ls : list A)(val : A) : reverse (val :: ls) = snoc (reverse ls) val :=
list.rec_on ls
 (show reverse (val :: []) = snoc (reverse []) val, from rfl)
 (
  assume aa : A,
  assume ls : list A,
  assume hyp: reverse (val :: ls) = snoc (reverse ls) val,
  show reverse (val :: aa :: ls) = snoc (reverse (aa :: ls)) val, from calc
    reverse (val :: aa :: ls) = reverse_core (val :: aa :: ls) [] :  by simp[reverse]
    ... = reverse_core (aa::ls) [val] : by simp[reverse_core]
    ... = reverse_core (aa::ls) [] ++ [val] : by simp[helper2 (aa::ls) ([val])] 
    ... = reverse (aa::ls) ++ [val] : by simp[reverse]
    ... = reverse (aa::ls) ++ snoc [] val : by simp[snoc]
    ... = snoc (reverse (aa::ls)) val : by simp[(helper1 (reverse (aa::ls)) (nil : list A) val).symm]
 )

theorem rev_cons_2 {A : Type}: ∀ (ls : list A)(val : A), reverse (val :: ls) = snoc (reverse ls) val 
| [] val := rfl
| (aa::ls) val :=
  show reverse (val :: aa ::ls) = snoc (reverse (aa::ls)) val , from calc
    reverse (val :: aa :: ls) = reverse_core (val :: aa :: ls) [] : by simp[reverse]
    ... = reverse_core (aa::ls) [] ++ snoc [] val : by simp[reverse_core, helper2 (aa::ls) ([val]), snoc]
    ... = snoc (reverse (aa::ls)) val : by simp[reverse, (helper1 (reverse_core (aa::ls) nil) nil val).symm]
    
