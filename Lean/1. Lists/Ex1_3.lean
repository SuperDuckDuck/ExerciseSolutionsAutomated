open list 
open bool

@[simp]
def alls {X:Type } : (X -> bool) -> list X -> bool 
| _ [] := tt
| P (x::xs) := P x && alls P xs

@[simp]
def exs {X:Type} : (X -> bool) -> list X -> bool
| _ [] := ff
| P (x::xs) := P x || exs P xs




lemma andb_comm  : forall (a b : bool), a && b = b && a 
| tt tt := rfl
| tt ff := rfl
| ff tt := rfl
| ff ff := rfl
  

lemma andb_assoc (a b c: bool) :  a && b && c = a && (b && c) := by cases a; cases b; cases c; simp


lemma alls1 {X:Type}: forall (P Q : X -> bool) (xs : list X),
  alls (λ x ,  P x && Q x) xs = (alls P xs && alls Q xs)
| P Q [] := rfl
| P Q (x::xs) := 
  show alls (λ x ,  P x && Q x) (x::xs) = (alls P (x::xs) && alls Q (x::xs)), from calc 
    alls (λ x ,  P x && Q x) (x::xs) =  (P x && Q x && alls (λ x ,  P x && Q x) xs) : by simp[alls]
    ... = (P x && Q x &&  (alls P xs && alls Q xs)) : by simp[alls1 P Q xs]
    ... = (Q x && P x  && (alls P xs && alls Q xs)) :by simp[andb_comm]
    ... = (Q x && P x && alls P xs && alls Q xs): by simp[andb_assoc]
    ... =  (Q x && (P x &&  alls P xs) && alls Q xs) : by simp[andb_assoc]
    ... =  (Q x && alls P (x::xs) && alls Q xs): by simp[alls]
    ... = (alls P (x::xs) && Q x && alls Q xs) : by simp[andb_comm]
    ... = (alls P (x::xs) && (Q x && alls Q xs)) :by simp[andb_assoc]
    ... = (alls P (x::xs) && alls Q (x::xs)) : by simp [alls]


lemma app_rev_core {X:Type}: forall (xs ys : list X), reverse_core xs ys = reverse_core xs [] ++ ys
| [] ys := rfl
| (x::xs) ys := 
  show reverse_core (x::xs) ys = reverse_core (x::xs) [] ++ ys, from calc
    reverse_core (x::xs) ys = reverse_core xs (x::ys) : by simp[reverse_core]
    ... = reverse_core xs [] ++ (x::ys) : by simp[app_rev_core xs (x::ys)] 
    ... = reverse_core xs [] ++ [x] ++ ys : by simp
    ... = reverse_core (x::xs) [] ++ ys : by simp[app_rev_core xs ([x]) ,reverse_core]



lemma app_alls {X:Type} : forall (P : X -> bool) (xs ys : list X), alls P (xs ++ ys) = (alls P xs && alls P ys) 
| P [] ys  := by simp
| P (x::xs) ys :=
  show alls P ((x::xs) ++ ys) = (alls P (x::xs) && alls P ys), from calc
    alls P(x::xs ++ ys) =  P x && alls P (xs ++ ys) : by simp
    ... = P x && alls P xs && alls P ys : by simp[app_alls P xs ys, andb_assoc]
    ... = alls P (x::xs) && alls P ys : by simp
 
lemma alls2 {X:Type} : forall (P : X -> bool) (xs :list X), alls P (reverse xs) = alls P  xs
| P [] := rfl
| P (x::xs) := 
  show alls P (reverse (x::xs)) = alls P  (x::xs) , from calc
     alls P (reverse (x::xs)) =  alls P (reverse xs ++ [x]) : by simp[reverse , reverse_core , app_rev_core xs ([x])] 
     ... = alls P (reverse xs) && alls P [x] : by simp[app_alls]
     ... = alls P [x] && alls P xs  : by simp[alls2, andb_comm]
     ... = alls P (x::xs) : by simp

lemma exs1_disproof  : ¬ (∀ (X: Type) (P Q : X -> bool) (xs : list X) , exs (λ x , P x && Q x) xs = exs P xs && exs Q xs)
