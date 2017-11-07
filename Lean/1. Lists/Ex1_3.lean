open list 
open bool

def alls {X:Type } : (X -> bool) -> list X -> bool 
| _ [] := true 
| P (x::xs) := P x && alls P xs

def exs {X:Type} : (X -> bool) -> list X -> bool
| _ [] := false
| P (x::xs) := P x || exs P xs


#check tt

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
    ... = (alls P (x::xs) && (Q x && alls Q xs)) :by simp[andb_comm , andb_assoc]
    ... = (alls P (x::xs) && alls Q (x::xs)) : by simp [alls]
