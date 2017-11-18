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





lemma exs1_disproof  : ¬ (∀ (X: Type) (P Q : X -> bool) (xs : list X) , exs (λ x , P x && Q x) xs = exs P xs && exs Q xs) :=
  let tmp1 := exs (λ x , (λ y, y = 0) x && (λ y , y = 1) x) [0,1] in
  let tmp2 := (exs (λ y, y = 0) [0,1] && exs (λ y , y = 1) [0,1]) in
  assume hyp: ∀ (X: Type) (P Q : X -> bool) (xs : list X) , exs (λ x , P x && Q x) xs = exs P xs && exs Q xs,
  have a:tmp1 = tmp2 , by simp[tmp1,tmp2,hyp], 

  have b: (tmp1 = tmp2) = (ff = tt) , from calc
    (tmp1 = tmp2) = (ff = tmp2): by reflexivity 
    ... = (ff = tt) : by reflexivity,
  
  have c: (ff = tt) = false, by simp,
  have d: false ,
  begin
    rewrite ← c,
    rewrite ← b,
    exact a
  end, 
  show  false , from d

   
lemma exs_map_composition {X Y : Type}: forall (P : Y -> bool) (f : X -> Y) (xs : list X), exs P (map f xs) = exs (P ∘ f) xs 
| P f [] := rfl
| P f (x::xs) := 
  show  exs P (map f (x::xs)) = exs (P ∘ f) (x::xs), from calc
    exs P (map f (x::xs)) = exs P (f x :: map f xs) : by simp
    ... = P (f x) || exs P (map f xs) : by simp
    ... = P (f x) || exs (P ∘ f) xs : by simp[exs_map_composition]
    ... = (P ∘ f) x || exs (P ∘ f) xs : by simp
    ... = exs (P ∘ f) (x ::xs) : by simp


lemma orb_assoc (b1 b2 b3 : bool) : b1 || b2 || b3 = b1 || (b2 || b3) := by cases b1 ; simp 

lemma app_exs {X : Type} : forall (P : X -> bool )(xs ys :list X) , exs P (xs ++ ys) = (exs P xs || exs P ys)
| P [] ys := by simp
| P (x::xs) ys := 
  show exs P ((x::xs) ++ ys) = (exs P (x::xs) || exs P ys), from calc
    exs P ((x::xs) ++ ys) = exs P (x :: (xs ++ ys)) : by simp
    ... = P x || exs P (xs ++ ys) : by simp
    ... = P x || (exs P xs || exs P ys) : by simp[app_exs]
    ... = P x || exs P xs || exs P ys : by simp[orb_assoc]
    ... = exs P (x::xs) || exs P ys : by simp


lemma orb_comm (b1 b2 : bool) : (b1 || b2) = (b2 || b1) := by cases b1 ; cases b2 ; reflexivity 

lemma exs_rev {X : Type}: forall (P : X -> bool)(xs : list X), exs P (reverse xs) = exs P xs 
| P [] := rfl
| P (x::xs) := 
  show  exs P (reverse (x::xs)) = exs P (x::xs), from calc
    exs P (reverse (x::xs)) = exs P (reverse_core xs [] ++ [x]) : by simp[reverse,reverse_core, app_rev_core xs ([x])]
    ... = exs P (reverse xs ++ [x]) : by simp[reverse]
    ... = exs P (reverse xs) || exs P [x] : by simp[app_exs]
    ... = (exs P xs || exs P [x]) : by simp[exs_rev]
    ... = (exs P [x] || exs P xs) : by simp[orb_comm]
    ... = P x || exs P xs : by simp
    ... = exs P (x::xs) : by simp


lemma exs_term_eq {X : Type}: forall (P Q : X -> bool)(xs : list X), exs (λ x , P x || Q x) xs = exs P xs || exs Q xs
| P Q [] := rfl
| P Q (x::xs) :=
  show  exs (λ x , P x || Q x) (x::xs) = exs P (x::xs) || exs Q (x::xs), from calc
     exs (λ x , P x || Q x) (x::xs) =  (λ x , P x || Q x) x ||  exs (λ x , P x || Q x) xs : by simp
     ... =  (λ x , P x || Q x) x ||  exs P xs || exs Q xs : by simp[orb_assoc , exs_term_eq]
     ... = P x || Q x || exs P xs || exs Q xs : by simp
     ... = P x || exs P xs || Q x || exs Q xs : by simp[orb_comm, orb_assoc]
     ... = exs P (x::xs) || exs Q (x::xs) :by simp[orb_assoc]


lemma de_morgan_andb (b1 b2 : bool) : bnot (b1 && b2) = bnot b1 || bnot b2 := by cases b1 ; simp

lemma ex_as_all {X : Type}:forall (P : X -> bool)(xs :list X), exs P xs = bnot (alls (bnot ∘ P) xs)
| P [] := rfl
| P (x::xs) := 
  show exs P (x::xs) = bnot (alls (bnot ∘ P) (x::xs)), from calc
    exs P (x::xs) = P x || exs P xs : by simp
    ... = P x || bnot (alls (bnot ∘ P) xs) : by simp[ex_as_all]
    ... = bnot (bnot (P x) && alls (bnot ∘ P) xs) : by simp[de_morgan_andb]
    ... = bnot (alls (bnot ∘ P) (x::xs)) : by simp

