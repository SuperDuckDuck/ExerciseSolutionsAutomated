theory Ex1_1
  imports Main 
begin 
  
  
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where 
  "snoc [] val = [val]"|
  "snoc (x # xs) val = x # snoc xs val"

theorem helper : "snoc (xs @ ys) x = xs @ snoc ys x" by (induct xs , auto)
  
theorem rev_cons : "rev (x # xs) = snoc (rev xs) x" by (induct xs , auto simp add : helper)
    
    
    