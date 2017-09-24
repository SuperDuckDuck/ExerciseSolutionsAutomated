theory Ex1_2
  imports Main 
begin 
  
primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "replace _ _ [] = []"|
  "replace old new (x # xs) = (if x = old then new else x) # replace old new xs"
  
theorem helper1 : "replace x y (xs @ ys) =  replace x y xs @ replace x y ys" by (induct xs, auto)
    
theorem "rev (replace x y zs) = replace x y (rev zs)" by (induct zs, auto simp add : helper1)
    
(* theorem "replace x y (replace u v zs) = replace u v (replace x y zs)" quickcheck *)
    
theorem "replace  a\<^sub>1 a\<^sub>2 (replace a\<^sub>2  a\<^sub>1 [a\<^sub>1]) = replace a\<^sub>2  a\<^sub>1 (replace  a\<^sub>1 a\<^sub>2 [a\<^sub>1]) \<Longrightarrow> a\<^sub>1 \<noteq> a\<^sub>2  \<Longrightarrow> False " by simp
    
(* theorem "replace y z (replace x y zs) = replace x z zs" quickcheck *)
    
theorem "replace y z (replace x y [y]) = replace x z [y] \<Longrightarrow> x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z \<Longrightarrow> False" by auto
    

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "del1 _ [] = []"|
  "del1 val (x # xs) = (if val = x then xs else x # del1 val xs)"
  
primrec delall:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "delall _ [] = []"|
  "delall val (x#xs) = (if val = x then delall val xs else x # delall val xs)"
  
theorem helper2 : "del1 x (delall x xs) = delall x xs" by (induct xs, auto)
    
theorem "delall x (delall x xs) = delall x xs" by (induct xs , auto)
    
theorem "delall x (del1 x xs) = delall x xs" by (induct xs , auto)
    
theorem "del1 x (del1  y zs) = del1 y (del1 x zs)" by (induct zs , auto)
    
theorem "delall x (del1 y zs) = del1 y (delall x zs)" 
proof (induct zs)
  case Nil
  then show ?case by simp
next
  case (Cons a zs)
  assume a:"delall x (del1 y zs) = del1 y (delall x zs)" 
  show ?case by (metis a del1.simps(2) delall.simps(2) helper2)    
qed
(*without metis*)

theorem "delall x (del1 y zs) = del1 y (delall x zs)" 
proof (induct zs)
  case Nil
  then show ?case by simp
next
  case (Cons a zs)
  assume a:"delall x (del1 y zs) = del1 y (delall x zs)" 
  show ?case 
  proof (cases "y = a"; cases "x = a")
    assume h1:"y = a"
       and h2:"x = a"
    hence tmp:"y = x" by simp
    have "delall x (del1 y (a # zs)) = delall x zs" by (simp add : h1)
    also have "\<dots> = del1 x (delall x zs)" by (simp add : helper2)
    also have "\<dots> = del1 x (delall x (a#zs))" by (simp add : h2)
    finally show ?thesis using a by (simp add : tmp)
  next
    assume h1:"y = a"
       and h2:"x \<noteq> a"
    with a show ?thesis by simp
  next 
    assume h1:"y \<noteq> a"
       and h2:"x = a"
    with a show ?thesis by simp
  next
    assume h1:"y \<noteq> a"
       and h2:"x \<noteq> a"
    with a show ?thesis by simp
  qed
qed
         
theorem "delall x (delall y zs) = delall y (delall x zs)" by (induct zs , auto)

(* theorem "del1 y (replace x y xs) = del1 x xs" quickcheck *)
    
theorem "del1 y (replace x y [x , x]) = del1 x [x , x] \<Longrightarrow> x \<noteq> y \<Longrightarrow> False" by simp
    
(*theorem "delall y (replace x y xs) = delall x xs" quickcheck *)
    
theorem "delall y (replace x y [y])  = delall x [y] \<Longrightarrow> x \<noteq> y \<Longrightarrow> False" by simp
    
theorem "replace x y (delall x zs) = delall x zs" by (induct zs, auto)
    
(*theorem "replace x y (delall z zs) = delall z (replace x y zs)" quickcheck *)    
    
theorem "replace x y (delall x [x]) = delall x (replace x y [x]) \<Longrightarrow> y \<noteq> x \<Longrightarrow> False" by simp
    
(*theorem "rev (del1 x xs) = del1 x (rev xs)" quickcheck *)   
    
theorem "ls = [x , y , x, y] \<Longrightarrow> rev (del1 x ls) = del1 x (rev ls) \<Longrightarrow> x \<noteq> y \<Longrightarrow> False" by simp 

theorem helper3 : "delall x (xs @ ys) = delall x xs @ delall x ys" by (induct xs , auto)
    
theorem "rev (delall x xs) = delall x (rev xs)" by (induct xs, auto simp add : helper3)
    
    