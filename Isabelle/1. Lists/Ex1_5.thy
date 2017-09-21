theory Ex1_5
  imports Main 
begin 


  
primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs _ [] = 0"|
  "occurs val (x # xs) = (if x = val then 1 else 0) + occurs val xs"
  
corollary helper1 : "occurs a (xs @ ys) = occurs a xs + occurs a ys" by (induct xs , simp_all)  
  
lemma "occurs a xs = occurs a (rev xs)" by (induct xs , simp_all add : helper1)
    
lemma "occurs a xs \<le> length xs" by (induct xs, simp_all)
    
    
(*lemma "occurs a (map f xs) = occurs (f a) xs" quickcheck *)
    
lemma "a \<noteq> b \<Longrightarrow>let f = (\<lambda>x. if x = a then b else x) in occurs a (map f [a,b]) = occurs (f a) [a,b] \<Longrightarrow> False" by simp
    
lemma "occurs a (filter P xs) = occurs (a,True)( zip xs (map P xs))" by (induct xs ; simp)

lemma "occurs a (filter P xs) = (if P a then occurs a xs else 0 )" by (induct xs ; simp)
    
primrec remDups :: "'a list \<Rightarrow> 'a list" where
  "remDups [] = []"|
  "remDups (x#xs) = (if occurs x xs > 0 then remDups xs else x # remDups xs)"
  
lemma "occurs x (remDups xs) = (if occurs x xs \<ge> 1 then 1 else 0)" by (induct xs; simp)

primrec unique :: "'a list \<Rightarrow> bool" where 
  "unique [] = True"|
  "unique (x#xs) = ((occurs x xs = 0)  \<and> unique xs)"

lemma helper2 : "(occurs x xs = 0) = (occurs x (remDups xs) = 0)" by (induct xs; auto)
  
lemma "unique (remDups xs)" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"unique (remDups xs)"
  show ?case 
  proof (cases "occurs a xs")
    case 0
    assume a:"occurs a xs = 0"
    have "unique (remDups (a # xs)) = unique (a # remDups  xs) " by (simp add : a)
    also have "\<dots> = ((occurs a (remDups xs) = 0) \<and> unique (remDups xs))" by simp
    also have "\<dots> = ((occurs a  xs = 0) \<and> unique (remDups xs))" by (subst helper2, rule refl)
    finally show ?thesis using hyp by auto 
  next
    case (Suc nat)
    then show ?thesis using hyp by simp 
  qed
qed
  
  
  

    