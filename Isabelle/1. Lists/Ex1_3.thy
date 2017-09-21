theory Ex1_3
  imports Main 
begin 
  
primrec alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "alls _ [] = True"|
  "alls P (x # xs) = (P x \<and> alls P xs)"
  
primrec exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "exs _ [] = False"|
  "exs P (x # xs) = (P x \<or> exs P xs)"
  
  
lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)" by (induct xs , auto)
    
lemma helper : "alls P (xs @ ys) = (alls P xs \<and>  alls P ys)" by (induct xs ; simp)    
    
lemma "alls  P (rev xs) = alls P xs" by (induct xs, auto simp add : helper)
    
(* lemma "exs (\<lambda>x . P x \<and> Q x) xs = (exs  P xs \<and> exs Q xs)" quickcheck *)
    
lemma "P a  \<Longrightarrow> P b = False \<Longrightarrow> Q b \<Longrightarrow> Q a = False  \<Longrightarrow> a \<noteq> b \<Longrightarrow> exs (\<lambda>x. P x \<and> Q x) [a ,b] = (exs P [a,b] \<and> exs Q [a,b]) \<Longrightarrow> False" by simp
    
lemma "exs P (map f xs) = exs (P o f) xs " by (induct xs; simp)

lemma helper2 : "exs P (xs @ ys) = (exs P xs \<or> exs P ys)" by (induct xs, auto)    
    
lemma "exs P (rev xs) = exs P xs" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume a:"exs P (rev xs) = exs P xs" 
  have "exs P (rev (a # xs)) = exs P (rev xs @ [a])" by simp
  also have "\<dots> = (exs P (rev xs) \<or> exs P [a])" by (simp add : helper2)
  also have "\<dots> = (exs P xs \<or> exs P [a])"  by (simp add : a)
  finally show ?case by auto
qed
  
lemma "exs (\<lambda>x . P x \<or> Q x) xs = exs P xs \<or> exs Q xs"  by (induct xs; auto)
    
    
lemma "exs P xs = (\<not> (alls (\<lambda>x . \<not> (P x)) xs))" by (induct  xs, simp_all)

primrec is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "is_in _ []= False "|
  "is_in val (x # xs) = ((val = x) \<or> is_in val xs) "
  
lemma "is_in a xs = exs (\<lambda>x . x = a) xs" by (induct xs, auto)
    
primrec nodups :: "'a list \<Rightarrow> bool" where 
  "nodups [] = True"|
  "nodups (x#xs) = ((\<not>(is_in x xs))  \<and> nodups xs)"
  
primrec deldups :: "'a list \<Rightarrow> 'a list" where
  "deldups [] = []"|
  "deldups (x#xs) = (if is_in x xs  then deldups xs else x # deldups xs)"
 
lemma "length (deldups xs) \<le> length xs" by (induct xs, simp_all)

lemma helper3 : "\<not> (is_in x xs) \<Longrightarrow> \<not> (is_in x (deldups xs))" by (induct xs, simp_all)    
    
lemma "nodups (deldups xs)" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"nodups (deldups xs)"
  show ?case 
  proof (cases "is_in a xs")
    case True
    assume a:"is_in a xs"
    show ?thesis using hyp a by auto
  next
    case False
    assume a:"\<not> is_in a xs"
    have "nodups (deldups (a # xs)) = nodups (a # deldups (xs))" using a by simp
    also have "\<dots> = ((\<not>(is_in a (deldups xs))) \<and>  nodups (deldups xs))" by (simp only : nodups.simps)
    also have "\<dots> = ((\<not>(is_in a (deldups xs))) \<and> True )" using hyp by simp
    also have "\<dots> = (True \<and> True)" using helper3 and a by simp
    finally show ?thesis using helper3 and a and hyp by simp
  qed
qed
    
(* lemma "deldups (rev xs) = rev (deldups xs)" quickcheck *)
  
lemma "let ls = [x,y,x,x] in deldups (rev ls) = rev (deldups ls) \<Longrightarrow> x \<noteq> y \<Longrightarrow> False " by simp
  