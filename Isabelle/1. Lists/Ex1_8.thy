theory Ex1_8 
  imports Main 
begin 
  
  
primrec ListSum :: "nat list \<Rightarrow> nat " where 
  "ListSum [] = 0"|
  "ListSum (x#xs) = x + ListSum xs"

lemma helper : "ListSum (xs @ ys) = ListSum xs + ListSum ys" by (induct xs; simp)  
 
theorem "2 * ListSum [0 ..<n+1] = n * (n + 1)" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume hyp:" 2 * ListSum [0..<n + 1] = n * (n + 1)"  
  then show ?case by (auto simp add : helper)
qed
  
theorem "ListSum (replicate n a) = n * a" using helper by (induct n; simp)
    
primrec ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where 
  "ListSumTAux [] res = res"|
  "ListSumTAux (x#xs) res = ListSumTAux xs (res + x)"
    
definition ListSumT :: "nat list \<Rightarrow> nat " where 
  "ListSumT ls = ListSumTAux ls 0"

lemma "ListSumTAux xs n  = n + ListSumTAux xs 0" 
proof (induct xs arbitrary : n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  note hyp =  this
  have " n + ListSumTAux (a # xs) 0  = n + ListSumTAux xs a"  by (simp)
  also have "\<dots> =  n + a + ListSumTAux xs 0" by (subst hyp, simp)
  finally have tmp:" n + ListSumTAux (a # xs) 0  = n + a + ListSumTAux xs 0" by assumption
      
  have "ListSumTAux (a # xs) n = ListSumTAux xs (n + a)" by (simp)
  also have "\<dots> =n + a + ListSumTAux xs 0" by (subst hyp, rule refl)
  finally have tmp2:"ListSumTAux (a # xs) n = n + a + ListSumTAux xs 0" by simp

  from tmp and tmp2 show ?case by simp 
qed
  
  
lemma helper2 : "ListSumTAux xs n  = n + ListSumTAux xs 0" 
proof (induct xs  arbitrary : n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case  by (metis ListSumTAux.simps(2) semiring_normalization_rules(25) semiring_normalization_rules(5))
qed
  
  
  
theorem "ListSum xs = ListSumT xs" 
proof (induct xs)
  case Nil
  then show ?case by (simp add : ListSumT_def)
next
  case (Cons a xs)
  assume hyp:"ListSum xs = ListSumT xs"
  then show ?case by (metis ListSum.simps(2) ListSumTAux.simps(2) ListSumT_def add_cancel_left_left helper2)
qed

theorem "ListSum xs = ListSumT xs"
proof (induct xs)
  case Nil
  then show ?case by (simp add : ListSumT_def)
next
  case (Cons a xs)
  assume hyp:"ListSum xs = ListSumT xs"
  have " ListSum (a#xs) = a + ListSum xs" by simp
  also have "\<dots> = a + ListSumT xs" using hyp by simp
  also have "\<dots> = a + ListSumTAux xs 0" by (simp add: ListSumT_def)
  also have "\<dots> = ListSumTAux xs a" by (subst helper2, rule refl)
  also have "\<dots> = ListSumTAux (a#xs) 0 " by (simp)
  also have "\<dots> = ListSumT (a#xs)" by (simp only : ListSumT_def)
  finally show ?case by assumption
qed
  