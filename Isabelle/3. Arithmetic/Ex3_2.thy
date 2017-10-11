theory Ex3_2
  imports Main 
begin 
  
  
primrec sq :: "nat \<Rightarrow> nat" where 
  "sq 0 = 0"|
  "sq (Suc n) = sq n + n + (Suc n)"
  
theorem "sq n = n * n" by (induction n ; simp)
    
    
definition mm2 ::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "mm2 base value \<equiv> let diff = value - base ; qdiff = diff * diff in (value + diff)  * base + qdiff"
  
declare mm2_def [simp]  
  

  
theorem " n \<le> m   \<Longrightarrow>  mm2 n m = m * m" 
proof (induction n arbitrary : m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume hyp:"\<And>m . n \<le> m \<Longrightarrow> mm2 n m = m * m"
    and hyp2:"Suc n \<le> m"
  then show ?case 
  proof (cases "m = 0")
    case True
    then show ?thesis using hyp2 by simp
  next
    case False
      assume c1:"m \<noteq> 0"
      
    from hyp[of "m - 1"] hyp2 have tmp':"mm2 n (m - 1) = (m - 1) * (m - 1)" by simp
      
    have "mm2 n (m - 1) = (let diff = (m-1) - n ; qdiff = diff * diff in ((m - 1) + diff)  * n + qdiff)" by simp
    also have " \<dots> = ((m - 1) + ((m - 1) - n)) * n + ((m -1) -n)* ((m - 1) -n)"  by (simp only : Let_def)
    also have "\<dots> = (m - 1 + (m  - Suc n)) * n + (m - Suc n)* (m  - Suc n)" by simp
    also have "\<dots> = (m - 1) * n + (m - Suc n)* n + (m - Suc n) * (m - Suc n)" using distrib_right by simp
    finally have tmp:"mm2 n (m - 1) =  (m - 1) * n + (m - Suc n)* n + (m - Suc n) * (m - Suc n)"  by assumption

    have tmp2:"m * m = m + (m - 1) + (m - 1) * (m - 1)" by (induction m; simp)
     
    have "mm2 (Suc n) m =(let diff = m - (Suc n) ; qdiff = diff * diff in (m + diff)  * (Suc n) + qdiff)" by simp
    also have "\<dots> = (m + (m- (Suc n))) * (Suc n) + (m - Suc n) * (m - Suc n)" by (simp only : Let_def) 
    also have "\<dots> = (m + m- (Suc n)) * (Suc n) + (m - Suc n) * (m - Suc n)" using hyp2 by simp
    also have "\<dots> = (m + m - (Suc n)) + (m + m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by simp
    also have "\<dots> = m + (m - 1) - n + (m + m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by simp
    also have "\<dots> = m + (m - 1) - n + (m + (m - (Suc n)))* n + (m - Suc n) * (m - Suc n)" using hyp2 by simp
    also have "\<dots> = m + (m - 1) - n + m * n + (m - (Suc n))* n + (m - Suc n) * (m - Suc n) " by (simp add: distrib_right)
    also have "\<dots> =  m + (m - 1) +m * n - n + (m - (Suc n))* n + (m - Suc n) * (m - Suc n) " using Suc_leD hyp2 le_add1 order_trans ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 by simp
    also have "\<dots> =  m + (m - 1) +(m*n  - n) + (m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by (simp add: c1 mult_eq_if)
    also have "\<dots> = m + (m - 1) + (m*n  - 1*n) + (m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by simp
    also have "\<dots> =  m + (m - 1) + (m  - 1)*n + (m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by (simp add: left_diff_distrib')
    finally have tmp3:"mm2 (Suc n) m = m + (m - 1) + (m  - 1)*n + (m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by assumption
    show ?thesis using tmp tmp2 tmp3 tmp' by simp
  qed    
qed
  
lemma helper : "m \<le> n \<longrightarrow> sq n =  ((n + (n - m)) * m)  + sq (n - m)"
proof (induction n arbitrary : m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (cases m ; simp)
qed
  
theorem "100 \<le> n \<Longrightarrow> sq n =  ((n + (n - 100)) * 100)  + sq (n - 100)"using helper by (induction n; simp)
    
    
theorem ""
  