theory Ex3_1
  imports Main 
begin 

primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "pow _ 0 = 1"|
  "pow b (Suc e) = b * pow b e"
  
lemma lem1 : "pow 1 n = 1" by (induction n ; simp)  
    
lemma lem2 : "pow x (n + m) = pow x n * pow x m" 
proof (induction n arbitrary : m)
  case 0
  then show ?case by simp
next
  case (Suc n)
    assume hyp:"\<And> m . pow x (n + m) = pow x n * pow x m"
  then show ?case by simp
qed
  
    
theorem pow_mult : "pow x (m * n) = pow (pow x m) n" 
proof (induction m)
  case 0
  then show ?case using lem1 by simp
next
  case (Suc m)
  assume hyp:"pow x (m * n) = pow (pow x m) n"
  have "pow x (Suc m * n) = pow x ((m + 1) * n)" by simp
  also have "\<dots> = pow x (m * n + n)" by (simp add: semiring_normalization_rules(2))
  also have "\<dots> = pow x (m * n) * pow x n"  by (simp add : lem2)
  also have "\<dots> =  pow (pow x m) n * pow x n" by (simp add : hyp)
      
      
  show ?case 
qed
  