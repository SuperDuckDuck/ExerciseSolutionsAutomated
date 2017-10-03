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
  
lemma lem3 :  "pow (x * y) n = pow x n * pow y n" by (induction n; simp)
  
  
    
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
  finally have tmp:"pow x (Suc m * n) = pow (pow x m) n * pow x n" by assumption 
  have "pow (pow x (Suc m)) n = pow (x * pow x  m) n" by simp
  also have "\<dots> = pow x n * pow (pow x m) n" using lem3 by simp 
  finally show ?case using tmp by simp
qed
  
  
primrec sum :: "nat list \<Rightarrow> nat" where 
  "sum [] = 0"|
  "sum (x#xs) = x + sum xs"
  
lemma lem4 : "sum (xs @ ys) = sum xs + sum ys" by (induction xs ; simp)  
  
theorem sum_rev : "sum (rev ns) = sum ns"  by (induction ns ; simp add : lem4)
    
primrec Sum :: "(nat \<Rightarrow> nat ) \<Rightarrow> nat \<Rightarrow> nat" where 
  "Sum f 0 = 0"|
  "Sum f (Suc k) = f k + Sum f k"
  
theorem "Sum (\<lambda>i . f i + g i) k  = Sum f k + Sum g k" by (induction k ; simp)
    
theorem "Sum f (k + l) = Sum f k + Sum (\<lambda>x .f  (k + x)) l" by (induction l; simp)
    
theorem "Sum f k = sum (map f [0 ..<k])" 
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case by (simp add: lem4)
qed
  
  