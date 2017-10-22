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
    also have "\<dots> =  m + (m - 1) + (m  - 1)*n + (m - (Suc n))* n + (m - Suc n) * (m - Suc n)" by (simp add: c1 algebra_simps mult_eq_if)
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


definition "eq1 (n::nat) = (n -5)*(n-5 + 10) + 25" 
definition "eq2 (n::nat) = (n div 10 )* (n div 10 + 1) * 100 + 25"


lemma helper2:"(n::nat) mod 10 = 5 \<Longrightarrow>  n div 10 * 10 = n - 5" by (metis minus_mod_eq_div_mult)

theorem "(n::nat) mod 10 = 5 \<Longrightarrow>  n*n  = (n div 10 )* (n div 10 + 1) * 100 + 25" 
proof -
  assume hyp:"n mod 10 = 5"
  hence tmp:"5 \<le> n" by simp


  from tmp have tmp2:"(n - 5)*(n - 5) = n*n + 25 - 10*n" 
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume hyp1:"5 \<le> n \<Longrightarrow> (n - 5) * (n - 5) = n * n + 25 - 10 * n"
       and hyp2:"5 \<le> Suc n"
    then show ?case 
    proof (cases "n = 4")
      case True
      then show ?thesis by simp 
    next
      case False
      assume c1:"n \<noteq> 4"
      with hyp2 have tmp:"5 \<le> n" by simp
      with hyp1 have tmp2:" (n - 5) * (n - 5) = n * n + 25 - 10 * n" by simp

      have tmp3:"Suc n - 5 = Suc (n - 5)" 
      proof -
        have "Suc n - 5 = 1 + n - 5" by simp
        also have "\<dots> = 1+ (n - 5)" using tmp by simp
        also have "\<dots> = Suc (n - 5)" by simp
        finally show ?thesis by assumption
      qed

      from tmp have h:"n * n + 25 \<ge> n*10" 
      proof  (induction n)
        case 0
        then show ?case by simp
      next
        case (Suc n)
        assume a:"5 \<le> n \<Longrightarrow> n * 10 \<le> n * n + 25"
           and b:"5 \<le> Suc n"
        then show ?case
        proof (cases "n = 4")
          case True
          then show ?thesis by simp
        next
          case False
          with b have c:"5 \<le> n" by simp
          with a have d:"n * 10 \<le> n * n + 25" by simp
          have "Suc n + n  > 10" using c by simp
          with c d show ?thesis by simp
        qed
      qed

      have "(Suc n - 5) * (Suc n - 5) =  (n + 1 - 5)* ( n + 1 - 5)" using hyp2 by simp
      also have "\<dots> = Suc n * Suc n + 25 - 10*Suc n" using tmp tmp2 tmp3 algebra_simps h by simp
      finally show ?thesis by assumption
    qed
  qed

  from tmp have tmp3:"n*n + 25 \<ge> 10*n" 
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume a:"5 \<le> n \<Longrightarrow> 10 * n \<le> n * n + 25"
       and b:"5 \<le> Suc n"
    then show ?case 
    proof (cases "n = 4")
      case True
      then show ?thesis by simp
    next
      case False
      assume c:"n \<noteq>4"
      from c and b have d:"5 \<le> n" by simp
      with a have e:"10 * n \<le> n * n + 25" by simp
      have "Suc n + n \<ge> 10" using d by simp 
      with d e show ?thesis by simp
    qed
  qed

  from tmp have tmp4:"n*n \<ge> 25" 
  proof (induction n )
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume a:"5 \<le> n \<Longrightarrow> 25 \<le> n * n"
       and b:"5 \<le> Suc n"
    then show ?case 
    proof (cases "n = 4")
      case True
      then show ?thesis by simp
    next
      case False
      with b have "5 \<le> n" by simp
      with a have "25 \<le> n*n" by simp
      then show ?thesis by simp
    qed
  qed

  have "(n div 10 )* (n div 10 + 1) * 100 + 25 = (n div 10 )*  Suc (n div 10 ) * 100 + 25" by simp
  also have "\<dots> = n div 10 * 10 *10 + (n div 10 )*  (n div 10 ) * 100 + 25 " using algebra_simps  by simp
  also have "\<dots> = (n - 5 ) *10 + (n div 10 ) * (n div 10  ) * 10  * 10 + 25" using hyp  by (simp add : helper2 )
  also have "\<dots> = (n - 5 ) *10 + (n div 10  * 10)  * (n div 10 * 10)   + 25" by simp
  also have "\<dots> = n*n + 10*n -25 - 10*n + 25" using tmp tmp3 tmp2 hyp helper2 algebra_simps by simp
  also have "\<dots> = n*n " using tmp4 by simp
  finally show ?thesis by (rule sym)
qed


theorem "sq((10 * n) + 5) = ((n * (Suc n)) * 100) + 25" 
proof (induction n)
case 0
  then show ?case by (simp add : sq_def)
next
  case (Suc n)
  then show ?case by (simp add: sq_def algebra_simps)
qed
