theory Ex2_3
  imports Main 
begin 
  
datatype tree = Tp | Nd tree tree 
  
primrec tips :: "tree \<Rightarrow> nat " where 
  "tips Tp = 1"|
  "tips (Nd l r) = op + (tips l) (tips r)"
  
  
primrec height :: "tree \<Rightarrow> nat" where
  "height Tp = 0"|
  "height (Nd l r) = 1 +  max (height l) (height r)"
  
  
primrec cbt :: "nat \<Rightarrow> tree" where
  "cbt 0 = Tp"|
  "cbt (Suc n) = (let tmp = (cbt n) in Nd tmp tmp)"

  
primrec iscbt :: " (tree \<Rightarrow> 'a) \<Rightarrow> tree  \<Rightarrow> bool" where
  "iscbt f Tp = True"|
  "iscbt f (Nd l r) = (iscbt f l \<and> iscbt f r \<and> (f l = f r))"
 
lemma helper1 : "iscbt height t \<Longrightarrow>  tips t = 2 ^ height t" by  (induction t, simp_all)


lemma helper1_arith : fixes n::nat and m::nat shows  "((2 ^ n :: nat) = (2 ^ m)) = (n = m)" by simp
    
theorem main1 : "iscbt height t = iscbt tips t"
proof (induction t)
  case Tp
  then show ?case by simp
next
  case (Nd t1 t2)
  assume h1:"iscbt height t1 = iscbt tips t1"
    and h2:"iscbt height t2 = iscbt tips t2"
  show ?case 
  proof (cases "iscbt height (Nd t1 t2)")
    case True
    assume c1:"iscbt height (Nd t1 t2)"
    show ?thesis 
    proof (cases "iscbt tips (Nd t1 t2)")
      case True
      with c1 show ?thesis by simp
    next
      case False
      assume c2:"\<not> iscbt tips (Nd t1 t2)"
      from c1 have tmp:"height t1 = height t2" by simp
      from c1 have tmp2:"iscbt height t1" by simp
      from c1 have tmp3:"iscbt height t2" by simp
      then have tmp4:"tips t2 = 2 ^ height t2" by (rule helper1[of t2])
          
      have  "iscbt tips (Nd t1 t2) = (iscbt tips t1 \<and> iscbt tips t2 \<and> (tips t1 = tips t2))"  by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (tips t1 = tips t2))" using h1 h2 by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (2 ^ height t1 = tips t2 ))" using helper1[of t1]  tmp2  by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (2 ^ height t1 = (2 ^ height t2 :: nat)))" by (subst tmp4, rule refl)
      also have  "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (height t1 = height t2 ))" by (simp add : helper1_arith)
      also have "\<dots> = True" using tmp tmp2 tmp3 by simp
      finally have False using c2 by simp
      then show ?thesis by (rule FalseE)
    qed
  next
    case False
    assume c1:"\<not> iscbt height (Nd t1 t2)"
    then show ?thesis 
    proof (cases "iscbt tips (Nd t1 t2)")
      case True
      then show ?thesis using h1 h2 helper1 by simp
    next
      case False
      then show ?thesis using c1 by auto
    qed    
  qed
qed

lemma helper1_tips : "tips t > 0 " by (induction t, simp_all)  
  
lemma helper2 : "iscbt tips t \<Longrightarrow> size t = tips t  - 1"  
proof (induction t)
  case Tp
  then show ?case by simp
next
  case (Nd t1 t2)
  assume hyp1:"iscbt tips t1 \<Longrightarrow> size t1 = tips t1 - 1"
    and hyp2:"iscbt tips t2 \<Longrightarrow> size t2 = tips t2 - 1"
    and hyp3:"iscbt tips (Nd t1 t2)"
  from hyp3 have tmp1:"iscbt tips t1" by simp
  from hyp3 have tmp2:"iscbt tips t2" by simp
  from tmp1 and hyp1 have tmp4:"size t1 = tips t1 - 1" by simp
  from tmp2 and hyp2 have tmp5:"size t2 = tips t2 - 1" by simp
  have "size (Nd t1 t2) = 1 + size t1 + size t2" by simp
  also  have "\<dots> = 1 + (tips t1 - 1) + (tips t2 - 1)" using tmp4 tmp5 by simp
  finally show ?case using helper1_tips 
  by (metis One_nat_def Suc_pred add_Suc add_Suc_right add_cancel_right_left diff_Suc_1 tips.simps(2))
qed
  
  
theorem main2 :"iscbt tips t= iscbt size t" 
proof (induction t)
  case Tp
  then show ?case by simp
next
  case (Nd t1 t2)
  assume hyp1:"iscbt tips t1 = iscbt size t1"
    and hyp2:"iscbt tips t2 = iscbt size t2"
  then show ?case using helper2 proof (cases "iscbt tips (Nd t1 t2)")
    case True
    assume c1:"iscbt tips (Nd t1 t2)"
    show ?thesis 
    proof (cases "iscbt size (Nd t1 t2)")
      case True
      then show ?thesis using c1 by simp
    next
      case False
      then show ?thesis using hyp1 hyp2 helper2 by auto
    qed
  next
    case False
    assume c1:"\<not> iscbt tips (Nd t1 t2)"
    show ?thesis 
    proof (cases "iscbt size (Nd t1 t2)")
      case True
      assume c2:"iscbt size (Nd t1 t2)"
      with  hyp1 have tmp1:"iscbt tips t1" by simp
      from c2 and hyp2 have tmp2:"iscbt tips t2" by simp
          
      have tmp3:"size t1 = tips t1 - 1" using tmp1 helper2 by simp
      have tmp4:"size t2 = tips t2 - 1" using tmp2 helper2 by simp
          
      have "size t1 = size t2" using c2 by simp    
          
      with tmp3 tmp4 have "tips t1 - 1= tips t2 - 1" using c2  by simp
      hence "tips t1 = tips t2" using helper1_tips[of t1] helper1_tips[of t2] by simp
      then show  ?thesis using tmp1 tmp2 hyp1 hyp2 helper2 by simp 
    next
      case False
      then show ?thesis using c1 by auto
    qed
  qed  
qed
  
theorem main3 :"iscbt height t = iscbt size t" using main1 main2 by simp
    
theorem main4: "iscbt height (cbt n)" 
  using [[simp_trace_new mode=full]]
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume hyp:"iscbt height (cbt n)"
  have " iscbt height (cbt (Suc n)) = iscbt height ((let tmp = (cbt n) in Nd tmp tmp))" by simp
  also have "\<dots> = iscbt height (Nd (cbt n) (cbt n))" by (simp only : Let_def)
  finally  show ?case using hyp by simp
qed
  
theorem "iscbt size (cbt n)" using main4 main3 by simp
    
theorem "iscbt tips (cbt n)" using main4 main1 by simp
    
theorem "iscbt f (cbt n)" by (induction n; simp add : Let_def)
    
    
theorem "iscbt height t \<Longrightarrow> t = (cbt (height t))"  by (induction t; simp add : Let_def)
thm cong
theorem "iscbt (\<lambda> x . True) \<noteq>  iscbt size"  
proof (rule notI)
  assume h1:" iscbt (\<lambda>x. True) = iscbt size"
  let ?tmp = "Nd (Nd Tp Tp) Tp"
  have "?tmp = ?tmp" by (rule refl)
  with h1 have " iscbt (\<lambda>x. True) ?tmp = iscbt size ?tmp" by (rule cong)
  thus False by simp
qed
  